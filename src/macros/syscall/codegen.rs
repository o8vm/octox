//! Code generation for syscall derive macros.
//!
//! This module implements the final phase of macro processing, converting the
//! intermediate representation into actual Rust code. It generates userspace
//! syscall wrappers, kernel dispatch logic, and type conversion implementations.

include!("../common/quote.rs");
use super::ir;
use crate::syscall::ir::{ArchSpec, ValueType};

/// Generates complete syscall implementation code from the IR.
///
/// This function orchestrates the generation of all necessary code components:
/// - Type conversion traits and implementations
/// - Userspace syscall wrapper functions  
/// - Kernel dispatch and handling logic
/// - TrapFrame core functionality
///
/// # Arguments
/// * `registry` - The syscall registry containing all parsed syscall information
///
/// # Returns
/// A TokenStream containing all generated implementation code
pub fn emit(registry: &ir::SyscallRegistry) -> TokenStream {
    let mut stream = TokenStream::new();

    // Generate conversion traits and implementations
    stream.extend(emit_conversion_traits(registry));

    // Generate TrapFrameCore
    stream.extend(emit_trapframe_core());

    stream.extend(emit_trait(registry));

    stream.extend(emit_from_usize(registry));

    stream
}

/// Generates the main trait implementation containing both userspace and kernel code.
///
/// This function creates conditional compilation blocks that generate different
/// code for userspace and kernel environments, providing the appropriate syscall
/// interfaces for each context.
///
/// # Arguments
/// * `registry` - The syscall registry with all syscall definitions
///
/// # Returns
/// TokenStream containing the trait implementation
fn emit_trait(registry: &ir::SyscallRegistry) -> TokenStream {
    let enum_name = &registry.name;
    let mut user_methods = TokenStream::new();

    for syscall in &registry.syscalls {
        user_methods.extend(emit_syscall_method(syscall));
    }

    let dispatch_body = emit_dispatch_body(registry);
    let syscall_signatures = emit_syscall_signature(registry);

    quote!(
        #[cfg(all(target_os = "none", feature = "user"))]
        impl @enum_name {
            #user_methods
        }

        #[cfg(all(target_os = "none", feature = "kernel"))]
        trait SyscallDispatch {
            fn copyin<T: ?Sized + AsBytes>(dst: &mut T, src: usize) -> Result<()> {
                unimplemented!("copyin must be implemented by kernel")
                }

            fn dispatch(tf: &mut TrapFrameCore) -> Result<()> {
                #dispatch_body
            }

            fn copyout<T: ?Sized + AsBytes>(dst: usize, src: &T) -> Result<()> {
                unimplemented!("copyout must be implemented by kernel")
            }

            #syscall_signatures
        }

        #[cfg(all(target_os = "none", feature = "kernel"))]
        impl SyscallDispatch for @enum_name {}
    )
}

fn emit_conversion_traits(registry: &ir::SyscallRegistry) -> TokenStream {
    // Collect all unique return types from syscalls
    let mut return_types = std::collections::HashSet::new();

    for syscall in &registry.syscalls {
        if let ir::ReturnType::Result(Some(ty)) = &syscall.ret {
            return_types.insert(ty.clone());
        }
    }

    let mut stream = TokenStream::new();

    // Define conversion traits
    stream.extend(quote!(
        /// Trait for converting to isize at syscall boundaries
        pub trait IntoIsize {
            fn into_isize(self) -> isize;
        }

        /// Trait for converting from isize at syscall boundaries
        pub trait FromIsize: Sized {
            fn from_isize(val: isize) -> Self;
        }

        // Basic IntoIsize implementations
        impl IntoIsize for () {
            fn into_isize(self) -> isize {
                0
            }
        }

        impl IntoIsize for usize {
            fn into_isize(self) -> isize {
                self as isize
            }
        }

        // Basic FromIsize implementations
        impl FromIsize for () {
            fn from_isize(_: isize) -> Self {
                ()
            }
        }

        impl FromIsize for usize {
            fn from_isize(val: isize) -> Self {
                val as usize
            }
        }
    ));

    // Generate conversion implementations for types that appear in Result<T>
    for ty in return_types {
        match ty {
            ValueType::Fd => {
                stream.extend(quote!(
                    impl IntoIsize for Fd {
                        fn into_isize(self) -> isize {
                            self.0 as isize
                        }
                    }

                    impl FromIsize for Fd {
                        fn from_isize(val: isize) -> Self {
                            Fd(val as usize)
                        }
                    }
                ));
            }
            ValueType::PId => {
                stream.extend(quote!(
                    impl IntoIsize for PId {
                        fn into_isize(self) -> isize {
                            self.0 as isize
                        }
                    }

                    impl FromIsize for PId {
                        fn from_isize(val: isize) -> Self {
                            PId(val as usize)
                        }
                    }
                ));
            }
            ValueType::Usize => {
                // Already implemented above
            }
            _ => {
                // Generate for other numeric types if needed
                let type_name = Ident::new(&ty.to_string(), Span::call_site());
                stream.extend(quote!(
                    impl IntoIsize for @type_name {
                        fn into_isize(self) -> isize {
                            self as isize
                        }
                    }

                    impl FromIsize for @type_name {
                        fn from_isize(val: isize) -> Self {
                            val as @type_name
                        }
                    }
                ));
            }
        }
    }

    // Result type implementations for syscalls
    stream.extend(quote!(
        impl<T: IntoIsize> IntoIsize for Result<T> {
            fn into_isize(self) -> isize {
                match self {
                    Ok(v) => v.into_isize(),
                    Err(e) => e as isize,
                }
            }
        }

        impl<T: FromIsize> FromIsize for Result<T> {
            fn from_isize(val: isize) -> Self {
                if val >= 0 {
                    Ok(T::from_isize(val))
                } else {
                    Err(Error::from(val))
                }
            }
        }
    ));

    stream
}

fn emit_trapframe_core() -> TokenStream {
    quote!(
        // Architecture-specific constants
        #[cfg(target_arch = "aarch64")]
        pub mod arch {
            pub const SYSCALL_REG: usize = 8;    // x8
            pub const RETURN_REG: usize = 0;     // x0
            pub const ARG_REGS: &[usize] = &[0, 1, 2, 3, 4, 5]; // x0-x5
            pub const SP_REG: usize = 31;        // sp (conceptual)
        }

        #[cfg(target_arch = "riscv64")]
        pub mod arch {
            pub const SYSCALL_REG: usize = 17;   // a7 (x17)
            pub const RETURN_REG: usize = 10;    // a0 (x10)
            pub const ARG_REGS: &[usize] = &[10, 11, 12, 13, 14, 15]; // a0-a5
            pub const SP_REG: usize = 2;         // x2/sp
        }

        #[repr(C)]
        pub struct TrapFrameCore {
            #[cfg(target_arch = "aarch64")]
            pub regs: [usize; 31],    // x0-x30 (AArch64)
            #[cfg(target_arch = "riscv64")]
            pub regs: [usize; 32],    // x0-x31 (RISC-V)

            pub sp: usize,            // Stack pointer
            pub pc: usize,            // Program counter
        }

        impl TrapFrameCore {
            pub fn syscall_num(&self) -> usize {
                use arch::SYSCALL_REG;
                self.regs[SYSCALL_REG]
            }

            pub fn arg(&self, n: usize) -> usize {
                use arch::ARG_REGS;
                ARG_REGS.get(n).map(|&reg_idx| self.regs[reg_idx]).unwrap_or(0)
            }

            pub fn set_return(&mut self, val: usize) {
                use arch::RETURN_REG;
                self.regs[RETURN_REG] = val;
            }

            pub fn set_syscall_num(&mut self, val: usize) {
                use arch::SYSCALL_REG;
                self.regs[SYSCALL_REG] = val;
            }

            #[cfg(target_arch = "aarch64")]
            pub fn new() -> Self {
                Self {
                    regs: [0; 31],
                    sp: 0,
                    pc: 0,
                }
            }

            #[cfg(target_arch = "riscv64")]
            pub fn new() -> Self {
                Self {
                    regs: [0; 32],
                    sp: 0,
                    pc: 0,
                }
            }
        }
    )
}

fn emit_syscall_method(syscall: &ir::Syscall) -> TokenStream {
    let rust_name = &syscall.rust_name;
    let params = emit_method_params(&syscall.params);
    let ret = emit_return_type(&syscall.ret);
    let user_body = emit_user_body(syscall);

    quote!(
        fn @rust_name(#params) #ret {
            #user_body
        }
    )
}

fn emit_method_params(params: &[ir::Param]) -> TokenStream {
    let mut out = TokenStream::new();

    for (i, param) in params.iter().enumerate() {
        if i > 0 {
            out.extend(quote!(,));
        }
        let name = &param.rust_name;
        let typ = emit_type(&param.ty);
        out.extend(quote!(@name: #typ));
    }
    out
}

fn emit_type(ty: &ir::Type) -> TokenStream {
    match ty {
        ir::Type::Value(val) => emit_value_type(val),
        ir::Type::Ptr { inner, mutable } => {
            let inner_ty = emit_type(inner);
            if *mutable {
                quote!(*mut #inner_ty)
            } else {
                quote!(*const #inner_ty)
            }
        }
        ir::Type::Ref { inner, mutable } => {
            let inner_ty = emit_type(inner);
            if *mutable {
                quote!(&mut #inner_ty)
            } else {
                quote!(&#inner_ty)
            }
        }
        ir::Type::Slice { inner, mutable } => {
            let inner_ty = emit_type(inner);
            if *mutable {
                quote!(&mut [#inner_ty])
            } else {
                quote!(&[#inner_ty])
            }
        }
        ir::Type::Str { mutable } => {
            if *mutable {
                quote!(&mut str)
            } else {
                quote!(&str)
            }
        }
        ir::Type::Option { inner } => {
            let inner_ty = emit_type(inner);
            quote!(Option<#inner_ty>)
        }
        ir::Type::Custom(tokens) => {
            // use original tokens for custom types
            tokens.clone()
        }
    }
}

fn emit_value_type(val: &ir::ValueType) -> TokenStream {
    match val {
        &ir::ValueType::Fd => quote!(Fd),
        &ir::ValueType::PId => quote!(PId),
        _ => {
            let s = val.to_string();
            let ident = Ident::new(&s, Span::call_site());
            quote!(@ident)
        }
    }
}

fn emit_return_type(ret: &ir::ReturnType) -> TokenStream {
    match ret {
        ir::ReturnType::Never => quote!(-> !),
        ir::ReturnType::Result(None) => quote!(-> Result<()>),
        ir::ReturnType::Result(Some(ty)) => {
            let inner_ty = emit_value_type(ty);
            quote!(-> Result<#inner_ty>)
        }
    }
}

/// Generates userspace syscall implementation using inline assembly.
///
/// This function creates architecture-specific assembly code for making system calls
/// from userspace applications. It handles register allocation and calling conventions
/// for each target architecture.
///
/// # Arguments
/// * `syscall` - The syscall definition containing ID, parameters, and return type
///
/// # Returns
/// TokenStream containing the userspace syscall implementation
fn emit_user_body(syscall: &ir::Syscall) -> TokenStream {
    // Generate code with target-time architecture detection
    // (not host-time detection like proc_macro execution)
    let aarch64_body = emit_user_body_generic::<ir::Aarch64>(syscall);
    let riscv64_body = emit_user_body_generic::<ir::RiscV64>(syscall);

    quote!(
        #[cfg(target_arch = "aarch64")]
        {
            #aarch64_body
        }
        #[cfg(target_arch = "riscv64")]
        {
            #riscv64_body
        }
        #[cfg(not(any(target_arch = "aarch64", target_arch = "riscv64")))]
        {
            #aarch64_body
        }
    )
}

/// Generates architecture-specific userspace syscall implementation.
///
/// This function creates the actual inline assembly code for making system calls,
/// handling register assignments, syscall instructions, and return value processing
/// according to the calling conventions of the target architecture.
///
/// # Type Parameters
/// * `A` - Architecture specification implementing ArchSpec trait
///
/// # Arguments
/// * `syscall` - The syscall definition to generate code for
///
/// # Returns
/// TokenStream containing the complete syscall implementation with safety comments
fn emit_user_body_generic<A: ArchSpec>(syscall: &ir::Syscall) -> TokenStream {
    let syscall_id = Literal::u16_unsuffixed(syscall.id.0);
    let insn = Literal::string(A::INSN);
    let syscall_reg = Literal::string(A::SYSCALL_REGS);
    let out_reg = Literal::string(A::OUT_REGS);

    let reg_assignments = emit_register_assignments::<A>(&syscall.params);

    match &syscall.ret {
        ir::ReturnType::Never => {
            quote!(
                // SAFETY: System call safety conditions:
                // - Register constraints are correctly specified
                // - noreturn option ensures no subsequent code execution
                unsafe {
                    core::arch::asm!(
                        @insn,
                        in(@syscall_reg) @syscall_id,
                        #reg_assignments
                        options(noreturn)
                    );
                }
            )
        }
        _ => {
            let ret_conversion = emit_return_conversion(&syscall.ret);
            quote! {
                let _ret: isize;
                // SAFETY: System call safety conditions:
                // - Input registers are read-only
                // - Output register is correctly specified with lateout
                unsafe {
                    core::arch::asm!(
                        @insn,
                        in(@syscall_reg) @syscall_id,
                        #reg_assignments
                        lateout(@out_reg) _ret,
                    );
                }
                <#ret_conversion>::from_isize(_ret)
            }
        }
    }
}

/// Generates register assignments for syscall parameters.
///
/// This function maps syscall parameters to appropriate CPU registers according to
/// the target architecture's calling convention. It handles different parameter types
/// including values, references, slices, and optional types with proper pointer handling.
///
/// # Type Parameters
/// * `A` - Architecture specification implementing ArchSpec trait
///
/// # Arguments
/// * `params` - Array of syscall parameters to map to registers
///
/// # Returns
/// TokenStream containing register assignment code for inline assembly
///
/// # Type Handling
/// - Value types: Passed directly as usize
/// - Fd/PId types: Extract inner value (.0)
/// - References: Passed as pointer addresses
/// - Slices/Strings: Passed as fat pointer addresses (&name)
/// - Options: Passed as memory addresses for proper Some(0)/None distinction
fn emit_register_assignments<A: ArchSpec>(params: &[ir::Param]) -> TokenStream {
    let mut assignments = TokenStream::new();

    // Use only the registers needed for the actual parameters
    for (param, &reg) in params.iter().zip(A::IN_REGS) {
        let reg_lit = Literal::string(reg);
        let name = &param.rust_name;

        let assignment = match &param.ty {
            ir::Type::Value(ValueType::Fd | ValueType::PId) => {
                quote!(in(@reg_lit) @name.0 as usize,)
            }
            ir::Type::Value(_) => {
                quote!(in(@reg_lit) @name as usize,)
            }
            ir::Type::Ptr { .. } => {
                quote!(in(@reg_lit) @name as usize,)
            }
            ir::Type::Ref { .. } => {
                // Reference types are passed as simple pointer addresses
                quote!(in(@reg_lit) @name as *const _ as usize,)
            }
            ir::Type::Slice { .. } | ir::Type::Str { .. } => {
                // Slice types are passed as fat pointer addresses
                quote!(in(@reg_lit) &@name as *const _ as usize,)
            }
            ir::Type::Option { inner } => {
                match inner.as_ref() {
                    ir::Type::Slice { .. } | ir::Type::Str { .. } => {
                        // Option<&[T]> and Option<&str> passed as fat pointer addresses
                        quote!(in(@reg_lit) &@name as *const _ as usize,)
                    }
                    ir::Type::Ref { .. } => {
                        // Option<&T> passed as reference addresses
                        quote!(in(@reg_lit) &@name as *const _ as usize,)
                    }
                    ir::Type::Value(_) => {
                        // Option<numeric types> placed in memory and passed as pointer
                        // This approach correctly distinguishes Some(0) from None
                        quote!(in(@reg_lit) &@name as *const _ as usize,)
                    }
                    _ => {
                        // Unsupported Option inner types
                        quote!(compile_error!("Option can contain only ref, slice and value types");)
                    }
                }
            }
            ir::Type::Custom(_) => {
                // Custom types should not appear directly as parameters
                // They should be wrapped in Ref
                quote!(compile_error!("Custom types must be passed by reference");)
            }
        };
        assignments.extend(assignment);
    }
    assignments
}

fn emit_return_conversion(ret: &ir::ReturnType) -> TokenStream {
    match ret {
        ir::ReturnType::Never => quote!(unreachable!()),
        ir::ReturnType::Result(None) => quote!(Result<()>),
        ir::ReturnType::Result(Some(ty)) => {
            let inner_ty = emit_value_type(ty);
            quote!(Result<#inner_ty>)
        }
    }
}

/// Generates syscall dispatcher implementation for kernel-side handling.
///
/// This function creates the main dispatch logic that routes incoming system calls
/// to appropriate handler functions based on the syscall number. It handles argument
/// extraction, type conversion, and result processing.
///
/// # Arguments
/// * `registry` - The syscall registry containing all syscall definitions
///
/// # Returns
/// TokenStream containing the complete dispatch implementation
fn emit_dispatch_body(registry: &ir::SyscallRegistry) -> TokenStream {
    let mut match_arms = TokenStream::new();

    for syscall in &registry.syscalls {
        let id = Literal::u16_unsuffixed(syscall.id.0);
        let handler = emit_syscall_handler(syscall);
        match_arms.extend(quote!(@id => {
            let handler_result = #handler;
            handler_result.into_isize()
        },));
    }

    quote!(
        let result_isize = match tf.syscall_num() as u16 {
            #match_arms
            _ => Error::ENOSYS as isize,
        };

        tf.set_return(result_isize as usize);
        Ok(())
    )
}

/// Generates individual syscall handler for kernel dispatch.
///
/// This function creates the argument fetching and method calling logic for a single
/// Emits the complete syscall handler implementation for a specific system call.
///
/// This function generates the kernel-side handler function that serves as the entry
/// point for syscall execution from userspace. It converts raw trap frame register
/// values into typed parameters, invokes the actual syscall implementation, and
/// handles return value processing including special cases for mutable references.
/// For syscalls with mutable reference parameters, it performs copyout operations
/// to write modified data back to userspace memory.
///
/// # Arguments
/// * `syscall` - The syscall definition containing name, parameters, and return type
///
/// # Returns
/// TokenStream containing the complete syscall handler implementation
///
/// # Generated Handler Structure
/// - Argument extraction from trap frame registers
/// - Type conversion and validation for complex types
/// - Syscall function invocation with converted arguments
/// - Copyout operations for mutable reference parameters
/// - Error handling and return value encoding
fn emit_syscall_handler(syscall: &ir::Syscall) -> TokenStream {
    let method = &syscall.rust_name;
    let args_fetch = emit_handler_args(&syscall.params);
    let args_pass = emit_args_conversion(&syscall.params);

    // Check for mutable reference parameters requiring special handling
    let mut has_mutable_ref = false;
    let mut mutable_ref_index = 0;

    for (i, param) in syscall.params.iter().enumerate() {
        if let ir::Type::Ref {
            mutable: true,
            inner: _,
        } = &param.ty
        {
            has_mutable_ref = true;
            mutable_ref_index = i;
            break;
        }
    }

    if has_mutable_ref {
        let arg_name = Ident::new(&format!("arg{}", mutable_ref_index), Span::call_site());
        let arg_ptr_name = Ident::new(&format!("arg{}_ptr", mutable_ref_index), Span::call_site());

        quote!({
            #args_fetch
            let result = Self::@method(#args_pass)?;

            Self::copyout(@arg_ptr_name, &@arg_name)?;

            Ok(result)
        })
    } else {
        quote!({
            #args_fetch
            Self::@method(#args_pass)
        })
    }
}

/// Generates argument fetching code for kernel-side syscall handlers.
///
/// This function creates code to extract and convert raw register values into
/// typed parameters suitable for kernel syscall implementations. It handles
/// complex parameter types including slices, strings, and nested optional types
/// with proper memory copying from userspace.
///
/// # Arguments
/// * `params` - Array of syscall parameters to generate fetching code for
///
/// # Returns
/// TokenStream containing argument fetching and conversion code
///
/// # Parameter Type Handling
/// - Value types: Direct register value extraction
/// - References: copyin from userspace memory addresses
/// - Slices: Fat pointer resolution and buffer allocation
/// - Strings: Fat pointer resolution with UTF-8 validation
/// - Options: Null pointer checking with recursive type handling
fn emit_handler_args(params: &[ir::Param]) -> TokenStream {
    let mut args = TokenStream::new();

    for (i, param) in params.iter().enumerate() {
        let arg_name_owned = Ident::new(&format!("_arg{}", i), Span::call_site());
        let arg_name = Ident::new(&format!("arg{}", i), Span::call_site());
        let index = Literal::usize_unsuffixed(i);

        let fetch = match &param.ty {
            ir::Type::Value(ir::ValueType::Fd) => {
                quote!(let @arg_name = Fd(tf.arg(@index));)
            }
            ir::Type::Value(ir::ValueType::PId) => {
                quote!(let @arg_name = PId(tf.arg(@index));)
            }
            ir::Type::Value(_) => {
                quote!(let @arg_name = tf.arg(@index) as _;)
            }
            ir::Type::Ptr { .. } => {
                // Raw pointers interpreted as userspace addresses
                quote!(let @arg_name = tf.arg(@index) as _;)
            }
            ir::Type::Ref { inner, mutable } => {
                let inner_ty = emit_type(inner);

                if *mutable {
                    let arg_ptr_name = Ident::new(&format!("arg{}_ptr", i), Span::call_site());
                    quote!(
                        let @arg_ptr_name = tf.arg(@index);
                        let mut @arg_name: #inner_ty = Default::default();
                        Self::copyin(&mut @arg_name, @arg_ptr_name)?;
                    )
                } else {
                    quote!(
                        let @arg_name = {
                            let addr = tf.arg(@index);
                            let mut value: #inner_ty = Default::default();
                            Self::copyin(&mut value, addr)?;
                            value
                        };
                    )
                }
            }
            ir::Type::Slice { inner, mutable } => {
                match inner.as_ref() {
                    // Handle &[&str] - array of string references
                    ir::Type::Str { .. } => {
                        let let_keyword = if *mutable {
                            quote!(let mut)
                        } else {
                            quote!(let)
                        };
                        quote!(
                            #let_keyword @arg_name_owned = {
                                let mut fat: (*const (*const u8, usize), usize) = (core::ptr::null(), 0);
                                Self::copyin(&mut fat, tf.arg(@index))?;

                                let mut str_fats: Vec<(*const u8, usize)> = vec![(core::ptr::null(), 0usize); fat.1];
                                Self::copyin(&mut str_fats[..], fat.0 as usize)?;

                                let mut string_vec = Vec::with_capacity(fat.1);
                                for str_fat in str_fats {
                                    let mut buf = vec![0u8; str_fat.1];
                                    Self::copyin(&mut buf[..], str_fat.0 as usize)?;

                                    let s = String::from_utf8(buf)
                                        .map_err(|_| Error::EINVAL)?;
                                    string_vec.push(s);
                                }
                                string_vec
                            };
                            #let_keyword @arg_name: Vec<&str> = @arg_name_owned.iter().map(String::as_str).collect();
                        )
                    }
                    // Handle &[T] for other types
                    _ => {
                        let inner_ty = emit_type(inner);
                        let let_keyword = if *mutable {
                            quote!(let mut)
                        } else {
                            quote!(let)
                        };
                        quote!(
                            #let_keyword @arg_name = {
                                let mut fat: (*const #inner_ty, usize) = (core::ptr::null(), 0);
                                Self::copyin(&mut fat, tf.arg(@index))?;

                                let mut buf = vec![Default::default(); fat.1];
                                Self::copyin(&mut buf[..], fat.0 as usize)?;

                                buf
                            };
                        )
                    }
                }
            }
            ir::Type::Str { mutable } => {
                let let_keyword = if *mutable {
                    quote!(let mut)
                } else {
                    quote!(let)
                };
                quote!(
                    #let_keyword @arg_name_owned =  {
                        let mut fat: (*const u8, usize) = (core::ptr::null(), 0);
                        Self::copyin(&mut fat, tf.arg(@index))?;

                        let mut buf = vec![0u8; fat.1];
                        Self::copyin(&mut buf[..], fat.0 as usize)?;

                        String::from_utf8(buf)
                            .map_err(|_| Error::EINVAL)?
                    };
                    #let_keyword @arg_name = @arg_name_owned.as_str();
                )
            }
            ir::Type::Option { inner } => {
                match inner.as_ref() {
                    ir::Type::Slice {
                        inner: inner_slice, ..
                    } => {
                        match inner_slice.as_ref() {
                            // Handle Option<&[Option<&str>]> - optional array of optional strings
                            ir::Type::Option { inner: opt_inner } => {
                                if matches!(opt_inner.as_ref(), ir::Type::Str { .. }) {
                                    quote!(
                                        let @arg_name_owned = {
                                            let opt_addr = tf.arg(@index);
                                            if opt_addr == 0 {
                                                None
                                            } else {
                                                let mut fat: (*const (*const u8, usize), usize) = (core::ptr::null(), 0);
                                                Self::copyin(&mut fat, opt_addr)?;

                                                let mut str_fats: Vec<(*const u8, usize)> = vec![(core::ptr::null(), 0usize); fat.1];
                                                Self::copyin(&mut str_fats[..], fat.0 as usize)?;

                                                let mut string_vec = Vec::with_capacity(fat.1);
                                                for str_fat in str_fats {
                                                    if str_fat.0.is_null() {
                                                        string_vec.push(None);
                                                    } else {
                                                        let mut buf = vec![0u8; str_fat.1];
                                                        Self::copyin(&mut buf[..], str_fat.0 as usize)?;

                                                        let s = String::from_utf8(buf)
                                                            .map_err(|_| Error::EINVAL)?;
                                                        string_vec.push(Some(s));
                                                    }
                                                }
                                                Some(string_vec)
                                            }
                                        };
                                        let @arg_name = @arg_name_owned.as_ref().map(|string_vec| {
                                            let mut args = Vec::with_capacity(string_vec.len());
                                            for opt_s in string_vec {
                                                args.push(opt_s.as_ref().map(String::as_str));
                                            }
                                            args
                                        });
                                    )
                                } else {
                                    // Handle other Option<&[Option<T>]> types
                                    let inner_ty = emit_type(inner_slice);
                                    quote!(
                                        let @arg_name = {
                                            let opt_addr = tf.arg(@index);
                                            if opt_addr == 0 {
                                                None
                                            } else {
                                                let mut fat: (*const #inner_ty, usize) = (core::ptr::null(), 0);
                                                Self::copyin(&mut fat, opt_addr)?;

                                                let mut buf = vec![Default::default(); fat.1];
                                                Self::copyin(&mut buf[..], fat.0 as usize)?;
                                                Some(buf)
                                            }
                                        };
                                    )
                                }
                            }
                            // Handle Option<&[&str]> - optional array of strings
                            ir::Type::Str { .. } => {
                                quote!(
                                    let @arg_name_owned = {
                                        let opt_addr = tf.arg(@index);
                                        if opt_addr == 0 {
                                            None
                                        } else {
                                            let mut fat: (*const (*const u8, usize), usize) = (core::ptr::null(), 0);
                                            Self::copyin(&mut fat, opt_addr)?;

                                            let mut str_fats: Vec<(*cont u8, usize)> = vec![(core::ptr::null(), 0usize); fat.1];
                                            Self::copyin(&mut str_fats[..], fat.0 as usize)?;

                                            let mut string_vec = Vec::with_capacity(fat.1);
                                            for str_fat in str_fats {
                                                let mut buf = vec![0u8; str_fat.1];
                                                Self::copyin(&mut buf[..], str_fat.0 as usize)?;

                                                let s = String::from_utf8(buf)
                                                    .map_err(|_| Error::EINVAL)?;
                                                string_vec.push(s);
                                            }
                                            Some(string_vec)
                                        }
                                    };
                                    let @arg_name = @arg_name_owned.as_ref().map(|string_vec| {
                                        string_vec.iter().map(String::as_str).collect()
                                    });
                                )
                            }
                            // Handle other Option<&[T]> types
                            _ => {
                                let inner_ty = emit_type(inner_slice);
                                quote!(
                                    let @arg_name = {
                                        let opt_addr = tf.arg(@index);
                                        if opt_addr == 0 {
                                            None
                                        } else {
                                            let mut fat: (*const #inner_ty, usize) = (core::ptr::null(), 0);
                                            Self::copyin(&mut fat, opt_addr)?;

                                            let mut buf = vec![Default::default(); fat.1];
                                            Self::copyin(&mut buf[..], fat.0 as usize)?;
                                            Some(buf)
                                        }
                                    };
                                )
                            }
                        }
                    }
                    ir::Type::Str { .. } => {
                        quote!(
                            let @arg_name_owned = {
                                let opt_addr = tf.arg(@index);
                                if opt_addr == 0 {
                                    None
                                } else {
                                    let mut fat: (*const u8, usize) = (core::ptr::null(), 0);
                                    Self::copyin(&mut fat, opt_addr)?;

                                    let mut buf = vec![0u8; fat.1];
                                    Self::copyin(&mut buf[..], fat.0 as usize)?;
                                    Some(String::from_utf8(buf)
                                        .map_err(|_| Error::EINVAL)?
                                    )
                                }
                            };
                            let @arg_name = @arg_name_owned.as_ref().map(String::as_str);
                        )
                    }
                    ir::Type::Value(_) => {
                        // Handle Option<numeric types> by reading Option struct from memory
                        // This approach correctly distinguishes Some(0) from None
                        // Supports all numeric types: Fd, PId, usize, isize, etc.
                        let inner_ty = emit_value_type(match inner.as_ref() {
                            ir::Type::Value(v) => v,
                            _ => unreachable!(),
                        });
                        quote!(
                            let @arg_name = {
                                let opt_addr = tf.arg(@index);
                                if opt_addr == 0 {
                                    None
                                } else {
                                    let mut opt_value: Option<#inner_ty> = None;
                                    Self::copyin(&mut opt_value, opt_addr)?;
                                    opt_value
                                }
                            };
                        )
                    }
                    _ => {
                        quote!(
                            let @arg_name = {
                                compile_error!("Unsupported Option inner type");
                                unreachable!()
                            };
                        )
                    }
                }
            }
            ir::Type::Custom(_) => {
                // Custom types should not appear directly as parameters
                // They should be wrapped in Ref
                quote!(compile_error!("Custom types must be passed by reference");)
            }
        };
        args.extend(fetch);
    }
    args
}

/// Generates argument list for syscall function invocation.
///
/// This function creates the argument list used when calling the actual syscall
/// implementation function. It maps the extracted and converted parameters to
/// the appropriate argument positions for the function call.
///
/// # Arguments
/// * `params` - Array of syscall parameters to generate argument list for
///
/// # Returns
/// TokenStream containing comma-separated argument names for function invocation
///
/// # Argument Mapping
/// Each parameter is mapped to its corresponding arg{index} variable name
/// that was created during the argument extraction phase.
fn emit_args_conversion(params: &[ir::Param]) -> TokenStream {
    let mut conversions = TokenStream::new();

    for (i, param) in params.iter().enumerate() {
        if i > 0 {
            conversions.extend(quote!(,));
        }

        let arg_name = Ident::new(&format!("arg{}", i), Span::call_site());

        let conversion = match &param.ty {
            ir::Type::Str { mutable } => {
                if *mutable {
                    quote!(&mut @arg_name) // String => &mut str
                } else {
                    quote!(&@arg_name) // String => &str
                }
            }
            ir::Type::Slice { mutable, .. } => {
                if *mutable {
                    quote!(&mut @arg_name) // Vec<T> => &mut [T]
                } else {
                    quote!(&@arg_name) // Vec<T> => &[T]
                }
            }
            ir::Type::Ref { mutable, .. } => {
                if *mutable {
                    quote!(&mut @arg_name) // T => &mut T
                } else {
                    quote!(&@arg_name) // T => &T
                }
            }
            ir::Type::Option { inner } => {
                match inner.as_ref() {
                    ir::Type::Slice { mutable, .. } => {
                        if *mutable {
                            quote!(@arg_name.as_deref_mut()) // Option<Vec<T>> => &mut [T]
                        } else {
                            quote!(@arg_name.as_deref()) // Option<Vec<T>> => &[T]
                        }
                    }
                    ir::Type::Str { mutable } => {
                        if *mutable {
                            quote!(@arg_name.as_deref_mut()) // Option<String> => &mut str
                        } else {
                            quote!(@arg_name.as_deref()) // Option<String> => &str
                        }
                    }
                    _ => quote!(@arg_name), // Other types passed directly
                }
            }
            _ => quote!(@arg_name), // Other types passed directly
        };
        conversions.extend(conversion);
    }
    conversions
}

fn emit_syscall_signature(registry: &ir::SyscallRegistry) -> TokenStream {
    let mut sigs = TokenStream::new();

    for syscall in &registry.syscalls {
        let rust_name = &syscall.rust_name;
        let params = emit_method_params(&syscall.params);
        let ret = emit_return_type(&syscall.ret);

        sigs.extend(quote!(fn @rust_name(#params) #ret;));
    }
    sigs
}

fn emit_from_usize(registry: &ir::SyscallRegistry) -> TokenStream {
    let enum_name = &registry.name;
    let mut match_arms = TokenStream::new();

    for syscall in &registry.syscalls {
        let variant = &syscall.variant_name;
        let id = Literal::u16_unsuffixed(syscall.id.0);
        match_arms.extend(quote!(@id => @enum_name::@variant,));
    }
    match_arms.extend(quote!(_ => @enum_name::Invalid,));

    quote!(
        impl @enum_name {
            fn from_usize(n: usize) -> Self {
                match n as u16 {
                    #match_arms
                }
            }
        }
    )
}
