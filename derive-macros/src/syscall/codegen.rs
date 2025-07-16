include!("../utils/quote.rs");
use crate::syscall::ir::{ArchSpec, ValueType};
use super::ir;

pub fn emit(registry: &ir::SyscallRegistry) -> TokenStream {
    let mut stream = TokenStream::new();

    stream.extend(emit_trait(registry));

    stream.extend(emit_from_usize(registry));

    stream
}

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
            // Default implementation for kernel syscalls
            fn copyin<T>(dst: &mut T, src: usize) -> Result<()> {
                unimplemented!("copyin is not implemented for kernel syscalls");
            }

            fn dispatch(tf: &mut ir::TrapFrame) -> Result<()> {
                #dispatch_body
            }

            #syscall_signatures
        }

        #[cfg(all(target_os = "none", feature = "kernel"))]
        impl SyscallDispatch for @enum_name {}
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
        },
        ir::Type::Ref { inner, mutable } => {
            let inner_ty = emit_type(inner);
            if *mutable {
                quote!(&mut #inner_ty)
            } else {
                quote!(&#inner_ty)
            }
        },
        ir::Type::Slice { inner, mutable } => {
            let inner_ty = emit_type(inner);
            if *mutable {
                quote!(&mut [#inner_ty])
            } else {
                quote!(&[#inner_ty])
            }
        },
        ir::Type::Str { mutable } => {
            if *mutable {
                quote!(&mut str)
            } else {
                quote!(&str)
            }
        },
        ir::Type::Option { inner } => {
            let inner_ty = emit_type(inner);
            quote!(Option<#inner_ty>)
        },
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
        },
    }
}

fn emit_user_body(syscall: &ir::Syscall) -> TokenStream {
    // アーキテクチャ検出
    #[cfg(target_arch = "aarch64")]
    {
        emit_user_body_generic::<ir::Aarch64>(syscall)
    }
    #[cfg(target_arch = "riscv64")]
    {
        emit_user_body_generic::<ir::RiscV64>(syscall)
    }
    #[cfg(not(any(target_arch = "aarch64", target_arch = "riscv64")))]
    {
        emit_user_body_generic::<ir::Aarch64>(syscall)
    }
}

fn emit_user_body_generic<A: ArchSpec>(syscall: &ir::Syscall) -> TokenStream {
    let syscall_id = Literal::u16_unsuffixed(syscall.id.0);
    let insn = Literal::string(A::INSN);
    let syscall_reg = Literal::string(A::SYSCALL_REGS);
    let out_reg = Literal::string(A::OUT_REGS);

    let reg_assignments = emit_register_assignments::<A>(&syscall.params);

    match &syscall.ret {
        ir::ReturnType::Never => {
            quote!(
                // SAFETY: システムコールは以下の条件で安全:
                // - レジスタ制約が正しく指定されている
                // - noreturn オプションにより後続コードが実行されないことが保証されている
                unsafe {
                    core::arch::asm!(
                        @insn,
                        in(@syscall_reg) @syscall_id,
                        #reg_assignments
                        options(noreturn)
                    );
                } 
            )
        },
        _ => {
            let ret_conversion = emit_return_conversion(&syscall.ret);
            quote! {
                let _ret: isize;
                // SAFETY: システムコールは以下の条件で安全:
                // - 入力レジスタは読み取り専用
                // - 出力レジスタは lateout で正しく指定
                unsafe {
                    core::arch::asm!(
                        @insn,
                        in(@syscall_reg) @syscall_id,
                        #reg_assignments
                        lateout(@out_reg) _ret,
                    );
                }
                use crate::syscall::syscall_return::FromSyscallRaw;
                <#ret_conversion>::from_syscall_raw(_ret)
            }
        },
    }
}

// todo: reconsider this function
fn emit_register_assignments<A: ArchSpec>(params: &[ir::Param]) -> TokenStream {
    let mut assignments = TokenStream::new();

    for (param, &reg) in params.iter().zip(A::IN_REGS) {
        let reg_lit = Literal::string(reg);
        let name = &param.rust_name;

        let assignment = match &param.ty {
            ir::Type::Value(ValueType::Fd | ValueType::PId) => {
                quote!(in(@reg_lit) @name.into(),)
            },
            ir::Type::Value(_) => {
                quote!(in(@reg_lit) @name as usize,)
            },
            ir::Type::Ptr { .. } => {
                quote!(in(@reg_lit) @name as usize,)
            },
            ir::Type::Ref { .. } | ir::Type::Slice { ..} | ir::Type::Str { .. } => {
                // 本当か？
                // we treat slice(including str) as referece to its value? like &@name
                quote!(in(&reg_lit) @name as *const _ as usize,)
            },
            ir::Type::Option { .. } => {
                // we use Option as a wrapper for pointers
                quote!(in(&reg_lit) &@name as *const _ as usize, )
            },
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
        },
    }
}

fn emit_dispatch_body(registry: &ir::SyscallRegistry) -> TokenStream {
    let mut match_arms = TokenStream::new();

    for syscall in &registry.syscalls {
        let id = Literal::u16_unsuffixed(syscall.id.0);
        let handler = emit_syscall_handler(syscall);
        match_arms.extend(quote!(@id => #handler,));
    }

    quote!(
        let result = match tf.syscall_id as u16 {
            #match_arms
            _ => {
                Err(Errno::ENOSYS),
            }
        };
        tf.set_return(result.into_syscall_raw() as usize);
        Ok(())
    )
}

fn emit_syscall_handler(syscall: &ir::Syscall) -> TokenStream {
    let method = &syscall.rust_name;
    let args_fetch = emit_handler_args(&syscall.params);
    let args_pass = emit_args_conversion(&syscall.params);

    quote!({
        #args_fetch
        Self::@method(#args_pass)
    })
}

fn emit_handler_args(params: &[ir::Param]) -> TokenStream {
    let mut args = TokenStream::new();

    for (i, param) in params.iter().enumerate() {
        let arg_name = Ident::new(&format!("arg{}", i), Span::call_site());
        let index = Literal::usize_unsuffixed(i);

        let fetch = match &param.ty {
            ir::Type::Value(ir::ValueType::Fd) => {
                quote!(let @arg_name = Fd::from(ft.arg(@index));)
            },
            ir::Type::Value(ir::ValueType::PId) => {
                quote!(let @arg_name = PId::from(ft.arg(@index));)
            },
            ir::Type::Value(_) => {
                quote!(let @arg_name = ft.arg(@index) as _;)
            },
            ir::Type::Ptr { .. } => {
                // 生ポインタはユーザー空間のアドレスとして解釈
                quote!(let @arg_name = ft.arg(@index) as _;)
            },
            ir::Type::Ref { inner, .. } => {
                let inner_ty = emit_type(inner);

                quote!(
                    let @arg_name = {
                        let addr = ft.arg(@index);
                        let mut value: #inner_ty = Default::default();
                        Self::copyin(&mut value, addr)?;
                        Box::new(value)
                    };
                )
            }
            ir::Type::Slice { inner, .. } => {
                let inner_ty = emit_type(inner);

                quote!(
                    let @arg_name = {
                        let mut fat: (*const #inner_ty, usize) = (core::ptr::null(), 0);
                        Self::copyin(&mut fat, ft.arg(@index))?;

                        let mut buf = vec![Default::default(); fat.1];
                        Self::copyin(&mut buf, fat.0 as usize)?;

                        buf
                    };
                )
            },
            ir::Type::Str { .. } => {
                quote!(
                    let @arg_name =  {
                        let mut fat: (*const u8, usize) = (core::ptr::null(), 0);
                        Self::copyin(&mut fat, ft.arg(@index))?;

                        let mut buf = vec![0u8; fat.1];
                        Self::copyin(&mut buf, fat.0 as usize)?;

                        String::from_utf8(buf)
                            .map_err(|_| Errno::EINVAL)?
                    };
                )
            },
            ir::Type::Option { inner } => {
                match inner.as_ref() {
                    ir::Type::Slice { inner, .. } => {
                        let inner_ty = emit_type(inner);
                        quote!(
                            let @arg_name = {
                                let opt_addr = ft.arg(@index);
                                if opt_addr == 0 {
                                    None
                                } else {
                                    let mut fat: (*const #inner_ty, usize) = (core::ptr::null(), 0);
                                    Self::copyin(&mut fat, opt_addr)?;

                                    let mut buf = vec![Default::default(); fat.1];
                                    Self::copyin(&mut buf, fat.0 as usize)?;
                                    Some(buf)
                                }
                            };
                        )
                    }, 
                    ir::Type::Str { .. } => {
                        quote!(
                            let @arg_name = {
                                let opt_addr = ft.arg(@index);
                                if opt_addr == 0 {
                                    None
                                } else {
                                    let mut fat: (*const u8, usize) = (core::ptr::null(), 0);
                                    Self::copyin(&mut fat, opt_addr)?;

                                    let mut buf = vec![0u8; fat.1];
                                    Self::copyin(&mut buf, fat.0 as usize)?;
                                    Some(String::from_utf8(buf)
                                        .map_err(|_| Errno::EINVAL)?
                                    )
                                }
                            };
                        )
                    },
                    ir::Type::Value(ValueType::Fd) => {
                        quote!(
                            let @arg_name = {
                                let opt_addr = tf.arg(@index);
                                if opt_addr == 0 {
                                    None
                                } else {
                                    Some(Fd::from(opt_addr))
                                }
                            };
                        )
                    }
                    ir::Type::Value(ValueType::PId) => {
                        quote!(
                            let @arg_name = {
                                let opt_addr = tf.arg(@index);
                                if opt_addr == 0 {
                                    None
                                } else {
                                    Some(PId::from(opt_addr))
                                }
                            };
                        )
                    }
                    ir::Type::Value(_) => {
                        quote!(
                            let @arg_name = {
                                let opt_addr = ft.arg(@index);
                                if opt_addr == 0 {
                                    None
                                } else {
                                    Some(ft.arg(@index) as _)
                                }
                            };
                        )
                    },
                    _ => {
                        quote!(
                            let @arg_name = {
                                compile_error!("Unsupported Option inner type");
                                unreachable!()
                            };
                        )
                    }
                }
            },
        };
        args.extend(fetch);
    }
    args
}


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
            },
            ir::Type::Slice {  mutable, .. } => {
                if *mutable {
                    quote!(&mut @arg_name) // Vec<T> => &mut [T]
                } else {
                    quote!(&@arg_name) // Vec<T> => &[T]
                }
            },
            ir::Type::Ref { mutable, .. } => {
                if *mutable {
                    quote!(&mut *@arg_name) // Box<T> => &mut T
                } else {
                    quote!(&*@arg_name) // Box<T> => &T
                }
            },
            ir::Type::Option { inner } => {
                match inner.as_ref() {
                    ir::Type::Slice { mutable, .. } => {
                        if *mutable {
                            quote!(&mut @arg_name.as_deref_mut()) // Option<Vec<T>> => &mut [T]
                        } else {
                            quote!(&@arg_name.as_deref()) // Option<Vec<T>> => &[T]
                        }
                    },
                    ir::Type::Str { mutable } => {
                        if *mutable {
                            quote!(&mut @arg_name.as_deref_mut()) // Option<String> => &mut str
                        } else {
                            quote!(&@arg_name.as_deref()) // Option<String> => &str
                        }
                    },
                    _ => quote!(@arg_name), // 他の型はそのまま
                }
            },
            _ => quote!(@arg_name), // 他の型はそのまま
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
    match_arms = quote!(_ => @enum_name::Invalid,);

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