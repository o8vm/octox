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
            fn copyin<T: AsBytes>(dst: &mut T, src: usize) -> Result<(), Error> {
                unimplemented!("copyin must be implemented by kernel")
            }
            
            fn dispatch(tf: &mut TrapFrame) -> Result<(), Error> {
                #dispatch_body
            }
            
            fn copyout<T: AsBytes>(dst: usize, src: &T) -> Result<(), Error> {
                unimplemented!("copyout must be implemented by kernel")
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
        ir::Type::Custom(tokens) => {
            // 元のトークンストリームをそのまま使用
            tokens.clone()
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
                use crate::syscall_return::FromIsize;
                <#ret_conversion>::from_isize(_ret)
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
                quote!(in(@reg_lit) @name as *const _ as usize,)
            },
            ir::Type::Option { .. } => {
                // we use Option as a wrapper for pointers
                quote!(in(@reg_lit) &@name as *const _ as usize,)
            },
            ir::Type::Custom(_) => {
                // Custom types should not appear directly as parameters
                // They should be wrapped in Ref
                panic!("Custom types must be passed by reference")
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
        let result = match tf.syscall_num as u16 {
            #match_arms
            _ => Err(Error::ENOSYS),
        };
        
        tf.set_return(result.into_isize() as usize);
        Ok(())
    )
}

fn emit_syscall_handler(syscall: &ir::Syscall) -> TokenStream {
    let method = &syscall.rust_name;
    let args_fetch = emit_handler_args(&syscall.params);
    let args_pass = emit_args_conversion(&syscall.params);
    
    // &mut パラメータがある場合の特別な処理を確認
    let mut has_mutable_ref = false;
    let mut mutable_ref_index = 0;
    let mut mutable_ref_type = None;
    
    for (i, param) in syscall.params.iter().enumerate() {
        if let ir::Type::Ref { mutable: true, inner } = &param.ty {
            has_mutable_ref = true;
            mutable_ref_index = i;
            mutable_ref_type = Some(inner.clone());
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

fn emit_handler_args(params: &[ir::Param]) -> TokenStream {
    let mut args = TokenStream::new();

    for (i, param) in params.iter().enumerate() {
        let arg_name = Ident::new(&format!("arg{}", i), Span::call_site());
        let index = Literal::usize_unsuffixed(i);

        let fetch = match &param.ty {
            ir::Type::Value(ir::ValueType::Fd) => {
                quote!(let @arg_name = Fd(tf.arg(@index));)
            },
            ir::Type::Value(ir::ValueType::PId) => {
                quote!(let @arg_name = PId(tf.arg(@index));)
            },
            ir::Type::Value(_) => {
                quote!(let @arg_name = tf.arg(@index) as _;)
            },
            ir::Type::Ptr { .. } => {
                // 生ポインタはユーザー空間のアドレスとして解釈
                quote!(let @arg_name = tf.arg(@index) as _;)
            },
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
            ir::Type::Slice { inner, .. } => {
                match inner.as_ref() {
                    // &[&str]の場合
                    ir::Type::Str { .. } => {
                        quote!(
                            let @arg_name = {
                                let mut fat: (*const (*const u8, usize), usize) = (core::ptr::null(), 0);
                                Self::copyin(&mut fat, tf.arg(@index))?;
                                
                                let mut str_fats = vec![(core::ptr::null(), 0usize); fat.1];
                                Self::copyin(&mut str_fats[..], fat.0 as usize)?;
                                
                                let mut argv_vec = Vec::with_capacity(fat.1);
                                for str_fat in str_fats {
                                    let mut buf = vec![0u8; str_fat.1];
                                    Self::copyin(&mut buf[..], str_fat.0 as usize)?;
                                    
                                    let s = String::from_utf8(buf)
                                        .map_err(|_| Error::EINVAL)?;
                                    argv_vec.push(s);
                                }
                                argv_vec
                            };
                        )
                    },
                    // その他の&[T]の場合
                    _ => {
                        let inner_ty = emit_type(inner);
                        quote!(
                            let @arg_name = {
                                let mut fat: (*const #inner_ty, usize) = (core::ptr::null(), 0);
                                Self::copyin(&mut fat, tf.arg(@index))?;

                                let mut buf = vec![Default::default(); fat.1];
                                Self::copyin(&mut buf[..], fat.0 as usize)?;

                                buf
                            };
                        )
                    }
                }
            },
            ir::Type::Str { .. } => {
                quote!(
                    let @arg_name =  {
                        let mut fat: (*const u8, usize) = (core::ptr::null(), 0);
                        Self::copyin(&mut fat, tf.arg(@index))?;

                        let mut buf = vec![0u8; fat.1];
                        Self::copyin(&mut buf[..], fat.0 as usize)?;

                        String::from_utf8(buf)
                            .map_err(|_| Error::EINVAL)?
                    };
                )
            },
            ir::Type::Option { inner } => {
                match inner.as_ref() {
                    ir::Type::Slice { inner: inner_slice, .. } => {
                        match inner_slice.as_ref() {
                            // Option<&[Option<&str>]>の場合
                            ir::Type::Option { inner: opt_inner } => {
                                if matches!(opt_inner.as_ref(), ir::Type::Str { .. }) {
                                    quote!(
                                        let @arg_name = {
                                            let opt_addr = tf.arg(@index);
                                            if opt_addr == 0 {
                                                None
                                            } else {
                                                let mut fat: (*const usize, usize) = (core::ptr::null(), 0);
                                                Self::copyin(&mut fat, opt_addr)?;
                                                
                                                let mut opt_ptrs = vec![0usize; fat.1];
                                                Self::copyin(&mut opt_ptrs[..], fat.0 as usize)?;
                                                
                                                let mut envp_vec = Vec::with_capacity(fat.1);
                                                for opt_ptr in opt_ptrs {
                                                    if opt_ptr == 0 {
                                                        envp_vec.push(None);
                                                    } else {
                                                        let mut str_fat: (*const u8, usize) = (core::ptr::null(), 0);
                                                        Self::copyin(&mut str_fat, opt_ptr)?;
                                                        
                                                        let mut buf = vec![0u8; str_fat.1];
                                                        Self::copyin(&mut buf[..], str_fat.0 as usize)?;
                                                        
                                                        let s = String::from_utf8(buf)
                                                            .map_err(|_| Error::EINVAL)?;
                                                        envp_vec.push(Some(s));
                                                    }
                                                }
                                                Some(envp_vec)
                                            }
                                        };
                                    )
                                } else {
                                    // その他のOption<&[Option<T>]>の場合
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
                            },
                            // Option<&[&str]>の場合
                            ir::Type::Str { .. } => {
                                quote!(
                                    let @arg_name = {
                                        let opt_addr = tf.arg(@index);
                                        if opt_addr == 0 {
                                            None
                                        } else {
                                            let mut fat: (*const (*const u8, usize), usize) = (core::ptr::null(), 0);
                                            Self::copyin(&mut fat, opt_addr)?;
                                            
                                            let mut str_fats = vec![(core::ptr::null(), 0usize); fat.1];
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
                                )
                            },
                            // その他のOption<&[T]>の場合
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
                    }, 
                    ir::Type::Str { .. } => {
                        quote!(
                            let @arg_name = {
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
                        )
                    },
                    ir::Type::Value(ValueType::Fd) => {
                        quote!(
                            let @arg_name = {
                                let opt_addr = tf.arg(@index);
                                if opt_addr == 0 {
                                    None
                                } else {
                                    Some(Fd(opt_addr))
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
                                    Some(PId(opt_addr))
                                }
                            };
                        )
                    }
                    ir::Type::Value(_) => {
                        quote!(
                            let @arg_name = {
                                let opt_addr = tf.arg(@index);
                                if opt_addr == 0 {
                                    None
                                } else {
                                    Some(opt_addr as _)
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
            ir::Type::Custom(_) => {
                // Custom types should not appear directly as parameters
                // They should be wrapped in Ref
                panic!("Custom types must be passed by reference")
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