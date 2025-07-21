//! Code generation for SyscallError derive macro.
//!
//! This module implements the final phase of the SyscallError derive macro,
//! converting the intermediate representation into actual Rust code that
//! implements the `From<isize>` trait and related conversion methods.

include!("../common/quote.rs");
use super::ir;

/// Generates the complete `From<isize>` implementation for an error enum.
///
/// This function creates a match expression that converts isize values
/// (typically negative error codes from syscalls) into the appropriate
/// enum variants. It includes a fallback case for unrecognized error codes.
///
/// # Arguments
/// * `registry` - The error registry containing all variant information
///
/// # Returns
/// A TokenStream containing the complete `From<isize>` implementation
///
/// # Generated Code Example
/// ```rust
/// impl From<isize> for MyError {
///     fn from(value: isize) -> Self {
///         match value {
///             -2 => MyError::ResourceBusy,
///             -3 => MyError::NotFound,
///             _ => MyError::Uncategorized,
///         }
///     }
/// }
/// ```
pub fn emit(registry: &ir::ErrorRegistry) -> proc_macro::TokenStream {
    let enum_name = Ident::new(&registry.name, Span::call_site());

    let from_isize_arms = emit_from_isize_arms(registry);

    quote!(
        impl From<isize> for @enum_name {
            fn from(value: isize) -> Self {
                match value {
                    #from_isize_arms
                    _ => @enum_name::Uncategorized,
                }
            }
        }
    )
}

/// Generates match arms for the `From<isize>` implementation.
///
/// This function creates individual match arms that map specific isize values
/// to their corresponding enum variants. Each arm matches a negative error
/// code value and returns the appropriate enum variant.
///
/// # Arguments
/// * `registry` - The error registry containing variant information
///
/// # Returns
/// A TokenStream containing all the match arms for known error values
///
/// # Generated Code Example
/// ```rust
/// -2isize => MyError::ResourceBusy,
/// -3isize => MyError::NotFound,
/// -4isize => MyError::OutOfMemory,
/// ```
fn emit_from_isize_arms(registry: &ir::ErrorRegistry) -> TokenStream {
    let mut arms = TokenStream::new();

    for variant in &registry.variants {
        let value = Literal::isize_suffixed(variant.value);
        let variant_name = Ident::new(&variant.name, Span::call_site());
        let enum_name = Ident::new(&registry.name, Span::call_site());

        arms.extend(quote!(@value => @enum_name::@variant_name,));
    }

    arms
}

// Future enhancement: Generate Into<isize> implementation
// This would allow converting error enum variants back to their isize values
//
// fn emit_into_isize_arms(registry: &ir::ErrorRegistry) -> TokenStream {
//     let mut arms = TokenStream::new();

//     for variant in &registry.variants {
//         let value = Literal::isize_suffixed(variant.value);
//         let variant_name = Ident::new(&variant.name, Span::call_site());
//         let enum_name = Ident::new(&registry.name, Span::call_site());

//         arms.extend(quote!(@enum_name::@variant_name => @value,));
//     }

//     arms
// }
