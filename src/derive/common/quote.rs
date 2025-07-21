// Macro quotation utilities for code generation.
//
// This module provides a `quote!` macro implementation that allows for easy
// generation of TokenStreams in procedural macros. It supports interpolation
// of variables and expressions into the generated token stream.
//
// # Features
//
// - Token interpolation with `#variable` syntax
// - Expression interpolation with `#(expression)` syntax  
// - Single token interpolation with `@variable` syntax
// - Automatic handling of delimiters (braces, brackets, parentheses)
// - Proper spacing and punctuation handling
//
// # Example
//
// ```rust
// let name = Ident::new("MyStruct", Span::call_site());
// let tokens = quote! {
//     struct @name {
//         field: u32,
//     }
// };
// ```

use proc_macro::{TokenStream, TokenTree, Group, Delimiter, Ident, Literal, Punct, Spacing, Span};

/// Main quotation macro for generating TokenStreams.
///
/// This macro provides a domain-specific language for constructing TokenStreams
/// with support for variable interpolation and proper token handling.
///
/// # Interpolation Syntax
///
/// - `#variable` - Interpolates a TokenStream or collection of tokens
/// - `#(expression)` - Interpolates the result of an expression
/// - `@variable` - Interpolates a single token (typically an Ident)
///
/// # Examples
///
/// ```rust
/// // Empty token stream
/// let empty = quote!();
///
/// // Simple token sequence
/// let tokens = quote!(fn hello() {});
///
/// // With variable interpolation
/// let name = Ident::new("test", Span::call_site());
/// let function = quote!(fn @name() {});
/// ```
macro_rules! quote {
    () => { TokenStream::new() };
    ($($tt:tt)*) => {{
        let mut _stream = TokenStream::new();
        quote_impl!(_stream, $($tt)*);
        _stream
    }};
}

/// Internal implementation macro for the quote! macro.
///
/// This macro handles the recursive processing of tokens and interpolation
/// syntax, building up the final TokenStream through pattern matching.
macro_rules! quote_impl {
    // Base case
    ($stream:ident,) => {};
    
    // Interpolation with # for TokenStream
    ($stream:ident, #$var:ident $($rest:tt)*) => {
        $stream.extend($var.clone());
        quote_impl!($stream, $($rest)*);
    };
    
    // Interpolation with #(...) for function call results
    ($stream:ident, #($expr:expr) $($rest:tt)*) => {
        $stream.extend($expr);
        quote_impl!($stream, $($rest)*);
    };
    
    // Interpolation with @ for single tokens (Ident)
    ($stream:ident, @$var:ident $($rest:tt)*) => {
        $stream.extend(Some(TokenTree::from($var.clone())));
        quote_impl!($stream, $($rest)*);
    };
    
    // Group with {}
    ($stream:ident, { $($inner:tt)* } $($rest:tt)*) => {
        let inner = quote!($($inner)*);
        $stream.extend(Some(TokenTree::Group(Group::new(Delimiter::Brace, inner))));
        quote_impl!($stream, $($rest)*);
    };
    
    // Group with []
    ($stream:ident, [ $($inner:tt)* ] $($rest:tt)*) => {
        let inner = quote!($($inner)*);
        $stream.extend(Some(TokenTree::Group(Group::new(Delimiter::Bracket, inner))));
        quote_impl!($stream, $($rest)*);
    };
    
    // Group with ()
    ($stream:ident, ( $($inner:tt)* ) $($rest:tt)*) => {
        let inner = quote!($($inner)*);
        $stream.extend(Some(TokenTree::Group(Group::new(Delimiter::Parenthesis, inner))));
        quote_impl!($stream, $($rest)*);
    };
    
    // Identifier
    ($stream:ident, $ident:ident $($rest:tt)*) => {
        $stream.extend(Some(TokenTree::Ident(Ident::new(stringify!($ident), Span::call_site()))));
        quote_impl!($stream, $($rest)*);
    };
    
    // Literal string
    ($stream:ident, $lit:literal $($rest:tt)*) => {
        let lit_str = stringify!($lit);
        let lit = if lit_str.starts_with('"') && lit_str.ends_with('"') {
            Literal::string(&lit_str[1..lit_str.len()-1])
        } else if lit_str.ends_with("u8") {
            let num_str = &lit_str[..lit_str.len()-2];
            Literal::u8_unsuffixed(num_str.parse::<u8>().unwrap())
        } else if lit_str.ends_with("u16") {
            let num_str = &lit_str[..lit_str.len()-3];
            Literal::u16_unsuffixed(num_str.parse::<u16>().unwrap())
        } else if lit_str.ends_with("usize") {
            let num_str = &lit_str[..lit_str.len()-5];
            Literal::usize_unsuffixed(num_str.parse::<usize>().unwrap())
        } else if let Ok(n) = lit_str.parse::<usize>() {
            Literal::usize_unsuffixed(n)
        } else if let Ok(n) = lit_str.parse::<isize>() {
            Literal::isize_unsuffixed(n)
        } else {
            Literal::string(lit_str)
        };
        $stream.extend(Some(TokenTree::Literal(lit)));
        quote_impl!($stream, $($rest)*);
    };
    
    // Punctuation patterns
    ($stream:ident, :: $($rest:tt)*) => {
        $stream.extend(Some(TokenTree::Punct(Punct::new(':', Spacing::Joint))));
        $stream.extend(Some(TokenTree::Punct(Punct::new(':', Spacing::Alone))));
        quote_impl!($stream, $($rest)*);
    };
    
    ($stream:ident, -> $($rest:tt)*) => {
        $stream.extend(Some(TokenTree::Punct(Punct::new('-', Spacing::Joint))));
        $stream.extend(Some(TokenTree::Punct(Punct::new('>', Spacing::Alone))));
        quote_impl!($stream, $($rest)*);
    };
    
    ($stream:ident, => $($rest:tt)*) => {
        $stream.extend(Some(TokenTree::Punct(Punct::new('=', Spacing::Joint))));
        $stream.extend(Some(TokenTree::Punct(Punct::new('>', Spacing::Alone))));
        quote_impl!($stream, $($rest)*);
    };
    
    ($stream:ident, == $($rest:tt)*) => {
        $stream.extend(Some(TokenTree::Punct(Punct::new('=', Spacing::Joint))));
        $stream.extend(Some(TokenTree::Punct(Punct::new('=', Spacing::Alone))));
        quote_impl!($stream, $($rest)*);
    };
    
    ($stream:ident, .. $($rest:tt)*) => {
        $stream.extend(Some(TokenTree::Punct(Punct::new('.', Spacing::Joint))));
        $stream.extend(Some(TokenTree::Punct(Punct::new('.', Spacing::Alone))));
        quote_impl!($stream, $($rest)*);
    };
    
    // Underscore (wildcard pattern)
    ($stream:ident, _ $($rest:tt)*) => {
        $stream.extend(Some(TokenTree::Ident(Ident::new("_", Span::call_site()))));
        quote_impl!($stream, $($rest)*);
    };
    
    // Single punctuation
    ($stream:ident, $punct:tt $($rest:tt)*) => {
        let ch = stringify!($punct).chars().next().unwrap();
        $stream.extend(Some(TokenTree::Punct(Punct::new(ch, Spacing::Alone))));
        quote_impl!($stream, $($rest)*);
    };
}