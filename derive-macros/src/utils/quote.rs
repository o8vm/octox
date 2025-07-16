// =============================================================================
// Quote macro implementation
// =============================================================================

use proc_macro::{TokenStream, TokenTree, Group, Delimiter, Ident, Literal, Punct, Spacing, Span};

macro_rules! quote {
    () => { TokenStream::new() };
    ($($tt:tt)*) => {{
        let mut _stream = TokenStream::new();
        quote_impl!(_stream, $($tt)*);
        _stream
    }};
}

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
    
    // Single punctuation
    ($stream:ident, $punct:tt $($rest:tt)*) => {
        let ch = stringify!($punct).chars().next().unwrap();
        $stream.extend(Some(TokenTree::Punct(Punct::new(ch, Spacing::Alone))));
        quote_impl!($stream, $($rest)*);
    };
}