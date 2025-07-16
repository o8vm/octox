use proc_macro::{Ident, Literal, Span, TokenStream, TokenTree};

pub struct Error {
    pub message: String,
    pub span: Span,
}

impl Error {
    pub fn new(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }
}

pub fn emit(msg: String, span: Span) -> proc_macro::TokenStream {
    let lit = Literal::string(&msg);
    let mut ts = TokenStream::new();
    ts.extend([
        TokenTree::Ident(Ident::new("compile_error", span)),
        TokenTree::Punct(proc_macro::Punct::new('!', proc_macro::Spacing::Alone)),
        TokenTree::Group(proc_macro::Group::new(
            proc_macro::Delimiter::Parenthesis,
            TokenStream::from(TokenTree::Literal(lit)),
        )),
    ]);
    ts
}

pub type Result<T> = std::result::Result<T, Error>;
