use proc_macro::{Ident, Span, TokenStream};

/// AST representation of a syscall enum definition
#[derive(Debug)]
pub struct Enum {
    /// The name of the enum
    pub name: Ident,
    /// List of variants in the enum
    pub variants: Vec<Variant>,
}

/// AST representation of a syscall variant
#[derive(Debug)]
pub struct Variant {
    /// The name of the variant
    pub name: Ident,
    /// The syscall ID number
    pub id: usize,
    /// List of parameters for this syscall
    pub params: Vec<Param>,
    /// Return type of this syscall
    pub ret: ReturnType,
}

/// AST representation of a syscall parameter
#[derive(Debug)]
pub struct Param {
    /// The name of the parameter
    pub name: Ident,
    /// The type of the parameter
    pub ty: Type,
}

/// Represents the return type of a syscall
#[derive(Debug)]
pub enum ReturnType {
    /// A specific type
    Type(Type),
    /// The never type (!)
    Never,
}

/// Type information for syscall parameters and return values
#[derive(Debug, Clone)]
pub struct Type {
    /// The token stream representing the type
    pub tokens: TokenStream,
    /// Source code location information
    pub span: Span,
}
