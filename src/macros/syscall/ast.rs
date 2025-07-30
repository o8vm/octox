use proc_macro::{Ident, Span, TokenStream};

/// Abstract Syntax Tree representation of a syscall enum definition.
///
/// This structure represents the parsed form of a syscall enum decorated with
/// the `#[derive(Syscalls)]` attribute. It contains all the information needed
/// to generate syscall wrapper functions and dispatch logic.
#[derive(Debug)]
pub struct Enum {
    /// The identifier name of the enum (e.g., `SysCalls`)
    pub name: Ident,
    /// Collection of syscall variants defined within the enum
    pub variants: Vec<Variant>,
}

/// AST representation of a single syscall variant.
///
/// Each variant corresponds to one system call and contains all the metadata
/// needed to generate the appropriate wrapper functions and dispatch code.
#[derive(Debug)]
pub struct Variant {
    /// The identifier name of the variant (e.g., `Read`, `Write`)
    pub name: Ident,
    /// The unique syscall number used for identification in the kernel
    /// None means the ID should be inferred from enum discriminant
    pub id: Option<usize>,
    /// Ordered list of parameters that this syscall accepts
    pub params: Vec<Param>,
    /// The return type specification for this syscall
    pub ret: ReturnType,
}

/// AST representation of a syscall parameter.
///
/// Represents a single parameter in a syscall's parameter list, including
/// both its name and type information.
#[derive(Debug)]
pub struct Param {
    /// The parameter name as it appears in the syscall signature
    pub name: Ident,
    /// The type information for this parameter
    pub ty: Type,
}

/// Represents the return type specification of a syscall.
///
/// This enum encodes the different kinds of return types that a syscall
/// can have, which affects how the generated code handles return values.
#[derive(Debug)]
pub enum ReturnType {
    /// A concrete type that the syscall returns (e.g., `Result<usize>`, `Fd`)
    Type(Type),
    /// The never type (`!`) indicating the syscall never returns normally
    Never,
}

/// Type information for syscall parameters and return values.
///
/// This structure captures both the token representation of a type and its
/// source location information for error reporting purposes.
#[derive(Debug, Clone)]
pub struct Type {
    /// The raw token stream representing the type as parsed from source
    pub tokens: TokenStream,
    /// Source code span information for error reporting and diagnostics
    pub span: Span,
}
