// abstract syntax tree data structure.

use serde::{Deserialize, Serialize};

pub mod associated_impl;
pub mod display_impl;
pub mod fromstr_impl;

pub use associated_impl::*;
pub use display_impl::*;
pub use fromstr_impl::*;

// SECTION: cflat types

// conceptually these are different from the LIR types, but in practical terms
// for cflat they are the same. rather than make redundant definitions, we'll
// just reuse them.

// types.
pub use crate::middle_end::lir::Type;

// type factories.
pub use crate::middle_end::lir::func_ty;
pub use crate::middle_end::lir::int_ty;
pub use crate::middle_end::lir::ptr_ty;
pub use crate::middle_end::lir::struct_ty;

// for struct_ty.
pub use crate::middle_end::lir::struct_id;

// SECTION: AST

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Program {
    pub globals: Vec<Decl>,
    pub typedefs: Vec<Typedef>,
    pub externs: Vec<Decl>,
    pub functions: Vec<Function>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Decl {
    pub name: String,
    pub typ: Type,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Typedef {
    pub name: String,
    pub fields: Vec<Decl>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Function {
    pub name: String,
    pub params: Vec<Decl>,
    // this is optional because the return type can be _
    pub rettyp: Option<Type>,
    pub body: Body,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Body {
    pub decls: Vec<(Decl, Option<Exp>)>, // optional initializers
    pub stmts: Vec<Stmt>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum Stmt {
    Break,
    Continue,
    Return(Option<Exp>),
    Assign {
        lhs: Lval,
        rhs: Rhs,
    },
    Call {
        callee: Lval,
        args: Vec<Exp>,
    },
    If {
        guard: Exp,
        tt: Vec<Stmt>,
        ff: Vec<Stmt>,
    },
    While {
        guard: Exp,
        body: Vec<Stmt>,
    },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum Rhs {
    Exp(Exp),
    New { typ: Type, num: Option<Exp> },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum Lval {
    // variables
    Id(String),
    // *lval
    Deref(Box<Lval>),
    // lval[exp]
    ArrayAccess { ptr: Box<Lval>, index: Exp },
    // lval.id
    FieldAccess { ptr: Box<Lval>, field: String },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum Exp {
    // literals
    Num(i32),
    // variables
    Id(String),
    Nil,
    // - exp
    Neg(Box<Exp>),
    // * exp
    Deref(Box<Exp>),
    // ! exp
    Not(Box<Exp>),
    Arith(Box<Exp>, ArithOp, Box<Exp>),
    Compare(Box<Exp>, CompareOp, Box<Exp>),
    And(Box<Exp>, Box<Exp>),
    Or(Box<Exp>, Box<Exp>),
    // exp[exp] -- ptr is the left-hand side
    ArrayAccess { ptr: Box<Exp>, index: Box<Exp> },
    // exp.id -- ptr is the left-hand side
    FieldAccess { ptr: Box<Exp>, field: String },
    Call { callee: Box<Exp>, args: Vec<Exp> },
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum ArithOp {
    Add,
    Subtract,
    Multiply,
    Divide,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum CompareOp {
    Equal,
    NotEq,
    Lt,
    Lte,
    Gt,
    Gte,
}
