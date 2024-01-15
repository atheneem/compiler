// cflat's low-level intermediate representation (LIR).

// we're defining a data structure, so it's all dead code.
#![allow(dead_code, unused_macros)]

// use ordered sets and maps to allow for deterministic test outputs.
use std::collections::{BTreeMap as Map, BTreeSet as Set};

use derive_more::Display;
use hashconsing::HConsed;
use serde::{Deserialize, Serialize};

mod associated_impl;
mod cfg_dump_impl;
mod display_impl;
mod fromstr_impl;
mod id_type_factories;
mod misc_impl;
mod validate;

pub use self::associated_impl::*;
pub use self::cfg_dump_impl::*;
pub use self::display_impl::*;
pub use self::fromstr_impl::*;
pub use self::id_type_factories::*;
pub use self::misc_impl::*;
pub use self::validate::*;

// SECTION: lir identifiers

// names are hashconsed for efficiency, since there will be many copies of the
// names floating around.

#[derive(Clone, Debug, Display, Eq, Hash, PartialEq)]
pub struct StructId(HConsed<String>);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FieldId {
    pub name: HConsed<String>,
    pub typ: Type,
}

#[derive(Clone, Debug, Display, Eq, Hash, PartialEq)]
pub struct FuncId(HConsed<String>);

#[derive(Clone, Debug, Display, Eq, Hash, PartialEq)]
pub struct BbId(HConsed<String>);

// for non-globals we need the enclosing function in order to distinguish
// variables in different scopes that have the same name.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct LirVar {
    name: HConsed<String>,
    typ: Type,
    scope: Option<FuncId>,
}

// never make a LirVar, always use var_id() to make a VarId.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct VarId(HConsed<LirVar>);

// SECTION: lir types

// types are hashconsed for efficiency, since there will be many copies of the
// various types floating around.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Type(pub HConsed<LirType>);

#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub enum LirType {
    Int,
    Struct(StructId),
    Function {
        ret_ty: Option<Type>,
        param_ty: Vec<Type>,
    },
    Pointer(Type),
}

// SECTION: lir programs

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Program {
    pub structs: Map<StructId, Set<FieldId>>,
    pub globals: Set<VarId>,
    pub functions: Map<FuncId, Function>,
    pub externs: Map<FuncId, Type>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Function {
    pub id: FuncId,
    pub ret_ty: Option<Type>,
    pub params: Vec<VarId>,
    pub locals: Set<VarId>,
    pub body: Map<BbId, BasicBlock>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct BasicBlock {
    pub id: BbId,
    pub insts: Vec<Instruction>,
    pub term: Terminal,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum Instruction {
    Alloc {
        // 'num' is the number of elements to allocate; the type of elements is inferred from the
        // type of 'lhs'. 'id' is a unique identifier for the allocated object(s), used by the
        // pointer analysis heap model.
        lhs: VarId,
        num: Operand,
        id: VarId,
    },
    Arith {
        lhs: VarId,
        aop: ArithmeticOp,
        op1: Operand,
        op2: Operand,
    },
    CallExt {
        // only used for calls to external functions (which can only be direct calls).
        lhs: Option<VarId>,
        ext_callee: FuncId,
        args: Vec<Operand>,
    },
    Cmp {
        lhs: VarId,
        rop: ComparisonOp,
        op1: Operand,
        op2: Operand,
    },
    Copy {
        lhs: VarId,
        op: Operand,
    },
    Gep {
        // Get Element Pointer.  Sets lhs to an offset of idx elements from src.
        // Both lhs and src are pointers of the same type.
        lhs: VarId,
        src: VarId,
        idx: Operand,
    },
    Gfp {
        // Get Field Pointer.  Sets lhs to a pointer to the given field of the
        // object src points to.
        lhs: VarId,
        src: VarId,
        field: FieldId,
    },
    Load {
        lhs: VarId,
        src: VarId,
    },
    Phi {
        lhs: VarId,
        args: Vec<Operand>,
    },
    Store {
        dst: VarId,
        op: Operand,
    },
}

// these are instructions for which there must be exactly one at the end of each
// basic block. call instructions aren't traditionally terminal, but we will be
// using an ICFG for interprocedural static analyses (which does make calls
// terminal) and it's easier to just make them always terminal rather than
// translate back and forth.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum Terminal {
    Branch {
        cond: Operand,
        tt: BbId,
        ff: BbId,
    },
    CallDirect {
        // only used for calls to internal functions.
        lhs: Option<VarId>,
        callee: FuncId,
        args: Vec<Operand>,
        next_bb: BbId,
    },
    CallIndirect {
        // only used for calls to internal functions.
        lhs: Option<VarId>,
        callee: VarId,
        args: Vec<Operand>,
        next_bb: BbId,
    },
    Jump(BbId),
    Ret(Option<Operand>),
}

#[derive(Clone, Debug, Deserialize, Display, Eq, PartialEq, Serialize)]
pub enum Operand {
    CInt(i32),
    Var(VarId),
}

#[derive(Copy, Clone, Debug, Deserialize, Display, Eq, PartialEq, Serialize)]
pub enum ArithmeticOp {
    #[display(fmt = "add")]
    Add,
    #[display(fmt = "sub")]
    Subtract,
    #[display(fmt = "mul")]
    Multiply,
    #[display(fmt = "div")]
    Divide,
}

#[derive(Copy, Clone, Debug, Deserialize, Display, Eq, PartialEq, Serialize)]
pub enum ComparisonOp {
    #[display(fmt = "eq")]
    Eq,
    #[display(fmt = "neq")]
    Neq,
    #[display(fmt = "lt")]
    Less,
    #[display(fmt = "lte")]
    LessEq,
    #[display(fmt = "gt")]
    Greater,
    #[display(fmt = "gte")]
    GreaterEq,
}

// A convenient and more fluent way to refer to arithmetic and comparison
// operations.
macro_rules! LirOp {
    [+] => { crate::middle_end::lir::ArithmeticOp::Add };
    [-] => { crate::middle_end::lir::ArithmeticOp::Subtract };
    [*] => { crate::middle_end::lir::ArithmeticOp::Multiply };
    [/] => { crate::middle_end::lir::ArithmeticOp::Divide };
    [==] => { crate::middle_end::lir::ComparisonOp::Eq };
    [!=] => { crate::middle_end::lir::ComparisonOp::Neq };
    [<] => { crate::middle_end::lir::ComparisonOp::Less };
    [<=] => { crate::middle_end::lir::ComparisonOp::LessEq };
    [>] => { crate::middle_end::lir::ComparisonOp::Greater };
    [>=] => { crate::middle_end::lir::ComparisonOp::GreaterEq };
}

#[allow(unused_imports)]
pub(crate) use LirOp;
