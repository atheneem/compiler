// hashconsing factories for identifiers and types.

use hashconsing::{consign, HashConsign};

use super::*;

consign! {
    let STRING_FACTORY = consign(20) for String;
}

consign! {
    let VAR_FACTORY = consign(20) for LirVar;
}

pub fn struct_id(id: &str) -> StructId {
    StructId(STRING_FACTORY.mk(id.to_string()))
}

pub fn field_id(id: &str, typ: Type) -> FieldId {
    FieldId {
        name: STRING_FACTORY.mk(id.to_string()),
        typ,
    }
}

pub fn func_id(id: &str) -> FuncId {
    FuncId(STRING_FACTORY.mk(id.to_string()))
}

pub fn var_id(id: &str, typ: Type, scope: Option<FuncId>) -> VarId {
    VarId(VAR_FACTORY.mk(LirVar {
        name: STRING_FACTORY.mk(id.to_string()),
        typ,
        scope,
    }))
}

// needed for deserialization.
pub fn lir_var(id: &str, typ: Type, scope: Option<FuncId>) -> LirVar {
    LirVar {
        name: STRING_FACTORY.mk(id.to_string()),
        typ,
        scope,
    }
}

pub fn bb_id(id: &str) -> BbId {
    BbId(STRING_FACTORY.mk(id.to_string()))
}

consign! {
    let TYPE_FACTORY = consign(10) for LirType;
}

pub fn int_ty() -> Type {
    Type(TYPE_FACTORY.mk(LirType::Int))
}

pub fn struct_ty(id: StructId) -> Type {
    Type(TYPE_FACTORY.mk(LirType::Struct(id)))
}

pub fn func_ty(ret_ty: Option<Type>, param_ty: Vec<Type>) -> Type {
    Type(TYPE_FACTORY.mk(LirType::Function { ret_ty, param_ty }))
}

pub fn ptr_ty(deref_ty: Type) -> Type {
    Type(TYPE_FACTORY.mk(LirType::Pointer(deref_ty)))
}

// needed for deserialization.
pub fn typ_ty(typ: LirType) -> Type {
    match typ {
        LirType::Int => int_ty(),
        LirType::Struct(id) => struct_ty(id),
        LirType::Function { ret_ty, param_ty } => func_ty(ret_ty, param_ty),
        LirType::Pointer(deref_ty) => ptr_ty(deref_ty),
    }
}
