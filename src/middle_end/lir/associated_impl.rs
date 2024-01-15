// associated function definitions for the datatypes defined in the lir module.

use super::*;
use crate::commons::*;

impl StructId {
    pub fn name(&self) -> &str {
        self.0.as_str()
    }
}

impl FuncId {
    pub fn name(&self) -> &str {
        self.0.as_str()
    }
}

impl BbId {
    pub fn name(&self) -> &str {
        self.0.as_str()
    }
}

impl FieldId {
    pub fn typed_to_string(&self) -> String {
        format!("{}:{}", self.name, self.typ)
    }
}

impl LirVar {
    pub fn typed_to_string(&self) -> String {
        format!("{}:{}", self.name, self.typ)
    }
}

impl VarId {
    pub fn typed_to_string(&self) -> String {
        self.0.typed_to_string()
    }

    pub fn name(&self) -> &str {
        self.0.name.as_str()
    }

    pub fn typ(&self) -> Type {
        self.0.typ.clone()
    }

    pub fn scope(&self) -> Option<FuncId> {
        self.0.scope.clone()
    }

    pub fn is_global(&self) -> bool {
        self.0.scope.is_none()
    }
}

impl Type {
    pub fn is_int(&self) -> bool {
        matches!(*self.0, LirType::Int)
    }

    pub fn is_struct(&self) -> bool {
        matches!(*self.0, LirType::Struct(_))
    }

    pub fn is_function(&self) -> bool {
        matches!(*self.0, LirType::Function { .. })
    }

    pub fn is_ptr(&self) -> bool {
        matches!(*self.0, LirType::Pointer(_))
    }

    // returns whether the type ultimately reachable via zero or more pointer
    // dereferences is equal to rhs.
    pub fn base_typ_is(&self, rhs: Type) -> bool {
        match &*self.0 {
            LirType::Pointer(deref_ty) => deref_ty.base_typ_is(rhs),
            _ => self == &rhs,
        }
    }

    /// Returns the dereference type if this is a pointer type.
    pub fn get_deref_type(&self) -> Option<&Type> {
        if let LirType::Pointer(deref_ty) = &*self.0 {
            Some(deref_ty)
        } else {
            None
        }
    }
}

impl Operand {
    pub fn typ(&self) -> Type {
        if let Operand::Var(v) = self {
            v.typ()
        } else {
            int_ty()
        }
    }
}

impl Program {
    pub fn validate(self) -> Result<Valid<Self>, ValidationError> {
        validate::validate(&self)?;
        Ok(Valid(self))
    }

    pub fn check_valid(&self) -> Result<(), ValidationError> {
        validate::validate(&self)
    }
}
