// implements miscellaneous traits for program elements.

use super::*;

// SECTION: Identifiers

// Identifiers should all be ordered by name.

impl std::cmp::PartialOrd for StructId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for StructId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (*self.0).cmp(&*(other.0))
    }
}

impl Serialize for StructId {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for StructId {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let id = String::deserialize(deserializer)?;
        Ok(struct_id(&id))
    }
}

impl std::cmp::PartialOrd for FieldId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FieldId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (*self.name).cmp(&*(other.name)) {
            std::cmp::Ordering::Equal => (self.typ.0).cmp(&(other.typ.0)),
            result => result,
        }
    }
}

impl Serialize for FieldId {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut state = serializer.serialize_struct("FieldId", 2)?;
        state.serialize_field("name", &*self.name)?;
        state.serialize_field("typ", &self.typ)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for FieldId {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        struct FieldId {
            name: String,
            typ: Type,
        }
        let field = FieldId::deserialize(deserializer)?;
        Ok(field_id(&field.name, field.typ))
    }
}

impl std::cmp::PartialOrd for FuncId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FuncId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (*self.0).cmp(&*(other.0))
    }
}

impl Serialize for FuncId {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for FuncId {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let id = String::deserialize(deserializer)?;
        Ok(func_id(&id))
    }
}

impl std::cmp::PartialOrd for BbId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BbId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (*self.0).cmp(&*(other.0))
    }
}

impl Serialize for BbId {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for BbId {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let id = String::deserialize(deserializer)?;
        Ok(bb_id(&id))
    }
}

impl std::cmp::PartialOrd for LirVar {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LirVar {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (*self.name).cmp(&*(other.name)) {
            std::cmp::Ordering::Equal => match (self.typ.0).cmp(&(other.typ.0)) {
                std::cmp::Ordering::Equal => (self.scope).cmp(&(other.scope)),
                result => result,
            },
            result => result,
        }
    }
}

impl Serialize for LirVar {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut state = serializer.serialize_struct("LirVar", 3)?;
        state.serialize_field("name", &*self.name)?;
        state.serialize_field("typ", &self.typ)?;
        state.serialize_field("scope", &self.scope)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for LirVar {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        struct Var {
            name: String,
            typ: Type,
            scope: Option<FuncId>,
        }
        let var = Var::deserialize(deserializer)?;
        Ok(lir_var(&var.name, var.typ, var.scope))
    }
}

impl std::cmp::PartialOrd for VarId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for VarId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (*self.0).cmp(&*(other.0))
    }
}

impl Serialize for VarId {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for VarId {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let var = LirVar::deserialize(deserializer)?;
        Ok(var_id(&var.name, var.typ, var.scope))
    }
}

// SECTION: Type

impl std::cmp::PartialOrd for Type {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Type {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (*self.0).cmp(&*(other.0))
    }
}

impl Serialize for Type {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Type {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let typ = LirType::deserialize(deserializer)?;
        Ok(typ_ty(typ))
    }
}

// SECTION: Program

// index structs by name.
impl std::ops::Index<StructId> for Program {
    type Output = Set<FieldId>;

    // panics if no such struct exists.
    fn index(&self, index: StructId) -> &Self::Output {
        self.structs.get(&index).unwrap()
    }
}

// index functions by name.
impl std::ops::Index<FuncId> for Program {
    type Output = Function;

    // panics if no such function exists.
    fn index(&self, index: FuncId) -> &Self::Output {
        self.functions.get(&index).unwrap()
    }
}

// SECTION: Function

// index basic blocks by label.
impl std::ops::Index<BbId> for Function {
    type Output = BasicBlock;

    // panics if no such label exists.
    fn index(&self, index: BbId) -> &Self::Output {
        self.body.get(&index).unwrap()
    }
}
