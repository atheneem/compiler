use super::*;

use std::fmt::{Display, Formatter, Result as FmtResult};

impl Display for Program {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", serde_lexpr::to_string(self).unwrap())
    }
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", serde_lexpr::to_string(self).unwrap())
    }
}

impl Display for Typedef {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", serde_lexpr::to_string(self).unwrap())
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", serde_lexpr::to_string(self).unwrap())
    }
}

impl Display for Body {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", serde_lexpr::to_string(self).unwrap())
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", serde_lexpr::to_string(self).unwrap())
    }
}

impl Display for Rhs {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", serde_lexpr::to_string(self).unwrap())
    }
}

impl Display for Lval {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", serde_lexpr::to_string(self).unwrap())
    }
}

impl Display for Exp {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", serde_lexpr::to_string(self).unwrap())
    }
}
