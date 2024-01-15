use super::*;

use std::str::FromStr;

impl FromStr for Program {
    type Err = serde_lexpr::error::Error;
    fn from_str(code: &str) -> Result<Self, Self::Err> {
        serde_lexpr::from_str(code)
    }
}

impl FromStr for Decl {
    type Err = serde_lexpr::error::Error;
    fn from_str(code: &str) -> Result<Self, Self::Err> {
        serde_lexpr::from_str(code)
    }
}

impl FromStr for Typedef {
    type Err = serde_lexpr::error::Error;
    fn from_str(code: &str) -> Result<Self, Self::Err> {
        serde_lexpr::from_str(code)
    }
}

impl FromStr for Function {
    type Err = serde_lexpr::error::Error;
    fn from_str(code: &str) -> Result<Self, Self::Err> {
        serde_lexpr::from_str(code)
    }
}

impl FromStr for Body {
    type Err = serde_lexpr::error::Error;
    fn from_str(code: &str) -> Result<Self, Self::Err> {
        serde_lexpr::from_str(code)
    }
}

impl FromStr for Stmt {
    type Err = serde_lexpr::error::Error;
    fn from_str(code: &str) -> Result<Self, Self::Err> {
        serde_lexpr::from_str(code)
    }
}

impl FromStr for Rhs {
    type Err = serde_lexpr::error::Error;
    fn from_str(code: &str) -> Result<Self, Self::Err> {
        serde_lexpr::from_str(code)
    }
}

impl FromStr for Lval {
    type Err = serde_lexpr::error::Error;
    fn from_str(code: &str) -> Result<Self, Self::Err> {
        serde_lexpr::from_str(code)
    }
}

impl FromStr for Exp {
    type Err = serde_lexpr::error::Error;
    fn from_str(code: &str) -> Result<Self, Self::Err> {
        serde_lexpr::from_str(code)
    }
}
