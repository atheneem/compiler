//! Common utilities that are shared between different parts of the compiler.

use serde::{Deserialize, Serialize};
use std::collections::BTreeSet as Set;

// SECTION: validation errors

// 'errors' will hold a list of generated validation errors.
#[derive(Clone, Debug)]
pub struct ValidationError {
    pub errors: Set<String>,
}

impl ValidationError {
    pub fn new() -> Self {
        Self { errors: Set::new() }
    }

    pub fn from_string(s: String) -> Self {
        Self {
            errors: Set::from([s]),
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Self {
        Self::from_string(s.to_string())
    }

    pub fn from_str_ctx(ctx: &str, s: &str) -> Self {
        Self::from_string(format!("[{ctx}] {s}"))
    }

    pub fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }

    pub fn add_error(&mut self, err: String) {
        self.errors.insert(err);
    }
}

impl std::ops::AddAssign for ValidationError {
    fn add_assign(&mut self, mut other: Self) {
        self.errors.append(&mut other.errors)
    }
}

impl Default for ValidationError {
    fn default() -> Self {
        ValidationError::new()
    }
}

// SECTION: newtype for valid programs

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Valid<T>(pub T);

// The helper below is only for student templates.  It skips validation as we
// don't give them the validation code.
pub fn skip_validation<T>(x: T) -> Valid<T> {
    Valid(x)
}
