//! Optimization passes.

use std::collections::BTreeMap as Map;

pub mod constant_prop;
pub mod copy_prop;
pub mod dead_store_elimination;
pub mod inlining;

#[cfg(test)]
mod tests;
