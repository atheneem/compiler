//! The inlining pass.
//!
//! Inlining a call replaces the call instruction with a jump to a copy of the
//! callee's control flow graph (CFG).  Creating a copy of the CFG requires
//! creating mangled variable and basic block names.  The components of the
//! inliner are as follows:
//!
//! - [NameGenerator] maintains a set of used names in the caller's body, and
//! generates mangled names when needed.
//!
//! - [gen_inlined_code] contains the core of the inlining functionality.  It
//! creates a copy of the callee's control flow graph, using [NameGenerator] to
//! generate mangled names for basic blocks and variables.
//!
//! - `inline_call` inlines given call site by inserting the inlined code into
//! the caller's CFG.
//!
//! - [inline_call_sites] inlines all given call sites.  This function can be
//! used for implementing different inlining strategies.
//!
//! - [inline_leaf_functions] implements a simple inlining strategy: it inlines
//! direct calls to leaf functions (functions that do not make any internal
//! calls) in the original program's call graph.

use crate::commons::Valid;

use super::super::lir::*;
use std::{
    collections::{BTreeMap as Map, BTreeSet as Set},
    ops::Bound,
};

// A type that generates mangled names that do not appear among names declared in
// the current scope.
pub struct NameGenerator {
    // Variable names that are already declared when this generator was created.
    // This contains strings rather than VarId because variables with the same
    // name but different type are not equal.
    pub declared_vars: Set<String>,
    // Basic block names that are already declared when this generator was
    // created.
    declared_bbs: Set<BbId>,
    // The scope of the generated variables.
    scope: FuncId,
}

impl NameGenerator {
    pub fn new(defining_fn: &Function) -> NameGenerator {
        let mut declared_vars = defining_fn
            .locals
            .iter()
            .map(|x| x.name().to_string())
            .collect::<Set<String>>();
        declared_vars.extend(defining_fn.params.iter().map(|x| x.name().to_string()));

        NameGenerator {
            declared_vars,
            declared_bbs: defining_fn.body.keys().cloned().collect(),
            scope: defining_fn.id.clone(),
        }
    }

    // Create a new variable whose name is based on the given variable.  The new
    // variable name contains the scope and the name of the original variable.
    //
    // The new variable is named as `bb.scope.name.N` where
    //
    // - `bb` is the name of the basic block that contains the call site.
    // - `scope` is the scope of the original variable.  If there is no associated
    //   scope (e.g. for allocation site IDs), `scope` is the empty string.
    // - `name` is the name of the original variable.
    // - `N` is a number to ensure that the freshly-generated number is unique.
    pub(super) fn mangle_var(&mut self, bb: &BbId, orig: &VarId) -> VarId {
        todo!()
    }

    // Create a fresh basic block ID based on the given call site and basic block.
    //
    // The fresh variable is named as `call_site.callee.bb.N` where
    //
    // - `call_site` is the name of the basic block that contains the call site.
    // - `callee` is the name of the callee.
    // - `bb` is the original basic block ID.
    // - `N` is a number to ensure that the freshly-generated number is unique.
    pub(super) fn mangle_bb(&mut self, call_site: &BbId, callee: &FuncId, bb: &BbId) -> BbId {
        // this one is given for free
        Self::mangle_name(
            &format!("{}.{}.{}", call_site, callee, bb),
            &mut self.declared_bbs,
            bb_id,
        )
    }

    // Generates different kinds of fresh names based on given counters and
    // checks.  This function is used by NameGenerator to generate different
    // kinds of named entities (variables, basic blocks, etc.)
    //
    // This is a helper you can implement and use for implementing mangle_var
    // and mangle_bb.
    fn mangle_name<Name: Ord + Eq + Clone, Builder: Fn(&str) -> Name>(
        prefix: &str,
        existing_names: &mut Set<Name>,
        builder: Builder,
    ) -> Name {
        todo!()
    }
}

/// Inline direct call with given components.
///
/// This function returns:
/// - a new set of basic blocks that inline the call.
/// - fresh variables created for the inlined code.
/// - ID of the entry block of the inlined code.
///
/// After adding the returned basic blocks, the call can be replaced with a jump
/// to the entry block.
pub fn gen_inlined_code(
    call_site: &BbId,
    lhs: &Option<VarId>,
    callee: &Function,
    args: &[Operand],
    next_bb: BbId,
    generator: &mut NameGenerator,
) -> (Map<BbId, BasicBlock>, Set<VarId>, BbId) {
    // Inlining:
    //  - Generate fresh basic block IDs
    //  - Rewrite each basic block in terminals
    //  - Rewrite ret instructions to (1) set lhs, (2) jump to next_bb
    //  - Rewrite all instructions
    //  - Prepend $copy instructions to the beginning of the entry block to copy
    //    the arguments

    todo!()
}

// Inline given call at the end of the basic block with given ID.
//
// This function returns an error if the given basic block does not end with a
// $call_dir instruction.
fn inline_call(
    program: &Program,
    caller: &mut Function,
    call_site: BbId,
    generator: &mut NameGenerator,
) {
    todo!()
}

/// Inline given call sites.  The call sites are grouped by function for a more
/// efficient implementation.  All inlining happens simultaneously, later
/// inlines don't copy the callee result from previous inlines.
pub fn inline_call_sites(program: &Program, call_sites: &Map<FuncId, Set<BbId>>) -> Program {
    todo!()
}

/// A compiler pass that inlines all leaf functions in the call graph formed by
/// direct calls.
pub fn inline_leaf_functions(program: Valid<Program>) -> Valid<Program> {
    todo!()
}

/// A compiler pass that inlines all non-recursive calls where the number of
/// parameters and the number of instructions the callee has are fewer than the
/// given bounds.
///
/// The number of instructions is the total number of instructions in the body.
pub fn inline_small_fns(
    program: Valid<Program>,
    param_bound: usize,
    inst_bound: usize,
) -> Valid<Program> {
    todo!()
}
