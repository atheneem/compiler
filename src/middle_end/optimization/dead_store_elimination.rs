//! Dead store elimination.

use super::*;
use crate::commons::*;
use crate::middle_end::analysis::{liveness::*, *};
use crate::middle_end::lir::*;

/// The actual optimization pass.
pub fn dead_store_elim(valid_program: Valid<Program>) -> Valid<Program> {
    let mut program = valid_program.0.clone();

    program.functions = program
        .functions
        .iter()
        .map(|(id, f)| {
            let (pre_bb, pre_inst) = analyze(&valid_program, id.clone());
            (id.clone(), dse_func(pre_bb, pre_inst, f))
        })
        .collect();

    // Do not remove this validation check.  It is there to help you catch the
    // bugs early on.  The autograder uses an internal final validation check.
    program.validate().unwrap()
}

/// Dead store elimination for a single function
fn dse_func(pre_bb: Map<BbId, Env>, pre_inst: Map<InstId, Env>, func: &Function) -> Function {
    todo!("remove unused stores");
    todo!("remove unused variables")
}
