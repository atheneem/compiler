//! Intraprocedural liveness analysis.
//!
//! Remember that this is a backwards analysis!

use std::rc::Rc;

use crate::commons::Valid;

use super::*;

// SECTION: analysis interface

// The abstract environment.
#[derive(Clone, Debug)]
pub struct Env {
    // Result of reaching definitions analysis (pre sets).
    //
    // You should treat the `Rc` object just like a `Box` you cannot modify.
    reaching_defs: Rc<Map<InstId, super::reaching_defs::Env>>,
    // result of this analysis
    pub live_defs: Set<InstId>,
}

// Performs the analysis: use `backward_analysis` to implement this.
pub fn analyze(program: &Valid<Program>, func: FuncId) -> (Map<BbId, Env>, Map<InstId, Env>) {
    let reaching_def_results = Rc::new(super::reaching_defs::analyze(program, func.clone()).0);
    let program = &program.0;

    let init_store = todo!("map everything to empty set");

    todo!("call backward_analysis");
}

// SECTION: analysis implementation

impl AbstractEnv for Env {
    fn join_with(&mut self, rhs: &Self, _block: &BbId) -> bool {
        todo!()
    }

    fn analyze_inst(&mut self, inst: &Instruction) {
        todo!()
    }

    fn analyze_term(&mut self, term: &Terminal) {
        todo!()
    }

    fn analyze_bb(&self, bb: &BasicBlock) -> Vec<Self> {
        todo!()
    }
}
