//! Static analysis of lir programs.

#![allow(dead_code)]

use std::collections::{BTreeMap as Map, BTreeSet as Set, VecDeque};
use std::fmt::Display;

use super::lir::*;

pub mod call_graph;
pub mod constant_prop;
// pub mod copy_prop;
pub mod liveness;
pub mod reaching_defs;

#[cfg(test)]
mod tests;

/// Instruction IDs: this is just a combination of the basic block ID and the
/// index of the instruction in the block.
pub type InstId = (BbId, usize);

/// The control-flow graph *for a function* (abstracted so that we can easily
/// get successors and predecessors and also perform forward analyses on the
/// actual cfg or backwards analyses by reversing the edges to get a backwards
/// cfg).
#[derive(Clone, Debug)]
pub struct Cfg {
    pub entry: BbId,
    pub exit: BbId,
    succ_edges: Map<BbId, Set<BbId>>,
    pred_edges: Map<BbId, Set<BbId>>,
}

impl Cfg {
    // construct a Cfg from the given function's basic blocks.
    pub fn new(function: &Function) -> Self {
        println!("MAKING CFG");

        let entry = bb_id("entry");
        let mut exit = bb_id("exit");
        let mut succ_edges: Map<BbId, Set<BbId>> = Map::new();
        let mut pred_edges: Map<BbId, Set<BbId>> = Map::new();

        for (bbid, bb) in &function.body {
            succ_edges.insert(bbid.clone(), Set::new()); //add curr to sucessors

            if !pred_edges.contains_key(bbid) {
                //add curr to predicessors if dne
                pred_edges.insert(bbid.clone(), Set::new());
            }

            match &bb.term {
                Terminal::Branch { cond: _, tt, ff } => {
                    succ_edges.get_mut(bbid).unwrap().insert(tt.clone()); //add succ edge from curr to next
                    succ_edges.get_mut(bbid).unwrap().insert(ff.clone());

                    if pred_edges.contains_key(tt) {
                        //check in map and insert new set if dne
                        pred_edges.get_mut(tt).unwrap().insert(bbid.clone());
                    } else {
                        pred_edges.insert(tt.clone(), Set::new());
                        pred_edges.get_mut(tt).unwrap().insert(bbid.clone()); //add pred edge from next to curr
                    }

                    if pred_edges.contains_key(ff) {
                        //check in map and insert new set if dne
                        pred_edges.get_mut(ff).unwrap().insert(bbid.clone());
                    } else {
                        pred_edges.insert(ff.clone(), Set::new());
                        pred_edges.get_mut(ff).unwrap().insert(bbid.clone()); //add pred edge from next to curr
                    }
                }
                Terminal::CallDirect {
                    lhs: _,
                    callee: _,
                    args: _,
                    next_bb,
                } => {
                    succ_edges.get_mut(bbid).unwrap().insert(next_bb.clone()); //add succ edge from curr to next

                    if pred_edges.contains_key(next_bb) {
                        //check in map and insert new set if dne
                        pred_edges.get_mut(next_bb).unwrap().insert(bbid.clone());
                    } else {
                        pred_edges.insert(next_bb.clone(), Set::new());
                        pred_edges.get_mut(next_bb).unwrap().insert(bbid.clone());
                        //add pred edge from next to curr
                    }
                }
                Terminal::CallIndirect {
                    lhs: _,
                    callee: _,
                    args: _,
                    next_bb,
                } => {
                    succ_edges.get_mut(bbid).unwrap().insert(next_bb.clone()); //add succ edge from curr to next

                    if pred_edges.contains_key(next_bb) {
                        //check in map and insert new set if dne
                        pred_edges.get_mut(next_bb).unwrap().insert(bbid.clone());
                    } else {
                        pred_edges.insert(next_bb.clone(), Set::new());
                        pred_edges.get_mut(next_bb).unwrap().insert(bbid.clone());
                        //add pred edge from next to curr
                    }
                }
                Terminal::Jump(next) => {
                    succ_edges.get_mut(bbid).unwrap().insert(next.clone()); //add succ edge from curr to next

                    if pred_edges.contains_key(next) {
                        //check in map and insert new set if dne
                        pred_edges.get_mut(next).unwrap().insert(bbid.clone());
                    } else {
                        pred_edges.insert(next.clone(), Set::new());
                        pred_edges.get_mut(next).unwrap().insert(bbid.clone()); //add pred edge from next to curr
                    }
                }
                Terminal::Ret(_) => {
                    exit = bbid.clone();
                }
            }
        }

        Cfg {
            entry,
            exit,
            succ_edges,
            pred_edges,
        }
    }

    // an iterator over the successor edges of bb.
    pub fn succ(&self, bb: &BbId) -> impl Iterator<Item = &BbId> {
        self.succ_edges[bb].iter()
    }

    // an iterator over the predecessor edges of bb.
    pub fn pred(&self, bb: &BbId) -> impl Iterator<Item = &BbId> {
        self.pred_edges[bb].iter()
    }
}

/// An abstract value from an abstract lattice.
///
/// Any abstract domain for a variable implements this.
pub trait AbstractValue: Clone + Display + Eq + PartialEq {
    /// The concrete values we're abstracting.
    ///
    /// This is a generic type, basically.
    type Concrete;

    /// The bottom value of the join semi-lattice.
    const BOTTOM: Self;

    /// The abstraction of a concrete value.
    fn alpha(val: Self::Concrete) -> Self;

    /// The join of two abstract values.
    fn join(&self, rhs: &Self) -> Self;
}

/// The abstract environment (the abstract state) used for any dfa.  It needs to
/// know how to combine with other stores and how to modify itself when
/// processing an instruction or terminal.
pub trait AbstractEnv: Clone {
    // compute self = self ⊔ rhs
    //
    // `block` is the basic block self belongs to.
    //
    // Return whether the block has changed as the result of this operation.
    fn join_with(&mut self, rhs: &Self, block: &BbId) -> bool;

    // Transfer function for instructions.  Emulates what an instruction would
    // do.  Note that this function changes the current state!
    fn analyze_inst(&mut self, inst: &Instruction);

    // Transfer function for terminals.  Emulates what a terminal would do.
    // Note that this function changes the current state!
    fn analyze_term(&mut self, inst: &Terminal);

    // Transfer function for basic blocks.
    //
    // If this environment is part of a forward analysis, `self` is the pre
    // state for the basic block, and this function should return all the post
    // states for all instructions and the terminal in the block.
    //
    // If this environment is part of a backward analysis, `self` is the post
    // state for the basic block, and this function should return all the pre
    // states for all instructions and the terminal in the block.
    fn analyze_bb(&self, bb: &BasicBlock) -> Vec<Self>;
}

/// An abstract environment built as a pointwise extension of the abstract
/// domain `A`.  It is a map from variables to abstract values.
///
/// To use this in an analysis, we need to provide the abstract domain `A` for
/// each variable.
#[derive(Clone, Debug)]
pub struct PointwiseEnv<A: AbstractValue> {
    pub values: Map<VarId, A>,
    pub curr_inst: Option<InstId>,
}

impl<A: AbstractValue> PointwiseEnv<A> {
    fn new(values: Map<VarId, A>) -> Self {
        Self {
            values,
            curr_inst: None,
        }
    }

    // get the value of a variable, or bottom if it isn't present.
    pub fn get(&self, key: &VarId) -> A {
        self.values.get(key).unwrap_or(&A::BOTTOM).clone()
    }

    // insert a value for a variable.
    fn insert(&mut self, key: &VarId, val: &A) {
        self.values.insert(key.clone(), val.clone());
    }

    // get a mutable reference to the value of a variable, which will be inserted
    // with value bottom if not already present.
    fn get_mut(&mut self, key: &VarId) -> &mut A {
        self.values.entry(key.clone()).or_insert(A::BOTTOM)
    }
}

impl<A: AbstractValue> Display for PointwiseEnv<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let str = self
            .values
            .iter()
            .filter(|(x, _)| x.scope().is_some())
            .fold("".to_string(), |acc, (var, val)| {
                if *val == A::BOTTOM {
                    acc
                } else {
                    format!("{acc}{var} -> {val}\n")
                }
            });
        write!(f, "{str}")
    }
}

// SECTION: intraprocedural dataflow analysis framework

/// Analyze the given function.  Assumes that the function is from a valid
/// program.
///
/// This function starts from the entry, end performs a forward analysis.  It
/// returns:
///
/// (1) the pre state for each basic block
/// (2) the pre state for each instruction
///
/// bottom_state is the bottom value for the abstract state `A`.  You should use
/// it as the starting state for the analysis.
///
/// Hint: You can compute (1) first, then process each block only once to compute
/// (2).
pub fn forward_analysis<A: AbstractEnv + Display>(
    f: &Function,
    cfg: &Cfg,
    entry_state: &A,
    bottom_state: &A,
) -> (Map<BbId, A>, Map<InstId, A>) {
    // 1. Create an initial solution that maps entry block → entry state.
    // 2. Create a worklist containing entry.
    // 3. Implement the worklist algorithm.
    // 4. Compute per-instruction pre states.
    // 1. Create an initial solution that maps entry block → entry state.
    let mut bb_states: Map<BbId, A> = Map::new();
    let mut inst_states: Map<InstId, A> = Map::new();
    bb_states.insert(cfg.entry.clone(), entry_state.clone());

    //worklist containing entry.
    let mut worklist: VecDeque<BbId> = VecDeque::new();
    worklist.push_back(cfg.entry.clone());

    //worklist algorithm.
    while let Some(curr_bb) = worklist.pop_front() {
        //until queue empty
        let curr_state = bb_states.get(&curr_bb).unwrap_or(bottom_state).clone(); //curr state or bottom is none

        // println!("IN FORWARD ANALYSIS");

        if let Some(bb) = f.body.get(&curr_bb) {
            //procces bb insts
            let mut i = 0;
            let mut state = curr_state.clone();
            let mut fin = curr_state.clone(); //end state

            for inst in bb.insts.iter() {
                //for each inst
                // println!("inst: {}", inst);
                state.analyze_inst(inst);
                inst_states.insert((curr_bb.clone(), i), state.clone());
                i = i + 1;

                fin.analyze_inst(inst);
            }
            //terminal
            state.analyze_term(&bb.term);
            fin.analyze_term(&bb.term);
            inst_states.insert((curr_bb.clone(), bb.insts.len()), state.clone());

            // println!("States at Basic Block Start:");
            // for (bb_id, state) in &bb_states {
            //     println!("BB: {}, State: {}", bb_id, state);
            // }
            // println!("States at Instruction Start:");
            // for ((bb_id, inst_idx), state) in &inst_states {
            //     println!("BB: {}, Inst Index: {}, State: {}", bb_id, inst_idx, state);
            // }

            //add final states to sucessors
            for succ in cfg.succ(&curr_bb) {
                //start of succ bb (or bott if dne)
                let succ_state = bb_states
                    .entry(succ.clone())
                    .or_insert_with(|| bottom_state.clone());

                let updated = succ_state.join_with(&fin, &curr_bb);
                if updated {
                    //add to queue/continue analysis if state changed
                    worklist.push_back(succ.clone());
                }
            }
        }
    }

    (bb_states, inst_states)
}
