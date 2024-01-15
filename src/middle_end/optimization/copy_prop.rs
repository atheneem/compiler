/*!

Copy propagation.

This optimization uses the result of a reaching definitions-like analysis to
figure out whether propagating a copy is valid.

The steps of the optimization are:

For each instruction i:
  For x ∈ use(i):
    If x has only one reaching definition, and
      that definition is a copy instruction `x = $copy y`, and
      `y` is not modified since the `$copy` instruction:
    Then, replace x with y in i.

You could use reaching definitions for the first 2 conditions, but it cannot
answer the third question (whether `y` is modified since).  So, you need to
implement another forward analysis that keeps track of modifications since last
copy (there is no starter code for that analysis).  This analysis is called the
_copy propagation analysis_.

The parameter for this analysis are:

Abstract values: sets of pairs of variables, like {(x, y)} to denote which
copies are still valid.  However, the join operator is SET INTERSECTION (not
union).  So, the lattice is flipped.

gen and kill sets:

gen(i) = {(x,y)}, if i is a copy instruction `x = $copy y`
         ∅,       otherwise

kill(i) = def(i)

fixpoint equations:

post(i) = (pre(i) \ kill(i)) ∪ gen(i)

pre(bb) = post(bb₁) ∩ post(bb₂) ∩ …

  where pred(bb) = {bb₁, bb₂, …}

Here is the intuition behind using intersection: We are keeping track of copies
whose left-hand side and right-hand side are not modified (the valid copies).
If a copy instruction is invalidated in one of the paths reaching the current
block, we need to remove it from the set of valid copy instructions.
So, we take the intersection of all predecessor nodes.

 */

use super::*;
use crate::commons::*;
use crate::middle_end::lir::*;

/// The actual optimization pass.
pub fn copy_prop(program: Valid<Program>) -> Valid<Program> {
    let mut program = program.0;

    program.functions = program
        .functions
        .iter()
        .map(|(id, f)| -> (FuncId, Function) {
            (
                id.clone(),
                todo!("define your per-function optimization routine and call it here"),
            )
        })
        .collect();

    // Do not remove this validation check.  It is there to help you catch the
    // bugs early on.  The autograder uses an internal final validation check.
    program.validate().unwrap()
}
