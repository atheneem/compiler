//! Intraprocedural reaching definitions analysis.

use crate::commons::Valid;

use super::*;

// SECTION: analysis interface

// The powerset lattice.  It represents the definitions
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Value(pub Set<InstId>);

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        self.0
            .iter()
            .try_for_each(|(bb, n)| write!(f, "{bb}.{n}, "))?;
        write!(f, "}}")
    }
}

// Abstract environment
pub type Env = PointwiseEnv<Value>;

// Performs the analysis: use `forward_analysis` to implement this.
pub fn analyze(program: &Valid<Program>, func: FuncId) -> (Map<BbId, Env>, Map<InstId, Env>) {
    let program = &program.0;
    let f = &program.functions[&func];

    let init_store = Env::new(Map::new());

    forward_analysis(f, &Cfg::new(f), &init_store, &init_store)
}

// SECTION: analysis implementation

impl AbstractValue for Value {
    type Concrete = InstId;

    const BOTTOM: Self = Value(Set::new());

    fn alpha(def: InstId) -> Self {
        Value(Set::from([def]))
    }

    fn join(&self, rhs: &Self) -> Value {
        Value(self.0.union(&rhs.0).cloned().collect())
    }
}

impl AbstractEnv for Env {
    fn join_with(&mut self, rhs: &Self, _block: &BbId) -> bool {
        let mut changed = false;

        for (x, lhs) in self.values.iter_mut() {
            if let Some(rhs) = rhs.values.get(x) {
                let old = lhs.clone();
                *lhs = lhs.join(rhs);

                changed = changed || *lhs != old;
            }
        }

        for (x, rhs) in &rhs.values {
            let old = self.get(x);
            let lhs = old.join(rhs);
            self.insert(x, &lhs);

            changed = changed || lhs != old;
        }

        changed
    }

    fn analyze_inst(&mut self, inst: &Instruction) {
        use Instruction::*;

        let def = match inst {
            Alloc { lhs, .. } => Some(lhs),
            Arith { lhs, .. } => Some(lhs),
            Cmp { lhs, .. } => Some(lhs),
            CallExt { lhs, .. } => lhs.as_ref(),
            Copy { lhs, op: _ } => Some(lhs),
            Gep {
                lhs,
                src: _,
                idx: _,
            } => Some(lhs),
            Gfp { lhs, .. } => Some(lhs),
            Load { lhs, src: _ } => Some(lhs),
            Store { dst: _, op: _ } => None,
            Phi { .. } => unreachable!(),
        };

        if let Some(lhs) = def {
            self.values.insert(
                lhs.clone(),
                Value(Set::from([self.curr_inst.clone().unwrap()])),
            );
        }
    }

    fn analyze_term(&mut self, term: &Terminal) {
        use Terminal::*;

        let def = match term {
            CallDirect { lhs, .. } => lhs.as_ref(),
            CallIndirect { lhs, .. } => lhs.as_ref(),
            _ => None,
        };

        if let Some(lhs) = def {
            self.values.insert(
                lhs.clone(),
                Value(Set::from([self.curr_inst.clone().unwrap()])),
            );
        }
    }

    fn analyze_bb(&self, bb: &BasicBlock) -> Vec<Self> {
        let mut v = vec![];
        let mut s = self.clone();

        for (i, inst) in bb.insts.iter().enumerate() {
            s.curr_inst = Some((bb.id.clone(), i));
            s.analyze_inst(inst);
            v.push(s.clone());
        }

        s.curr_inst = Some((bb.id.clone(), bb.insts.len()));
        s.analyze_term(&bb.term);
        v.push(s.clone());

        v
    }
}
