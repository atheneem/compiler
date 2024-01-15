//! Intraprocedural integer constant propagation, with no pointer information.

use derive_more::Display;

use crate::commons::Valid;

use super::*;

// SECTION: analysis interface

// The constant lattice.  It represents the abstract value for an integer
// variable.
#[derive(Copy, Clone, Debug, Display, Eq, PartialEq)]
pub enum Value {
    Top,
    Int(i64),
    Bot,
}

// Abstract environment
pub type Env = PointwiseEnv<Value>;

// Performs the analysis: use `forward_analysis` to implement this.
pub fn analyze(program: &Valid<Program>, func: FuncId) -> (Map<BbId, Env>, Map<InstId, Env>) {
    let program = &program.0;
    let f = &program.functions[&func];
    let mut init_env = Map::new(); //map locals to 0, params to top
    let mut bottom_env = Map::new(); //map everything to bottom

    for var in &program.globals {
        init_env.insert(var.clone(), Value::Top);
        bottom_env.insert(var.clone(), Value::Bot);
    }

    //fill init_env and bottom_env
    //locals
    for var in &f.locals {
        if !is_int_or_ptr(&var.typ()) {
            continue;
        }

        // init_env.insert(var.clone(), init);
        init_env.insert(var.clone(), Value::Int(0));
        // bottom_env.insert(var.clone(), bottom);
        bottom_env.insert(var.clone(), Value::Bot);
    }
    //params
    for var in &f.params {
        // let init = {
        //     if var.is_global() || is_int_or_ptr(&var.typ()) {
        //         Value::Top
        //     } else {
        //         println!("error params");
        //         Value::Int(0) //null
        //     }
        // };
        // let bottom = Value::Bot;

        // init_env.insert(var.clone(), init);
        init_env.insert(var.clone(), Value::Top);
        // bottom_env.insert(var.clone(), bottom);
        bottom_env.insert(var.clone(), Value::Bot);
    }

    //call forward analysis
    forward_analysis(f, &Cfg::new(f), &Env::new(init_env), &Env::new(bottom_env))
}

// SECTION: helpers

fn is_int_or_ptr(typ: &Type) -> bool {
    typ.is_int() || typ.is_ptr()
}

// SECTION: analysis implementation

use Value as V;

impl AbstractValue for Value {
    type Concrete = i32;

    const BOTTOM: Self = V::Bot;

    fn alpha(val: i32) -> Self {
        V::Int(val as i64)
    }

    fn join(&self, other: &Self) -> Self {
        //return top if not equal, else val

        match (self, other) {
            (V::Bot, val) | (val, V::Bot) => val.clone(), //if either is bot, return non bot

            (V::Int(s), V::Int(o)) => {
                //If both ints, return int
                if s == o {
                    other.clone() //return the val
                } else {
                    V::Top //else top
                }
            }
            _ => V::Top, //else return top
        }
    }
}

impl AbstractEnv for Env {
    fn join_with(&mut self, rhs: &Self, _block: &BbId) -> bool {
        let mut changed = false;

        for (var, curr_val) in &mut self.values {
            //mutible reference of vars in value map

            if let Some(rhs_val) = rhs.values.get(&var) {
                //if theres a val for current var..
                // println!("Var: {}", var);
                // println!("Current Value: {:?}", curr_val);
                // println!("RHS Value: {:?}", rhs_val);

                let new_val = curr_val.join(rhs_val); //get joined val

                // println!("New Value: {:?}", new_val);

                //check if new val has changed from curr val
                if curr_val.clone() != new_val {
                    *curr_val = new_val; //update
                    changed = true; //changed
                                    // println!("Value Updated");
                }
            }
        }
        // println!("Changed: {}\n", changed);

        //return if changed
        changed
    }

    fn analyze_inst(&mut self, inst: &Instruction) {
        use Instruction::*;

        match inst {
            Alloc { lhs, num: _, id: _ } => self.insert(lhs, &Value::Top),
            Arith { lhs, aop, op1, op2 } => {
                let x = get_result_val(self, op1);
                let y = get_result_val(self, op2);

                match (x, y) {
                    (V::Top, V::Top) => self.insert(lhs, &Value::Top),
                    (V::Top, V::Int(_)) | (V::Int(_), V::Top) => self.insert(lhs, &Value::Top),
                    (V::Int(o1), V::Int(o2)) => {
                        let val = match aop {
                            ArithmeticOp::Add => o1 + o2,
                            ArithmeticOp::Subtract => o1 - o2,
                            ArithmeticOp::Multiply => o1 * o2,
                            // if denominator=0, bot
                            ArithmeticOp::Divide => {
                                if o2 == 0 {
                                    self.insert(lhs, &Value::Bot);
                                    return;
                                } else {
                                    o1 / o2
                                }
                            }
                        };
                        self.insert(lhs, &Value::Int(val as i64));
                    }
                    (V::Int(_), V::Bot) | (V::Bot, V::Int(_)) => self.insert(lhs, &Value::Bot),
                    (V::Bot, V::Top) | (V::Top, V::Bot) => self.insert(lhs, &Value::Top),
                    (V::Bot, V::Bot) => self.insert(lhs, &Value::Bot),
                }
            }
            CallExt {
                lhs,
                ext_callee: _,
                args: _,
            } => {
                if let Some(var) = lhs {
                    self.insert(var, &Value::Top);
                }
            }
            Cmp { lhs, rop, op1, op2 } => {
                let x = get_result_val(self, op1);
                let y = get_result_val(self, op2);

                match (x, y) {
                    (V::Top, V::Top) => self.insert(lhs, &Value::Top),
                    (V::Top, V::Int(_)) | (V::Int(_), V::Top) => self.insert(lhs, &Value::Top),
                    (V::Top, V::Bot) | (V::Bot, V::Top) => self.insert(lhs, &Value::Bot),
                    (V::Int(o1), V::Int(o2)) => {
                        let val = match rop {
                            ComparisonOp::Eq => o1 == o2,
                            ComparisonOp::Neq => o1 != o2,
                            ComparisonOp::Less => o1 < o2,
                            ComparisonOp::LessEq => o1 <= o2,
                            ComparisonOp::Greater => o1 > o2,
                            ComparisonOp::GreaterEq => o1 >= o2,
                        };
                        self.insert(lhs, &Value::Int(val as i64));
                    }
                    (V::Int(_), V::Bot) | (V::Bot, V::Int(_)) => self.insert(lhs, &Value::Bot),
                    (V::Bot, V::Bot) => self.insert(lhs, &Value::Bot),
                }
            }
            Copy { lhs, op } => {
                //insert result val
                self.insert(lhs, &get_result_val(self, op));
            }
            Gep {
                lhs,
                src: _,
                idx: _,
            } => self.insert(lhs, &Value::Top),
            Gfp {
                lhs,
                src: _,
                field: _,
            } => self.insert(lhs, &Value::Top),
            Load { lhs, src: _ } => self.insert(lhs, &Value::Top),
            Phi { lhs: _, args: _ } => {}
            Store { dst: _, op: _ } => {}
        }

        fn get_int(env: &PointwiseEnv<Value>, op: &Operand) -> Option<i32> {
            match op {
                Operand::CInt(num) => Some(num.clone()),
                Operand::Var(var) => match env.get(var) {
                    Value::Int(num) => Some(num as i32),
                    _ => None,
                },
            }
        }

        fn get_result_val(env: &PointwiseEnv<Value>, op: &Operand) -> Value {
            match op {
                Operand::CInt(num) => Value::Int(num.clone() as i64),
                Operand::Var(var) => env.get(var),
            }
        }

        // fn get_result_val(env: &PointwiseEnv<Value>, op: &Operand) -> Value {
        //     match op {
        //         Operand::CInt(num) => Value::Int(num.clone() as i64),
        //         Operand::Var(var) => {
        //             if is_int_or_ptr(&var.typ()) {
        //                 //if pointer/int get val
        //                 let val = env.get(var);
        //                 match val {
        //                     Value::Top | Value::Bot => Value::Top, //top if top/bot
        //                     Value::Int(_) => val,                  //val if int
        //                 }
        //             } else {
        //                 //else, assign to int val                   ???????????
        //                 env.get(var)
        //             }
        //         }
        //     }
        // }
    }

    fn analyze_term(&mut self, term: &Terminal) {
        use Terminal::*;

        match term {
            //calls = if some, insert into env w top
            CallDirect {
                lhs,
                callee: _,
                args: _,
                next_bb: _,
            } => {
                if let Some(var) = lhs {
                    self.insert(var, &Value::Top);
                }
            }
            CallIndirect {
                lhs,
                callee: _,
                args: _,
                next_bb: _,
            } => {
                if let Some(var) = lhs {
                    self.insert(var, &Value::Top);
                }
            }
            Ret(_op) => {}
            _ => {}
        }
    }

    fn analyze_bb(&self, bb: &BasicBlock) -> Vec<Self> {
        let mut curr_state = self.clone();
        let mut states = Vec::new();

        for inst in &bb.insts {
            //for each inst, analyze and
            curr_state.analyze_inst(inst); //analyze inst
            states.push(curr_state.clone());
        }

        //terminal
        curr_state.analyze_term(&bb.term); //analyze term
        states.push(curr_state);

        //return vec of states
        states
    }
}
