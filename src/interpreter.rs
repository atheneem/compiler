// LIR interpreter, support everything except external functions.

use crate::middle_end::lir::*;
use derive_more::Display;
use std::{collections::BTreeMap as Map, mem};
use Address::ToHeap;

// Maximum number of instructions to run a program for.
const INST_LIMIT: usize = 1_000_000;

// Interpret given program, return the return value of `main`.
pub fn interpret(program: Program) -> Result<i64, RuntimeError> {
    interpret_with_output(program).map(|(r, _)| r)
}

// Interpret given program, return the return value of `main` and the integers
// printed via the external function `print`.
pub fn interpret_with_output(program: Program) -> Result<(i64, Vec<i64>), RuntimeError> {
    let mut s = State::new(program);
    for _ in 0..INST_LIMIT {
        if let Some(r) = s.step()? {
            return Ok((r, s.output));
        }
    }

    Err(RuntimeError(format!(
        "the program did not finish in {INST_LIMIT} instructions."
    )))
}

// A runtime error with explanatory message.
#[derive(Clone, Debug, Display, Eq, PartialEq)]
pub struct RuntimeError(pub String);
impl std::error::Error for RuntimeError {}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Address {
    // null pointer
    Nil,
    // addresses to arrays on the heap
    ToHeap(u32),
    // addresses to a field of an object
    Field(Box<Address>, FieldId),
}

// LIR values
#[derive(Debug, Clone)]
enum Value {
    // function pointer
    FnPtr(FuncId),
    Ptr(Address),
    Int(i64),
    Struct(Map<FieldId, Box<Value>>),
}

// call sites for returning
#[derive(Debug)]
struct CallSite {
    next: BasicBlock,
    dst: Option<VarId>,
    env: Map<VarId, Value>,
    func: FuncId,
}

// Interpreter state. This is a CESK machine
#[derive(Debug)]
struct State {
    // the program's source code
    program: Program,
    // current basic block
    control: BasicBlock,
    // current function
    func: FuncId,
    // current environment
    env: Map<VarId, Value>,
    // global environment
    glob: Map<VarId, Value>,
    // store/heap
    store: Map<u32, Value>,
    // call stack
    stack: Vec<CallSite>,
    // next available heap address
    next_address: u32,
    // output of the program.  This is the collection of the integers printed
    // when print: (int) -> _ is called.
    output: Vec<i64>,
}

impl State {
    pub fn new(program: Program) -> State {
        let main = func_id("main");
        let control = program.functions[&main].body[&bb_id("entry")].clone();

        let fn_globals = program
            .globals
            .iter()
            .filter_map(|g| {
                let f = func_id(g.name());
                if program.functions.contains_key(&f) {
                    Some((g.clone(), Value::FnPtr(f)))
                } else {
                    None
                }
            })
            .collect::<Map<VarId, Value>>();

        let mut state = State {
            control,
            program,
            env: Map::new(),
            glob: Map::new(),
            store: Map::new(),
            stack: vec![],
            func: func_id("main"),
            next_address: 1,
            output: Vec::new(),
        };

        let globals = state
            .program
            .globals
            .iter()
            .map(|x| (x.clone(), state.zero_init(&x.typ())))
            .collect();
        state.env = state.new_env(&main);
        state.glob = globals;
        state.glob.extend(fn_globals);

        state
    }

    fn err<T>(&self, msg: String) -> Result<T, RuntimeError> {
        Err(RuntimeError(format!("{}: {msg}", self.func)))
    }

    // create a zero-initialized environment for given function's locals
    fn new_env(&self, f: &FuncId) -> Map<VarId, Value> {
        let f = &self.program.functions[f];
        f.locals
            .iter()
            .map(|x| (x.clone(), self.zero_init(&x.typ())))
            .collect()
    }

    // Take a step: execute a whole basic block.  Returns Some(main's return
    // value) if this is the final step.
    pub fn step(&mut self) -> Result<Option<i64>, RuntimeError> {
        for inst in self.control.insts.clone() {
            self.execute_inst(inst)?;
        }

        self.execute_terminal()
    }

    fn alloc_array(&mut self, n: u32, typ: &Type) -> Address {
        let a = self.next_address;
        self.next_address += n.max(1); // make sure that each address is unique.

        let zero_initialized_value = self.zero_init(typ);

        for i in a..(a + n) {
            self.store.insert(i, zero_initialized_value.clone());
        }

        ToHeap(a)
    }

    fn bind(&mut self, x: VarId, v: Value) -> Result<(), RuntimeError> {
        // handle nil
        let v = if let Value::Int(0) = v {
            if x.typ().is_ptr() {
                Value::Ptr(Address::Nil)
            } else {
                Value::Int(0)
            }
        } else {
            v
        };

        if let Some(existing) = self.env.get_mut(&x).or(self.glob.get_mut(&x)) {
            *existing = v;
            Ok(())
        } else {
            self.err(format!("undefined variable: {x}"))
        }
    }

    fn execute_inst(&mut self, inst: Instruction) -> Result<(), RuntimeError> {
        use Instruction::*;
        use Value::Ptr;

        match inst.clone() {
            Alloc { lhs, num, id } => {
                let n = match self.eval_to_int(&num)? {
                    n if n >= 0 => n as u32,
                    _ => return self.err("cannot allocate a negative number of elements".into()),
                };
                let a = self.alloc_array(n, &id.typ());
                self.bind(lhs, Ptr(a))?;
            }
            Arith { lhs, aop, op1, op2 } => {
                let (n1, n2) = (self.eval_to_int(&op1)?, self.eval_to_int(&op2)?);
                self.bind(
                    lhs,
                    Value::Int(match aop {
                        ArithmeticOp::Add => n1 + n2,
                        ArithmeticOp::Subtract => n1 - n2,
                        ArithmeticOp::Multiply => n1 * n2,
                        ArithmeticOp::Divide if n2 == 0 => {
                            return self.err("division by zero".into())
                        }
                        ArithmeticOp::Divide => n1 / n2,
                    }),
                )?;
            }
            CallExt {
                lhs,
                ext_callee,
                args,
            } => {
                let int_args = args
                    .iter()
                    .map(|a| self.eval_to_int(a))
                    .collect::<Result<Vec<_>, _>>();
                let args = args
                    .iter()
                    .map(|a| self.eval(a))
                    .collect::<Result<Vec<_>, _>>()?;
                match (ext_callee.name(), args.len(), lhs.is_some()) {
                ("print", 1, false) => {
		    let n = int_args?[0];
                    // println!("{n}");
		    self.output.push(n);
                },
                ("tab", 0, false) => {
                    print!("  ");
                },
                ("line", 0, false) => {
                    println!("---------------");
                },
                ("isPythagorean", 3, true) => {
                    let x = int_args?;
                    self.bind(lhs.unwrap(), Value::Int((x[0] * x[0] + x[1] * x[1] == x[2] * x[2]) as i64))?;
                },
                _ => self.err("the interpreter supports only these external functions: print: (int) -> _, isPythagorean: (int, int, int) -> int".into())?,
            }
            }
            Cmp { lhs, rop, op1, op2 } => {
                let result = match (self.eval(&op1)?, self.eval(&op2)?) {
                    (Value::Int(n1), Value::Int(n2)) => compare(rop, n1, n2),
                    (Value::Ptr(a1), Value::Ptr(a2)) => compare(rop, a1, a2),
                    (Value::Ptr(a1), Value::Int(0)) => compare(rop, a1, Address::Nil),
                    (Value::Int(0), Value::Ptr(a2)) => compare(rop, Address::Nil, a2),
                    (Value::FnPtr(a1), Value::FnPtr(a2)) => compare(rop, a1, a2),
                    (Value::FnPtr(_), Value::Ptr(Address::Nil)) => Value::Int(matches!(rop, ComparisonOp::Greater | ComparisonOp::GreaterEq) as i64),
                    (Value::Ptr(Address::Nil), Value::FnPtr(_)) => Value::Int(matches!(rop, ComparisonOp::Less | ComparisonOp::LessEq) as i64),
                    (v1, v2) => self.err(format!("comparison is allowed only between ints or between pointers, or between function pointers and nil.\nThe arguments are {v1:?}, {v2:?}"))?,
                };
                self.bind(lhs, result)?;
            }
            Copy { lhs, op } => {
                self.bind(lhs, self.eval(&op)?)?;
            }
            Gep { lhs, src, idx } => {
                let i = self.eval_to_int(&idx)?;
                if i < 0 {
                    return self.err(format!(
                        "Out-of-bounds array access, tried accessing element {i}"
                    ));
                }
                match self.lookup(&src)? {
                    Ptr(ToHeap(address)) => {
                        self.bind(lhs, Ptr(ToHeap(address + i as u32)))?;
                    }
                    v => self.err(format!("src in {inst} must be a heap pointer, got {v:?}"))?,
                }
            }
            Gfp { lhs, src, field } => match self.lookup(&src)? {
                Ptr(address) => {
                    self.bind(lhs, Ptr(Address::Field(Box::new(address), field)))?;
                }
                v => self.err(format!("src in {inst} must be a pointer, got {v:?}"))?,
            },
            Load { lhs, src } => match self.lookup(&src)? {
                Ptr(address) => {
                    let v = self.value_ref(&address)?.clone();
                    self.bind(lhs, v)?;
                }
                v => self.err(format!("expected a non-nil pointer in $store, got {v:?}"))?,
            },
            Phi { .. } => {
                unreachable!("generated LIR code shouldn't contain $phi instructions.")
            }
            Store { dst, op } => {
                let value = self.eval(&op)?;
                match self.lookup(&dst)? {
                    Ptr(address) => self.update_store(address, value)?,
                    v => self.err(format!("expected a non-nil pointer in $store, got {v:?}"))?,
                }
            }
        }

        Ok(())
    }

    fn execute_terminal(&mut self) -> Result<Option<i64>, RuntimeError> {
        match &self.control.term.clone() {
            Terminal::Branch { cond, tt, ff } => {
                let next_id = match self.eval(cond)? {
                    Value::Int(0) => ff,
                    Value::Int(_) => tt,
                    _ => self.err("argument of $branch is not an int".into())?,
                };
                self.control = self.program.functions[&self.func].body[next_id].clone();
                Ok(None)
            }
            Terminal::CallDirect {
                lhs,
                callee,
                args,
                next_bb,
            } => self.call(lhs, callee, args, next_bb),
            Terminal::CallIndirect {
                lhs,
                callee,
                args,
                next_bb,
            } => match self.lookup(callee)? {
                Value::FnPtr(f) => self.call(lhs, &f, args, next_bb),
                v => self.err(format!("tried to call non-function value {v:?}")),
            },
            Terminal::Jump(bb_id) => {
                self.control = self.program.functions[&self.func].body[bb_id].clone();
                Ok(None)
            }
            Terminal::Ret(None) => {
                let CallSite {
                    next,
                    dst,
                    env,
                    func,
                } = self
                    .stack
                    .pop()
                    .ok_or(RuntimeError("there is no callee to return to".to_owned()))?;
                assert!(dst.is_none());
                self.control = next;
                self.env = env;
                self.func = func;
                Ok(None)
            }
            Terminal::Ret(Some(e)) => {
                let v = self.eval(e)?;
                if let Some(CallSite {
                    next,
                    dst,
                    env,
                    func,
                }) = self.stack.pop()
                {
                    self.env = env;
                    self.func = func;
                    self.control = next;
                    if let Some(dst) = dst {
                        self.bind(dst, v)?;
                    }
                    Ok(None)
                } else {
                    // we are returning from main
                    assert_eq!(self.func.to_string(), "main");
                    if let Value::Int(n) = v {
                        Ok(Some(n))
                    } else {
                        self.err(format!("main returned non-int value {v:?}"))
                    }
                }
            }
        }
    }

    fn eval_to_int(&self, op: &Operand) -> Result<i64, RuntimeError> {
        match self.eval(op)? {
            Value::Int(n) => Ok(n),
            v => self.err(format!("Expected int when evaluating {op:?}, got {v:?}")),
        }
    }

    fn eval(&self, op: &Operand) -> Result<Value, RuntimeError> {
        match op {
            Operand::CInt(n) => Ok(Value::Int(*n as i64)),
            Operand::Var(x) => self.lookup(x),
        }
    }

    fn lookup(&self, x: &VarId) -> Result<Value, RuntimeError> {
        self.env
            .get(x)
            .or_else(|| self.glob.get(x))
            .cloned()
            .ok_or_else(|| RuntimeError(format!("undefined variable {x}")))
    }

    fn zero_init(&self, typ: &Type) -> Value {
        use LirType::*;
        match &*typ.0 {
            Int => Value::Int(0),
            Struct(name) => Value::Struct(
                self.program.structs[name]
                    .iter()
                    .map(|f| (f.clone(), Box::new(self.zero_init(&f.typ))))
                    .collect(),
            ),
            Function { .. } => unreachable!("function values are not allowed in LIR"),
            Pointer(_) => Value::Ptr(Address::Nil),
        }
    }

    fn update_store(&mut self, address: Address, v: Value) -> Result<(), RuntimeError> {
        *self.value_ref(&address)? = v;
        Ok(())
    }

    fn value_ref(&mut self, address: &Address) -> Result<&mut Value, RuntimeError> {
        let f = self.func.clone();
        match address {
            ToHeap(a) => self
                .store
                .get_mut(a)
                .ok_or_else(|| RuntimeError("out-of-bounds access".into())),
            Address::Field(base, field) => match self.value_ref(base)? {
                Value::Struct(strukt) => strukt.get_mut(field).map(Box::as_mut).ok_or_else(|| {
                    RuntimeError(format!(
                        "invalid address: the struct at {base:?} does not have the field {field}"
                    ))
                }),
                _ => err_(format!(
                    "{f}: invalid address: {base:?} does not refer to a struct",
                )),
            },
            Address::Nil => self.err("tried to dereference a null pointer".into()),
        }
    }

    fn call(
        &mut self,
        lhs: &Option<VarId>,
        callee: &FuncId,
        args: &[Operand],
        next_bb: &BbId,
    ) -> Result<Option<i64>, RuntimeError> {
        let mut new_env = self.new_env(callee);
        // initialize the arguments
        let params = &self.program.functions[callee].params;
        assert_eq!(params.len(), args.len());
        for (param, arg) in params.iter().zip(args) {
            new_env.insert(param.clone(), self.eval(arg)?);
        }

        self.stack.push(CallSite {
            next: self.program.functions[&self.func].body[next_bb].clone(),
            dst: lhs.clone(),
            env: mem::replace(&mut self.env, new_env),
            func: mem::replace(&mut self.func, callee.clone()),
        });
        self.control = self.program.functions[callee].body[&bb_id("entry")].clone();
        Ok(None)
    }
}

fn compare<T: Ord>(rop: ComparisonOp, n1: T, n2: T) -> Value {
    Value::Int(match rop {
        ComparisonOp::Eq => n1 == n2,
        ComparisonOp::Neq => n1 != n2,
        ComparisonOp::Less => n1 < n2,
        ComparisonOp::LessEq => n1 <= n2,
        ComparisonOp::Greater => n1 > n2,
        ComparisonOp::GreaterEq => n1 >= n2,
    } as i64)
}

fn err_<T>(msg: String) -> Result<T, RuntimeError> {
    Err(RuntimeError(msg))
}
