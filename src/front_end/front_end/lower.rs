// lower the AST to Lir. assumes the AST is valid; may panic if it is not.

use std::mem::swap;

use super::*;
use crate::middle_end::lir::{self, bb_id, field_id, func_id, struct_id, var_id};

// SECTION: public interface

pub fn lower(ast: &Valid<Program>) -> lir::Program {
    // initialize the variable information data structure with non-function-specific
    // info; everything else will be filled in per-function by lower_functions().
    let mut info = Lowering::new();
    info.externs = lower_externs(&ast.0.externs);
    info.structs = lower_structs(&ast.0.typedefs);
    info.globals = lower_globals(&ast.0.globals);

    // fills in more info.globals info too, so this needs to come before copying
    // info.globals into the Program.
    let functions = lower_functions(&ast.0.functions, &mut info);

    lir::Program {
        structs: info.structs,
        globals: info.globals,
        externs: info.externs,
        functions,
    }
}

// SECTION: utilities

#[derive(Clone, Debug)]
struct Lowering {
    externs: Map<lir::FuncId, Type>,                // external functions
    structs: Map<lir::StructId, Set<lir::FieldId>>, // struct type info
    globals: Set<lir::VarId>,                       // global variables
    func_names: Set<lir::FuncId>,                   // function names
    curr_func: Option<lir::FuncId>,                 // current function
    params: Vec<lir::VarId>,                        // per-function parameters
    locals: Set<lir::VarId>,                        // per-function locals
    loop_info: Vec<(lir::BbId, lir::BbId)>,         // stack of loop header and loop exit blocks.
    tmp_ctr: u32,                                   // for generating fresh temporary variables
    bb_ctr: u32,                                    // for generating fresh basic blocks
}

impl Lowering {
    fn new() -> Self {
        Lowering {
            externs: Map::new(),
            structs: Map::new(),
            globals: Set::new(),
            func_names: Set::new(),
            curr_func: None,
            params: vec![],
            locals: Set::new(),
            loop_info: vec![],
            tmp_ctr: 0,
            bb_ctr: 0,
        }
    }

    // reset everything that's function-specific.
    fn reset(&mut self) {
        self.curr_func = None;
        self.params.clear();
        self.locals.clear();
        self.loop_info = vec![];
        self.tmp_ctr = 0;
        self.bb_ctr = 0;
    }

    // creates a fresh temporary variable with the given prefix and records it in
    // self.locals.
    fn create_tmp(&mut self, typ: &Type, prefix: &str) -> lir::VarId {
        self.tmp_ctr += 1;
        let tmp = var_id(
            &(prefix.to_string() + &self.tmp_ctr.to_string()),
            typ.clone(),
            self.curr_func.clone(),
        );
        self.locals.insert(tmp.clone());
        tmp
    }

    // creates a fresh basic block label.
    fn create_bb(&mut self) -> lir::BbId {
        self.bb_ctr += 1;
        bb_id(&("bb".to_string() + &self.bb_ctr.to_string()))
    }

    // looks up name in locals, parameters, and globals (in that order) to get
    // the corresponding VarId.
    fn name_to_var(&self, name: &str) -> lir::VarId {
        match self.locals.iter().find(|v| v.name() == name) {
            Some(var) => var.clone(),
            None => match self.params.iter().find(|v| v.name() == name) {
                Some(var) => var.clone(),
                None => match self.globals.iter().find(|v| v.name() == name) {
                    Some(var) => var.clone(),
                    None => unreachable!(),
                },
            },
        }
    }

    // returns whether name is an extern (consulting locals and parameters to make
    // sure the name hasn't been shadowed). we don't need to look in globals because
    // a valid program can't have any overlap between externs and globals.
    fn is_extern(&self, name: &str) -> bool {
        match self.locals.iter().find(|v| v.name() == name) {
            Some(_) => false,
            None => match self.params.iter().find(|v| v.name() == name) {
                Some(_) => false,
                None => self.externs.contains_key(&func_id(name)),
            },
        }
    }

    // returns whether id is a global function pointer with the same name as an
    // internal function.
    fn is_internal_func(&self, id: &lir::VarId) -> bool {
        id.typ().is_ptr()
            && id.typ().get_deref_type().unwrap().is_function()
            && id.scope().is_none()
            && self.func_names.contains(&func_id(id.name()))
    }

    // returns the field id with the given name of a given struct type.
    fn get_field_by_name(&self, struct_id: &lir::StructId, field_name: &str) -> lir::FieldId {
        match self.structs[struct_id]
            .iter()
            .find(|f| *f.name == field_name)
        {
            Some(field) => field.clone(),
            None => unreachable!(),
        }
    }
}

// add an instruction to the end of the curr_bb basic block.
fn add_inst(
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    curr_bb: &lir::BbId,
    inst: lir::Instruction,
) {
    body.get_mut(curr_bb).unwrap().insts.push(inst);
}

// set the terminal of the curr_bb basic block, which should be a sentinel
// value.
fn set_terminal(
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    curr_bb: &lir::BbId,
    term: lir::Terminal,
) {
    // the terminal should be a sentinel.
    assert!(
        matches!(&body[curr_bb].term, lir::Terminal::Jump(bb) if bb.name() == "_SENTINEL"),
        "terminal isn't a sentinel value: {:?}",
        &body[curr_bb].term
    );
    body.get_mut(curr_bb).unwrap().term = term;
}

// reset the terminal of the curr_bb basic block, which should not be a sentinel
// value.
fn reset_terminal(
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    curr_bb: &lir::BbId,
    term: lir::Terminal,
) {
    // the terminal should not be a sentinel.
    assert!(!matches!(&body[curr_bb].term, lir::Terminal::Jump(bb) if bb.name() == "_SENTINEL"));
    body.get_mut(curr_bb).unwrap().term = term;
}

// SECTION: lowering implementation

fn lower_structs(typedefs: &[Typedef]) -> Map<lir::StructId, Set<lir::FieldId>> {
    typedefs
        .iter()
        .map(|Typedef { name, fields }| {
            let id = struct_id(name);
            let fields = fields
                .iter()
                .map(|Decl { name, typ }| field_id(name, typ.clone()))
                .collect();
            (id, fields)
        })
        .collect()
}

fn lower_globals(globals: &[Decl]) -> Set<lir::VarId> {
    globals
        .iter()
        .map(|Decl { name, typ }| var_id(name, typ.clone(), None))
        .collect()
}

fn lower_externs(externs: &[Decl]) -> Map<lir::FuncId, Type> {
    externs
        .iter()
        .map(|Decl { name, typ }| (func_id(name), typ.clone()))
        .collect()
}

fn lower_functions(functions: &[Function], info: &mut Lowering) -> Map<lir::FuncId, lir::Function> {
    // record all internally-defined function names and create global function
    // pointers to all functions except main. translating function calls requires
    // this info, so it needs to be done before lowering each individual function.
    for func in functions {
        info.func_names.insert(func_id(&func.name));
        if func.name != "main" {
            info.globals.insert(var_id(
                &func.name,
                ptr_ty(func_ty(
                    func.rettyp.clone(),
                    func.params
                        .iter()
                        .map(|Decl { typ, .. }| typ.clone())
                        .collect(),
                )),
                None,
            ));
        }
    }

    functions
        .iter()
        .map(|func| {
            info.reset();

            // the function identifier.
            let id = func_id(&func.name);

            // initialize info with function-specific information.
            info.curr_func = Some(id.clone());
            info.params = lower_params(&func.params, id.clone());
            info.locals = lower_locals(&func.body.decls, id.clone());

            // eliminate local variable initializations.
            let stmts = eliminate_inits(&func.body);

            // lower the function body (assumes there are no local initializations or
            // logical operators, per the above transformations).
            let mut body = Map::new();
            let fin = lower_stmts(&stmts, &mut body, bb_id("entry"), info);
            assert!(fin.is_none());

            // guarantee there is a single return statement.
            eliminate_multiple_ret(&mut body, &func.rettyp, info);

            // the lowered function, minus the parameters and locals.
            let mut lir_func = lir::Function {
                id: id.clone(),
                ret_ty: func.rettyp.clone(),
                params: vec![],
                locals: Set::new(),
                body,
            };

            // put the final versions of the parameters and locals into the lir function.
            swap(&mut lir_func.params, &mut info.params);
            swap(&mut lir_func.locals, &mut info.locals);

            (id, lir_func)
        })
        .collect()
}

fn lower_params(params: &[Decl], func: lir::FuncId) -> Vec<lir::VarId> {
    params
        .iter()
        .map(|Decl { name, typ }| var_id(name, typ.clone(), Some(func.clone())))
        .collect()
}

fn lower_locals(locals: &[(Decl, Option<Exp>)], func: lir::FuncId) -> Set<lir::VarId> {
    locals
        .iter()
        .map(|(Decl { name, typ }, _)| var_id(name, typ.clone(), Some(func.clone())))
        .collect()
}

// curr_bb is the basic block we're currently inserting instructions into; the
// function returns the id of the basic block ending the lowering of stmts
// unless that block is already terminal (i.e., cannot have any instruction or
// terminal added).
fn lower_stmts(
    stmts: &[Stmt],
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    mut curr_bb: lir::BbId,
    info: &mut Lowering,
) -> Option<lir::BbId> {
    // create the basic block that we're inserting instructions into by inserting a
    // basic block with the given label, using '$jump _SENTINEL' as a sentinel for
    // the terminal indicating it hasn't been given a real value yet.
    assert!(!body.contains_key(&curr_bb));
    body.insert(
        curr_bb.clone(),
        lir::BasicBlock {
            id: curr_bb.clone(),
            insts: vec![],
            term: lir::Terminal::Jump(bb_id("_SENTINEL")),
        },
    );

    // lower each statement in turn.
    for stmt in stmts {
        match stmt {
            Stmt::If { guard, tt, ff } => match lower_if(guard, tt, ff, body, &curr_bb, info) {
                Some(bb) => curr_bb = bb,
                None => return None,
            },
            Stmt::While {
                guard,
                body: while_body,
            } => curr_bb = lower_while(guard, while_body, body, &curr_bb, info),
            Stmt::Assign { lhs, rhs } => curr_bb = lower_assign(lhs, rhs, body, &curr_bb, info),
            Stmt::Call { callee, args } => curr_bb = lower_call(callee, args, body, &curr_bb, info),
            Stmt::Break => {
                let (_, end_bb) = info.loop_info.last().unwrap(); //get curr loop (end bb)
                set_terminal(body, &curr_bb, lir::Terminal::Jump(end_bb.clone()));
                return None; //don't process other stmts
            }
            Stmt::Continue => {
                let (cond_bb, _) = info.loop_info.last().unwrap(); //get curr loop (cond check bb)
                set_terminal(body, &curr_bb, lir::Terminal::Jump(cond_bb.clone()));
                return None; //don't process other stmts
            }
            Stmt::Return(op) => {
                match op {
                    Some(exp) => {
                        let (op, bb) = lower_exp_to_operand(exp, body, &curr_bb, info);
                        curr_bb = bb;
                        set_terminal(body, &curr_bb, lir::Terminal::Ret(Some(op)));
                    }
                    None => {
                        set_terminal(body, &curr_bb, lir::Terminal::Ret(None));
                    }
                }
                return None;
            }
        }
    }

    Some(curr_bb)
}

//makes the basic block
fn create_bb(body: &mut Map<lir::BbId, lir::BasicBlock>, curr_bb: lir::BbId) {
    // create the basic block that we're inserting instructions into by inserting a
    // basic block with the given label, using '$jump _SENTINEL' as a sentinel for
    // the terminal indicating it hasn't been given a real value yet.
    assert!(!body.contains_key(&curr_bb));
    body.insert(
        curr_bb.clone(),
        lir::BasicBlock {
            id: curr_bb.clone(),
            insts: vec![],
            term: lir::Terminal::Jump(bb_id("_SENTINEL")),
        },
    );
}
// returns the join basic block, or None if both branches of the If end in
// Break/Continue/Return and hence there is no join.
fn lower_if(
    guard: &Exp,
    tt: &[Stmt],
    ff: &[Stmt],
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    curr_bb: &lir::BbId,
    info: &mut Lowering,
) -> Option<lir::BbId> {
    //if both have no stmts, can just return the same block
    if tt.is_empty() && ff.is_empty() {
        print!("both empty");
        return Some(curr_bb.clone());
    }

    let end_bb = info.create_bb(); //merging bb

    let mut both_null = true;

    let true_bb = if tt.is_empty() {
        //true (only create if not empty)
        both_null = false;
        end_bb.clone()
    } else {
        info.create_bb()
    };

    let false_bb = if ff.is_empty() {
        //false (only create if not empty)
        both_null = false;
        end_bb.clone()
    } else {
        info.create_bb()
    };

    //lower gaurd
    let (cond, cond_bb) = lower_exp_to_operand(guard, body, curr_bb, info);

    //branch based on cond, if cond true go to true_bb, else false_bb
    set_terminal(
        body,
        &cond_bb,
        lir::Terminal::Branch {
            cond,
            tt: true_bb.clone(),
            ff: false_bb.clone(),
        },
    );

    if !tt.is_empty() {
        //if there are statements
        //get returned bb
        let bb = lower_stmts(tt, body, true_bb.clone(), info);
        if let Some(ret_bb) = bb {
            set_terminal(body, &ret_bb, lir::Terminal::Jump(end_bb.clone())); //jump to end bb after exicuting stmts
            both_null = false;
        }
    }

    if !ff.is_empty() {
        //if there are statements
        //get returned bb
        let bb = lower_stmts(ff, body, false_bb.clone(), info);
        if let Some(ret_bb) = bb {
            set_terminal(body, &ret_bb, lir::Terminal::Jump(end_bb.clone())); //jump to end bb after exicuting stmts
            both_null = false;
        }
    }

    if both_null {
        return None;
    }

    //make end_bb
    create_bb(body, end_bb.clone());

    Some(end_bb)
}

// returns the loop exit basic block.
fn lower_while(
    guard: &Exp,
    while_body: &[Stmt],
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    curr_bb: &lir::BbId,
    info: &mut Lowering,
) -> lir::BbId {
    //create a block for the loop condition
    let loop_bb = info.create_bb();
    //jump to new block
    set_terminal(body, curr_bb, lir::Terminal::Jump(loop_bb.clone()));
    create_bb(body, loop_bb.clone()); //create a helper that makes a basic block

    //lower gaurd
    let (cond, cond_bb) = lower_exp_to_operand(guard, body, &loop_bb, info);

    let body_bb = info.create_bb(); //loop body (true)
    let end_bb = info.create_bb(); //after loop (false)
    create_bb(body, end_bb.clone());

    set_terminal(
        body,
        &cond_bb,
        lir::Terminal::Branch {
            //detemine where to branch based on cond
            cond,
            tt: body_bb.clone(),
            ff: end_bb.clone(),
        },
    );

    info.loop_info.push((loop_bb.clone(), end_bb.clone()));

    //lower the loop body stmts
    let bb = lower_stmts(while_body, body, body_bb, info);
    if let Some(ret_bb) = bb {
        set_terminal(body, &ret_bb, lir::Terminal::Jump(loop_bb.clone())); //return to cond bb
    }

    info.loop_info.pop();

    end_bb //return ending bb
}

fn lower_assign(
    lhs: &Lval,
    rhs: &Rhs,
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    curr_bb: &lir::BbId,
    info: &mut Lowering,
) -> lir::BbId {
    // NOTE: in direct assignments, you should emit a $copy instruction, in
    // indirect assignments you should emit a $store instruction.
    let (var, direct) = lower_lval(lhs, body, curr_bb, info); //lower lhs
    match rhs {
        Rhs::Exp(exp) => {
            //copy when lhs direct, store when indirect
            let (op, curr_bb) = lower_exp_to_operand(exp, body, curr_bb, info); //get rhs

            if direct {
                //copy
                let copy_inst = lir::Instruction::Copy { lhs: var, op };
                add_inst(body, &curr_bb, copy_inst);
            } else {
                //store
                let store_inst = lir::Instruction::Store { dst: var, op };
                add_inst(body, &curr_bb, store_inst);
            }
            curr_bb
        }
        Rhs::New { typ, num } => {
            //store

            let expr = match num {
                Some(x) => x,
                None => &Exp::Num(1), //if no number designated (ex. new int)
            };

            let (op, curr_bb) = lower_exp_to_operand(expr, body, curr_bb, info); //get rhs

            let alloc_temp = info.create_tmp(typ, "_alloc");

            if direct {
                //copy
                let alloc_inst = lir::Instruction::Alloc {
                    lhs: var,
                    num: op,
                    id: alloc_temp,
                };
                add_inst(body, &curr_bb, alloc_inst);
            } else {
                //store

                let result_var = info.create_tmp(&ptr_ty(typ.clone()), "_t"); //create a pointer to t

                //alloc space
                let alloc_inst = lir::Instruction::Alloc {
                    lhs: result_var.clone(),
                    num: op,
                    id: alloc_temp,
                };

                let store_inst = lir::Instruction::Store {
                    dst: var, //set to og var
                    op: lir::Operand::Var(result_var),
                };

                add_inst(body, &curr_bb, alloc_inst);
                add_inst(body, &curr_bb, store_inst);
            }

            curr_bb
        }
    }
}

// returns the call-return basic block, or the current basic block if this is a
// call to an external function.
//
// NOTE: This is extremely similar to the call expression implementation.
fn lower_call(
    callee: &Lval,
    args: &[Exp],
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    curr_bb: &lir::BbId,
    info: &mut Lowering,
) -> lir::BbId {
    let mut curr_bb = curr_bb.clone();

    // lower the arguments and collect the resulting operands; this may update the
    // current basic block.
    let args = {
        let mut new_args = vec![];

        for exp in args.iter() {
            let (op, bb) = lower_exp_to_operand(exp, body, &curr_bb, info);
            curr_bb = bb;
            new_args.push(op);
        }
        new_args
    };

    // the extern check has to be done before calling lower_lval() because an extern
    // doesn't have a corresponding VarId.
    match callee {
        Lval::Id(name) if info.is_extern(name) => {
            //get func id
            let fun_id = func_id(name);
            //get ty
            let vartyp = info.externs[&fun_id].clone();
            //get retty
            let retty = match &*vartyp.0 {
                lir::LirType::Function {
                    ret_ty,
                    param_ty: _,
                } => ret_ty,
                _ => panic!("not a func"),
            };

            let lhs = retty.as_ref().map(|x| info.create_tmp(x, "_t"));

            //instruction according to what ret ty is
            let call_inst = lir::Instruction::CallExt {
                // only used for calls to external functions (which can only be direct calls).
                lhs,
                ext_callee: fun_id,
                args,
            };

            add_inst(body, &curr_bb, call_inst);

            return curr_bb;
        }
        _ => {}
    }

    // if we're here then it's a direct or indirect call and we'll need a
    // call-return basic block.
    let next_bb = info.create_bb();

    // lower the lval to a VarId and a boolean indicating whether the VarId holds
    // the final function pointer value or is a pointer to the final function
    // pointer.
    let (mut callee, direct) = lower_lval(callee, body, &curr_bb, info);

    // determine if this is a direct or indirect call. callee will always be a
    // function pointer due to lowering the lval, but if it's a global function
    // pointer with the same name as an internal function then it should be a direct
    // call to that function.

    if !direct {
        //set callee to what the pointer is pointing to (load from memory adress)
        let lhs = info.create_tmp(callee.typ().get_deref_type().unwrap(), "_t");

        if !lhs.typ().is_ptr() {
            panic!("lhs should be a pointer type");
        } else {
            let load_inst = lir::Instruction::Load {
                lhs: lhs.clone(),
                src: callee.clone(),
            };
            add_inst(body, &curr_bb, load_inst);
            callee = lhs;
        }
    }

    if info.is_internal_func(&callee) {
        //direct

        let funid = func_id(callee.name());

        let t = callee.typ();
        let typ = t.get_deref_type().unwrap();

        //get type
        let retty = match &*typ.0 {
            lir::LirType::Function {
                ret_ty,
                param_ty: _,
            } => ret_ty,
            _ => panic!("not a func"),
        };

        let lhs = retty.as_ref().map(|x| info.create_tmp(x, "_t"));

        // let ret_var = info.create_tmp(&retty, "_t");

        let dir_inst = lir::Terminal::CallDirect {
            // only used for calls to internal functions.
            lhs,
            callee: funid,
            args,
            next_bb: next_bb.clone(),
        };

        set_terminal(body, &curr_bb, dir_inst);
        create_bb(body, next_bb.clone());
    } else {
        //indirect

        //get type
        let t = callee.typ();
        let typ = t.get_deref_type().unwrap();

        let retty = match &*typ.0 {
            lir::LirType::Function {
                ret_ty,
                param_ty: _,
            } => ret_ty,
            _ => panic!("not a func"),
        };

        let lhs = retty.as_ref().map(|x| info.create_tmp(x, "_t"));

        let indir_inst = lir::Terminal::CallIndirect {
            // only used for calls to internal functions.
            lhs,
            callee,
            args,
            next_bb: next_bb.clone(),
        };

        set_terminal(body, &curr_bb, indir_inst);
        create_bb(body, next_bb.clone());
    }

    // insert next_bb into the function body, using "$jump _SENTINEL" as a sentinel
    // value for the terminal indicating it hasn't been given a real value yet.
    body.insert(
        next_bb.clone(),
        lir::BasicBlock {
            id: next_bb.clone(),
            insts: vec![],
            term: lir::Terminal::Jump(bb_id("_SENTINEL")),
        },
    );

    next_bb
}

// evaluating an expression may require multiple basic blocks if the expression
// contains a call; we return the final basic block from evaluating the
// expression along with the final operand.
fn lower_exp_to_operand(
    exp: &Exp,
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    curr_bb: &lir::BbId,
    info: &mut Lowering,
) -> (lir::Operand, lir::BbId) {
    use lir::Operand::*;

    // for each instruction kind, emit the instructions to compute that
    // expression's value, then return the operand containing the value as well
    // as the new `curr_bb`.  Only `And`, `Or`, `Call` create new basic blocks,
    // but the subexpressions you have may create basic blocks too!
    match exp {
        Exp::Num(n) => (CInt(*n), curr_bb.clone()),
        Exp::Id(name) => (Var(info.name_to_var(name)), curr_bb.clone()),
        Exp::Nil => (CInt(0), curr_bb.clone()),
        Exp::Neg(e) => {
            // Handle negation: e.g., "-x"
            let (operand, new_bb) = lower_exp_to_operand(e, body, curr_bb, info);
            let result_var = info.create_tmp(&operand.typ(), "_t");
            let neg_inst = lir::Instruction::Arith {
                lhs: result_var.clone(),
                aop: lir::ArithmeticOp::Subtract,
                op1: CInt(0),
                op2: operand,
            };
            add_inst(body, &new_bb, neg_inst);
            (Var(result_var), new_bb)
        }
        Exp::Not(e) => {
            let (operand, new_bb) = lower_exp_to_operand(e, body, curr_bb, info);
            let result_var = info.create_tmp(&operand.typ(), "_t");
            let not_inst = lir::Instruction::Cmp {
                //compare to 0
                lhs: result_var.clone(),
                rop: lir::ComparisonOp::Eq,
                op1: operand,
                op2: CInt(0),
            };
            add_inst(body, &new_bb, not_inst);
            (Var(result_var), new_bb)
        }
        Exp::Deref(e) => {
            let (op, curr_bb) = match lower_exp_to_operand(e, body, curr_bb, info) {
                //make sure the lowered expr is reachable
                (Var(id), curr) => (id, curr),
                _ => unreachable!(),
            };

            let result_var = info.create_tmp(op.typ().get_deref_type().unwrap(), "_t");

            let load_inst = lir::Instruction::Load {
                lhs: result_var.clone(),
                src: op,
            };

            add_inst(body, &curr_bb, load_inst);
            (Var(result_var), curr_bb)
        }
        Exp::Arith(e1, op, e2) => {
            // Handle arithmetic operations: e.g., "e1 + e2"
            let (left_op, curr_bb) = lower_exp_to_operand(e1, body, curr_bb, info);
            let (right_op, curr_bb) = lower_exp_to_operand(e2, body, &curr_bb, info);
            let result_var = info.create_tmp(&int_ty(), "_t"); //return val is an int
            let arith_inst = match op {
                ArithOp::Add => lir::Instruction::Arith {
                    lhs: result_var.clone(),
                    aop: lir::ArithmeticOp::Add,
                    op1: left_op,
                    op2: right_op,
                },
                ArithOp::Subtract => lir::Instruction::Arith {
                    lhs: result_var.clone(),
                    aop: lir::ArithmeticOp::Subtract,
                    op1: left_op,
                    op2: right_op,
                },
                ArithOp::Multiply => lir::Instruction::Arith {
                    lhs: result_var.clone(),
                    aop: lir::ArithmeticOp::Multiply,
                    op1: left_op,
                    op2: right_op,
                },
                ArithOp::Divide => lir::Instruction::Arith {
                    lhs: result_var.clone(),
                    aop: lir::ArithmeticOp::Divide,
                    op1: left_op,
                    op2: right_op,
                },
            };
            // Add the arithmetic instruction to the current basic block.
            add_inst(body, &curr_bb, arith_inst);
            (Var(result_var), curr_bb)
        }
        Exp::Compare(e1, op, e2) => {
            let (lhs, curr_bb) = lower_exp_to_operand(e1, body, curr_bb, info);
            let (rhs, curr_bb) = lower_exp_to_operand(e2, body, &curr_bb, info);
            let result_var = info.create_tmp(&int_ty(), "_t");
            let cmp_inst = match op {
                CompareOp::Equal => lir::Instruction::Cmp {
                    lhs: result_var.clone(),
                    rop: lir::ComparisonOp::Eq,
                    op1: lhs,
                    op2: rhs,
                },
                CompareOp::NotEq => lir::Instruction::Cmp {
                    lhs: result_var.clone(),
                    rop: lir::ComparisonOp::Neq,
                    op1: lhs,
                    op2: rhs,
                },
                CompareOp::Lt => lir::Instruction::Cmp {
                    lhs: result_var.clone(),
                    rop: lir::ComparisonOp::Less,
                    op1: lhs,
                    op2: rhs,
                },
                CompareOp::Lte => lir::Instruction::Cmp {
                    lhs: result_var.clone(),
                    rop: lir::ComparisonOp::LessEq,
                    op1: lhs,
                    op2: rhs,
                },
                CompareOp::Gt => lir::Instruction::Cmp {
                    lhs: result_var.clone(),
                    rop: lir::ComparisonOp::Greater,
                    op1: lhs,
                    op2: rhs,
                },
                CompareOp::Gte => lir::Instruction::Cmp {
                    lhs: result_var.clone(),
                    rop: lir::ComparisonOp::GreaterEq,
                    op1: lhs,
                    op2: rhs,
                },
            };

            // Add the arithmetic instruction to the current basic block.
            add_inst(body, &curr_bb, cmp_inst);
            (Var(result_var), curr_bb)
        }
        Exp::ArrayAccess { ptr, index } => {
            let (point, curr_bb) = lower_exp_to_operand(ptr, body, curr_bb, info);
            let (ind, curr_bb) = lower_exp_to_operand(index, body, &curr_bb, info);

            let result_var = info.create_tmp(&point.typ(), "_t"); //pointer of the same type as array

            let varid = match point.clone() {
                //get varid
                Var(x) => x,
                CInt(_) => panic!("supposed to be a var"),
            };

            let gep_inst = lir::Instruction::Gep {
                // Get Element Pointer.  Sets lhs to an offset of idx elements from src.
                // Both lhs and src are pointers of the same type.
                lhs: result_var.clone(),
                src: varid.clone(),
                idx: ind,
            };
            let ptr_ty = point.typ();
            let ptr_ty_res = match ptr_ty.get_deref_type() {
                Some(x) => x,
                None => panic!("not a pointer type"),
            };
            let result_var2 = info.create_tmp(ptr_ty_res, "_t"); //get the type its pointing to

            let load_inst = lir::Instruction::Load {
                lhs: result_var2.clone(),
                src: result_var, //load for the old temp
            };

            //add gep and load inst
            add_inst(body, &curr_bb, gep_inst);
            add_inst(body, &curr_bb, load_inst);

            (Var(result_var2), curr_bb)
        }
        Exp::FieldAccess { ptr, field } => {
            let (point, curr_bb) = lower_exp_to_operand(ptr, body, curr_bb, info);

            let pt_ty = point.typ(); //get the type of what ptr points to
            let ptr_ty_res = match pt_ty.get_deref_type() {
                Some(x) => x,
                None => panic!("not a pointer type"),
            };
            //get struct id
            let struct_id = match &*ptr_ty_res.0 {
                lir::LirType::Struct(x) => x,
                _ => panic!("not a struct id"),
            };
            //get field id
            let field_id = info.get_field_by_name(struct_id, field);

            let varid = match point.clone() {
                //get varid
                Var(x) => x,
                CInt(_) => panic!("supposed to be a var"),
            };

            let ptr_typ = ptr_ty(field_id.typ.clone()); //pointer type that points to field type

            let result_var = info.create_tmp(&ptr_typ, "_t"); //load the field from the struct the pointers pointing to

            let gfp_inst = lir::Instruction::Gfp {
                // Get Field Pointer.  Sets lhs to a pointer to the given field of the
                // object src points to.
                lhs: result_var.clone(),
                src: varid.clone(),
                field: field_id.clone(),
            };

            let result_var2 = info.create_tmp(&field_id.typ, "_t"); //get the type its pointing to

            let load_inst = lir::Instruction::Load {
                lhs: result_var2.clone(),
                src: result_var,
            };

            //add gep and load inst
            add_inst(body, &curr_bb, gfp_inst);
            add_inst(body, &curr_bb, load_inst);

            (Var(result_var2), curr_bb)
        }
        Exp::Call { callee, args } => {
            let mut curr_bb = curr_bb.clone();

            // lower the arguments and collect the resulting operands; this may update the
            // current basic block.
            let args = {
                let mut new_args = vec![];

                for exp in args.iter() {
                    let (op, bb) = lower_exp_to_operand(exp, body, &curr_bb, info);
                    curr_bb = bb;
                    new_args.push(op);
                }
                new_args
            };

            // the extern check has to be done before calling lower_lval() because an extern
            // doesn't have a corresponding VarId.
            match &**callee {
                Exp::Id(name) if info.is_extern(name) => {
                    //get func id
                    let fun_id = func_id(name);
                    //get ty
                    let vartyp = info.externs[&fun_id].clone();
                    //get retty
                    let retty = match &*vartyp.0 {
                        lir::LirType::Function {
                            ret_ty,
                            param_ty: _,
                        } => ret_ty.as_ref().unwrap(),
                        _ => panic!("not a func"),
                    };

                    let result_var = info.create_tmp(retty, "_t");

                    //instruction according to what ret ty is
                    let call_inst = lir::Instruction::CallExt {
                        // only used for calls to external functions (which can only be direct calls).
                        lhs: Some(result_var.clone()),
                        ext_callee: fun_id,
                        args,
                    };

                    add_inst(body, &curr_bb, call_inst);

                    return (Var(result_var), curr_bb);
                }
                _ => {}
            }

            // if we're here then it's a direct or indirect call and we'll need a
            // call-return basic block.
            let next_bb = info.create_bb();

            // emit lhs = $call_{dir, idr} callee(args)
            let (callee, curr_bb) = lower_exp_to_operand(callee, body, &curr_bb, info);

            // the callee must be a VarId.
            let callee: lir::VarId = match callee {
                lir::Operand::Var(var) => var,
                _ => unreachable!(),
            };

            let funid = func_id(callee.name());

            //get ty
            let mut lirtyp = &*callee.typ().0; //either fun ty or pointer to fun ty

            while let lir::LirType::Pointer(inner_ty) = lirtyp {
                //check if lirtyp is a pointer, extract the inner type
                lirtyp = &*inner_ty.0; //update lirtyp with the inner type
            }

            let retty = match lirtyp {
                //get ret ty
                lir::LirType::Function {
                    ret_ty,
                    param_ty: _,
                } => ret_ty.as_ref(),
                _ => panic!("not a func"),
            };

            let lhs = match retty {
                //if ret type is some, make temp, otherwise none
                Some(x) => info.create_tmp(x, "_t"),
                _ => panic!("must have retty"),
            };

            //determine extern vs intern
            if info.is_internal_func(&callee) {
                //direct

                // let ret_var = info.create_tmp(&retty, "_t");

                let dir_inst = lir::Terminal::CallDirect {
                    // only used for calls to internal functions.
                    lhs: Some(lhs.clone()),
                    callee: funid,
                    args,
                    next_bb: next_bb.clone(),
                };

                set_terminal(body, &curr_bb, dir_inst);
            } else {
                //indirect

                let indir_inst = lir::Terminal::CallIndirect {
                    // only used for calls to internal functions.
                    lhs: Some(lhs.clone()),
                    callee,
                    args,
                    next_bb: next_bb.clone(),
                };

                set_terminal(body, &curr_bb, indir_inst);
            }

            create_bb(body, next_bb.clone());

            (Var(lhs), next_bb)
        }
        Exp::And(e1, e2) => {
            // given 'e1 and e2' generate the following code:
            //
            //   _t <- eval(e1)
            //   // create basic blocks bb2 and bb3
            //   $branch _t bb2 bb3
            // bb2:
            //   _t' <- eval(e2)  // may create new basic blocks
            //   _t = $copy _t'
            //   $jump bb3
            // bb3:
            //   // empty
            //
            // then, curr_bb = bb3, result = _t
            //
            let (op1, curr_bb) = lower_exp_to_operand(e1, body, curr_bb, info);
            let true_bb = info.create_bb(); //create bbs
            let false_bb = info.create_bb();

            let tmp = info.create_tmp(&op1.clone().typ(), "_t");
            add_inst(
                body,
                &curr_bb,
                lir::Instruction::Copy {
                    lhs: tmp.clone(),
                    op: op1.clone(),
                },
            ); //copy op1 to temp

            create_bb(body, true_bb.clone()); //init true_bb

            let (op2, curr_bb) = lower_exp_to_operand(e2, body, &curr_bb, info);

            let branch_inst = lir::Terminal::Branch {
                //branch depending on e1
                cond: Var(tmp.clone()),
                tt: true_bb.clone(),
                ff: false_bb.clone(),
            };
            set_terminal(body, &curr_bb, branch_inst);

            add_inst(
                body,
                &true_bb,
                lir::Instruction::Copy {
                    lhs: tmp.clone(),
                    op: op2.clone(),
                },
            ); //copy o2 to temp

            create_bb(body, false_bb.clone()); //init true_bb

            set_terminal(body, &true_bb, lir::Terminal::Jump(false_bb.clone()));

            (Var(tmp), false_bb)
        }
        Exp::Or(e1, e2) => {
            // given 'e1 and e2' generate the following code:
            //
            //   _t <- eval(e1)
            //   // create basic blocks bb2 and bb3
            //   $branch _t bb3 bb2
            // bb2:
            //   _t' <- eval(e2)  // may create new basic blocks
            //   _t = $copy _t'
            //   $jump bb3
            // bb3:
            //   // empty
            //
            // then, curr_bb = bb3, result = _t
            let (op1, curr_bb) = lower_exp_to_operand(e1, body, curr_bb, info);
            let true_bb = info.create_bb(); //create bbs
            let false_bb = info.create_bb();

            let tmp = info.create_tmp(&op1.clone().typ(), "_t");
            add_inst(
                body,
                &curr_bb,
                lir::Instruction::Copy {
                    lhs: tmp.clone(),
                    op: op1.clone(),
                },
            ); //copy op1 to temp

            create_bb(body, true_bb.clone()); //init true_bb

            let (op2, curr_bb) = lower_exp_to_operand(e2, body, &curr_bb, info); //up to date basic blocks

            let branch_inst = lir::Terminal::Branch {
                //branch depending on e1
                cond: Var(tmp.clone()),
                tt: false_bb.clone(),
                ff: true_bb.clone(),
            };
            set_terminal(body, &curr_bb, branch_inst);

            add_inst(
                body,
                &true_bb,
                lir::Instruction::Copy {
                    lhs: tmp.clone(),
                    op: op2.clone(),
                },
            ); //copy o2 to temp

            create_bb(body, false_bb.clone()); //init true_bb

            set_terminal(body, &true_bb, lir::Terminal::Jump(false_bb.clone()));

            (Var(tmp), false_bb)
        }
    }
}

// given an Lval (i.e., an expression indicating where to store a value) returns
// a VarId and a boolean indicating whether the VarId should directly hold the
// value (true) or it holds a pointer to where the value should be held (false).
fn lower_lval(
    lval: &Lval,
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    curr_bb: &lir::BbId,
    info: &mut Lowering,
) -> (lir::VarId, bool) {
    // helper function: creates a temporary and loads the ptr value into that
    // temporary, returning the created temporary. the temporary should itself be a
    // pointer.
    fn create_load(
        ptr: &lir::VarId,
        body: &mut Map<lir::BbId, lir::BasicBlock>,
        curr_bb: &lir::BbId,
        info: &mut Lowering,
    ) -> lir::VarId {
        let lhs = info.create_tmp(ptr.typ().get_deref_type().unwrap(), "_t"); //type of what ptr points to

        if !lhs.typ().is_ptr() {
            panic!("lhs should be a pointer type");
        } else {
            let load_inst = lir::Instruction::Load {
                lhs: lhs.clone(),
                src: ptr.clone(),
            };
            add_inst(body, curr_bb, load_inst);
            lhs
        }
    }

    match lval {
        // var (a direct access to a variable)
        Lval::Id(var) => (info.name_to_var(var), true),
        //ptr *
        Lval::Deref(ptr) => {
            let (mut ptr, b) = lower_lval(ptr, body, curr_bb, info);
            if !b {
                //if no direct access
                ptr = create_load(&ptr, body, curr_bb, info);
            }

            (ptr, false) //don't have direct access to var
        }
        // ptr[index]
        Lval::ArrayAccess { ptr, index } => {
            let (mut val, b) = lower_lval(ptr, body, curr_bb, info); //seeing if have dir access to val
            if !b {
                //if no direct access
                val = create_load(&val, body, curr_bb, info);
            }

            let lhs = info.create_tmp(&val.typ(), "_t");

            let (ind, bb) = lower_exp_to_operand(index, body, curr_bb, info); //getting value itself out, need instruction

            assert_eq!(curr_bb, &bb); //make sure theyre the same bb

            let gep_inst = lir::Instruction::Gep {
                // Get Element Pointer.  Sets lhs to an offset of idx elements from src.
                // Both lhs and src are pointers of the same type.
                lhs: lhs.clone(),
                src: val,
                idx: ind,
            };

            add_inst(body, curr_bb, gep_inst);

            (lhs, false) //no direct access
        }

        // ptr.field
        Lval::FieldAccess { ptr, field } => {
            let (mut ptr, b) = lower_lval(ptr, body, curr_bb, info); //seeing if have dir access to val
            if !b {
                //if no direct access
                ptr = create_load(&ptr, body, curr_bb, info);
            }

            let struct_id = match &*ptr.typ().get_deref_type().unwrap().0 {
                //struct id (dereferenced type of pointer)
                lir::LirType::Struct(x) => x.clone(),
                _ => panic!("not a struct id"),
            };

            //get field from struct id
            let field_id = info.get_field_by_name(&struct_id, field);

            //create pointer type
            let lhs = info.create_tmp(&ptr_ty(field_id.typ.clone()), "_t");

            //get field pointer
            let gfp_inst = lir::Instruction::Gfp {
                // Get Element Pointer.  Sets lhs to an offset of idx elements from src.
                // Both lhs and src are pointers of the same type.
                lhs: lhs.clone(),
                src: ptr,
                field: field_id.clone(),
            };

            add_inst(body, curr_bb, gfp_inst);
            (lhs, false) //no direct field access (returning var to field access)
        }
    }
}

// SECTION: eliminating initializations and cleaning up $ret instructions

// takes a Body (containing declarations and statements) and returns the
// statements prepended with assignments implementing any initializations in the
// declarations.
fn eliminate_inits(body: &Body) -> Vec<Stmt> {
    let mut ret = vec![]; //vec of stmts to return

    ret.extend(body.decls.iter().filter_map(|(decl, initializer)| {
        initializer.clone().map(|init_exp| {
            //create assignment from initilizer, add to vec
            Stmt::Assign {
                lhs: Lval::Id(decl.name.clone()),
                rhs: Rhs::Exp(init_exp),
            }
        })
    }));

    ret.extend(body.stmts.clone()); //add stmts to vec
    ret
}

// if there are multiple return statements, transform them so there is a single
// return statement.
fn eliminate_multiple_ret(
    body: &mut Map<lir::BbId, lir::BasicBlock>,
    rettyp: &Option<Type>,
    info: &mut Lowering,
) {
    // collect all basic blocks ending in a $ret.
    let mut ret_blocks = vec![];
    for (bb_id, bb) in body.iter() {
        if let lir::Terminal::Ret(_) = &bb.term {
            ret_blocks.push(bb_id.clone());
        }
    }
    // if there's only one $ret, there's nothing else to do.
    if ret_blocks.len() <= 1 {
        return;
    }

    // create a new basic block named "exit" containing the sole $ret in the
    // function. we rely on the fact that lowering a function does not create
    // any basic blocks named "exit" before this step.
    let exit_id = bb_id("exit");

    let ret = if let Some(typ) = rettyp {
        // replace each $ret with a jump to the exit block. since the function returns a
        // value, insert an assignment at the end of each such basic block storing the
        // returned value in a temporary variable and have the sole $ret return that
        // variable.
        let tmp = info.create_tmp(typ, "_ret"); //store ret val             // MOVE OUT OF IF?

        for bb_id in ret_blocks {
            //for every ret block
            if let Some(bb) = body.get_mut(&bb_id) {
                //get bbid

                let op = match &mut bb.term {
                    //get operand
                    lir::Terminal::Ret(op) => op,
                    _ => panic!("should be a ret"),
                };

                if let Some(ret_op) = op {
                    let copy_inst = lir::Instruction::Copy {
                        //store ret to temp
                        lhs: tmp.clone(),
                        op: ret_op.clone(),
                    };
                    add_inst(body, &bb_id.clone(), copy_inst);
                }
                reset_terminal(body, &bb_id, lir::Terminal::Jump(exit_id.clone()));
                //replace the $ret terminal w jump to exit ???
            }
        }
        Some(lir::Operand::Var(tmp))
    } else {
        // do the same thing except we don't need to return anything.
        for bb_id in ret_blocks {
            if let Some(bb) = body.get_mut(&bb_id) {
                //get bb

                if let lir::Terminal::Ret(_) = &bb.term {
                    reset_terminal(body, &bb_id, lir::Terminal::Jump(exit_id.clone()));
                    //replace the $ret terminal w jump to exit
                }
            }
        }
        None
    };

    body.insert(
        exit_id.clone(),
        lir::BasicBlock {
            id: exit_id.clone(),
            insts: vec![],
            term: lir::Terminal::Ret(ret),
        },
    );
}
