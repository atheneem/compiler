// check whether a Program is valid:
//
// - identifiers:
//     - all identifiers match the valid regular expression.
//     - identifiers aren't reserved words (struct, fn, decl, then, int, void).
//     - every alloc has a unique identifier (across the entire program).
// - every struct has at least one field.
// - every function/basic block name maps to a function/block with that name.
// - there is a function 'main' with signature '() -> int'; every function has a
//   basic block 'entry'.
// - every function parameter is unique.
// - every function has exactly one $ret instruction.
// - for terminal instructions:
//     - target basic blocks are to existing targets.
//     - every $call_dir calls an internal function (but not main).
// - every instruction variable is declared in locals, params, or globals.
// - no local, parameter, or global variable or struct field should have a
//   Function type.
// - all instructions are well-typed.
// - every basic block is reachable from entry and reaches the exit block.
// - if a global variable has the same name as a function then that variable is
//   a function pointer to a function with the same type as the named function;
//   there cannot be a global variable named 'main'.

use super::*;
use crate::commons::ValidationError;

// SECTION: program validation

pub fn validate(program: &Program) -> Result<(), ValidationError> {
    // we separate out each check, which isn't the most efficient implementation but
    // keeps things simple.
    let mut errors = ValidationError::new();
    errors += check_identifiers(program);
    errors += check_structs(program);
    errors += check_name_mapping(program);
    errors += check_for_required_elements(program);
    errors += check_parameters(program);
    errors += check_ret(program);
    errors += check_terminators(program);
    errors += check_declared(program);
    errors += check_no_func_type(program);
    errors += check_reachability(program);
    errors += check_func_and_extern_names(program);
    errors += check_global_func_ptrs(program);

    // check_types() depends on some earlier checks for correct behavior, and so is
    // only run if all the previous checks have passed (this is overly conservative
    // but easy to maintain).
    if errors.is_empty() {
        errors += check_types(program);
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

// - function and extern declaration names:
//     - there shouldn't be an extern function with the same name as a defined
//     function
fn check_func_and_extern_names(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    for f in program.externs.keys() {
        if program.functions.contains_key(f) {
            err.add_error(format!(
                "{f} is both declared as an extern and defined as a function"
            ));
        }
    }

    err
}

// - identifiers:
//     - all identifiers match the valid regular expression.
//     - identifiers aren't reserved words (struct, fn, decl, then, int, void).
//     - every alloc has a unique identifier (across the entire program).
//
// we don't check variables inside basic blocks because the type checker will
// catch them if they differ from globals, params, and locals.
fn check_identifiers(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();
    let mut alloc_err = ValidationError::new();
    let mut seen_ids = Set::new();

    // helper function that does the actual validation check.
    let mut check = |s: &str| {
        if s.is_empty() {
            err.add_error("identifier cannot be the empty string".to_string())
        } else {
            let hdr = s.chars().next().unwrap();
            if (hdr != '_' && hdr != '@' && !hdr.is_alphabetic())
                || s[1..]
                    .chars()
                    .any(|c| c != '_' && c != '.' && !char::is_alphanumeric(c))
            {
                err.add_error(format!("{s} is an invalid identifier"));
            } else if ["struct", "fn", "decl", "then", "int", "void"].contains(&s) {
                err.add_error(format!("reserved word \"{s}\" used as identifier"));
            }
        }
    };

    // check structs.
    for (StructId(name), fields) in &program.structs {
        check(name);
        for field in fields {
            check(field.name.as_str());
        }
    }

    // check globals.
    for var in &program.globals {
        check(var.name());
    }

    // check functions.
    for (func_id, func) in &program.functions {
        check(func_id.0.as_str());
        for param in &func.params {
            check(param.name());
        }
        for local in &func.locals {
            check(local.name());
        }
        seen_ids.clear();
        for (bb_id, bb) in &func.body {
            check(bb_id.0.as_str());

            for inst in &bb.insts {
                if let Instruction::Alloc { lhs: _, num: _, id } = inst {
                    check(id.name());
                    if seen_ids.contains(&id) {
                        alloc_err.add_error(format!("alloc id \"{id}\" is not unique"));
                    } else {
                        seen_ids.insert(id);
                    }
                }
            }
        }
    }

    err += alloc_err;
    err
}

// - every struct has at least one field.
fn check_structs(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();
    for (name, fields) in &program.structs {
        if fields.is_empty() {
            err.add_error(format!("struct {name} has 0 fields"));
        }
    }
    err
}

// - every function/basic block name maps to a function/block with that name.
fn check_name_mapping(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    for (name, func) in &program.functions {
        if *name != func.id {
            err.add_error(format!("'functions' maps {name} to {}", func.id));
        }
        for (label, bb) in &func.body {
            if *label != bb.id {
                err.add_error(format!("{name}'s 'body' maps {label} to {}", bb.id));
            }
        }
    }

    err
}

// - there is a function 'main' with signature '() -> int'; every function has a
//   basic block 'entry'.
fn check_for_required_elements(program: &Program) -> ValidationError {
    let mut err = if program.functions.contains_key(&func_id("main")) {
        let mut err = ValidationError::new();
        if !program.functions[&func_id("main")].params.is_empty()
            || !matches!(&program.functions[&func_id("main")].ret_ty, Some(ty) if ty == &int_ty())
        {
            err.add_error("function main should have type () -> int".to_string());
        }
        err
    } else {
        ValidationError::from_str("there is no main function")
    };

    for (name, func) in &program.functions {
        if !func.body.contains_key(&bb_id("entry")) {
            err.add_error(format!("function {name} does not have an 'entry' block"))
        }
    }

    err
}

// - every function parameter is unique.
fn check_parameters(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    for (name, func) in &program.functions {
        let mut seen = Set::new();
        for param in &func.params {
            if seen.contains(&param) {
                err.add_error(format!("function {name} has duplicated parameter {param}"));
            } else {
                seen.insert(param);
            }
        }
    }

    err
}

// - every function has exactly one $ret instruction.
fn check_ret(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    for (name, func) in &program.functions {
        let mut num_ret = 0;

        for bb in func.body.values() {
            if let Terminal::Ret(_) = bb.term {
                num_ret += 1;
            }
        }

        if num_ret == 0 {
            err.add_error(format!("function {name} has no $ret instruction"));
        } else if num_ret > 1 {
            err.add_error(format!("function {name} has multiple $ret instructions"));
        }
    }

    err
}

// - for terminal instructions:
//     - target basic blocks are to existing targets.
//     - every $call_dir calls an internal function (but not main).
fn check_terminators(program: &Program) -> ValidationError {
    use Terminal as T;

    let mut err = ValidationError::new();

    let mut report_err = |name: &FuncId, label: &BbId, msg: &str| {
        err.add_error(format!(
            "malformed basic block {label} in function {name}: {msg}"
        ));
    };

    for (name, func) in &program.functions {
        for (label, bb) in &func.body {
            match &bb.term {
                T::Branch { tt, ff, .. } => {
                    if !func.body.contains_key(tt) || !func.body.contains_key(ff) {
                        report_err(name, label, "invalid branch target");
                    }
                }
                T::CallDirect {
                    callee, next_bb, ..
                } => {
                    if !func.body.contains_key(next_bb) {
                        report_err(name, label, "invalid call next_bb");
                    }
                    if !program.functions.contains_key(callee) {
                        report_err(name, label, "invalid callee");
                    }
                    if callee.name() == "main" {
                        report_err(name, label, "cannot call function main");
                    }
                }
                T::CallIndirect { next_bb, .. } => {
                    if !func.body.contains_key(next_bb) {
                        report_err(name, label, "invalid call next_bb");
                    }
                }
                T::Jump(target) => {
                    if !func.body.contains_key(target) {
                        report_err(name, label, "invalid jump target");
                    }
                }
                T::Ret(_) => (),
            }
        }
    }

    err
}

// - every instruction variable is declared in locals, params, or globals.
fn check_declared(program: &Program) -> ValidationError {
    use Instruction as I;
    use Operand as O;
    use Terminal as T;

    let mut err = ValidationError::new();

    for func in program.functions.values() {
        // checks whether v is declared somewhere.
        let mut check_var = |v: VarId| {
            if (v.is_global() && !program.globals.contains(&v))
                || (!v.is_global() && !func.locals.contains(&v) && !func.params.contains(&v))
            {
                err.add_error(format!(
                    "variable {v} in function {} is undeclared",
                    func.id
                ));
            }
        };

        for bb in func.body.values() {
            for inst in &bb.insts {
                match inst {
                    I::Alloc { lhs, .. } => check_var(lhs.clone()),
                    I::Arith { lhs, op1, op2, .. } => {
                        check_var(lhs.clone());
                        if let O::Var(v) = op1 {
                            check_var(v.clone());
                        }
                        if let O::Var(v) = op2 {
                            check_var(v.clone());
                        }
                    }
                    I::CallExt { lhs, args, .. } => {
                        lhs.iter().for_each(|v| check_var(v.clone()));
                        args.iter().for_each(|op| {
                            if let O::Var(v) = op {
                                check_var(v.clone());
                            }
                        })
                    }
                    I::Cmp { lhs, op1, op2, .. } => {
                        check_var(lhs.clone());
                        if let O::Var(v) = op1 {
                            check_var(v.clone());
                        }
                        if let O::Var(v) = op2 {
                            check_var(v.clone());
                        }
                    }
                    I::Copy { lhs, op } => {
                        check_var(lhs.clone());
                        if let O::Var(v) = op {
                            check_var(v.clone());
                        }
                    }
                    I::Gep { lhs, src, idx } => {
                        check_var(lhs.clone());
                        check_var(src.clone());
                        if let O::Var(v) = idx {
                            check_var(v.clone());
                        }
                    }
                    I::Gfp { lhs, src, .. } => {
                        check_var(lhs.clone());
                        check_var(src.clone());
                    }
                    I::Load { lhs, src } => {
                        check_var(lhs.clone());
                        check_var(src.clone());
                    }
                    I::Phi { lhs, args } => {
                        check_var(lhs.clone());
                        args.iter().for_each(|op| {
                            if let O::Var(v) = op {
                                check_var(v.clone());
                            }
                        })
                    }
                    I::Store { dst, op } => {
                        check_var(dst.clone());
                        if let O::Var(v) = op {
                            check_var(v.clone());
                        }
                    }
                }
            }

            match &bb.term {
                T::Branch { cond, .. } => {
                    if let O::Var(v) = cond {
                        check_var(v.clone());
                    }
                }
                T::CallDirect {
                    lhs,
                    callee: _,
                    args,
                    next_bb: _,
                } => {
                    lhs.iter().for_each(|v| check_var(v.clone()));
                    args.iter().for_each(|op| {
                        if let O::Var(v) = op {
                            check_var(v.clone());
                        }
                    })
                }
                T::CallIndirect {
                    lhs, callee, args, ..
                } => {
                    lhs.iter().for_each(|v| check_var(v.clone()));
                    check_var(callee.clone());
                    args.iter().for_each(|op| {
                        if let O::Var(v) = op {
                            check_var(v.clone());
                        }
                    })
                }
                T::Jump(_) => (),
                T::Ret(op) => {
                    op.iter().for_each(|op| {
                        if let O::Var(v) = op {
                            check_var(v.clone());
                        }
                    });
                }
            }
        }
    }

    err
}

// - all instructions are well-typed.
fn check_types(program: &Program) -> ValidationError {
    use Instruction as I;
    use LirType as LT;
    use Operand as O;
    use Terminal as T;

    let mut err = ValidationError::new();

    for (name, func) in &program.functions {
        for (label, bb) in &func.body {
            for (pos, inst) in bb.insts.iter().enumerate() {
                let mut report_err = || {
                    err.add_error(format!("instruction at {name}.{label}.{pos} is ill-typed"));
                };

                match inst {
                    // lhs must be a pointer, and not a function pointer.
                    // num must be a integer.
                    I::Alloc { lhs, num, .. } => match lhs.typ().get_deref_type() {
                        Some(typ) if (!typ.is_function()) && num.typ().is_int() => {}
                        _ => report_err(),
                    },
                    // lhs and both operands must be integers.
                    I::Arith { lhs, op1, op2, .. } => {
                        match (&*lhs.typ().0, &*op1.typ().0, &*op2.typ().0) {
                            (LT::Int, LT::Int, LT::Int) => {}
                            _ => report_err(),
                        }
                    }
                    // ext_callee should not be an internal function. lhs and args must match the
                    // type of callee (but we don't require lhs to exist even if the callee has a
                    // return type).
                    I::CallExt {
                        lhs,
                        ext_callee,
                        args,
                    } => match program.externs.get(ext_callee).map(|x| &*x.0) {
                        Some(LT::Function { ret_ty, param_ty }) => {
                            // lhs and return types should match.
                            match (lhs.as_ref().map(VarId::typ), ret_ty) {
                                (t1, t2) if t1 == *t2 => {}
                                (None, _) => {}
                                _ => report_err(),
                            }

                            // argument types and parameter types should match (taking into account
                            // that `0` can represent the nil pointer).
                            if args.len() != param_ty.len()
                                || args.iter().zip(param_ty.iter()).any(|(arg, ty)| {
                                    arg.typ() != *ty && (!ty.is_ptr() || *arg != O::CInt(0))
                                })
                            {
                                report_err()
                            }
                        }
                        _ => report_err(),
                    },
                    // lhs must be an integer and op1 and op2 must be the same type and either
                    // integers or pointers.
                    I::Cmp { lhs, op1, op2, .. } => {
                        match (&*lhs.typ().0, &*op1.typ().0, &*op2.typ().0) {
                            (LT::Int, x, y) if x == y => match x {
                                LT::Int | LT::Pointer(_) => (),
                                _ => report_err(),
                            },
                            (LT::Int, LT::Pointer(_), LT::Int) if matches!(op2, O::CInt(0)) => {}
                            (LT::Int, LT::Int, LT::Pointer(_)) if matches!(op1, O::CInt(0)) => {}
                            _ => report_err(),
                        }
                    }
                    // lhs and op must be the same type. a constant 0 can be treated as the null
                    // pointer.
                    I::Copy { lhs, op } => match (&*lhs.typ().0, &*op.typ().0) {
                        (ty1, ty2) if ty1 == ty2 => {}
                        (LT::Pointer(_), LT::Int) if matches!(op, O::CInt(0)) => {}
                        _ => report_err(),
                    },
                    // idx must be an integer. src and lhs must be pointers to the same type.
                    I::Gep { lhs, src, idx } => match (&*lhs.typ().0, &*src.typ().0, &*idx.typ().0)
                    {
                        (LT::Pointer(lhs_ty), LT::Pointer(src_ty), LT::Int) if lhs_ty == src_ty => {
                        }
                        _ => report_err(),
                    },
                    // src must be a pointer to a struct that has field and lhs must be a pointer to
                    // the type of that field.
                    I::Gfp { lhs, src, field } => match (&*lhs.typ().0, &*src.typ().0) {
                        (LT::Pointer(lhs_ty), LT::Pointer(src_ty)) => match &*src_ty.0 {
                            LT::Struct(s) => {
                                if !program.structs.contains_key(s)
                                    || !program.structs[s].contains(field)
                                    || *lhs_ty != field.typ
                                {
                                    report_err();
                                }
                            }
                            _ => report_err(),
                        },
                        _ => report_err(),
                    },
                    // src must be a pointer to the type of lhs.
                    I::Load { lhs, src } => match (&lhs.typ(), &*src.typ().0) {
                        (lhs_ty, LT::Pointer(deref_ty)) if lhs_ty == deref_ty => {}
                        _ => report_err(),
                    },
                    // args must be non-empty and lhs and all args must be the same type (taking
                    // into account that `0` can represent the nil pointer).
                    I::Phi { lhs, args } => {
                        if args.is_empty()
                            || args.iter().any(|op| {
                                op.typ() != lhs.typ() && (!lhs.typ().is_ptr() || *op != O::CInt(0))
                            })
                        {
                            report_err()
                        }
                    }
                    // dst must be a pointer to the type of op. a constant 0 can be treated as the
                    // null pointer.
                    I::Store { dst, op } => match (&*dst.typ().0, &op.typ()) {
                        (LT::Pointer(deref_ty), op_ty) if deref_ty == op_ty => {}
                        (LT::Pointer(deref_ty), _)
                            if matches!(&*deref_ty.0, LT::Pointer(_))
                                && matches!(op, O::CInt(0)) => {}
                        _ => report_err(),
                    },
                }
            }

            let mut report_err = || {
                err.add_error(format!(
                    "terminal instruction at {name}.{label}.{} is ill-typed",
                    bb.insts.len()
                ));
            };

            match &bb.term {
                // cond must be an integer.
                T::Branch { cond, .. } => match &*cond.typ().0 {
                    LT::Int => {}
                    _ => report_err(),
                },
                // lhs and args must match the type of callee (but we don't require lhs to exist
                // even if the callee has a return type).
                T::CallDirect {
                    lhs, callee, args, ..
                } => match program.functions.get(callee) {
                    Some(callee) => {
                        // lhs and return types should match.
                        if let Some(lhs) = lhs {
                            if callee.ret_ty.is_none() {
                                report_err();
                            } else if &lhs.typ() != callee.ret_ty.as_ref().unwrap() {
                                report_err();
                                continue;
                            }
                        }

                        // argument types and parameter types should match (taking into account
                        // that `0` can represent the nil pointer).
                        if args.len() != callee.params.len()
                            || args.iter().zip(callee.params.iter()).any(|(a, p)| {
                                a.typ() != p.typ() && (!p.typ().is_ptr() || *a != O::CInt(0))
                            })
                        {
                            report_err();
                        }
                    }
                    None => report_err(),
                },
                // callee must be a function pointer and lhs and args must match the type that
                // callee points to.
                T::CallIndirect {
                    lhs, callee, args, ..
                } => match &*callee.typ().0 {
                    LT::Pointer(fun_ty) => match &*fun_ty.0 {
                        LT::Function { ret_ty, param_ty } => {
                            // lhs and return types should match.
                            if let Some(lhs) = lhs {
                                if ret_ty.is_none() {
                                    report_err();
                                } else if &lhs.typ() != ret_ty.as_ref().unwrap() {
                                    report_err();
                                    continue;
                                }
                            }

                            // argument types and parameter types should match (taking into account
                            // that `0` can represent the nil pointer).
                            if args.len() != param_ty.len()
                                || args.iter().zip(param_ty.iter()).any(|(a, ty)| {
                                    a.typ() != *ty && (!ty.is_ptr() || *a != O::CInt(0))
                                })
                            {
                                report_err();
                            }
                        }
                        _ => report_err(),
                    },
                    _ => report_err(),
                },
                // nothing to check.
                T::Jump(_) => (),
                // op's type must match the enclosing function's return type (taking into account
                // that `0` can represent the nil pointer).
                T::Ret(op) => match (op.as_ref().map(|o| o.typ()), &func.ret_ty) {
                    (x, y) if x == *y => {}
                    (_, Some(t)) if op == &Some(O::CInt(0)) && t.is_ptr() => {}
                    _ => report_err(),
                },
            }
        }
    }

    err
}

// - no local, parameter, or global variable or struct field should have a
//   Function type.
fn check_no_func_type(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    for (st, fs) in &program.structs {
        for f in fs {
            if f.typ.is_function() {
                err.add_error(format!("struct {st}'s field {f} cannot be a function type"));
            }
        }
    }

    for v in &program.globals {
        if v.typ().is_function() {
            err.add_error(format!("global {v} cannot be a function type"));
        }
    }

    for f in program.functions.values() {
        for v in &f.params {
            if v.typ().is_function() {
                err.add_error(format!(
                    "function {}'s parameter {v} cannot be a function type",
                    f.id
                ));
            }
        }

        for v in &f.locals {
            if v.typ().is_function() {
                err.add_error(format!(
                    "function {}'s local {v} cannot be a function type",
                    f.id
                ));
            }
        }
    }

    err
}

// - every basic block is reachable from entry and reaches the exit block.
//
// we do _not_ check for the case where a function makes a recursive call s.t.
// somewhere in the recursive cycle a recursive call dominates the exit (thus
// making the recursion an infinite loop, and rendering everything locally
// reachable from a recursive call block unreachable in practice).
//
// lint suppression due to ascent! macro clippy warning.
#[allow(clippy::let_unit_value, clippy::collapsible_if)]
fn check_reachability(program: &Program) -> ValidationError {
    use ascent::ascent;
    use Terminal::*;

    // define reachability. we can't seem to define a generic rule that every node
    // reaches itself, so we'll have to add that information explicitly when we add
    // the edge facts.
    ascent! {
        relation entry(BbId);
        relation exit(BbId);
        relation edge(BbId, BbId);
        relation reaches(BbId, BbId);
        relation entry_reaches(BbId);
        relation reaches_exit(BbId);
        reaches(a, b) <-- edge(a, b);
        reaches(a, b) <-- reaches(a, c), edge(c, b);
        entry_reaches(a) <-- entry(bb), reaches(bb, a);
        reaches_exit(a) <-- exit(bb), reaches(a, bb);
    }

    let mut err = ValidationError::new();

    // check each function's body for the reachability property.
    for func in program.functions.values() {
        let mut ascent = AscentProgram::default();
        ascent.entry.push((bb_id("entry"),));

        // define the edge facts for the CFG.
        for (label, bb) in &func.body {
            // every node reaches itself.
            ascent.reaches.push((label.clone(), label.clone()));

            match &bb.term {
                Branch { tt, ff, .. } => {
                    ascent.edge.push((label.clone(), tt.clone()));
                    ascent.edge.push((label.clone(), ff.clone()));
                }
                CallDirect { next_bb, .. } => {
                    ascent.edge.push((label.clone(), next_bb.clone()));
                }
                CallIndirect { next_bb, .. } => {
                    ascent.edge.push((label.clone(), next_bb.clone()));
                }
                Jump(tgt) => {
                    ascent.edge.push((label.clone(), tgt.clone()));
                }
                Ret(_) => {
                    ascent.exit.push((label.clone(),));
                }
            }
        }

        ascent.run();

        if ascent.entry_reaches.len() != func.body.len() {
            let good_blocks = ascent
                .entry_reaches
                .into_iter()
                .collect::<std::collections::HashSet<_>>();
            for block in func.body.keys() {
                if !good_blocks.contains(&(block.clone(),)) {
                    err.add_error(format!(
                        "block {block} in function {} is unreachable from entry",
                        func.id
                    ));
                }
            }
        }

        if ascent.reaches_exit.len() != func.body.len() {
            let good_blocks = ascent
                .reaches_exit
                .into_iter()
                .collect::<std::collections::HashSet<_>>();
            for block in func.body.keys() {
                if !good_blocks.contains(&(block.clone(),)) {
                    err.add_error(format!(
                        "block {block} in function {} does not reach a $ret instruction",
                        func.id
                    ));
                }
            }
        }
    }

    err
}

// - if a global variable has the same name as a function then that variable is
//   a function pointer to a function with the same type as the named function;
//   there cannot be a global variable named 'main'.
fn check_global_func_ptrs(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    for glob in &program.globals {
        if glob.name() == "main" {
            err.add_error("global variable cannot be named 'main'".to_string());
            continue;
        }

        let fid = func_id(glob.name());
        if program.functions.contains_key(&fid) {
            let ftyp = func_ty(
                program.functions[&fid].ret_ty.clone(),
                program.functions[&fid]
                    .params
                    .iter()
                    .map(|p| p.typ().clone())
                    .collect(),
            );
            if !glob.typ().is_ptr() || *glob.typ().get_deref_type().unwrap() != ftyp {
                err.add_error(format!("global variable with same name as function but incorrect type: {glob} should be &{ftyp}"));
            }
        }
    }

    err
}
