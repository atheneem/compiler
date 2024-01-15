// check whether a Program is valid:
//
// - identifiers:
//     - all identifiers match the pattern "(alpha)(alphanumeric)*".
//     - identifiers aren't reserved words (struct, fn, decl, then, int).
//     - no duplicates are allowed among globals, extern function declarations
//       and defined functions.
// - every struct has at least one field.
// - no duplicates are allowed among struct names.
// - there is a function 'main' with the type () -> int
// - every function parameter is unique.
// - no local, parameter, or global variable or struct field should have a
//   Function type.
// - all expressions and statements are well-typed.  this check also involves:
//   - every used variable is declared in locals, params, or globals.
//   - no calls allowed to main.
//   - the type of the expression inside return statements match the return type
//     of a function.
//   - new cannot allocate functions (i.e., `new (int) -> int` is invalid).
// - if a function has a return type, all control flow inside that function
//   reaches a return statement.
// - break and continue only occur inside loop
//
// the following checks related to the address-of operator `&` are not done, but
// would be required for memory safety.  we ensure memory safety in the subset
// of the language used in the compilers course by removing the address-of
// operator entirely.
//
// - pointers to locals (result of `&x`) should not escape the current stack
//   frame.  otherwise, they become dangling pointers.
//
// - pointers to locals (i.e., stack pointers) should not be used in array
//   indexing because they don't have header words.  this could be solved by
//   adding an array type to distinguish arrays (result of `new`) and non-array
//   pointers (result of `&`).

use super::*;
use crate::commons::*;
use crate::middle_end::lir::{LirType, StructId, Type};

use std::collections::{BTreeMap as Map, BTreeSet as Set};
use std::fmt::{Display, Formatter, Result as FmtResult};

// SECTION: data structures for type checking

// An extended version of LIR types that accommodates for null pointers and
// function calls with no type. Nil can be of any pointer type, so we represent
// its type as an unknown pointer type.
#[derive(Clone, PartialEq, Eq, Debug)]
enum PartialType {
    FullType(Type),
    // type of nil
    NullPtr,
    // "type" for calls to functions with type (...) -> _
    NoType,
}

// This implementation is used only for diagnostics.
impl Display for PartialType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            PartialType::NullPtr => write!(f, "* ??? (null pointer)"),
            PartialType::NoType => write!(
                f,
                "<no type> (result of calling a function that returns nothing)"
            ),
            PartialType::FullType(ty) => ty.fmt(f),
        }
    }
}

// Context for type checking
#[derive(Clone)]
struct TypeCtx<'a> {
    // look-up table for identifiers
    id2type: Map<&'a str, Type>,
    // look-up table for struct fields
    structs: Map<StructId, Map<&'a str, Type>>,
    // expected return type of the current function
    rettyp: PartialType,
    // current function, for error messages
    func: String,
}

// SECTION: program validation

pub fn validate(program: &Program) -> Result<(), ValidationError> {
    // we separate out each check, which isn't the most efficient implementation but
    // keeps things simple.
    let mut errors = ValidationError::new();
    errors += check_identifiers(program);
    errors += check_duplicate_toplevels(program);
    errors += check_structs(program);
    errors += check_main(program);
    errors += check_local_uniqueness(program);
    errors += check_no_func_typed_vars_or_fields(program);
    errors += check_guaranteed_return(program);
    errors += check_break_and_continue(program);

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

// - identifiers:
//     - all identifiers match the pattern "(alpha)(alphanumeric)*".
//     - identifiers aren't reserved words (struct, fn, decl, then, int).
//
// we don't check variables inside basic blocks because the type checker will
// catch them if they differ from globals, params, and locals.
fn check_identifiers(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    // helper function that does the actual validation check (except for
    // checking for duplicates).
    let mut check = |s: &str| {
        if s.is_empty() {
            err.add_error("identifier cannot be the empty string".to_string())
        } else {
            let hdr = s.chars().next().unwrap();
            if (!hdr.is_alphabetic()) || s[1..].chars().any(|c| !char::is_alphanumeric(c)) {
                err.add_error(format!("{s} is an invalid identifier"));
            } else if ["struct", "fn", "decl", "then", "int"].contains(&s) {
                err.add_error(format!("reserved word \"{s}\" used as identifier"));
            }
        }
    };

    // check typedefs.
    for typedef in &program.typedefs {
        check(&typedef.name);
        for field in &typedef.fields {
            check(&field.name);
        }
    }

    // check globals.
    for decl in &program.globals {
        check(&decl.name);
    }

    // check externs.
    for decl in &program.externs {
        check(&decl.name);
    }

    // check functions.
    for func in &program.functions {
        check(&func.name);
        for param in &func.params {
            check(&param.name);
        }
        for decl in &func.body.decls {
            check(&decl.0.name);
        }
    }

    err
}

// - no duplicates are allowed among globals, extern function declarations and
//   defined functions.
// - no struct is defined twice.
fn check_duplicate_toplevels(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();
    let mut seen_ids = Set::new();

    // check for duplicates among globals, externs, and functions

    // helper function that does the validation checks for duplicates
    let mut check_duplicates = |s: &str| {
        if !seen_ids.insert(s.to_owned()) {
            err.add_error(format!("The identifier {s} is declared as a global, extern, or declared function more than once."));
        }
    };

    for decl in &program.globals {
        check_duplicates(&decl.name);
    }

    for decl in &program.externs {
        check_duplicates(&decl.name);
    }

    for func in &program.functions {
        check_duplicates(&func.name);
    }

    // check for duplicates among structs
    seen_ids.clear();

    // just like check_duplicates, but with a different error message
    let mut check_struct_duplicates = |s: &str| {
        if !seen_ids.insert(s.to_owned()) {
            err.add_error(format!("The struct {s} is declared more than once."));
        }
    };

    for typedef in &program.typedefs {
        check_struct_duplicates(&typedef.name);
    }

    err
}

// - Check types.
// - Ensure that main is never called.
fn check_types(program: &Program) -> ValidationError {
    use PartialType::*;

    // Look up an identifier in given typing context
    fn lookup<S: AsRef<str>>(ctx: &TypeCtx, name: &S) -> Result<Type, ValidationError> {
        ctx.id2type.get(name.as_ref()).cloned().ok_or_else(|| {
            ValidationError::from_string(format!(
                "[{}] undefined variable: {}",
                ctx.func,
                name.as_ref()
            ))
        })
    }

    // Type check the arguments of an operator that accepts only ints and
    // produces an int.
    //
    // The op_name argument is the name of the operator to provide some context
    // for the error message.
    fn check_int_op(
        ctx: &TypeCtx,
        op_name: &str,
        args: &[&Exp],
    ) -> Result<PartialType, ValidationError> {
        // check that all arguments are ints
        for arg in args {
            let arg_ty = type_of(ctx, arg)?;
            if arg_ty != FullType(int_ty()) {
                return Err(ValidationError::from_string(format!(
                    "[{}] arguments to {op_name} must be ints but found an expression of type {arg_ty}",
                    ctx.func
                )));
            }
        }

        // then, the return type is also an int
        Ok(FullType(int_ty()))
    }

    // Check that the given two types are equal to each other (modulo null
    // pointer types, which can be equal to any pointer type).
    //
    // message_ctx provides some context for the type error message.
    fn check_type_eq(
        ctx: &TypeCtx,
        message_ctx: &str,
        lhs_ty: PartialType,
        rhs_ty: PartialType,
    ) -> Result<(), ValidationError> {
        let error_message = |ty1: PartialType, ty2: PartialType| {
            Err(ValidationError::from_string(format!(
                "[{}] In {message_ctx}, expected the two types to be equal, found {ty1} and {ty2}",
                ctx.func
            )))
        };

        let check_ptr = |ty: Type, on_the_lhs: bool| {
            if ty.is_ptr() {
                Ok(())
            } else {
                let ptr_msg = "a pointer type".to_owned();
                let ty_msg = ty.to_string();
                Err(ValidationError::from_string(format!(
                    "[{2}] In {message_ctx}, expected {0}, found {1}",
                    if on_the_lhs { &ty_msg } else { &ptr_msg },
                    if on_the_lhs { &ptr_msg } else { &ty_msg },
                    ctx.func,
                )))
            }
        };

        match (lhs_ty, rhs_ty) {
            (NullPtr, FullType(ty)) => check_ptr(ty, false),
            (FullType(ty), NullPtr) => check_ptr(ty, true),
            (ty1, ty2) => {
                if ty1 == ty2 {
                    Ok(())
                } else {
                    error_message(ty1, ty2)
                }
            }
        }
    }

    // Check if given type is a primitive type (int or pointer), if not raise an
    // error.
    //
    // message_ctx provides some context for the type error message.
    fn check_primitive(
        ctx: &TypeCtx,
        message_ctx: &str,
        ty: &PartialType,
    ) -> Result<(), ValidationError> {
        match ty {
            FullType(ty) if (!ty.is_int()) && (!ty.is_ptr()) => {
                Err(ValidationError::from_string(format!(
                    "[{}] In {message_ctx}, expected an int or a pointer, got a {ty}",
                    ctx.func
                )))
            }
            _ => Ok(()),
        }
    }

    // Type-check given call and return the return type if the call is well-typed.
    fn check_call(
        ctx: &TypeCtx,
        callee_ty: PartialType,
        arg_ty: Vec<PartialType>,
    ) -> Result<PartialType, ValidationError> {
        // get the underlying Type, after dereferencing the function pointer.
        match callee_ty {
            FullType(ty) => {
                let inner_ty = ty.get_deref_type().unwrap_or(&ty);
                if let LirType::Function { ret_ty, param_ty } = &*inner_ty.0 {
                    if arg_ty.len() != param_ty.len() {
                        return Err(ValidationError::from_str_ctx(&ctx.func, "Number of arguments of a function call does not match the number of parameters."));
                    }

                    arg_ty
                        .into_iter()
                        .zip(param_ty.clone().into_iter())
                        .try_for_each(|(ty1, ty2)| {
                            check_type_eq(ctx, "argument of function call", ty1, FullType(ty2))
                        })?;

                    Ok(ret_ty.clone().map_or(NoType, FullType))
                } else {
                    Err(ValidationError::from_string(format!(
                        "[{}] Tried to call a non-function.",
                        ctx.func
                    )))
                }
            }
            _ => Err(ValidationError::from_string(format!(
                "[{}] Tried to call a non-function.",
                ctx.func
            ))),
        }
    }

    fn type_of_rhs(ctx: &TypeCtx, r: &Rhs) -> Result<PartialType, ValidationError> {
        match r {
            Rhs::Exp(e) => type_of(ctx, e),
            Rhs::New { typ, num } => {
                if let Some(e) = num {
                    check_type_eq(
                        ctx,
                        "number of elements in new",
                        type_of(ctx, e)?,
                        FullType(int_ty()),
                    )?;
                }
                if typ.is_function() {
                    Err(ValidationError::from_string(format!(
                        "[{}] new cannot allocate objects of a function type. The argument of new is {}",
                        ctx.func,
                        typ
                    )))
                } else {
                    Ok(FullType(ptr_ty(typ.clone())))
                }
            }
        }
    }

    fn type_of_lval(ctx: &TypeCtx, l: &Lval) -> Result<PartialType, ValidationError> {
        match l {
            Lval::Id(name) => lookup(ctx, name).map(FullType),
            Lval::Deref(inner) => match type_of_lval(ctx, inner)? {
                FullType(typ) => match &*typ.0 {
                    LirType::Pointer(pointee_ty) => Ok(FullType(pointee_ty.clone())),
                    _ => Err(ValidationError::from_str_ctx(
                        &ctx.func,
                        "argument of dereference must be a fully-known pointer type.",
                    )),
                },
                _ => Err(ValidationError::from_str_ctx(
                    &ctx.func,
                    "argument of dereference must be a fully-known pointer type.",
                )),
            },
            Lval::ArrayAccess { ptr, index } => {
                check_type_eq(ctx, "array index", type_of(ctx, index)?, FullType(int_ty()))?;

                match type_of_lval(ctx, ptr)? {
                    NullPtr => Err(ValidationError::from_str_ctx(
                        &ctx.func,
                        "Cannot index into a null pointer",
                    )),
                    NoType => Err(ValidationError::from_str_ctx(
                        &ctx.func,
                        "Cannot index into an expression with no type",
                    )),
                    FullType(ty) => ty
                        .get_deref_type()
                        .ok_or_else(|| {
                            ValidationError::from_string(format!(
                                "[{}] Cannot index into non-pointer type {ty}",
                                ctx.func
                            ))
                        })
                        .map(|ty| FullType(ty.clone())),
                }
            }
            Lval::FieldAccess { ptr, field } => match type_of_lval(ctx, ptr)? {
                NullPtr => Err(ValidationError::from_str_ctx(
                    &ctx.func,
                    "Cannot access fields of a null pointer",
                )),
                NoType => Err(ValidationError::from_str_ctx(
                    &ctx.func,
                    "Cannot access fields of an expression with no type",
                )),
                FullType(ty) => match ty.get_deref_type().map(|t| &*t.0) {
                    Some(LirType::Struct(id)) => ctx
                        .structs
                        .get(id)
                        .ok_or_else(|| {
                            ValidationError::from_string(format!(
                                "[{}] Struct {id} is undefined",
                                ctx.func
                            ))
                        })?
                        .get(field.as_str())
                        .ok_or_else(|| {
                            ValidationError::from_string(format!(
                                "[{}] Struct {id} does not have a field {field}",
                                ctx.func
                            ))
                        })
                        .map(|ty| FullType(ty.clone())),
                    _ => Err(ValidationError::from_string(format!(
                        "[{}] Expected a pointer to a struct in field access, got: {ty}",
                        ctx.func
                    ))),
                },
            },
        }
    }

    fn type_of(ctx: &TypeCtx, e: &Exp) -> Result<PartialType, ValidationError> {
        match e {
            Exp::Num(_) => Ok(FullType(int_ty())),
            Exp::Id(name) => lookup(ctx, name).map(FullType),
            Exp::Nil => Ok(NullPtr),
            Exp::Neg(inner) => check_int_op(ctx, "arithmetic negation", &[inner]),
            Exp::Deref(inner) => match type_of(ctx, inner)? {
                FullType(typ) => match &*typ.0 {
                    LirType::Pointer(pointee_ty) => Ok(FullType(pointee_ty.clone())),
                    _ => Err(ValidationError::from_str_ctx(
                        &ctx.func,
                        "argument of dereference must be a fully-known pointer type.",
                    )),
                },
                _ => Err(ValidationError::from_str_ctx(
                    &ctx.func,
                    "argument of dereference must be a fully-known pointer type.",
                )),
            },
            Exp::Not(inner) => check_int_op(ctx, "logical negation", &[inner]),
            Exp::Arith(lhs, _, rhs) => check_int_op(ctx, "arithmetic operation", &[lhs, rhs]),
            Exp::Compare(lhs, CompareOp::Equal, rhs) => {
                let lhs_ty = type_of(ctx, lhs)?;
                let rhs_ty = type_of(ctx, rhs)?;
                check_primitive(ctx, "argument of equality", &lhs_ty)?;
                check_primitive(ctx, "argument of equality", &rhs_ty)?;
                check_type_eq(ctx, "equality", lhs_ty, rhs_ty)?;
                Ok(FullType(int_ty()))
            }
            Exp::Compare(lhs, CompareOp::NotEq, rhs) => {
                let lhs_ty = type_of(ctx, lhs)?;
                let rhs_ty = type_of(ctx, rhs)?;
                check_primitive(ctx, "argument of inequality", &lhs_ty)?;
                check_primitive(ctx, "argument of inequality", &rhs_ty)?;
                check_type_eq(ctx, "inequality", lhs_ty, rhs_ty)?;
                Ok(FullType(int_ty()))
            }
            Exp::Compare(lhs, _, rhs) => check_int_op(ctx, "arithmetic comparison", &[lhs, rhs]),
            Exp::And(lhs, rhs) => check_int_op(ctx, "conjunction", &[lhs, rhs]),
            Exp::Or(lhs, rhs) => check_int_op(ctx, "disjunction", &[lhs, rhs]),
            Exp::ArrayAccess { ptr, index } => {
                check_type_eq(ctx, "array index", type_of(ctx, index)?, FullType(int_ty()))?;

                match type_of(ctx, ptr)? {
                    NullPtr => Err(ValidationError::from_str_ctx(
                        &ctx.func,
                        "Cannot index into a null pointer",
                    )),
                    NoType => Err(ValidationError::from_str_ctx(
                        &ctx.func,
                        "Cannot index into an expression with no type",
                    )),
                    FullType(ty) => ty
                        .get_deref_type()
                        .ok_or_else(|| {
                            ValidationError::from_string(
                                "Cannot index into non-pointer type ty".to_string(),
                            )
                        })
                        .map(|ty| FullType(ty.clone())),
                }
            }
            Exp::FieldAccess { ptr, field } => match type_of(ctx, ptr)? {
                NullPtr => Err(ValidationError::from_str_ctx(
                    &ctx.func,
                    "Cannot access fields of a null pointer",
                )),
                NoType => Err(ValidationError::from_str_ctx(
                    &ctx.func,
                    "Cannot access fields of an expression with no type",
                )),
                FullType(ty) => match ty.get_deref_type().map(|t| &*t.0) {
                    Some(LirType::Struct(id)) => ctx
                        .structs
                        .get(id)
                        .ok_or_else(|| {
                            ValidationError::from_string(format!("Struct {id} is undefined"))
                        })?
                        .get(field.as_str())
                        .ok_or_else(|| {
                            ValidationError::from_string(format!(
                                "Struct {id} does not have a field {field}"
                            ))
                        })
                        .map(|ty| FullType(ty.clone())),
                    _ => Err(ValidationError::from_string(format!(
                        "Expected a pointer to a struct in field access, got: {ty}"
                    ))),
                },
            },
            Exp::Call { callee, args } => {
                let mut arg_types = Vec::new();
                for arg in args {
                    arg_types.push(type_of(ctx, arg)?);
                }
                check_call(ctx, type_of(ctx, callee)?, arg_types)
            }
        }
    }

    fn type_ck(ctx: &TypeCtx, s: &Stmt) -> Result<(), ValidationError> {
        match s {
            Stmt::If { guard, tt, ff } => {
                if type_of(ctx, guard)? != FullType(int_ty()) {
                    return Err(ValidationError::from_str_ctx(
                        &ctx.func,
                        "guards of conditionals must be of type int",
                    ));
                }
                for s in tt.iter().chain(ff.iter()) {
                    type_ck(ctx, s)?;
                }

                Ok(())
            }
            Stmt::While { guard, body } => {
                if type_of(ctx, guard)? != FullType(int_ty()) {
                    return Err(ValidationError::from_str_ctx(
                        &ctx.func,
                        "guards of loops must be of type int",
                    ));
                }
                for s in body {
                    type_ck(ctx, s)?;
                }

                Ok(())
            }
            Stmt::Assign { lhs, rhs } => check_type_eq(
                ctx,
                "assignment",
                type_of_lval(ctx, lhs)?,
                type_of_rhs(ctx, rhs)?,
            ),
            Stmt::Call { callee, args } => {
                let mut arg_types = Vec::new();
                for arg in args {
                    arg_types.push(type_of(ctx, arg)?);
                }
                check_call(ctx, type_of_lval(ctx, callee)?, arg_types).map(|_| ())
            }
            Stmt::Return(Some(expr)) => check_type_eq(
                ctx,
                "return expression",
                ctx.rettyp.clone(),
                type_of(ctx, expr)?,
            ),
            Stmt::Return(None) if ctx.rettyp != NoType => Err(ValidationError::from_str_ctx(
                &ctx.func,
                "return statement has no expression, but the function has a return type",
            )),
            Stmt::Break | Stmt::Continue | Stmt::Return(None) => Ok(()),
        }
    }

    let global_ctx = {
        let mut global_ctx = Map::new();

        for decl in program.globals.iter().chain(program.externs.iter()) {
            global_ctx.insert(decl.name.as_str(), decl.typ.clone());
        }

        for func in &program.functions {
            global_ctx.insert(
                func.name.as_str(),
                ptr_ty(func_ty(
                    func.rettyp.clone(),
                    func.params.iter().map(|decl| decl.typ.clone()).collect(),
                )),
            );
        }

        // declare the type of print
        global_ctx.insert("print", func_ty(None, vec![int_ty()]));

        // remove main from available function declarations, so that its address
        // cannot be taken.
        global_ctx.remove("main");

        global_ctx
    };

    let mut err = ValidationError::new();

    let mut ctx = TypeCtx {
        structs: program
            .typedefs
            .iter()
            .map(|typedef| {
                (
                    struct_id(&typedef.name),
                    typedef
                        .fields
                        .iter()
                        .map(|decl| (decl.name.as_str(), decl.typ.clone()))
                        .collect::<Map<&str, Type>>(),
                )
            })
            .collect(),
        id2type: Default::default(),
        rettyp: NoType,
        func: String::new(),
    };

    for func in &program.functions {
        ctx.id2type = global_ctx
            .clone()
            .into_iter()
            .chain(
                func.params
                    .iter()
                    .chain(func.body.decls.iter().map(|(d, _)| d))
                    .map(|decl| (decl.name.as_str(), decl.typ.clone())),
            )
            .collect();
        ctx.rettyp = func.rettyp.clone().map_or(NoType, FullType);
        ctx.func = func.name.clone();
        for (x, init) in &func.body.decls {
            if let Some(init) = init {
                err += type_of(&ctx, init)
                    .and_then(|ty| {
                        check_type_eq(
                            &ctx,
                            "local variable initialization",
                            FullType(x.typ.clone()),
                            ty,
                        )
                    })
                    .err()
                    .unwrap_or_default();
            }
        }

        for s in &func.body.stmts {
            err += type_ck(&ctx, s).err().unwrap_or_default();
        }
    }

    err
}

// - every struct has at least one field.
fn check_structs(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    for typedef in &program.typedefs {
        if typedef.fields.is_empty() {
            err.add_error(format!("struct {0} has 0 fields", typedef.name));
        }
    }
    err
}

// - there is a function 'main' with the type (int) -> _
fn check_main(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    match program.functions.iter().find(|f| &f.name == "main") {
        None => err.add_error("There is no main function".to_owned()),
        Some(f) => {
            if !f.params.is_empty() {
                err.add_error(format!("The main function should have 0 parameters, but it has {0} declared parameter(s)", f.params.len()));
            }

            if let Some(rettyp) = &f.rettyp {
                if !rettyp.is_int() {
                    err.add_error(format!(
                        "The main function should return int, but it is given the return type {0}",
                        rettyp
                    ));
                }
            } else {
                err.add_error(
                    "The main function should return int, but it is not given a return type"
                        .to_owned(),
                );
            }
        }
    }

    err
}

// - every function parameter is unique.
fn check_local_uniqueness(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    for func in &program.functions {
        let mut seen_ids = Set::new();

        for param in &func.params {
            if !seen_ids.insert(&param.name) {
                err.add_error(format!(
                    "the parameter {} is declared multiple times in {}",
                    param.name, func.name
                ));
            }
        }

        // locals can shadow parameters, so reset seen_ids
        seen_ids.clear();

        for (decl, _) in &func.body.decls {
            if !seen_ids.insert(&decl.name) {
                err.add_error(format!(
                    "the local {} is declared multiple times in {}",
                    decl.name, func.name
                ));
            }
        }
    }

    err
}

// - no local, parameter, or global variable or struct field should have a
//   Function type.
fn check_no_func_typed_vars_or_fields(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    let mut check_decl = |decl: &Decl| {
        if decl.typ.is_function() {
            err.add_error(format!("Globals, locals and fields cannot have function types, but {} is declared to have a function type.", decl.name));
        }
    };

    for decl in &program.globals {
        check_decl(decl);
    }

    for typedef in &program.typedefs {
        for field in &typedef.fields {
            check_decl(field);
        }
    }

    for func in &program.functions {
        for param in &func.params {
            check_decl(param);
        }

        for (decl, _) in &func.body.decls {
            check_decl(decl);
        }
    }

    err
}

// - all control flow inside a function must reach a return statement.
fn check_guaranteed_return(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    // this function returns true if all execution paths in given statement
    // reach a return statement *inside the statement itself.*
    fn always_returns(stmt: &Stmt) -> bool {
        use Stmt::*;

        match stmt {
            If { guard: _, tt, ff } => {
                tt.iter().any(always_returns) && ff.iter().any(always_returns)
            }
            While { .. } => false, // a loop may be executed 0 times, so no
            // checking is done
            Return(_) => true,
            Break | Continue | Call { .. } | Assign { .. } => false,
        }
    }

    for func in &program.functions {
        if !func.body.stmts.iter().any(always_returns) {
            err += ValidationError::from_string(format!(
                "Control flow in {} does not always reach a return statement.",
                func.name
            ));
        }
    }

    err
}

// - break and continue only occur inside loops
fn check_break_and_continue(program: &Program) -> ValidationError {
    let mut err = ValidationError::new();

    // check a statement recursively
    fn check_stmt(func_name: &str, stmt: &Stmt) -> ValidationError {
        use Stmt::*;
        let mut err = ValidationError::new();

        match stmt {
            If { guard: _, tt, ff } => {
                for s in tt.iter().chain(ff.iter()) {
                    err += check_stmt(func_name, s);
                }
            }
            While { .. } | Call { .. } | Assign { .. } | Return(_) => {}
            Break | Continue => {
                err += ValidationError::from_string(format!(
                    "break or continue appears outside loop bodies in {func_name}."
                ));
            }
        }

        err
    }

    for func in &program.functions {
        for stmt in &func.body.stmts {
            err += check_stmt(&func.name, stmt);
        }
    }

    err
}
