// uses the pest parser combinator library to implement the FromStr trait for
// Program.

// NOTE: check into the lint warning suppressed below at some point.

use super::*;

use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;

#[derive(pest_derive::Parser)]
#[grammar_inline = r#"
WHITESPACE = _{ " " | "\t" }
COMMENT = _{ "//" ~ (!NEWLINE ~ ANY)* ~ &NEWLINE }

program = { SOI ~ NEWLINE* ~ (struct_def ~ NEWLINE*)* ~ (global_def ~ NEWLINE*)* ~ (extern_decl ~NEWLINE*)* ~ (function_def ~ NEWLINE*)+ ~ EOI }

struct_def = { struct_hdr ~ "{" ~ NEWLINE ~ field_def+ ~ "}" ~ NEWLINE }
struct_hdr = { "struct" ~ ident}
field_def = { ident ~ ":" ~ type_id ~ NEWLINE }

global_def = { ident ~ ":" ~ type_id ~ NEWLINE }

extern_decl = { "extern" ~ ident ~ ":" ~ func_typ ~ NEWLINE }

function_def = { function_hdr ~ "(" ~ parameters? ~ ")" ~ "->" ~ ret_ty ~ "{" ~ NEWLINE ~ body_def ~ "}" ~ NEWLINE }
function_hdr = { "fn" ~ ident }

parameters = _{ parameter ~ ("," ~ parameter)* }
parameter = { ident ~ ":" ~ type_id }

body_def = { NEWLINE* ~ decl? ~ NEWLINE* ~ (basic_block ~ NEWLINE*)+ }
decl = { "let" ~ local ~ ("," ~ local)* }
local = { ident ~ ":" ~ type_id }
basic_block = { ident ~ ":" ~ NEWLINE* ~ inst* ~ terminal }

inst = _{ (alloc | arith | callext | cmp | copy | gep | gfp | load | phi | store) ~ NEWLINE }
alloc = { ident ~ "=" ~ "$alloc" ~ operand ~ "[" ~ ident ~ "]" }
arith = { ident ~ "=" ~ "$arith" ~ aop ~ operand ~ operand }
callext = { (ident ~ "=")? ~ "$call_ext" ~ ident ~ "(" ~ (operand ~ ("," ~ operand)*)? ~ ")" }
cmp = { ident ~ "=" ~ "$cmp" ~ rop ~ operand ~ operand }
copy = { ident ~ "=" ~ "$copy" ~ operand }
gep = { ident ~ "=" ~ "$gep" ~ ident ~ operand }
gfp = { ident ~ "=" ~ "$gfp" ~ ident ~ ident }
load = { ident ~ "=" ~ "$load" ~ ident }
phi = { ident ~ "=" ~ "$phi" ~ "(" ~ operand ~ ("," ~ operand)* ~")" }
ret = { "$ret" ~ operand? }
store = { "$store" ~ ident ~ operand }

terminal = { (branch | calldir | callidr | jump | ret) ~ NEWLINE }
branch = { "$branch" ~ operand ~ ident ~ ident }
calldir = { (ident ~ "=")? ~ "$call_dir" ~ ident ~ "(" ~ (operand ~ ("," ~ operand)*)? ~ ")" ~ "then" ~ ident }
callidr = { (ident ~ "=")? ~ "$call_idr" ~ ident ~ "(" ~ (operand ~ ("," ~ operand)*)? ~ ")" ~ "then" ~ ident }
jump = { "$jump" ~ ident }

aop = { "add" | "sub" | "mul" | "div" }
rop = { "eq" | "neq" | "lte" | "lt" | "gte" | "gt" }

type_id = { "int" | ident | func_typ | ptr_typ }
func_typ = { "(" ~ (type_id ~("," ~ type_id)*)? ~ ")" ~ "->" ~ ret_ty }
ret_ty = { "_" | type_id }
ptr_typ = { "&" ~ type_id }

ident = @{ ((("@" | "_") ~ ASCII_ALPHANUMERIC) | ASCII_ALPHA) ~ ("_" | "." | ASCII_ALPHANUMERIC)* }
num = @{ "-"? ~ ASCII_DIGIT+ }
operand = { ident | num }
"#]
struct ProgramParser;

// We can get two kinds of errors: a parse error from pest, or a violation of
// the context-sensitive syntactic rules encountered when processing the parse
// tree resulting from pest.
#[derive(Clone, Debug, Display, Eq, PartialEq)]
pub enum Errors {
    Parse(Error<Rule>),
    ContextSensitive(String),
}

// allows for parse() to be called on strings containing lir code. returns a
// pest error if parsing fails.
impl std::str::FromStr for Program {
    type Err = Errors;

    fn from_str(prog_str: &str) -> Result<Self, Self::Err> {
        // get the parse tree from the provided string and use it to create a Program.
        match ProgramParser::parse(Rule::program, prog_str) {
            Ok(mut parse_tree) => create_program(parse_tree.next().unwrap()),
            Err(err) => Err(Errors::Parse(err)),
        }
    }
}

// create a Program from the parse tree rooted at program.
#[allow(clippy::result_large_err)]
fn create_program(parse_tree: Pair<Rule>) -> Result<Program, Errors> {
    assert_eq!(parse_tree.as_rule(), Rule::program);

    let mut structs: Map<StructId, Set<FieldId>> = Map::new();
    let mut globals: Set<VarId> = Set::new();
    let mut externs: Map<FuncId, Type> = Map::new();
    let mut functions: Map<FuncId, Function> = Map::new();

    for inner in parse_tree.into_inner() {
        // fill in structs, globals, and functions.
        match inner.as_rule() {
            Rule::struct_def => create_struct(&mut structs, inner)?,
            Rule::global_def => create_global(&mut globals, inner)?,
            Rule::extern_decl => create_extern(&mut externs, inner)?,
            Rule::function_def => create_function(&mut functions, inner, &globals)?,
            Rule::EOI => (),
            _ => unreachable!(),
        };
    }

    Ok(Program {
        structs,
        globals,
        functions,
        externs,
    })
}

// create a struct from the parse tree rooted at struct_def.
#[allow(clippy::result_large_err)]
fn create_struct(
    structs: &mut Map<StructId, Set<FieldId>>,
    struct_def: Pair<Rule>,
) -> Result<(), Errors> {
    assert_eq!(struct_def.as_rule(), Rule::struct_def);
    let mut struct_inner = struct_def.into_inner();

    let struct_id = struct_id(
        struct_inner
            .next()
            .unwrap()
            .into_inner()
            .next()
            .unwrap()
            .as_str(),
    );

    if structs.contains_key(&struct_id) {
        return Err(Errors::ContextSensitive(format!(
            "duplicate struct {struct_id}"
        )));
    }

    let mut fields: Set<FieldId> = Set::new();

    for field_def in struct_inner {
        let mut field_info = field_def.into_inner();
        let field_name = field_info.next().unwrap().as_str();

        if fields.iter().any(|f| f.name.as_str() == field_name) {
            return Err(Errors::ContextSensitive(format!(
                "duplicate field {field_name} in struct {struct_id}"
            )));
        }

        fields.insert(field_id(
            field_name,
            create_type(field_info.next().unwrap()),
        ));
    }

    structs.insert(struct_id, fields);
    Ok(())
}

// create a global from the parse tree rooted at global_def.
#[allow(clippy::result_large_err)]
fn create_global(globals: &mut Set<VarId>, global_def: Pair<Rule>) -> Result<(), Errors> {
    assert_eq!(global_def.as_rule(), Rule::global_def);
    let mut global_def = global_def.into_inner();

    let glob_name = global_def.next().unwrap().as_str();

    if globals.iter().any(|g| g.name() == glob_name) {
        return Err(Errors::ContextSensitive(format!(
            "duplicate global variable {glob_name}"
        )));
    }

    globals.insert(var_id(
        glob_name,
        create_type(global_def.next().unwrap()),
        None,
    ));
    Ok(())
}

// create an extern function declaration from the parse tree rooted at
// extern_def
#[allow(clippy::result_large_err)]
fn create_extern(externs: &mut Map<FuncId, Type>, extern_decl: Pair<Rule>) -> Result<(), Errors> {
    assert_eq!(extern_decl.as_rule(), Rule::extern_decl);
    let mut extern_decl = extern_decl.into_inner();

    let func_name = func_id(extern_decl.next().unwrap().as_str());

    if externs.contains_key(&func_name) {
        return Err(Errors::ContextSensitive(format!(
            "duplicate extern declaration {func_name}"
        )));
    }

    let func_ty = create_function_type(extern_decl.next().unwrap());

    externs.insert(func_name, func_ty);

    Ok(())
}

// create a Function from the parse tree rooted at function_def.
#[allow(clippy::result_large_err)]
fn create_function(
    functions: &mut Map<FuncId, Function>,
    function_def: Pair<Rule>,
    globals: &Set<VarId>,
) -> Result<(), Errors> {
    assert_eq!(function_def.as_rule(), Rule::function_def);
    let mut function_def = function_def.into_inner();

    let func_name = func_id(
        function_def
            .next()
            .unwrap()
            .into_inner()
            .next()
            .unwrap()
            .as_str(),
    );

    if functions.contains_key(&func_name) {
        return Err(Errors::ContextSensitive(format!(
            "duplicate function {func_name}"
        )));
    }

    let func = {
        let mut params = vec![];
        let mut ret_ty = None;
        let mut locals = Set::new();
        let mut body = Map::new();

        for node in function_def {
            match node.as_rule() {
                Rule::parameter => {
                    let mut inner = node.into_inner();
                    let param_name = inner.next().unwrap().as_str();

                    if params.iter().any(|p: &VarId| p.name() == param_name) {
                        return Err(Errors::ContextSensitive(format!(
                            "function {} has duplicate parameters {param_name}",
                            func_name
                        )));
                    }

                    params.push(var_id(
                        param_name,
                        create_type(inner.next().unwrap()),
                        Some(func_name.clone()),
                    ));
                }
                Rule::ret_ty => {
                    if node.as_str() != "_" {
                        ret_ty = Some(create_type(node.into_inner().next().unwrap()));
                    }
                }
                Rule::body_def => {
                    for inner in node.into_inner() {
                        match inner.as_rule() {
                            Rule::decl => {
                                for local in inner.into_inner() {
                                    let mut inner = local.into_inner();
                                    let loc_name = inner.next().unwrap().as_str();

                                    if locals.iter().any(|v: &VarId| v.name() == loc_name) {
                                        return Err(Errors::ContextSensitive(format!(
                                            "function {} contains duplicate local {loc_name}",
                                            func_name
                                        )));
                                    }

                                    locals.insert(var_id(
                                        loc_name,
                                        create_type(inner.next().unwrap()),
                                        Some(func_name.clone()),
                                    ));
                                }
                            }
                            Rule::basic_block => {
                                create_basic_block(&mut body, inner, globals, &params, &locals)?;
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                _ => unreachable!(),
            }
        }

        Function {
            id: func_name.clone(),
            ret_ty,
            params,
            locals,
            body,
        }
    };

    functions.insert(func_name, func);
    Ok(())
}

// create a BasicBlock from the parse tree rooted at bb_def.
#[allow(clippy::result_large_err)]
fn create_basic_block(
    body: &mut Map<BbId, BasicBlock>,
    bb_def: Pair<Rule>,
    globals: &Set<VarId>,
    params: &[VarId],
    locals: &Set<VarId>,
) -> Result<(), Errors> {
    assert_eq!(bb_def.as_rule(), Rule::basic_block);
    use Instruction::*;
    use Terminal::*;

    let mut bb_def = bb_def.into_inner();
    let label = bb_id(bb_def.next().unwrap().as_str());
    let mut insts = vec![];

    if body.contains_key(&label) {
        return Err(Errors::ContextSensitive(format!(
            "function contains duplicate basic blocks {label}"
        )));
    }

    // a hack around limitations in rustc's type inference for closures (see
    // Shepmaster's answer for https://stackoverflow.com/questions/31403723).
    // without this workaround lookup() gives lifetime errors.
    fn constrain<F: for<'a> Fn(&'a str) -> Result<VarId, Errors>>(f: F) -> F {
        f
    }

    // look up a variable by name to get a VarId, first in locals then parameters
    // then globals.
    let lookup = constrain(|v| -> Result<VarId, Errors> {
        match locals.iter().find(|x| x.name() == v) {
            Some(var) => Ok(var.clone()),
            None => match params.iter().find(|x| x.name() == v) {
                Some(var) => Ok(var.clone()),
                None => match globals.iter().find(|x| x.name() == v) {
                    Some(var) => Ok(var.clone()),
                    None => Err(Errors::ContextSensitive(format!(
                        "block {label} contains undefined variable {v}"
                    ))),
                },
            },
        }
    });

    // create an operand from the parse tree rooted at op_def.
    let create_operand = |op_def: Pair<Rule>| -> Result<Operand, Errors> {
        assert_eq!(op_def.as_rule(), Rule::operand);
        match op_def.as_str().parse::<i32>() {
            Ok(num) => Ok(Operand::CInt(num)),
            Err(_) => {
                let v = lookup(op_def.as_str())?;
                Ok(Operand::Var(v))
            }
        }
    };

    // create a Call{Direct,Indirect} terminal instruction from the parse tree
    // rooted at call_def; which one is determined by the is_direct flag.
    let create_call = |call_def: Pair<Rule>, is_direct: bool| -> Result<Terminal, Errors> {
        assert!(call_def.as_rule() == Rule::calldir || call_def.as_rule() == Rule::callidr);
        let mut inner = call_def.into_inner().rev();
        let next_bb = bb_id(inner.next().unwrap().as_str());
        let mut inner = inner.rev().peekable();
        let first_ident = inner.next().unwrap().as_str();

        if is_direct {
            let has_lhs =
                inner.peek().is_some() && matches!(inner.peek().unwrap().as_rule(), Rule::ident);

            // first_ident may be the lhs of the call if it exists or the function being
            // called if there is no lhs.
            let (lhs, callee) = if has_lhs {
                (
                    Some(lookup(first_ident)?),
                    func_id(inner.next().unwrap().as_str()),
                )
            } else {
                (None, func_id(first_ident))
            };

            let args = inner
                .map(create_operand)
                .collect::<Result<Vec<Operand>, _>>()?;

            Ok(Terminal::CallDirect {
                lhs,
                callee,
                args,
                next_bb,
            })
        } else {
            let has_lhs =
                inner.peek().is_some() && matches!(inner.peek().unwrap().as_rule(), Rule::ident);

            // first_ident may be the lhs of the call if it exists or the function pointer
            // being called if there is no lhs.
            let (lhs, callee) = if has_lhs {
                (
                    Some(lookup(first_ident)?),
                    lookup(inner.next().unwrap().as_str())?,
                )
            } else {
                (None, lookup(first_ident)?)
            };

            let args = inner
                .map(create_operand)
                .collect::<Result<Vec<Operand>, _>>()?;

            Ok(Terminal::CallIndirect {
                lhs,
                callee,
                args,
                next_bb,
            })
        }
    };

    // will be filled in by the loop below.
    let mut term: Terminal = Ret(None);

    for inst in bb_def {
        match inst.as_rule() {
            Rule::terminal => {
                // guaranteed to be the last rule in the basic block.
                let inst = inst.into_inner().next().unwrap();
                match inst.as_rule() {
                    Rule::branch => {
                        let mut inner = inst.into_inner();
                        let cond = create_operand(inner.next().unwrap())?;
                        term = Branch {
                            cond,
                            tt: bb_id(inner.next().unwrap().as_str()),
                            ff: bb_id(inner.next().unwrap().as_str()),
                        };
                    }
                    Rule::calldir => term = create_call(inst, true)?,
                    Rule::callidr => term = create_call(inst, false)?,
                    Rule::jump => {
                        let mut inner = inst.into_inner();
                        term = Jump(bb_id(inner.next().unwrap().as_str()));
                    }
                    Rule::ret => {
                        let mut inner = inst.into_inner();
                        let op = match inner.next() {
                            Some(op) => Some(create_operand(op)?),
                            None => None,
                        };
                        term = Ret(op);
                    }
                    _ => unreachable!(),
                }
            }
            Rule::alloc => {
                let mut inner = inst.into_inner();
                let lhs = lookup(inner.next().unwrap().as_str())?;
                let num = create_operand(inner.next().unwrap())?;
                let id = match &*lhs.typ().0 {
                    LirType::Pointer(deref_ty) => {
                        // heap-allocated objects don't have a scope; to distinguish different
                        // allocation sites the ids must be distinct across all functions.
                        var_id(inner.next().unwrap().as_str(), deref_ty.clone(), None)
                    }
                    _ => {
                        return Err(Errors::ContextSensitive(format!(
                            "in block {label}: left-hand side of $alloc isn't a pointer"
                        )))
                    }
                };
                insts.push(Alloc { lhs, num, id });
            }
            Rule::arith => {
                let mut inner = inst.into_inner();
                let lhs = lookup(inner.next().unwrap().as_str())?;
                let aop = match inner.next().unwrap().as_str().trim() {
                    "add" => LirOp![+],
                    "sub" => LirOp![-],
                    "mul" => LirOp![*],
                    "div" => LirOp![/],
                    _ => unreachable!(),
                };
                let op1 = create_operand(inner.next().unwrap())?;
                let op2 = create_operand(inner.next().unwrap())?;
                insts.push(Arith { lhs, aop, op1, op2 });
            }
            Rule::callext => {
                let mut inner = inst.into_inner();
                let (lhs, ext_callee) = {
                    let ident1 = inner.next().unwrap().as_str();
                    if inner.peek().is_some()
                        && matches!(inner.peek().unwrap().as_rule(), Rule::ident)
                    {
                        (
                            Some(lookup(ident1)?),
                            func_id(inner.next().unwrap().as_str()),
                        )
                    } else {
                        (None, func_id(ident1))
                    }
                };
                let args = inner
                    .map(create_operand)
                    .collect::<Result<Vec<Operand>, _>>()?;
                insts.push(CallExt {
                    lhs,
                    ext_callee,
                    args,
                });
            }
            Rule::cmp => {
                let mut inner = inst.into_inner();
                let lhs = lookup(inner.next().unwrap().as_str())?;
                let rop = match inner.next().unwrap().as_str().trim() {
                    "eq" => LirOp![==],
                    "neq" => LirOp![!=],
                    "lt" => LirOp![<],
                    "lte" => LirOp![<=],
                    "gt" => LirOp![>],
                    "gte" => LirOp![>=],
                    _ => unreachable!(),
                };
                let op1 = create_operand(inner.next().unwrap())?;
                let op2 = create_operand(inner.next().unwrap())?;
                insts.push(Cmp { lhs, rop, op1, op2 });
            }
            Rule::copy => {
                let mut inner = inst.into_inner();
                let lhs = lookup(inner.next().unwrap().as_str())?;
                let op = create_operand(inner.next().unwrap())?;
                insts.push(Copy { lhs, op });
            }
            Rule::gep => {
                let mut inner = inst.into_inner();
                let lhs = lookup(inner.next().unwrap().as_str())?;
                let src = lookup(inner.next().unwrap().as_str())?;
                let idx = create_operand(inner.next().unwrap())?;
                insts.push(Gep { lhs, src, idx });
            }
            Rule::gfp => {
                let mut inner = inst.into_inner();
                let lhs = lookup(inner.next().unwrap().as_str())?;
                let src = lookup(inner.next().unwrap().as_str())?;
                let field = match &*lhs.typ().0 {
                    LirType::Pointer(deref_ty) => {
                        field_id(inner.next().unwrap().as_str(), deref_ty.clone())
                    }
                    _ => {
                        return Err(Errors::ContextSensitive(format!(
                            "in block {label}: left-hand side of $gfp isn't a pointer"
                        )))
                    }
                };
                insts.push(Gfp { lhs, src, field });
            }
            Rule::load => {
                let mut inner = inst.into_inner();
                let lhs = lookup(inner.next().unwrap().as_str())?;
                let src = lookup(inner.next().unwrap().as_str())?;
                insts.push(Load { lhs, src });
            }
            Rule::phi => {
                let mut inner = inst.into_inner();
                let lhs = lookup(inner.next().unwrap().as_str())?;
                let args = inner
                    .map(create_operand)
                    .collect::<Result<Vec<Operand>, _>>()?;
                insts.push(Phi { lhs, args });
            }
            Rule::store => {
                let mut inner = inst.into_inner();
                let dst = lookup(inner.next().unwrap().as_str())?;
                let op = create_operand(inner.next().unwrap())?;
                insts.push(Store { dst, op });
            }
            _ => unreachable!(),
        }
    }

    body.insert(
        label.clone(),
        BasicBlock {
            id: label,
            insts,
            term,
        },
    );
    Ok(())
}

// create a Type from the parse tree rooted at type_id.
fn create_type(type_id: Pair<Rule>) -> Type {
    assert_eq!(type_id.as_rule(), Rule::type_id);
    let type_str = type_id.as_str();

    match type_str {
        "int" => int_ty(),
        _ => {
            let inner = type_id.into_inner().next().unwrap();
            match inner.as_rule() {
                Rule::ident => struct_ty(struct_id(type_str)),
                Rule::func_typ => create_function_type(inner),
                Rule::ptr_typ => ptr_ty(create_type(inner.into_inner().next().unwrap())),
                _ => unreachable!(),
            }
        }
    }
}

fn create_function_type(func_typ: Pair<Rule>) -> Type {
    assert_eq!(func_typ.as_rule(), Rule::func_typ);
    let mut types = func_typ.into_inner().rev().peekable();
    let ret = types.next().unwrap();
    let ret_ty = if ret.as_str() == "_" {
        None
    } else {
        Some(create_type(ret.into_inner().next().unwrap()))
    };
    let param_ty = types.rev().map(create_type).collect();
    func_ty(ret_ty, param_ty)
}
