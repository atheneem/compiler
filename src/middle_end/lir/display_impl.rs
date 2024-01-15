// implements the Display trait for Program elements.

use std::fmt::{Display, Formatter, Result};

use super::*;

// helper function: joins an iterable list of items into a single String with
// the items separated by 'sep', using 'tostr' to turn each item into an
// individual String before joining them.
fn join<T: IntoIterator, F: FnMut(T::Item) -> String>(x: T, tostr: F, sep: &str) -> String {
    x.into_iter().map(tostr).collect::<Vec<_>>().join(sep)
}

// by default we won't display the type information; use the associated function
// 'typed_to_string()' for that.
impl Display for FieldId {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}", self.name)
    }
}

// by default we won't display the type information; use the associated function
// 'typed_to_string()' for that.
impl Display for LirVar {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}", self.name)
    }
}

impl Display for VarId {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}", self.0)
    }
}

impl Display for LirType {
    fn fmt(&self, f: &mut Formatter) -> Result {
        use LirType::*;

        let string = match self {
            Int => "int".to_string(),
            Struct(id) => id.to_string(),
            Function { ret_ty, param_ty } => {
                let params = if !param_ty.is_empty() {
                    join(param_ty, |x| x.to_string(), ",")
                } else {
                    "".to_string()
                };
                format!(
                    "({}) -> {}",
                    params,
                    ret_ty.as_ref().map_or("_".to_string(), |t| t.to_string())
                )
            }
            Pointer(deref_ty) => format!("&{}", deref_ty),
        };

        write!(f, "{}", string)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}", self.0)
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let struct_info = join(
            &self.structs,
            |(k, v)| {
                let fields = join(v, |f| format!("  {}", f.typed_to_string()), "\n");
                format!("struct {k} {{\n{fields}\n}}")
            },
            "\n\n",
        );
        let globals = join(&self.globals, |v| v.typed_to_string(), "\n");
        let externs = join(&self.externs, |(f, ty)| format!("extern {f}:{ty}"), "\n");
        let functions = join(&self.functions, |(_, x)| x.to_string(), "\n");
        write!(
            f,
            "{struct_info}{}{globals}{}{externs}{}{functions}",
            if struct_info.is_empty() { "" } else { "\n\n" },
            if globals.is_empty() { "" } else { "\n\n" },
            if externs.is_empty() { "" } else { "\n\n" }
        )
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let name = self.id.to_string();
        let ret_ty = self
            .ret_ty
            .as_ref()
            .map_or("_".to_string(), |t| t.to_string());
        let params = join(&self.params, |x| x.typed_to_string(), ", ");
        let locals = if !self.locals.is_empty() {
            "let ".to_string() + &join(self.locals.iter(), |x| x.typed_to_string(), ", ")
        } else {
            "".to_string()
        };
        let body = join(&self.body, |(_, x)| x.to_string(), "\n");
        write!(
            f,
            "fn {name}({params}) -> {ret_ty} {{\n{locals}{}{body}}}\n",
            if locals.is_empty() { "" } else { "\n" }
        )
    }
}

impl Display for BasicBlock {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let lbl = self.id.to_string();
        let insts = join(&self.insts, |x| format!("  {x}"), "\n");
        let term = format!("  {}", self.term);
        write!(
            f,
            "{lbl}:\n{insts}{}{term}\n",
            if insts.is_empty() { "" } else { "\n" }
        )
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter) -> Result {
        use Instruction::*;
        let string = match self {
            Alloc { lhs, num, id } => format!("{lhs} = $alloc {num} [{id}]"),
            Arith { lhs, aop, op1, op2 } => format!("{lhs} = $arith {aop} {op1} {op2}"),
            CallExt {
                lhs,
                ext_callee,
                args,
            } => {
                let lhs = lhs.as_ref().map_or("".to_string(), |vn| format!("{vn} = "));
                let args = join(args, |arg| arg.to_string(), ", ");
                format!("{lhs}$call_ext {ext_callee}({args})")
            }
            Cmp { lhs, rop, op1, op2 } => format!("{lhs} = $cmp {rop} {op1} {op2}"),
            Copy { lhs, op } => format!("{lhs} = $copy {op}"),
            Gep { lhs, src, idx } => {
                format!("{lhs} = $gep {src} {idx}")
            }
            Gfp { lhs, src, field } => {
                format!("{lhs} = $gfp {src} {field}")
            }
            Load { lhs, src } => format!("{lhs} = $load {src}"),
            Phi { lhs, args } => {
                let args = join(args, |arg| arg.to_string(), ", ");
                format!("{lhs} = $phi({args})")
            }
            Store { dst, op } => format!("$store {dst} {op}"),
        };
        write!(f, "{}", string)
    }
}

impl Display for Terminal {
    fn fmt(&self, f: &mut Formatter) -> Result {
        use Terminal::*;
        let string = match self {
            Branch { cond, tt, ff } => format!("$branch {cond} {tt} {ff}"),
            CallDirect {
                lhs,
                callee,
                args,
                next_bb,
            } => {
                let lhs = lhs.as_ref().map_or("".to_string(), |vn| format!("{vn} = "));
                let args = join(args, |arg| arg.to_string(), ", ");
                format!("{lhs}$call_dir {callee}({args}) then {next_bb}")
            }
            CallIndirect {
                lhs,
                callee,
                args,
                next_bb,
            } => {
                let lhs = lhs.as_ref().map_or("".to_string(), |vn| format!("{vn} = "));
                let args = join(args, |arg| arg.to_string(), ", ");
                format!("{lhs}$call_idr {callee}({args}) then {next_bb}")
            }
            Jump(lbl) => format!("$jump {lbl}"),
            Ret(op) => {
                let op = op.as_ref().map_or("".to_string(), |op| op.to_string());
                format!("$ret {op}")
            }
        };
        write!(f, "{}", string)
    }
}
