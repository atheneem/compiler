use super::*;

impl Program {
    pub fn pretty_print(&self) -> String {
        let td = if !self.typedefs.is_empty() {
            format!(
                "{}\n",
                self.typedefs
                    .iter()
                    .map(|p| p.pretty_print())
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        } else {
            "".to_string()
        };

        let ex = if !self.externs.is_empty() {
            format!(
                "{}\n\n",
                self.externs
                    .iter()
                    .map(|p| format!("extern {};", p.pretty_print()))
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        } else {
            "".to_string()
        };

        let gl = if !self.globals.is_empty() {
            format!(
                "{}\n\n",
                self.globals
                    .iter()
                    .map(|g| format!("let {};", g.pretty_print()))
                    .collect::<Vec<_>>()
                    .join("\n"),
            )
        } else {
            "".to_string()
        };

        let fu = self
            .functions
            .iter()
            .map(|p| p.pretty_print())
            .collect::<Vec<_>>()
            .join("\n");

        format!("{td}{ex}{gl}{fu}")
    }
}

impl Decl {
    pub fn pretty_print(&self) -> String {
        format!("{}: {}", self.name, self.typ)
    }
}

impl Typedef {
    pub fn pretty_print(&self) -> String {
        format!(
            "struct {} {{\n  {}\n}}\n",
            self.name,
            &self
                .fields
                .iter()
                .map(|f| f.pretty_print())
                .collect::<Vec<_>>()
                .join(",\n  ")
        )
    }
}

impl Function {
    pub fn pretty_print(&self) -> String {
        format!(
            "fn {}({}) -> {} {{\n{}}}\n",
            self.name,
            self.params
                .iter()
                .map(|p| p.pretty_print())
                .collect::<Vec<_>>()
                .join(", "),
            self.rettyp
                .as_ref()
                .map(|r| r.to_string())
                .unwrap_or("_".to_string()),
            self.body.pretty_print()
        )
    }
}

impl Body {
    pub fn pretty_print(&self) -> String {
        let decls = if !self.decls.is_empty() {
            format!(
                "  let {};\n",
                self.decls
                    .iter()
                    .map(|(decl, init)| match init {
                        Some(exp) => format!("{} = {}", decl.pretty_print(), exp.pretty_print()),
                        None => decl.pretty_print(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        } else {
            "".to_string()
        };

        let stmts = self
            .stmts
            .iter()
            .map(|s| s.pretty_print(2))
            .collect::<Vec<_>>()
            .join("\n");

        format!("{decls}{stmts}\n")
    }
}

impl Stmt {
    pub fn pretty_print(&self, indent: usize) -> String {
        let ind = str::repeat(" ", indent);
        match self {
            Stmt::If { guard, tt, ff } => {
                if ff.is_empty() {
                    format!(
                        "{ind}if {} {{\n{}\n{ind}}}",
                        guard.pretty_print(),
                        tt.iter()
                            .map(|s| s.pretty_print(indent + 2))
                            .collect::<Vec<_>>()
                            .join("\n")
                    )
                } else {
                    format!(
                        "{ind}if {} {{\n{}\n{ind}}}\n{ind}else {{\n{}\n{ind}}}",
                        guard.pretty_print(),
                        tt.iter()
                            .map(|s| s.pretty_print(indent + 2))
                            .collect::<Vec<_>>()
                            .join("\n"),
                        ff.iter()
                            .map(|s| s.pretty_print(indent + 2))
                            .collect::<Vec<_>>()
                            .join("\n")
                    )
                }
            }
            Stmt::While { guard, body } => format!(
                "{ind}while {} {{\n{}\n{ind}}}",
                guard.pretty_print(),
                body.iter()
                    .map(|s| s.pretty_print(indent + 2))
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Stmt::Assign { lhs, rhs } => {
                format!("{ind}{} = {};", lhs.pretty_print(), rhs.pretty_print())
            }
            Stmt::Call { callee, args } => format!(
                "{ind}{}({});",
                callee.pretty_print(),
                args.iter()
                    .map(|a| a.pretty_print())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Stmt::Break => format!("{ind}break;"),
            Stmt::Continue => format!("{ind}continue;"),
            Stmt::Return(op) => match op {
                Some(exp) => format!("{ind}return {};", exp.pretty_print()),
                None => format!("{ind}return;"),
            },
        }
    }
}

impl Rhs {
    pub fn pretty_print(&self) -> String {
        match self {
            Rhs::Exp(exp) => exp.pretty_print(),
            Rhs::New { typ, num } => match num {
                Some(exp) => format!("new {} {}", typ, exp.pretty_print()),
                None => format!("new {}", typ),
            },
        }
    }
}

impl Lval {
    pub fn pretty_print(&self) -> String {
        match self {
            Lval::Id(name) => name.clone(),
            Lval::Deref(lv) => format!("*{}", lv.pretty_print()),
            Lval::ArrayAccess { ptr, index } => {
                format!("{}[{}]", ptr.pretty_print(), index.pretty_print())
            }
            Lval::FieldAccess { ptr, field } => {
                format!("{}.{field}", ptr.pretty_print())
            }
        }
    }
}

impl Exp {
    pub fn pretty_print(&self) -> String {
        use ArithOp::*;
        use CompareOp::*;
        use Exp::*;

        // returns the expression as a string, in parentheses if the expression is
        // compound.
        fn parenthesize(e: &Exp) -> String {
            match e {
                Arith(..) | Compare(..) | And(_, _) | Or(_, _) => {
                    format!("({})", e.pretty_print())
                }
                _ => e.pretty_print(),
            }
        }

        match self {
            Exp::Num(n) => n.to_string(),
            Exp::Id(name) => name.clone(),
            Exp::Nil => "nil".to_string(),
            Exp::Neg(e) => format!("-{}", parenthesize(e)),
            Exp::Deref(e) => format!("*{}", parenthesize(e)),
            Exp::Not(e) => format!("!{}", parenthesize(e)),
            Exp::Arith(lhs, op, rhs) => format!(
                "{} {} {}",
                parenthesize(lhs),
                match op {
                    Add => "+",
                    Subtract => "-",
                    Multiply => "*",
                    Divide => "/",
                },
                parenthesize(rhs)
            ),
            Exp::Compare(lhs, op, rhs) => format!(
                "{} {} {}",
                parenthesize(lhs),
                match op {
                    Equal => "==",
                    NotEq => "!=",
                    Lt => "<",
                    Lte => "<=",
                    Gt => ">",
                    Gte => ">=",
                },
                parenthesize(rhs)
            ),
            Exp::And(e1, e2) => format!("{} and {}", parenthesize(e1), parenthesize(e2)),
            Exp::Or(e1, e2) => format!("{} or {}", parenthesize(e1), parenthesize(e2)),
            Exp::ArrayAccess { ptr, index } => {
                format!("{}[{}]", parenthesize(ptr), index.pretty_print())
            }
            Exp::FieldAccess { ptr, field } => {
                format!("{}.{field}", parenthesize(ptr))
            }
            Exp::Call { callee, args } => format!(
                "{}({})",
                parenthesize(callee),
                args.iter()
                    .map(|a| a.pretty_print())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}
