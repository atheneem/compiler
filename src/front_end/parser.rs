// ll(1) parser for cflat.
//
// You are free to change any function or type signature except for `parse` and
// `ParseError`.

use derive_more::Display;

use super::*;
use TokenKind::*;

// SECTION: interface

pub fn parse(code: &str) -> Result<Program, ParseError> {
    let mut parser = Parser::new(code)?;
    program_r(&mut parser)
}

// A parse error with explanatory message.
#[derive(Clone, Debug, Display, Eq, PartialEq)]
pub struct ParseError(pub String);
impl std::error::Error for ParseError {}

// SECTION: parser functionality

#[derive(Clone, Debug)]
struct Parser<'a> {
    code: &'a str,      // the source code being parsed
    tokens: Vec<Token>, // the token stream
    pos: usize,         // the position in the token stream
}

// utility functions for traversing the token stream and creating error
// messages.
impl<'a> Parser<'a> {
    // always use this to create new Parsers.
    fn new(code: &'a str) -> Result<Self, ParseError> {
        let tokens = lex(code);
        if tokens.is_empty() {
            Err(ParseError("empty token stream".to_string()))
        } else {
            Ok(Parser {
                code,
                tokens,
                pos: 0,
            })
        }
    }

    // if the next token has the given kind advances the iterator and returns true,
    // otherwise returns false.
    fn eat(&mut self, kind: TokenKind) -> bool {
        match self.peek() {
            Some(k) if k == kind => {
                self.next();
                true
            }
            _ => false,
        }
    }

    // returns an Ok or Err result depending on whether the next token has the given
    // kind, advancing the iterator on an Ok result.
    fn expect(&mut self, kind: TokenKind) -> Result<(), ParseError> {
        if self.eat(kind) {
            Ok(())
        } else {
            self.error_next(&format!("expected `{kind}`"))
        }
    }

    // advances the iterator and returns the next token in the stream, or None if
    // there are no more tokens.
    fn next(&mut self) -> Option<TokenKind> {
        if !self.end() {
            self.pos += 1;
            Some(self.tokens[self.pos - 1].kind)
        } else {
            None
        }
    }

    // returns the next token (if it exists) without advancing the iterator.
    fn peek(&self) -> Option<TokenKind> {
        if !self.end() {
            Some(self.tokens[self.pos].kind)
        } else {
            None
        }
    }

    // returns whether the next token has the given kind, without advancing the
    // iterator.
    fn next_is(&self, kind: TokenKind) -> bool {
        self.peek() == Some(kind)
    }

    // returns whether the next token is one of the given kinds.
    fn next_is_one_of(&self, kinds: &[TokenKind]) -> bool {
        matches!(self.peek(), Some(k) if kinds.contains(&k))
    }

    // returns whether we're at the end of the token stream.
    fn end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    // returns the lexeme of the token immediately prior to the current token.
    fn slice_prev(&self) -> &str {
        &self.code[self.tokens[self.pos - 1].span.clone()]
    }

    // returns a parse error knowing that the previous token that we just advanced
    // past caused an error.
    fn error_prev<T>(&self, msg: &str) -> Result<T, ParseError> {
        self.error(self.pos - 1, msg)
    }

    // returns a parse error knowing that the next token to be inspected causes an
    // error (based on a call to peek(), next_is(), etc).
    fn error_next<T>(&self, msg: &str) -> Result<T, ParseError> {
        // handle the case where we're at the end of the token stream.
        if self.pos >= self.tokens.len() {
            Err(ParseError(format!(
                "parse error: unexpected end of input ({msg})\n"
            )))
        } else {
            self.error(self.pos, msg)
        }
    }

    // constructs a parse error given the position of the error-causing token in the
    // token stream.
    fn error<T>(&self, pos: usize, msg: &str) -> Result<T, ParseError> {
        // the position of the error-causing lexeme in the source code.
        let span = &self.tokens[pos].span;

        // the row number and the index of the start of the row containing the
        // error-causing token.
        let (row, row_start) = {
            let mut row = 0;
            let mut row_start = 0;
            for (idx, _) in self.code.match_indices('\n') {
                if idx > span.start {
                    break;
                }
                row += 1;
                row_start = idx + 1;
            }
            (row, row_start)
        };

        // the column where the error-causing lexeme starts.
        let col = span.start - row_start;

        // the line containing the error-causing lexeme.
        let line = self.code.lines().nth(row).unwrap();

        Err(ParseError(format!(
            "parse error in line {row}, column {col}\n{line}\n{:width$}^\n{msg}\n",
            " ",
            width = col
        )))
    }
}

// SECTION: parsing functions

// the function names come from the production rules of the LL(1) cflat grammar.

// type.
fn type_r(parser: &mut Parser) -> Result<Type, ParseError> {
    if parser.eat(Address) {
        //pointer type
        let typ = type_r(parser)?; //panics if returns error
        Ok(ptr_ty(typ))
    } else {
        //nonpointer types
        type_ad_r(parser)
    }
}

// non-pointer type.
fn type_ad_r(parser: &mut Parser) -> Result<Type, ParseError> {
    match parser.next() {
        Some(Int) => Ok(int_ty()),
        Some(Id) => Ok(struct_ty(struct_id(parser.slice_prev()))),
        Some(OpenParen) => type_op_r(parser),
        x => parser.error_prev(&format!("wanted int, id, open paren. got {x:?}")),
    }
}

// type in parentheses OR function type.
fn type_op_r(parser: &mut Parser) -> Result<Type, ParseError> {
    match parser.peek() {
        Some(CloseParen) => {
            //should see return type then
            parser.next(); //skip over )
            let ty = type_ar_r(parser)?; //return type
            Ok(func_ty(ty, vec![])) //create function type (no params, cause imidiately saw ')')
        }
        _ => {
            let ty = type_r(parser)?;
            match type_fp_r(parser)? {
                //handles parens/fun types
                None => Ok(ty), //no others, just return first one we got
                Some((mut vec, op_ty)) => {
                    vec.insert(0, ty); //add to front
                    Ok(func_ty(op_ty, vec))
                }
            }
        }
    }
}

// type in parentheses OR function type.
#[allow(clippy::type_complexity)]
fn type_fp_r(parser: &mut Parser) -> Result<Option<(Vec<Type>, Option<Type>)>, ParseError> {
    match parser.peek() {
        Some(Comma) => {
            let mut typs = vec![];
            while parser.eat(Comma) {
                //while can eat a comma (more params)
                let ty = type_r(parser)?; //get the type of next param
                typs.push(ty);
            }
            parser.expect(CloseParen)?; //once doe, close paren

            Ok(Some((typs, type_ar_r(parser)?)))
        }
        Some(CloseParen) => {
            parser.next(); //advance close paren
            Ok(if parser.next_is(Arrow) {
                Some((vec![], type_ar_r(parser)?))
            } else {
                None
            })
        }
        x => parser.error_prev(&format!("expected comma or close paren, got {x:?}")),
    }
}

// function return type.
fn type_ar_r(parser: &mut Parser) -> Result<Option<Type>, ParseError> {
    parser.expect(Arrow)?;
    rettyp_r(parser) //if got an arrow, get return type
}

// function type.
fn funtype_r(parser: &mut Parser) -> Result<Type, ParseError> {
    parser.expect(OpenParen)?;

    let mut tys = vec![];

    while !parser.eat(CloseParen) {
        //while it can't eat a close paren
        tys.push(type_r(parser)?); //get a type
        parser.eat(Comma);
    }

    let ret_ty = type_ar_r(parser)?; //ret types

    Ok(func_ty(ret_ty, tys))
}

// function return type.
fn rettyp_r(parser: &mut Parser) -> Result<Option<Type>, ParseError> {
    if parser.eat(Underscore) {
        Ok(None)
    } else {
        let ty = type_r(parser)?;
        Ok(Some(ty))
    }
}

// cflat program.
fn program_r(parser: &mut Parser) -> Result<Program, ParseError> {
    let mut program = Program {
        globals: vec![],
        typedefs: vec![],
        externs: vec![],
        functions: vec![],
    };

    loop {
        match parser.peek() {
            Some(Let) => program.globals.extend(glob_r(parser)?), // addding variavle declarations to vecs and coule be either ok/err
            Some(Struct) => program.typedefs.push(typedef_r(parser)?),
            Some(Extern) => program.externs.push(extern_r(parser)?),
            Some(Fn) => program.functions.push(fundef_r(parser)?),
            None => break, //if none, break cause nothing else to parse
            x => parser.error_prev(&format!("expected a let, struct, extern, or fn. Got {x:?}"))?, // not one of these things
        }
    }

    Ok(program)
}

// global variable declaration.
fn glob_r(parser: &mut Parser) -> Result<Vec<Decl>, ParseError> {
    parser.expect(Let)?;
    let declarations = decls_r(parser)?;
    parser.expect(Semicolon)?;

    Ok(declarations)
}

// struct type declaration.
fn typedef_r(parser: &mut Parser) -> Result<Typedef, ParseError> {
    parser.expect(Struct)?;
    parser.expect(Id)?;
    let name = parser.slice_prev().to_owned(); //get name from id, make owned
    parser.expect(OpenBrace)?;
    let declarations = decls_r(parser)?;
    parser.expect(CloseBrace)?;

    Ok(Typedef {
        name,
        fields: declarations,
    })
}

// variable declaration.
fn decl_r(parser: &mut Parser) -> Result<Decl, ParseError> {
    parser.expect(Id)?;
    let name = parser.slice_prev().to_owned(); //get name from id, make owned
    parser.expect(Colon)?;
    let typ = type_r(parser)?;

    Ok(Decl { name, typ })
}

// series of variable declarations.
fn decls_r(parser: &mut Parser) -> Result<Vec<Decl>, ParseError> {
    let mut decls = Vec::new();

    decls.push(decl_r(parser)?); //first decl

    while parser.eat(Comma) {
        //if can eat, at anouther decl
        decls.push(decl_r(parser)?); //other decl
    }

    Ok(decls)
}

// external function declaration.
fn extern_r(parser: &mut Parser) -> Result<Decl, ParseError> {
    parser.expect(Extern)?;
    parser.expect(Id)?;
    let name = parser.slice_prev().to_owned(); //get name from id, make owned
    parser.expect(Colon)?;
    let typ = funtype_r(parser)?;
    parser.expect(Semicolon)?;

    Ok(Decl { name, typ })
}

// function definition.
fn fundef_r(parser: &mut Parser) -> Result<Function, ParseError> {
    parser.expect(Fn)?;
    parser.expect(Id)?;
    let name = parser.slice_prev().to_owned(); //get name from id, make owned
    parser.expect(OpenParen)?;

    let mut decls = vec![];
    if parser.next_is(Id) {
        //eps or decls
        decls = decls_r(parser)?;
    }
    parser.expect(CloseParen)?;
    parser.expect(Arrow)?;

    let rettype = rettyp_r(parser)?; //rettyp

    parser.expect(OpenBrace)?;

    let mut lets = vec![];
    while parser.next_is(Let) {
        //lets
        lets.append(&mut let_r(parser)?);
    }

    let mut stmts = Vec::from([stmt_r(parser)?]); //stmt

    while !parser.next_is(CloseBrace) {
        //eps or stmt
        stmts.push(stmt_r(parser)?);
    }
    parser.expect(CloseBrace)?;

    Ok(Function {
        name,
        params: decls,
        rettyp: rettype,
        body: Body {
            decls: lets, // optional initializers
            stmts,
        },
    })
}

// internal variable declaration and possibly initialization.
fn let_r(parser: &mut Parser) -> Result<Vec<(Decl, Option<Exp>)>, ParseError> {
    parser.expect(Let)?;

    let mut decl_expr = vec![]; //return vector

    let decl = decl_r(parser)?; //get first decl
    if parser.eat(Gets) {
        decl_expr.push((decl, Some(exp_r(parser)?))); //add expr if exists, else none
    } else {
        decl_expr.push((decl, None));
    }

    while parser.eat(Comma) {
        //while a comma
        let decl = decl_r(parser)?; //get decl
        if parser.eat(Gets) {
            decl_expr.push((decl, Some(exp_r(parser)?))); //add expr if exists, else none
        } else {
            decl_expr.push((decl, None));
        }
    }

    parser.expect(Semicolon)?;

    Ok(decl_expr)
}

// statement.
fn stmt_r(parser: &mut Parser) -> Result<Stmt, ParseError> {
    match parser.peek() {
        Some(If) => cond_r(parser),    //first cond = if
        Some(While) => loop_r(parser), //first loop = while
        Some(Id) | Some(Star) => {
            let a_or_c = assign_or_call_r(parser); //first assign and call = first lval = id/star
            parser.expect(Semicolon)?;
            a_or_c
        }
        Some(Break) => {
            parser.next();
            parser.expect(Semicolon)?;
            Ok(Stmt::Break)
        }
        Some(Continue) => {
            parser.next();
            parser.expect(Semicolon)?;
            Ok(Stmt::Continue)
        }
        Some(Return) => {
            parser.next();
            let expr = if !parser.next_is(Semicolon) {
                Some(exp_r(parser)?)
            } else {
                None
            };
            parser.expect(Semicolon)?;
            Ok(Stmt::Return(expr))
        }
        x => parser.error_prev(&format!(
            "expected if, while, id, break, continue, or return. got {x:?}"
        )),
    }
}

// conditional statement.
fn cond_r(parser: &mut Parser) -> Result<Stmt, ParseError> {
    parser.expect(If)?;
    let expr = exp_r(parser)?; //expr

    let if_block = block_r(parser)?;

    let mut else_block = vec![];
    if parser.eat(Else) {
        //maybe else
        else_block.append(&mut block_r(parser)?);
    }
    Ok(Stmt::If {
        guard: expr,
        tt: if_block,   //if
        ff: else_block, //else
    })
}

// while or for loop.
fn loop_r(parser: &mut Parser) -> Result<Stmt, ParseError> {
    parser.expect(While)?;
    let expr = exp_r(parser)?; //expr

    let stmts = block_r(parser)?;

    Ok(Stmt::While {
        guard: expr,
        body: stmts,
    })
}

// sequence of statements.
fn block_r(parser: &mut Parser) -> Result<Vec<Stmt>, ParseError> {
    parser.expect(OpenBrace)?;

    let mut stmts = vec![];
    while !parser.eat(CloseBrace) {
        //stmts
        stmts.push(stmt_r(parser)?)
    }

    Ok(stmts)
}

// assignment or call statement.
fn assign_or_call_r(parser: &mut Parser) -> Result<Stmt, ParseError> {
    let lhs = lval_r(parser)?;

    match parser.next() {
        Some(Gets) => Ok(Stmt::Assign {
            lhs,
            rhs: rhs_r(parser)?,
        }),
        Some(OpenParen) => {
            let args = if parser.next_is(CloseParen) {
                vec![]
            } else {
                args_r(parser)?
            };
            parser.expect(CloseParen)?;
            Ok(Stmt::Call { callee: lhs, args })
        }
        x => parser.error_prev(&format!("expected let or open paren, got {x:?}")),
    }
}

// right-hand side of an assignment.
fn rhs_r(parser: &mut Parser) -> Result<Rhs, ParseError> {
    if parser.eat(New) {
        //new
        let typ = type_r(parser)?;
        let num = if parser.next_is(Semicolon) {
            //maybe expr
            None
        } else {
            Some(exp_r(parser)?)
        };

        Ok(Rhs::New { typ, num })
    } else {
        //expr
        Ok(Rhs::Exp(exp_r(parser)?))
    }
}

// left-hand side of an assignment.
fn lval_r(parser: &mut Parser) -> Result<Lval, ParseError> {
    Ok(if parser.eat(Star) {
        Lval::Deref(Box::new(lval_r(parser)?))
    } else {
        parser.expect(Id)?; //eventually hits this case after reaches id
        let mut id = Lval::Id(parser.slice_prev().to_string()); //base

        while parser.next_is_one_of(&[Dot, OpenBracket]) {
            id = access_r(parser, id)?; //uses base to create bigger elval until get final
        }
        id
    })
}

// access path.
fn access_r(parser: &mut Parser, base: Lval) -> Result<Lval, ParseError> {
    if parser.eat(OpenBracket) {
        // lval[exp]
        let expr = exp_r(parser)?;
        parser.expect(CloseBracket)?;
        Ok(Lval::ArrayAccess {
            ptr: Box::new(base),
            index: expr,
        })
    } else if parser.eat(Dot) {
        // lval.id
        parser.expect(Id)?;
        Ok(Lval::FieldAccess {
            ptr: Box::new(base),
            field: parser.slice_prev().to_string(),
        })
    } else {
        parser.error_prev("expected dot or open brace")
    }
}

// call arguments.
fn args_r(parser: &mut Parser) -> Result<Vec<Exp>, ParseError> {
    let mut exprs = Vec::from([exp_r(parser)?]); //first expr

    while parser.eat(Comma) {
        //other exprs (optional)
        exprs.push(exp_r(parser)?);
    }

    Ok(exprs)
}

// expression (precedence level 6).
fn exp_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    let lhs = exp_p5_r(parser)?;

    match parser.peek() {
        Some(And) => {
            parser.next();
            Ok(Exp::And(Box::new(lhs), Box::new(exp_r(parser)?)))
        }
        Some(Or) => {
            parser.next();
            Ok(Exp::Or(Box::new(lhs), Box::new(exp_r(parser)?)))
        }
        _ => Ok(lhs),
    }
}

// expression (precedence level 5).
fn exp_p5_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    //has lhs, get binop, hand rhs to p4
    let mut lhs = exp_p4_r(parser)?; //get lhs

    while let Some(comp) = binop_p3(parser) {
        lhs = Exp::Compare(Box::new(lhs), comp, Box::new(exp_p4_r(parser)?));
    }

    Ok(lhs)
}

//matching what the parser gets as a binop
fn binop_p3(parser: &mut Parser) -> Option<CompareOp> {
    match parser.peek() {
        Some(Equal) => {
            parser.next();
            Some(CompareOp::Equal)
        }
        Some(NotEq) => {
            parser.next();
            Some(CompareOp::NotEq)
        }
        Some(Lt) => {
            parser.next();
            Some(CompareOp::Lt)
        }
        Some(Lte) => {
            parser.next();
            Some(CompareOp::Lte)
        }
        Some(Gt) => {
            parser.next();
            Some(CompareOp::Gt)
        }
        Some(Gte) => {
            parser.next();
            Some(CompareOp::Gte)
        }
        _ => None,
    }
}

//matching what the parser gets as an ArithOp
fn binop_p1(parser: &mut Parser) -> Option<ArithOp> {
    match parser.peek() {
        Some(Slash) => {
            parser.next();
            Some(ArithOp::Divide)
        }
        Some(Star) => {
            parser.next();
            Some(ArithOp::Multiply)
        }
        _ => None,
    }
}
//matching what the parser gets as an ArithOp
fn binop_p2(parser: &mut Parser) -> Option<ArithOp> {
    match parser.peek() {
        Some(Plus) => {
            parser.next();
            Some(ArithOp::Add)
        }
        Some(Dash) => {
            parser.next();
            Some(ArithOp::Subtract)
        }
        _ => None,
    }
}

// expression (precedence level 4).
//figure out what exprs are and do the calculation
fn exp_p4_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    let mut lhs = exp_p3_r(parser)?; //get lhs

    while let Some(arith) = binop_p2(parser) {
        lhs = Exp::Arith(Box::new(lhs), arith, Box::new(exp_p3_r(parser)?));
    }

    Ok(lhs)
}

// expression (precedence level 3).
fn exp_p3_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    let mut lhs = exp_p2_r(parser)?; //get lhs

    while let Some(arith) = binop_p1(parser) {
        lhs = Exp::Arith(Box::new(lhs), arith, Box::new(exp_p2_r(parser)?));
    }

    Ok(lhs)
}

// expression (precedence level 2).
fn exp_p2_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    match parser.peek() {
        Some(Star) => {
            parser.next();
            Ok(Exp::Deref(Box::new(exp_p2_r(parser)?))) //repeat, bc migght have something else after (until hits p1)
        }
        Some(Dash) => {
            parser.next();
            Ok(Exp::Neg(Box::new(exp_p2_r(parser)?)))
        }
        Some(Bang) => {
            parser.next();
            Ok(Exp::Not(Box::new(exp_p2_r(parser)?)))
        }
        _ => exp_p1_r(parser), //nothing to do, so go to expr 1
    }
}

// expression (precedence level 1).
fn exp_p1_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    match parser.next() {
        Some(Nil) => Ok(Exp::Nil),
        Some(Num) => {
            let num = parser.slice_prev().parse::<i32>(); //gets str, parses str into num
            match num {
                Ok(x) => Ok(Exp::Num(x)),
                _ => parser.error_prev("can't be parsed as an i32"),
            }
            // num.map(|n| Ok(Exp::Num(n))).unwrap_or(parser.error_prev("wasn't an i32"))
        }
        Some(OpenParen) => {
            let exps = exp_r(parser)?; //get expressions in parens
            parser.expect(CloseParen)?;
            Ok(exps)
        }
        Some(Id) => {
            let mut exp = Exp::Id(parser.slice_prev().to_string()); //base

            while parser.next_is_one_of(&[Dot, OpenBracket, OpenParen]) {
                exp = exp_ac_r(parser, exp)?; //uses base to create bigger elval until get final
            }
            Ok(exp)
        }
        x => parser.error_prev(&format!("expected id, num, nil, or open paren. got {x:?}")),
    }
}

fn exp_ac_r(parser: &mut Parser, base: Exp) -> Result<Exp, ParseError> {
    match parser.next() {
        Some(OpenParen) => {
            let args = if !parser.next_is(CloseParen) {
                args_r(parser)?
            } else {
                vec![]
            };
            parser.expect(CloseParen)?;
            Ok(Exp::Call {
                callee: Box::new(base),
                args,
            })
        }
        Some(Dot) => {
            parser.expect(Id)?;
            Ok(Exp::FieldAccess {
                ptr: Box::new(base),
                field: parser.slice_prev().to_string(),
            })
        }
        Some(OpenBracket) => {
            let exp = exp_r(parser)?;
            parser.expect(CloseBracket)?;
            Ok(Exp::ArrayAccess {
                ptr: Box::new(base),
                index: Box::new(exp),
            })
        }
        x => parser.error_prev(&format!(
            "expected open paren, dot, or open brace. got {x:?}"
        )),
    }
}
