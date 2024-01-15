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
    todo!()
}

// non-pointer type.
fn type_ad_r(parser: &mut Parser) -> Result<Type, ParseError> {
    todo!()
}

// type in parentheses OR function type.
fn type_op_r(parser: &mut Parser) -> Result<Type, ParseError> {
    todo!()
}

// type in parentheses OR function type.
#[allow(clippy::type_complexity)]
fn type_fp_r(parser: &mut Parser) -> Result<Option<(Vec<Type>, Option<Type>)>, ParseError> {
    todo!()
}

// function return type.
fn type_ar_r(parser: &mut Parser) -> Result<Option<Type>, ParseError> {
    todo!()
}

// function type.
fn funtype_r(parser: &mut Parser) -> Result<Type, ParseError> {
    todo!()
}

// function return type.
fn rettyp_r(parser: &mut Parser) -> Result<Option<Type>, ParseError> {
    todo!()
}

// cflat program.
fn program_r(parser: &mut Parser) -> Result<Program, ParseError> {
    let mut program = Program {
        globals: vec![],
        typedefs: vec![],
        externs: vec![],
        functions: vec![],
    };

    todo!();

    Ok(program)
}

// global variable declaration.
fn glob_r(parser: &mut Parser) -> Result<Vec<Decl>, ParseError> {
    todo!()
}

// struct type declaration.
fn typedef_r(parser: &mut Parser) -> Result<Typedef, ParseError> {
    todo!()
}

// variable declaration.
fn decl_r(parser: &mut Parser) -> Result<Decl, ParseError> {
    todo!()
}

// series of variable declarations.
fn decls_r(parser: &mut Parser) -> Result<Vec<Decl>, ParseError> {
    todo!()
}

// external function declaration.
fn extern_r(parser: &mut Parser) -> Result<Decl, ParseError> {
    todo!()
}

// function definition.
fn fundef_r(parser: &mut Parser) -> Result<Function, ParseError> {
    todo!()
}

// internal variable declaration and possibly initialization.
fn let_r(parser: &mut Parser) -> Result<Vec<(Decl, Option<Exp>)>, ParseError> {
    todo!()
}

// statement.
fn stmt_r(parser: &mut Parser) -> Result<Stmt, ParseError> {
    todo!()
}

// conditional statement.
fn cond_r(parser: &mut Parser) -> Result<Stmt, ParseError> {
    todo!()
}

// while or for loop.
fn loop_r(parser: &mut Parser) -> Result<Stmt, ParseError> {
    todo!()
}

// sequence of statements.
fn block_r(parser: &mut Parser) -> Result<Vec<Stmt>, ParseError> {
    todo!()
}

// assignment or call statement.
fn assign_or_call_r(parser: &mut Parser) -> Result<Stmt, ParseError> {
    todo!()
}

// right-hand side of an assignment.
fn rhs_r(parser: &mut Parser) -> Result<Rhs, ParseError> {
    todo!()
}

// left-hand side of an assignment.
fn lval_r(parser: &mut Parser) -> Result<Lval, ParseError> {
    todo!()
}

// access path.
fn access_r(parser: &mut Parser, base: Lval) -> Result<Lval, ParseError> {
    todo!()
}

// call arguments.
fn args_r(parser: &mut Parser) -> Result<Vec<Exp>, ParseError> {
    todo!()
}

// expression (precedence level 6).
fn exp_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    // This is just a basic parser for variables. You need to replace this to
    // work with expressions in general.
    match parser.next() {
        Some(Id) => {
            let id = parser.slice_prev().to_string();
            Ok(Exp::Id(id))
        }
        _ => parser.error_prev("this is a dummy parse error, you need to implement exp_r"),
    }
}

// expression (precedence level 5).
fn exp_p5_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    todo!()
}

// expression (precedence level 4).
fn exp_p4_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    todo!()
}

// expression (precedence level 3).
fn exp_p3_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    todo!()
}

// expression (precedence level 2).
fn exp_p2_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    todo!()
}

// expression (precedence level 1).
fn exp_p1_r(parser: &mut Parser) -> Result<Exp, ParseError> {
    todo!()
}

fn exp_ac_r(parser: &mut Parser, base: Exp) -> Result<Exp, ParseError> {
    todo!()
}
