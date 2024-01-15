// lexer for cflat's front-end syntax.

use std::ops::Range;

use derive_more::Display;
use logos::Logos;

// tokenizes the given string; invalid lexemes are represented with Error tokens
// in the returned vector.
#[allow(dead_code)]
pub fn lex(code: &str) -> Vec<Token> {
    TokenKind::lexer(code)
        .spanned()
        .map(|(tk, span)| match tk {
            Ok(kind) => Token { kind, span },
            Err(_) => Token {
                kind: TokenKind::Error,
                span,
            },
        })
        .collect::<Vec<_>>()
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Range<usize>,
}

#[derive(Logos, Clone, Copy, Debug, Display, Eq, PartialEq)]
#[logos(skip r"[ \t\n\f]+")] // skip whitespace.
#[logos(skip r"//.*\n?")] // skip C++-style comments.
#[logos(skip r"/\*([^*]|\**[^*/])*\*+/")] // skip C-style comments.
#[logos(skip r"/\*([^*]|\*+[^*/])*\*?")] // skip unclosed C-style comments.
pub enum TokenKind {
    // represents invalid lexemes, i.e., unrecognized ASCII characters.
    Error,

    #[regex("[0-9]+")]
    #[display(fmt = "num")]
    Num,

    #[regex("[a-zA-Z][a-zA-Z0-9]*")]
    #[display(fmt = "id")]
    Id,

    #[regex("int")]
    #[display(fmt = "int")]
    Int,

    #[regex("struct")]
    #[display(fmt = "struct")]
    Struct,

    #[regex("nil")]
    #[display(fmt = "nil")]
    Nil,

    #[regex("break")]
    #[display(fmt = "break")]
    Break,

    #[regex("continue")]
    #[display(fmt = "continue")]
    Continue,

    #[regex("return")]
    #[display(fmt = "return")]
    Return,

    #[regex("if")]
    #[display(fmt = "if")]
    If,

    #[regex("else")]
    #[display(fmt = "else")]
    Else,

    #[regex("while")]
    #[display(fmt = "while")]
    While,

    #[regex("new")]
    #[display(fmt = "new")]
    New,

    #[regex("let")]
    #[display(fmt = "let")]
    Let,

    #[regex("extern")]
    #[display(fmt = "extern")]
    Extern,

    #[regex("fn")]
    #[display(fmt = "fn")]
    Fn,

    #[regex(":")]
    #[display(fmt = ":")]
    Colon,

    #[regex(";")]
    #[display(fmt = ";")]
    Semicolon,

    #[regex(",")]
    #[display(fmt = ",")]
    Comma,

    #[regex("_")]
    #[display(fmt = "_")]
    Underscore,

    #[regex("->")]
    #[display(fmt = "->")]
    Arrow,

    #[regex("&")]
    #[display(fmt = "&")]
    Address,

    #[regex("!")]
    #[display(fmt = "!")]
    Bang,

    #[regex("\\+")]
    #[display(fmt = "+")]
    Plus,

    #[regex("-")]
    #[display(fmt = "-")]
    Dash,

    #[regex("\\*")]
    #[display(fmt = "*")]
    Star,

    #[regex("/")]
    #[display(fmt = "/")]
    Slash,

    #[regex("==")]
    #[display(fmt = "==")]
    Equal,

    #[regex("!=")]
    #[display(fmt = "!=")]
    NotEq,

    #[regex("<")]
    #[display(fmt = "<")]
    Lt,

    #[regex("<=")]
    #[display(fmt = "<=")]
    Lte,

    #[regex(">")]
    #[display(fmt = ">")]
    Gt,

    #[regex(">=")]
    #[display(fmt = ">=")]
    Gte,

    #[regex("and")]
    #[display(fmt = "and")]
    And,

    #[regex("or")]
    #[display(fmt = "or")]
    Or,

    #[regex("\\.")]
    #[display(fmt = ".")]
    Dot,

    #[regex("=")]
    #[display(fmt = "=")]
    Gets,

    #[regex("\\(")]
    #[display(fmt = "(")]
    OpenParen,

    #[regex("\\)")]
    #[display(fmt = ")")]
    CloseParen,

    #[regex("\\[")]
    #[display(fmt = "[")]
    OpenBracket,

    #[regex("\\]")]
    #[display(fmt = "]")]
    CloseBracket,

    #[regex("\\{")]
    #[display(fmt = "{{")]
    OpenBrace,

    #[regex("\\}")]
    #[display(fmt = "}}")]
    CloseBrace,
}
