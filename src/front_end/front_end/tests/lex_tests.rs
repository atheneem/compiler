// lexer tests.

use super::*;

#[test]
fn lex_empty_string() {
    let code = "";
    assert_eq!(lex(code), []);
}

#[test]
fn lex_single_token() {
    use TokenKind::*;

    let code = "1";
    assert_eq!(
        lex(code),
        [Token {
            kind: Num,
            span: 0..1
        },]
    );

    let code = "x";
    assert_eq!(
        lex(code),
        [Token {
            kind: Id,
            span: 0..1
        },]
    );

    let code = "yolo";
    assert_eq!(
        lex(code),
        [Token {
            kind: Id,
            span: 0..4
        },]
    );

    let code = "ifwhile";
    assert_eq!(
        lex(code),
        [Token {
            kind: Id,
            span: 0..7
        }]
    );

    let code = "int";
    assert_eq!(
        lex(code),
        [Token {
            kind: Int,
            span: 0..3
        },]
    );

    let code = "struct";
    assert_eq!(
        lex(code),
        [Token {
            kind: Struct,
            span: 0..6
        },]
    );

    let code = "nil";
    assert_eq!(
        lex(code),
        [Token {
            kind: Nil,
            span: 0..3
        },]
    );

    let code = "break ";
    assert_eq!(
        lex(code),
        [Token {
            kind: Break,
            span: 0..5
        },]
    );

    let code = " continue";
    assert_eq!(
        lex(code),
        [Token {
            kind: Continue,
            span: 1..9
        },]
    );

    let code = "return";
    assert_eq!(
        lex(code),
        [Token {
            kind: Return,
            span: 0..6
        },]
    );

    let code = "if";
    assert_eq!(
        lex(code),
        [Token {
            kind: If,
            span: 0..2
        },]
    );

    let code = "else";
    assert_eq!(
        lex(code),
        [Token {
            kind: Else,
            span: 0..4
        },]
    );

    let code = "while";
    assert_eq!(
        lex(code),
        [Token {
            kind: While,
            span: 0..5
        },]
    );

    let code = "new";
    assert_eq!(
        lex(code),
        [Token {
            kind: New,
            span: 0..3
        },]
    );

    let code = "let";
    assert_eq!(
        lex(code),
        [Token {
            kind: Let,
            span: 0..3
        },]
    );

    let code = "extern";
    assert_eq!(
        lex(code),
        [Token {
            kind: Extern,
            span: 0..6
        },]
    );

    let code = "fn";
    assert_eq!(
        lex(code),
        [Token {
            kind: Fn,
            span: 0..2
        },]
    );

    let code = ": ::";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Colon,
                span: 0..1
            },
            Token {
                kind: Colon,
                span: 2..3
            },
            Token {
                kind: Colon,
                span: 3..4
            }
        ]
    );

    let code = ";";
    assert_eq!(
        lex(code),
        [Token {
            kind: Semicolon,
            span: 0..1
        },]
    );

    let code = ",";
    assert_eq!(
        lex(code),
        [Token {
            kind: Comma,
            span: 0..1
        },]
    );

    let code = "__";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Underscore,
                span: 0..1
            },
            Token {
                kind: Underscore,
                span: 1..2
            },
        ]
    );

    let code = "->->";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Arrow,
                span: 0..2
            },
            Token {
                kind: Arrow,
                span: 2..4
            },
        ]
    );

    let code = "&&";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Address,
                span: 0..1
            },
            Token {
                kind: Address,
                span: 1..2
            }
        ]
    );

    let code = "!!";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Bang,
                span: 0..1
            },
            Token {
                kind: Bang,
                span: 1..2
            }
        ]
    );

    let code = "++";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Plus,
                span: 0..1
            },
            Token {
                kind: Plus,
                span: 1..2
            }
        ]
    );

    let code = "--";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Dash,
                span: 0..1
            },
            Token {
                kind: Dash,
                span: 1..2
            },
        ]
    );

    let code = "**";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Star,
                span: 0..1
            },
            Token {
                kind: Star,
                span: 1..2
            },
        ]
    );

    let code = "/ /";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Slash,
                span: 0..1
            },
            Token {
                kind: Slash,
                span: 2..3
            }
        ]
    );

    let code = "==";
    assert_eq!(
        lex(code),
        [Token {
            kind: Equal,
            span: 0..2
        },]
    );

    let code = "!=";
    assert_eq!(
        lex(code),
        [Token {
            kind: NotEq,
            span: 0..2
        },]
    );

    let code = "<<";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Lt,
                span: 0..1
            },
            Token {
                kind: Lt,
                span: 1..2
            },
        ]
    );

    let code = "<=<=";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Lte,
                span: 0..2
            },
            Token {
                kind: Lte,
                span: 2..4
            },
        ]
    );

    let code = ">>";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Gt,
                span: 0..1
            },
            Token {
                kind: Gt,
                span: 1..2
            },
        ]
    );

    let code = ">=>=";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Gte,
                span: 0..2
            },
            Token {
                kind: Gte,
                span: 2..4
            },
        ]
    );

    let code = "and and";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: And,
                span: 0..3
            },
            Token {
                kind: And,
                span: 4..7
            }
        ]
    );

    let code = "or or";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Or,
                span: 0..2
            },
            Token {
                kind: Or,
                span: 3..5
            }
        ]
    );

    let code = "..";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Dot,
                span: 0..1
            },
            Token {
                kind: Dot,
                span: 1..2
            },
        ]
    );

    let code = "= =";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Gets,
                span: 0..1
            },
            Token {
                kind: Gets,
                span: 2..3
            }
        ]
    );

    let code = "((";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: OpenParen,
                span: 0..1
            },
            Token {
                kind: OpenParen,
                span: 1..2
            },
        ]
    );

    let code = "))";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: CloseParen,
                span: 0..1
            },
            Token {
                kind: CloseParen,
                span: 1..2
            },
        ]
    );

    let code = "[[";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: OpenBracket,
                span: 0..1
            },
            Token {
                kind: OpenBracket,
                span: 1..2
            },
        ]
    );

    let code = "]]";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: CloseBracket,
                span: 0..1
            },
            Token {
                kind: CloseBracket,
                span: 1..2
            },
        ]
    );

    let code = "{{";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: OpenBrace,
                span: 0..1
            },
            Token {
                kind: OpenBrace,
                span: 1..2
            },
        ]
    );

    let code = "}}";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: CloseBrace,
                span: 0..1
            },
            Token {
                kind: CloseBrace,
                span: 1..2
            }
        ]
    );
}

#[test]
fn lex_multiple_tokens() {
    use TokenKind::*;

    let code = "int whileif foo\n!10bar int";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Int,
                span: 0..3
            },
            Token {
                kind: Id,
                span: 4..11
            },
            Token {
                kind: Id,
                span: 12..15
            },
            Token {
                kind: Bang,
                span: 16..17
            },
            Token {
                kind: Num,
                span: 17..19
            },
            Token {
                kind: Id,
                span: 19..22
            },
            Token {
                kind: Int,
                span: 23..26
            }
        ]
    );
}

#[test]
fn lex_comments() {
    use TokenKind::*;

    let code = r"int//comment int
    int";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Int,
                span: 0..3
            },
            Token {
                kind: Int,
                span: 21..24
            }
        ]
    );

    let code = r"int//comment int";
    assert_eq!(
        lex(code),
        [Token {
            kind: Int,
            span: 0..3
        }]
    );

    let code = "int/*comment int*/int";

    assert_eq!(
        lex(code),
        [
            Token {
                kind: Int,
                span: 0..3
            },
            Token {
                kind: Int,
                span: 18..21
            }
        ]
    );

    let code = "int/*comment line 1
    comment line 2 
    int*/int";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Int,
                span: 0..3
            },
            Token {
                kind: Int,
                span: 49..52
            }
        ]
    );

    let code = "int/*comment line 1
    comment line 2 
    int int**/";
    assert_eq!(
        lex(code),
        [Token {
            kind: Int,
            span: 0..3
        }]
    );
}

#[test]
fn lex_mixed_tokens() {
    use TokenKind::*;

    let code = r"0foo0";
    assert_eq!(
        lex(code),
        &[
            Token {
                kind: Num,
                span: 0..1
            },
            Token {
                kind: Id,
                span: 1..5
            }
        ]
    );
}

#[test]
fn lex_error_test() {
    use TokenKind::*;

    let code = "@^%%foo";
    assert_eq!(
        lex(code),
        [
            Token {
                kind: Error,
                span: 0..1
            },
            Token {
                kind: Error,
                span: 1..2
            },
            Token {
                kind: Error,
                span: 2..3
            },
            Token {
                kind: Error,
                span: 3..4
            },
            Token {
                kind: Id,
                span: 4..7
            },
        ]
    );
}
