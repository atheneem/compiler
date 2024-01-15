// parser tests.

use super::*;

mod basic_tests;
mod expr_and_complex_tests;

/// Checks if given program doesn't change when parsed then unparsed.
fn parse_and_prettify(code: &str) {
    prettifies_to(code, code)
}

/// Checks if unparse(parse(code)) == prettified_code
fn prettifies_to(code: &str, prettified_code: &str) {
    let unparsed_program = match parse(code) {
        Ok(program) => program.pretty_print(),
        Err(ParseError(err)) => {
            panic!("Expected the parser to produce an AST. Parse error:\n{err}\nInput:\n{code}\n")
        }
    };

    assert_eq!(prettified_code, unparsed_program);
}

/// Return if given program fails to parse
fn fails_to_parse(program: &str) -> bool {
    parse(program).is_err()
}
