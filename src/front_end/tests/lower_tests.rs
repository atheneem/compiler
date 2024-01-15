// lowering tests.

use super::*;
use crate::commons::skip_validation;
use crate::interpreter::{interpret_with_output, RuntimeError};
use crate::middle_end::lir;
use std::error::Error;

// mod hidden;
mod part1_basic;
mod part1_second_point;
mod part2_basic;
mod part2_second_point;

// Parse given program, skip validation, lower to LIR, validate, run and return
// what `main` returns.
fn lower_and_run(code: &str) -> Result<i64, String> {
    lower_and_run_capture_output(code).map(|(r, _)| r)
}

// Run a program, return the value `main` returns and the list of numbers
// printed using `print`.
fn lower_and_run_capture_output(code: &str) -> Result<(i64, Vec<i64>), String> {
    // replace the call to `parse` with `mock_parse` if you are using the mock parser.
    let program = parse(code).map_err(|err| format!("{err}"))?;

    let lowered = lower(&skip_validation(program));
    lir::validate(&lowered).expect("The generated LIR program is not valid.");

    interpret_with_output(lowered).map_err(|RuntimeError(s)| format!("runtime error: {s}"))
}
