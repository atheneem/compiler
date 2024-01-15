use collapse::*;

use crate::{commons::Valid, middle_end::lir::Program};

mod constant_prop;
mod inlining;

// Read given test file, run given analysis, and compare its results to the
// expected results from given result file.
//
// This file checks only the pre state for each basic block.
fn run_test(test_name: &str, pass: fn(Valid<Program>) -> Valid<Program>, pass_name: &str) {
    let read = |input_file: &str| {
        String::from_utf8(
            std::fs::read(input_file)
                .unwrap_or_else(|_| panic!("Could not read the input file {}", input_file)),
        )
        .expect("The input file does not contain valid utf-8 text")
    };

    let input_program = read(&format!("test-data/{test_name}.lir"))
        .parse::<Program>()
        .unwrap()
        .validate()
        .unwrap();

    let output_program = pass(input_program).0.validate().unwrap().0;

    let actual = output_program.to_string();

    let expected = read(&format!("test-data/{test_name}.{pass_name}.lir"));

    collapsed_eq!(&actual, &expected);
}
