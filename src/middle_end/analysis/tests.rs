// General analysis tests

mod constant_prop;
mod reaching_defs;

use std::io::{BufWriter, Write};

use collapse::*;

use crate::commons::Valid;

use super::*;

type Analysis<Env> = fn(&Valid<Program>, FuncId) -> (Map<BbId, Env>, Map<InstId, Env>);

// Read given test file, run given analysis, and compare its results to the
// expected results from given result file.
//
// This file checks only the pre state for each basic block.
fn run_test<Env: AbstractEnv, Printer: Fn(&Env) -> String>(
    test_name: &str,
    analysis: Analysis<Env>,
    analysis_name: &str,
    pretty_print: Printer,
) {
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

    let mut w = BufWriter::new(Vec::new());

    for f in input_program.0.functions.keys() {
        let pre_bb = analysis(&input_program, f.clone()).0;

        write!(w, "{f}:\n\n").unwrap();

        for (id, state) in &pre_bb {
            write!(w, "{id}:\n{}\n\n", pretty_print(state)).unwrap();
        }
    }

    let actual = String::from_utf8(w.into_inner().unwrap()).unwrap();

    let expected = read(&format!("test-data/{test_name}.{analysis_name}"));

    collapsed_eq!(&actual, &expected);
}
