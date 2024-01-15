// General analysis tests

use clap::Parser;
use optimization::commons::Valid;
use std::collections::BTreeMap as Map;
use std::io::{BufWriter, Write};
use std::str::FromStr;

use optimization::middle_end::analysis::*;
use optimization::middle_end::lir::*;

type Analysis<Env> = fn(&Valid<Program>, FuncId) -> (Map<BbId, Env>, Map<InstId, Env>);

#[derive(Clone, Copy)]
struct Pass(fn(Valid<Program>) -> String);

impl Pass {
    fn run(&self, p: Valid<Program>) -> String {
        self.0(p)
    }
}

impl FromStr for Pass {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn const_prop_analysis(p: Valid<Program>) -> String {
            run_analysis(p, constant_prop::analyze, constant_prop::Env::to_string)
        }

        fn reaching_defs_analysis(p: Valid<Program>) -> String {
            run_analysis(p, reaching_defs::analyze, reaching_defs::Env::to_string)
        }

        fn liveness_analysis(p: Valid<Program>) -> String {
            run_analysis(p, liveness::analyze, |env| {
                let mut w = BufWriter::new(Vec::new());
                write!(w, "{{").unwrap();
                env.live_defs
                    .iter()
                    .for_each(|(bb, n)| write!(w, "{bb}.{n}, ").unwrap());
                write!(w, "}}\n").unwrap();

                String::from_utf8(w.into_inner().unwrap()).unwrap()
            })
        }

        let pass = match s {
            "const-prop" => Pass(const_prop_analysis),
            "reaching-defs" => Pass(reaching_defs_analysis),
            "liveness" => Pass(liveness_analysis),
            _ => return Err(format!("unknown analysis pass: {s}")),
        };

        Ok(pass)
    }
}

// Command-line arguments
#[derive(Parser)]
#[command(version, about)]
struct Args {
    analysis: Pass,
    input_file: String,
    output_file: String,
}

fn run_analysis<Env: AbstractEnv, Printer: Fn(&Env) -> String>(
    input_program: Valid<Program>,
    analysis: Analysis<Env>,
    pretty_print: Printer,
) -> String {
    let mut w = BufWriter::new(Vec::new());

    for f in input_program.0.functions.keys() {
        let pre_bb = analysis(&input_program, f.clone()).0;

        write!(w, "{f}:\n\n").unwrap();

        for (id, state) in &pre_bb {
            write!(w, "{id}:\n{}\n\n", pretty_print(state)).unwrap();
        }
    }

    String::from_utf8(w.into_inner().unwrap()).unwrap()
}

pub fn main() {
    let args = Args::parse();
    let input_file = args.input_file.as_str();
    let output_file = args.output_file.as_str();

    let read = |input_file: &str| {
        String::from_utf8(
            std::fs::read(input_file)
                .unwrap_or_else(|_| panic!("Could not read the input file {}", input_file)),
        )
        .expect("The input file does not contain valid utf-8 text")
    };

    let input_program = read(input_file)
        .parse::<Program>()
        .unwrap()
        .validate()
        .unwrap();

    let output = args.analysis.run(input_program);

    std::fs::write(output_file, output).unwrap_or_else(|_| {
        panic!(
            "Failed to write to the optimized program to the output file: {}",
            output_file
        )
    });
}
