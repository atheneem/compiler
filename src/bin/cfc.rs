// The compiler for CFlat code.

use clap::Parser;
use derive_more::Display;
use optimization::commons::{skip_validation, Valid};
use optimization::front_end::*;
use optimization::middle_end::lir;
use optimization::middle_end::optimization::{
    constant_prop::*, copy_prop::*, dead_store_elimination::*, inlining::*,
};
use std::str::FromStr;

// Input/output file types
#[derive(Display, Clone, Copy, PartialEq, Eq)]
enum FileType {
    CFlat,
    Ast,
    Lir,
    Dot,
}

// File names with associated file types.  This is used for determining input
// and output file types from file names.  The actual functionality is
// implemented in the `from_str` trait function.
#[derive(Clone)]
struct File {
    typ: FileType,
    name: String,
}

impl FromStr for File {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use FileType::*;

        let name = String::from(s);
        let typ = s.rsplit_once('.').and_then(|(_, extension)| match extension {
            "lir" => Some(Lir),
            "json" => Some(Ast),
            "cf" | "cb" => Some(CFlat),
            "dot" => Some(Dot),
            _ => None,
        }).ok_or_else(|| format!("Expected a file name with one of the following extensions: json, lir, cf, cb, dot. Got {}", s))?;

        Ok(File { typ, name })
    }
}

trait PassT {}

#[derive(Clone)]
enum Pass {
    Basic(fn(Valid<lir::Program>) -> Valid<lir::Program>),
    InlineSmall(usize, usize),
}

impl Pass {
    fn run(&self, p: Valid<lir::Program>) -> Valid<lir::Program> {
        use Pass::*;

        match self {
            Basic(f) => f(p),
            InlineSmall(n, m) => inline_small_fns(p, *n, *m),
        }
    }
}

impl FromStr for Pass {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use Pass::*;

        let pass = match s {
            "dse" => Basic(dead_store_elim),
            "const-prop" => Basic(constant_prop),
            "copy-prop" => Basic(copy_prop),
            "inline-leaves" => Basic(inline_leaf_functions),
            _ if s.starts_with("inline-small-") => {
                let s = &s["inline-small-".len()..];
                let dash = s
                    .find('-')
                    .ok_or(format!("unknown optimization pass: {s}"))?;
                let n = s[0..dash].parse::<usize>().map_err(|e| e.to_string())?;
                let m = s[(dash + 1)..]
                    .parse::<usize>()
                    .map_err(|e| e.to_string())?;
                InlineSmall(n, m)
            }
            _ => return Err(format!("unknown optimization pass: {s}")),
        };

        Ok(pass)
    }
}

// Command-line arguments
#[derive(Parser)]
#[command(version, about)]
struct Args {
    #[arg(short = 'O', long)]
    optimization_passes: Vec<Pass>,
    input_file: File,
    output_file: File,
}

pub fn main() {
    let args = Args::parse();
    let input_file = args.input_file.name.as_str();
    let output_file = args.output_file.name.as_str();

    let input_string = String::from_utf8(
        std::fs::read(input_file)
            .unwrap_or_else(|_| panic!("Could not read the input file {}", input_file)),
    )
    .expect("The input file does not contain valid utf-8 text");

    let mut cf_program: Option<ast::Program> = None;
    let program: lir::Program = match args.input_file.typ {
        FileType::Lir => input_string.parse().unwrap(),
        FileType::Ast => {
            cf_program = Some(
                serde_json::from_str(&input_string)
                    .unwrap_or_else(|e| panic!("AST JSON file is not valid: {e}")),
            );
            lower(&skip_validation(cf_program.as_ref().unwrap().clone()))
        }
        FileType::CFlat => {
            let cfp = parse(&input_string).unwrap_or_else(|e| panic!("Syntax error: {e}"));
            lower(&skip_validation(cfp.clone()))
        }
        _ => panic!("The input file cannot be a graph description."),
    };

    let mut program = program.validate().unwrap();

    for pass in args.optimization_passes {
        program = pass.run(program);
    }

    let output = match args.output_file.typ {
        FileType::Lir => program.0.to_string().into_bytes(),
        FileType::Ast if cf_program.is_some() => serde_json::to_string_pretty(&cf_program.unwrap())
            .unwrap()
            .into_bytes(),
        FileType::Dot => lir::dump_cfg_of_whole_program(&program.0).into_bytes(),
        _ => panic!("Cannot output a given file from the given input"),
    };

    std::fs::write(output_file, output).unwrap_or_else(|_| {
        panic!(
            "Failed to write to the optimized program to the output file: {}",
            output_file
        )
    });
}
