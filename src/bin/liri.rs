// The LIR interpreter

use clap::Parser;
use optimization::interpreter::interpret_with_output;
use optimization::middle_end::lir;

// Command-line arguments
#[derive(Parser)]
#[command(version, about)]
struct Args {
    program: String,
}

pub fn main() {
    let input_file = Args::parse().program;

    let input_string = String::from_utf8(
        std::fs::read(&input_file)
            .unwrap_or_else(|_| panic!("Could not read the input file {}", input_file)),
    )
    .expect("The input file does not contain valid utf-8 text");

    let program: lir::Program = input_string.parse().expect("Failed to parse LIR code");

    lir::validate(&program).unwrap();

    let (ret, out) = interpret_with_output(program).unwrap();
    for n in out {
        println!("{n}");
    }
    println!("main returned {ret}");
}
