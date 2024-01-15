use super::super::constant_prop::*;
use super::*;
use crate::middle_end::lir::*;

fn run_on_file(test_name: &str) {
    run_test(test_name, constant_prop, "const_prop");
}

// Check if the input program optimizes to the expected output program
fn optimizes_to(input: &str, expected: &str) {
    // parse & sanitize the inputs
    let input = input.parse::<Program>().unwrap().validate().unwrap();
    let expected = expected
        .parse::<Program>()
        .unwrap()
        .validate()
        .unwrap()
        .0
        .to_string();

    let actual = constant_prop(input).0;

    assert_eq!(actual.to_string(), expected);
}

#[test]
fn simple_arith1() {
    optimizes_to(
        r#"
    fn test(top:int) -> _ {
    let a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int, i:int, j:int, k:int, l:int, bot:int
    entry:
      a = $arith add 1 1
      b = $arith sub 1 1
      c = $arith mul 2 2
      d = $arith div 4 2
      bot = $arith div 2 0
      e = $arith add top 1
      f = $arith sub top 1
      g = $arith mul 1 top
      h = $arith div 1 top
      i = $arith add bot 1
      j = $arith sub bot 1
      k = $arith mul 1 bot
      l = $arith div 1 bot
      i = $arith add bot top
      j = $arith sub bot top
      k = $arith mul top bot
      l = $arith div top bot
      $ret
    }

    fn main() -> int {
    entry:
      $ret 0
    }
    "#,
        r#"
    fn test(top:int) -> _ {
    let a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int, i:int, j:int, k:int, l:int, bot:int
    entry:
      a = $copy 2
      b = $copy 0
      c = $copy 4
      d = $copy 2
      bot = $arith div 2 0
      e = $arith add top 1
      f = $arith sub top 1
      g = $arith mul 1 top
      h = $arith div 1 top
      i = $arith add bot 1
      j = $arith sub bot 1
      k = $arith mul 1 bot
      l = $arith div 1 bot
      i = $arith add bot top
      j = $arith sub bot top
      k = $arith mul top bot
      l = $arith div top bot
      $ret
    }

    fn main() -> int {
    entry:
      $ret 0
    }
    "#,
    );
}

#[test]
fn simple_arith2() {
    optimizes_to(
        r#"
    fn test(top:int) -> _ {
    let a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int, i:int, j:int, k:int, l:int, bot:int
    entry:
      a = $arith add 1 1
      b = $arith sub a 4
      a = $arith mul b 2
      d = $arith div a 3
      bot = $arith div 2 0
      e = $arith add top 1
      f = $arith sub top 1
      g = $arith mul 1 top
      h = $arith div 1 top
      i = $arith add bot 1
      j = $arith sub bot 1
      k = $arith mul 1 bot
      l = $arith div 1 bot
      i = $arith add bot top
      j = $arith sub bot top
      k = $arith mul top bot
      l = $arith div top bot
      $ret
    }

    fn main() -> int {
    entry:
      $ret 0
    }
    "#,
        r#"
    fn test(top:int) -> _ {
    let a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int, i:int, j:int, k:int, l:int, bot:int
    entry:
      a = $copy 2
      b = $copy -2
      a = $copy -4
      d = $copy -1
      bot = $arith div 2 0
      e = $arith add top 1
      f = $arith sub top 1
      g = $arith mul 1 top
      h = $arith div 1 top
      i = $arith add bot 1
      j = $arith sub bot 1
      k = $arith mul 1 bot
      l = $arith div 1 bot
      i = $arith add bot top
      j = $arith sub bot top
      k = $arith mul top bot
      l = $arith div top bot
      $ret
    }

    fn main() -> int {
    entry:
      $ret 0
    }
    "#,
    );
}

// These tests are in alphabetical order

#[test]
fn arith_div_by_zero() {
    run_on_file("arith-div-by-zero");
}

#[test]
fn arith0() {
    run_on_file("arith0");
}

#[test]
fn arith1() {
    run_on_file("arith1");
}

#[test]
fn arith2() {
    run_on_file("arith2");
}

#[test]
fn assign_and_arith() {
    run_on_file("assign_and_arith");
}

#[test]
fn assign_basic() {
    run_on_file("assign_basic");
}

#[test]
fn assign_basic2() {
    run_on_file("assign_basic2");
}

#[test]
fn assign_compare_nil() {
    run_on_file("assign_compare_nil");
}

#[test]
fn call() {
    run_on_file("call");
}

#[test]
fn call_direct1() {
    run_on_file("call_direct1");
}

#[test]
fn call_direct2() {
    run_on_file("call_direct2");
}

#[test]
fn call_extern() {
    run_on_file("call_extern");
}

#[test]
fn call_indirect() {
    run_on_file("call_indirect");
}

#[test]
fn compare1() {
    run_on_file("compare1");
}

#[test]
fn compare2() {
    run_on_file("compare2");
}

#[test]
fn fib1() {
    run_on_file("fib1");
}

#[test]
fn fib2() {
    run_on_file("fib2");
}

#[test]
fn global() {
    run_on_file("global");
}

#[test]
fn hw5() {
    run_on_file("hw5");
}

#[test]
fn hw6() {
    run_on_file("hw6");
}

#[test]
fn if1() {
    run_on_file("if1");
}

#[test]
fn if2() {
    run_on_file("if2");
}

#[test]
fn if3() {
    run_on_file("if3");
}

#[test]
fn if4() {
    run_on_file("if4");
}

#[test]
fn in_class_example() {
    run_on_file("in_class_example");
}

#[test]
fn linked_list() {
    run_on_file("linked_list");
}

#[test]
fn nested_field() {
    run_on_file("nested_field");
}

#[test]
fn nested_ptr() {
    run_on_file("nested_ptr");
}

#[test]
fn new_array() {
    run_on_file("new_array");
}

#[test]
fn new_deref() {
    run_on_file("new_deref");
}

#[test]
fn new_field() {
    run_on_file("new_field");
}

#[test]
fn not1() {
    run_on_file("not1");
}

#[test]
fn not2() {
    run_on_file("not2");
}

#[test]
fn not3() {
    run_on_file("not3");
}

#[test]
fn not_and_compare() {
    run_on_file("not_and_compare");
}

#[test]
fn tortoise_and_hare() {
    run_on_file("tortoise_and_hare");
}

#[test]
fn while1() {
    run_on_file("while1");
}

#[test]
fn while2() {
    run_on_file("while2");
}

#[test]
fn while3() {
    run_on_file("while3");
}
