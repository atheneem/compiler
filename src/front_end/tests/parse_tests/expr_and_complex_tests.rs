// Complex parser tests.  Note that spaces and new lines in test inputs matter.

use super::*;

#[test]
fn exp_simple() {
    prettifies_to(
        r"fn main() -> _ {
  return x;
  return nil;
  return 1;
  return (x);
}
",
        r"fn main() -> _ {
  return x;
  return nil;
  return 1;
  return x;
}
",
    );
}

#[test]
fn exp_ac() {
    parse_and_prettify(
        r"fn main() -> _ {
  return x;
  return x(y, z);
  return f(x);
  return f();
  return x[y(a, b).foo].bar;
}
",
    );
}

#[test]
fn exp_unop() {
    parse_and_prettify(
        r"fn main() -> _ {
  return !x;
  return -x;
  return *x;
  return !-*x;
}
",
    );
}

#[test]
fn exp_arith() {
    prettifies_to(
        r"fn main() -> _ {
  return x / (y * 2);
  return x / y * z;
  return x + y - z;
  return x + (y - z);
  return (x + y) * (z - t);
}
",
        r"fn main() -> _ {
  return x / (y * 2);
  return (x / y) * z;
  return (x + y) - z;
  return x + (y - z);
  return (x + y) * (z - t);
}
",
    );
}

#[test]
fn exp_compare() {
    prettifies_to(
        r"fn main() -> _ {
  return x == y != z;
  return x < y;
  return x <= y;
  return x > y;
  return x >= y;
}
",
        r"fn main() -> _ {
  return (x == y) != z;
  return x < y;
  return x <= y;
  return x > y;
  return x >= y;
}
",
    );
}

#[test]
fn exp_logic() {
    prettifies_to(
        r"fn main() -> _ {
  return x and y;
  return x or y;
  return x and y and z;
  return x or 0 and 1;
  return x and a or 1;
}
",
        r"fn main() -> _ {
  return x and y;
  return x or y;
  return x and (y and z);
  return x or (0 and 1);
  return x and (a or 1);
}
",
    );
}

#[test]
fn exp_multiple_precedence() {
    prettifies_to(
        r"fn main() -> _ {
  return x < y + z;
  return x + (y > z);
  return x + y <= z;
  return !x >= y;
  return !(x >= y);
  return x + y < z and -2 >= !1 / 4 or *p;
}
",
        r"fn main() -> _ {
  return x < (y + z);
  return x + (y > z);
  return (x + y) <= z;
  return !x >= y;
  return !(x >= y);
  return ((x + y) < z) and ((-2 >= (!1 / 4)) or *p);
}
",
    );
}

// todo:
// - different lvals, containing different expressions
// - combined statements
// - multiple top-levels
// - mixed top-levels

#[test]
fn large_program() {
    parse_and_prettify(
        r"struct stack {
  top: int,
  next: &stack
}

let true: int;
let false: int;

fn top(s: &stack) -> int {
  return s.top;
}

fn pop(s: &stack) -> int {
  let t: int = s.top;
  *s = s.next;
  return t;
}

fn isEmpty(s: &stack) -> int {
  return s == nil;
}

fn push(s: &stack, top: int) -> _ {
  let s2: &stack;
  s2 = new stack;
  s2.next = s;
  s2.top = top;
  *s = s2;
}

fn contains(s: &stack, x: int) -> int {
  while s != nil {
    if top(s) == x {
      return true;
    }
    s = s.next;
  }
  return false;
}

fn main() -> int {
  let s: &stack;
  s = new stack 1;
  true = 1;
  false = 0;
  push(s, 1);
  push(s, 2);
  push(s, 3);
  push(s, 4);
  while !isEmpty(s) {
    print(pop(s));
    if top(s) == 5 {
      break;
    }
    else {
      continue;
    }
  }
  return 0;
}
",
    );
}

#[test]
fn death_test_missing_rhs() {
    fails_to_parse(
        r"
    fn main() -> _ { return x + ; }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { return x * ; }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { return x / ; }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { return x < ; }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { return * ; }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { return x++ ; }
    ",
    );
}

#[test]
fn death_test_missing_semicolon() {
    fails_to_parse(
        r"
    fn main() -> _ { return }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { x = 3 }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { x = new bar x }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { break }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { continue }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { f(x) }
    ",
    );
}

#[test]
fn death_test_call() {
    fails_to_parse(
        r"
    fn main() -> _ { x = f(x,); }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { x = f(x y); }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { x = f(x ; }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { f(x,); }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { f(x y); }
    ",
    );
    fails_to_parse(
        r"
    fn main() -> _ { f(x ; }
    ",
    );
}

#[test]
fn death_test_missing_brace() {
    fails_to_parse(
        r"
    fn main() -> _ { return; 
    ",
    );
}

#[test]
fn death_test_global_init() {
    fails_to_parse(
        r"
    let foo:int = 42;
    fn main() -> _ { return; }
    ",
    );
}

#[test]
fn death_test_call_in_access_path() {
    fails_to_parse(
        r"
    fn main() -> _ { foo().bar(); }
    ",
    );
}

#[test]
fn death_test_missing_rettyp() {
    fails_to_parse(
        r"
    fn main() { return; }
    ",
    );
}

#[test]
fn death_test_no_fields() {
    fails_to_parse(
        r"
    struct foo {}
    fn main() -> _ { return; }
    ",
    );
}

#[test]
fn death_test_nonfunction_extern() {
    fails_to_parse(
        r"
    extern foo:int;
    fn main() -> _ { return; }
    ",
    );
}

#[test]
fn death_test_empty_function() {
    fails_to_parse(
        r"
    fn main() -> _ { let foo:int; }
    ",
    );
}

#[test]
fn death_test_exp_as_stmt() {
    fails_to_parse(
        r"
    fn main() -> _ { 2+2 }
    ",
    );
}

#[test]
fn death_test_number_too_large() {
    fails_to_parse(
        r"
    fn main() -> _ { let x:int; x = 12345678901234567890; return; }
    ",
    );
}
