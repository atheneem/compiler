// Basic tests for part 1.  You need to pass these to get 1/2 for part 1.

use super::*;

#[test]
fn minimal_program() {
    assert_eq!(lower_and_run("fn main() -> int { return 0; }"), Ok(0));
    assert_eq!(lower_and_run("fn main() -> int { return 7; }"), Ok(7));
}

#[test]
fn assign_basic() {
    assert_eq!(
        lower_and_run("fn main() -> int { let x: int; x = 2; return x; }"),
        Ok(2)
    );
    assert_eq!(
        lower_and_run("fn main() -> int { let x: int, y: int; x = 4; y = x; return y; }"),
        Ok(4)
    );
}

#[test]
fn assign_compare_nil() {
    assert_eq!(
        lower_and_run("fn main() -> int { let x: &int; x = nil; return x == nil; }"),
        Ok(1)
    );
}

#[test]
fn arith0() {
    assert_eq!(
        lower_and_run(
            r"fn main() -> int {
  return (-5);
}"
        ),
        Ok(-5)
    );
    assert_eq!(
        lower_and_run(
            r"fn main() -> int {
  return -(-5);
}"
        ),
        Ok(5)
    );
}

#[test]
fn arith1() {
    assert_eq!(
        lower_and_run(
            r"fn main() -> int {
  return 2 + 2;
}"
        ),
        Ok(4)
    );
}

#[test]
fn arith2() {
    assert_eq!(
        lower_and_run(
            r"fn main() -> int {
  return 5 * (3 + 4) - 2 / 6;
}"
        ),
        Ok(35)
    );
}

#[test]
fn arith3() {
    assert_eq!(
        lower_and_run(
            r"fn main() -> int {
  return 5 * (3 + 4) / (2 / 6);
}"
        ),
        Err("runtime error: division by zero".into())
    );
}

#[test]
fn assign_and_arith() {
    assert_eq!(
        lower_and_run(
            r"fn main() -> int {
  let x: int, y: int;
  x = 2;
  y = 3;
  return (20 - 2 * x) + y * 4 / (-5);
}"
        ),
        Ok(14)
    );
}

#[test]
fn compare1() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    return (1 > 0) + (1 < 0) + (1 == 0) + (1 != 0) + (1 >= 0) + (1 <= 0);
}
"
        ),
        Ok(3)
    );
}

#[test]
fn compare2() {
    assert_eq!(
        lower_and_run(
            r"
fn foo() -> _ { return; }

fn main() -> int {
    let p: &() -> _, q: &() -> _, x: int, r: &int;
    p = foo;
    r = new int;
    return (x > -2) + 10 * (
        (p == q) + 10 * (
            (q < p) + 10 * (r == nil)
    ));
}
"
        ),
        Ok(101)
    );
}

#[test]
fn not1() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    return !0;
}
"
        ),
        Ok(1)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    return !1;
}
"
        ),
        Ok(0)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    return !90;
}
"
        ),
        Ok(0)
    );
}

#[test]
fn not2() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    return (1 > 0) + !(1 < 0) + !(1 == 0) + (1 != 0) + (1 >= 0) + !(1 <= 0) + !99;
}
"
        ),
        Ok(6)
    );
}

#[test]
fn not3() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    return !!7;
}
"
        ),
        Ok(1)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    return !(-1);
}
"
        ),
        Ok(0)
    );
}

#[test]
fn new_deref() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    let x: &int;
    x = new int;
    return *x;
}
"
        ),
        Ok(0)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    let x: &int;
    x = new int;
    *x = 1;
    return *x;
}
"
        ),
        Ok(1)
    );
}

#[test]
fn new_array() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    let x: &int;
    x = new int 5;
    return x[3];
}
"
        ),
        Ok(0)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    let x: &int;
    x = new int 5;
    return x[9];
}
"
        ),
        Err("runtime error: out-of-bounds access".into())
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    let x: &int;
    x = new int 5;
    x[3] = 1;
    x[4] = 2;
    return x[3] + x[4];
}
"
        ),
        Ok(3)
    );
}

#[test]
fn new_field() {
    assert_eq!(
        lower_and_run(
            r"
struct foo {
  f1: int,
  f2: &foo
}

fn main() -> int {
    let x: &foo;
    x = new foo;
    return x.f2 == nil;
}
"
        ),
        Ok(1)
    );
    assert_eq!(
        lower_and_run(
            r"
struct foo {
  f1: int,
  f2: &foo
}

fn main() -> int {
    let x: &foo;
    x = new foo;
    x.f1 = 7;
    return x.f1;
}
"
        ),
        Ok(7)
    );
}
