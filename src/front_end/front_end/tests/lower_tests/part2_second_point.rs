// Second point tests.  You need to implement external function calls to pass
// the large tests.

use super::*;

#[test]
fn extern_call_stmt1() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn main() -> int {
  print(414);
  print(42);
  return 0;
}
"
        ),
        Ok((0, vec![414, 42]))
    );
}

#[test]
fn extern_call_stmt2() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern isPythagorean: (int, int, int) -> int;

fn main() -> int {
  isPythagorean(3, 4, 5);
  return 0;
}
"
        ),
        Ok((0, vec![]))
    );
}

#[test]
fn extern_call_expr() {
    assert_eq!(
        lower_and_run(
            r"
extern isPythagorean: (int, int, int) -> int;

fn main() -> int {
  let x: int, y: int, z: int;
  x = isPythagorean(3, 4, 5);
  y = isPythagorean(isPythagorean(3, 4, 5) * 5, 12, 13);
  z = isPythagorean(isPythagorean(3, 4, 5) * 4, 12, 13);
  return x * 100 + y * 10 + z;
}
"
        ),
        Ok(110)
    );
}

#[test]
fn direct_call1() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn f() -> _ {
  print(10);
  return;
}

fn main() -> int {
  f();
  f();
  return 0;
}
"
        ),
        Ok((0, vec![10, 10]))
    );
}

#[test]
fn direct_call2() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn f() -> int {
  print(10);
  return 7;
}

fn main() -> int {
  f();
  f();
  return 0;
}
"
        ),
        Ok((0, vec![10, 10]))
    );
}

#[test]
fn direct_call3() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn f(n: int) -> _ {
  print(n * 2);
  return;
}

fn main() -> int {
  f(5);
  f(8);
  return 0;
}
"
        ),
        Ok((0, vec![10, 16]))
    );
}

#[test]
fn direct_call4() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn f(n: int) -> int {
  print(n * 2);
  return n * 3;
}

fn main() -> int {
  f(5);
  f(8);
  return 0;
}
"
        ),
        Ok((0, vec![10, 16]))
    );
}

#[test]
fn direct_call5() {
    assert_eq!(
        lower_and_run(
            r"
extern print: (int) -> _;

fn f(n: int) -> int {
  return n * 3;
}

fn main() -> int {
  let x: int = f(f(f(5)) - 5);
  return x;
}
"
        ),
        Ok(120)
    );
}

#[test]
fn indirect_call1() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn f() -> _ {
  print(10);
  return;
}

fn main() -> int {
  let g: &() -> _;
  g = f;
  g();
  g();
  return 0;
}
"
        ),
        Ok((0, vec![10, 10]))
    );
}

#[test]
fn indirect_call2() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn f() -> _ {
  print(10);
  return;
}

fn main() -> int {
  let g: &() -> _;
  g = f;
  g();
  g = nil;
  g();
  return 0;
}
"
        ),
        Err("runtime error: tried to call non-function value Ptr(Nil)".into()),
    );
}

#[test]
fn multiple_ret() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn f(n: int) -> int {
  if n > 0 {
    return n;
  }
  return 0;
}

fn main() -> int {
  let x: int = -4;
  while x <= 5 {
    print(f(x));
    x = x + 1;
  }
  return 0;
}
"
        ),
        Ok((0, vec![0, 0, 0, 0, 0, 1, 2, 3, 4, 5]))
    );
}

#[test]
fn shadowing1() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn f(n: int) -> int {
  print(n * 2);
  return n * 3;
}

fn main() -> int {
  let print: &(int) -> int;
  print = f;
  print(4);
  print(15);
  return 0;
}
"
        ),
        Ok((0, vec![8, 30]))
    );
}

#[test]
fn shadowing2() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn f(n: int) -> int {
  return n * 3;
}

fn g(n: int) -> int {
  return n + 8;
}

fn h(n: int) -> int {
  return n / 2;
}

fn main() -> int {
  let f: &(int) -> int;
  f = g;
  print(f(10));
  f = h;
  print(f(10));
  return g(10);
}
"
        ),
        Ok((18, vec![18, 5]))
    );
}

#[test]
fn fib1() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn fib(n: int) -> int {
  let result: int = 1;
  print(n);
  if n > 2 {
    result = fib(n - 1) + fib(n - 2);
  }
  return result;
}

fn main() -> int {
  return fib(6);
}
"
        ),
        Ok((8, vec![6, 5, 4, 3, 2, 1, 2, 3, 2, 1, 4, 3, 2, 1, 2]))
    );
}

#[test]
fn fib2() {
    assert_eq!(
        lower_and_run_capture_output(
            r"
extern print: (int) -> _;

fn fib(n: int) -> int {
  print(n);
  if n <= 2 {
    return 1;
  }
  return fib(n - 1) + fib(n - 2);
}

fn main() -> int {
  return fib(6);
}
"
        ),
        Ok((8, vec![6, 5, 4, 3, 2, 1, 2, 3, 2, 1, 4, 3, 2, 1, 2]))
    );
}
