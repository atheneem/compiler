// Basic parser tests.  Note that spaces and new lines in test inputs matter.

use super::*;

#[test]
fn func() {
    parse_and_prettify(
        r"fn main() -> _ {
  return;
}
",
    );
    parse_and_prettify(
        r"fn foo(x: int, y: bar) -> &int {
  return;
}
",
    );
}

#[test]
fn glob() {
    parse_and_prettify("let x: int;\n\n");
    prettifies_to("let x: int, y: &foo;", "let x: int;\nlet y: &foo;\n\n");
}

#[test]
fn typedef() {
    parse_and_prettify(
        r"struct foo {
  f1: int
}

",
    );
    parse_and_prettify(
        r"struct foo {
  bar: foo,
  baz: &bar,
  bat: &&int
}

",
    );
}

#[test]
fn extern_fn() {
    parse_and_prettify("extern foo: () -> int;\n\n");
    parse_and_prettify("extern foo: (int) -> _;\n\n");
}

// todo: different stmts: loop, cond, assign, call, break, continue, return
#[test]
fn loop_test() {
    parse_and_prettify(
        r"fn main() -> _ {
  while x {

  }
}
",
    );
    parse_and_prettify(
        r"fn main() -> _ {
  while x {
    while y {
      while z {

      }
    }
  }
}
",
    );
}

#[test]
fn cond() {
    prettifies_to(
        r"fn main() -> _ {
  if x {

  } else {

  }
}
",
        r"fn main() -> _ {
  if x {

  }
}
",
    );
    parse_and_prettify(
        r"fn main() -> _ {
  if x {

  }
}
",
    );
    parse_and_prettify(
        r"fn main() -> _ {
  if x {
    if y {

    }
  }
  else {
    if z {

    }
    else {
      if t {

      }
    }
  }
}
",
    );
}

#[test]
fn assign() {
    parse_and_prettify(
        r"fn main() -> _ {
  x = y;
  x.foo = new bar;
  x = new baz len;
  x = new &&(foo,bar,&baz,(quux,int) -> _) -> int length;
  *x = y;
  *x.foo[bar] = y;
}
",
    );
}

#[test]
fn call() {
    parse_and_prettify(
        r"fn main() -> _ {
  f();
  g(x);
  h(x, y);
  i(x, y, z, t, u, v, w);
  x.f();
  *p(x);
  x[a](x, y);
}
",
    );
}

#[test]
fn break_and_continue() {
    parse_and_prettify(
        r"fn main() -> _ {
  break;
  continue;
}
",
    );
}

#[test]
fn let_test() {
    prettifies_to(
        r"fn main() -> _ {
  let x: int;
  let y: &int = z;
  let a: (int) -> foo = bar, b: &&() -> int = baz, c: foo;

  return;
}
",
        r"fn main() -> _ {
  let x: int, y: &int = z, a: (int) -> foo = bar, b: &&() -> int = baz, c: foo;
  return;
}
",
    );
}

// Programs that should fail

#[test]
fn death_empty_program() {
    fails_to_parse("");
}

#[test]
fn death_glob_init() {
    fails_to_parse("let x: int = 0;");
}

#[test]
fn death_missing_let() {
    fails_to_parse("fn main() -> _ { x: int = 5; return; }");
    fails_to_parse("fn main() -> _ { x: int; return; }");
}

#[test]
fn death_missing_type() {
    fails_to_parse("fn main() -> _ { let x = 5; return; }");
}

#[test]
fn death_empty_fn() {
    fails_to_parse("fn main() -> _ { }");
}

#[test]
fn death_missing_semi() {
    fails_to_parse("fn main() -> _ { return }");
}

#[test]
fn death_missing_brace() {
    fails_to_parse("fn main() -> _ { return;");
}

#[test]
fn death_missing_arg_paren() {
    fails_to_parse("fn main -> _ { return; }");
}
