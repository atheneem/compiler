use super::*;

#[test]
fn nested_ptr() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    let x: &&int, y: int;

    x = new &int;
    *x = new int;
    **x = 7;

    y = (x != nil) + **x;
    **x = **x * y;
    return **x;
}
"
        ),
        Ok(56)
    );
}

#[test]
fn nested_field() {
    assert_eq!(
        lower_and_run(
            r"
struct foo {
  f1: int,
  f2: &foo
}

fn main() -> int {
    let x: &foo, y: &foo;
    x = new foo;
    x.f1 = 7;
    x.f2 = new foo;
    x.f2.f2 = new foo;
    y = x.f2;
    y.f2.f1 = 4;
    y.f1 = 5;
    x.f1 = 3;
    return 1000 + x.f1 + x.f2.f1 * 10 + x.f2.f2.f1 * 100;
}
"
        ),
        Ok(1453)
    );
}

#[test]
fn let_elim() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int = 3, y: int;
  return x * 10 + y;
}
"
        ),
        Ok(30)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int = 3, y: int = x - z, z: int = 4;
  return x * 100 + y * 10 + z;
}
"
        ),
        Ok(334)
    );
}

#[test]
fn if1() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  if 1 { x = 3; }
  return x;
}
"
        ),
        Ok(3)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  x = 2;
  if 0 { x = 3; }
  return x;
}
"
        ),
        Ok(2)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  x = 4;
  if 1 { }
  return x;
}
"
        ),
        Ok(4)
    );
}

#[test]
fn if2() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  if 1 { x = 3; } else { x = 4; }
  return x;
}
"
        ),
        Ok(3)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  x = 2;
  if 0 { x = 3; } else { x = 4; }
  return x;
}
"
        ),
        Ok(4)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  x = 2;
  if 0 { x = 3; } else { x = 4; }
  x = 5;
  return x;
}
"
        ),
        Ok(5)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  x = 2;
  if 1 { x = 3; } else { x = 4; }
  x = 5;
  return x;
}
"
        ),
        Ok(5)
    );
}

#[test]
fn if3() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  if 3 { x = 3; }
  return x;
}
"
        ),
        Ok(3)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  if -1 { x = 3; } else { x = 4; }
  return x;
}
"
        ),
        Ok(3)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  x = 2;
  if 19 { x = 3; } else { x = 4; }
  x = 5;
  return x;
}
"
        ),
        Ok(5)
    );
}

#[test]
fn if4() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int;
  if x == 0 {
    if y == 0 {
      y = x + 5;
    } else {
      y = 4;
    }
    x = x + 1;
  } else {
    if y == 0 {
      x = 9;
    } else {
      y = 3;
    }
    y = y - 1;
    x = x - y;
  }
  return x * 10 + y;
}
"
        ),
        Ok(15)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int;
  if x > 0 {
    if y == 0 {
      y = x + 5;
    } else {
      y = 4;
    }
    x = x + 1;
  } else {
    if y <= 0 {
      x = 9;
    } else {
      y = 3;
    }
    y = y - 1;
    x = x - y;
  }
  return x * 10 + y;
}
"
        ),
        Ok(99)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int;
  if x >= 0 {
    if y < 0 {
      y = x + 5;
    } else {
      y = 4;
    }
    x = x + 1;
  } else {
    if y == 0 {
      x = 9;
    } else {
      y = 3;
    }
    y = y - 1;
    x = x - y;
  }
  return x * 10 + y;
}
"
        ),
        Ok(14)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int;
  if x > 0 {
    if y < 0 {
      y = x + 5;
    } else {
      y = 4;
    }
    x = x + 1;
  } else {
    if y < 0 {
      x = 9;
    } else {
      y = 3;
    }
    y = y - 1;
    x = x - y;
  }
  return x * 10 + y;
}
"
        ),
        Ok(-18)
    );
}

// todo: while
#[test]
fn while1() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  x = 2;
  while 0 { }
  return x;
}
"
        ),
        Ok(2)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  x = 2;
  while 0 { x = 3; }
  return x;
}
"
        ),
        Ok(2)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  x = 2;
  while x - 3 { x = 3; }
  return x;
}
"
        ),
        Ok(3)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int;
  x = 2;
  while x - 3 { x = 3; }
  x = 5;
  return x;
}
"
        ),
        Ok(5)
    );
}

#[test]
fn while2() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int, sum: int;
  x = 10;
  while y < x {
    y = y + 1;
    sum = sum + y;
  }
  return sum;
}
"
        ),
        Ok(55)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int, sum: int;
  x = 10;
  sum = 1;
  while y < x {
    y = y + 1;
    sum = sum * y;
  }
  return sum;
}
"
        ),
        Ok(3628800)
    );
}

#[test]
fn while3() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int;
  x = 2;
  while x - 9 {
    x = 3;
    y = 10;
    while x < y {
      x = x + 1;
      y = y - 1;
    }
    x = x + 2;
    y = y + 5;
  }
  x = x + 1;
  return x * y;
}
"
        ),
        Ok(110)
    );
}

#[test]
fn global() {
    assert_eq!(
        lower_and_run(
            r"
let y: int;

fn main() -> int {
  let x: int;
  x = 2;
  y = 10;
  return x * y;
}
"
        ),
        Ok(20)
    );
}

#[test]
fn linked_list() {
    assert_eq!(
        lower_and_run(
            r"
struct list {
  value: int,
  next: &list
}

fn main() -> int {
  let n: &list, m: &list;
  let i: int = 3;

  n = new list;
  m = n;
  while i > 0 {
    n.next = new list;
    n.value = i;
    n = n.next;
    i = i - 1;
  }

  while m != nil {
    i = 10 * i + m.value;
    m = m.next;
  }

  return i;
}
"
        ),
        Ok(3210)
    );
}

#[test]
fn tortoise_and_hare() {
    assert_eq!(
        lower_and_run(
            r"
struct list {
  value: int,
  next: &list
}

fn main() -> int {
  let n: &list, m: &list, p: &list;
  let i: int = 10;
  let tortoise: &list, hare: &list;

  n = new list;
  m = n;
  while i > 0 {
    n.next = new list;
    n.value = i;
    p = n;
    n = n.next;
    i = i - 1;
  }

  tortoise = m;
  hare = m.next;
  
  while (tortoise != nil) * (hare != nil) * (tortoise != hare) {
    tortoise = tortoise.next;
    hare = hare.next;
    if hare != nil {
      hare = hare.next;
    }
  }

  return tortoise == hare;
}
"
        ),
        Ok(0)
    );
}

#[test]
fn tortoise_and_hare2() {
    assert_eq!(
        lower_and_run(
            r"
struct list {
  value: int,
  next: &list
}

fn main() -> int {
  let n: &list, m: &list, p: &list;
  let i: int = 10;
  let tortoise: &list, hare: &list;

  n = new list;
  m = n;
  while i > 0 {
    n.next = new list;
    n.value = i;
    p = n;
    n = n.next;
    i = i - 1;
  }

  p.next = m.next.next.next.next.next;
  tortoise = m;
  hare = m.next;
  
  while (tortoise != nil) * (hare != nil) * (tortoise != hare) {
    tortoise = tortoise.next;
    hare = hare.next;
    if hare != nil {
      hare = hare.next;
    }
  }

  return tortoise == hare;
}
"
        ),
        Ok(1)
    );
}

#[test]
fn complex1() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int = 2;
  if 0 { x = 3; } else { x = x + 7; }
  return x;
}
"
        ),
        Ok(9)
    );
}

#[test]
fn very_nested_ptr() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    let x: &&&&&&&&&&&&&&&&&&&&&&int, y: int;

    x = new &&&&&&&&&&&&&&&&&&&&&int;
    *x = new &&&&&&&&&&&&&&&&&&&&int;
    **x = new &&&&&&&&&&&&&&&&&&&int;
    ***x = new &&&&&&&&&&&&&&&&&&int;
    ****x = new &&&&&&&&&&&&&&&&&int;
    *****x = new &&&&&&&&&&&&&&&&int;
    ******x = new &&&&&&&&&&&&&&&int;
    *******x = new &&&&&&&&&&&&&&int;
    ********x = new &&&&&&&&&&&&&int;
    *********x = new &&&&&&&&&&&&int;
    **********x = new &&&&&&&&&&&int;
    ***********x = new &&&&&&&&&&int;
    ************x = new &&&&&&&&&int;
    *************x = new &&&&&&&&int;
    **************x = new &&&&&&&int;
    ***************x = new &&&&&&int;
    ****************x = new &&&&&int;
    *****************x = new &&&&int;
    ******************x = new &&&int;
    *******************x = new &&int;
    ********************x = new &int;
    *********************x = new int;
    **********************x = 7;

    y = **********************x;

    y = 10 * y + (x != nil);
    y = 10 * y + (*x == nil);
    y = 10 * y + (**x == nil);
    y = 10 * y + (***x != nil);
    y = 10 * y + (****x == nil);
    y = 10 * y + (*****x != nil);
    y = 10 * y + (*******************x == nil);
    y = 10 * y + (********************x != nil);
    
    return y;
}
"
        ),
        Ok(710010101)
    );
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    let x: &&&&&&&&&&&&&&&&&&&&&&int, y: int;

    x = new &&&&&&&&&&&&&&&&&&&&&int;
    *x = new &&&&&&&&&&&&&&&&&&&&int;
    **x = new &&&&&&&&&&&&&&&&&&&int;
    ***x = new &&&&&&&&&&&&&&&&&&int;
    ****x = new &&&&&&&&&&&&&&&&&int;
    *****x = new &&&&&&&&&&&&&&&&int;
    ******x = new &&&&&&&&&&&&&&&int;
    *******x = new &&&&&&&&&&&&&&int;
    ********x = new &&&&&&&&&&&&&int;
    *********x = new &&&&&&&&&&&&int;
    **********x = new &&&&&&&&&&&int;
    ***********x = new &&&&&&&&&&int;
    ************x = new &&&&&&&&&int;
    *************x = new &&&&&&&&int;
    **************x = new &&&&&&&int;
    ****************x = new &&&&&int;
    *****************x = new &&&&int;
    ******************x = new &&&int;
    *******************x = new &&int;
    ********************x = new &int;
    *********************x = new int;
    **********************x = 7;

    y = **********************x;

    y = 10 * y + (x != nil);
    y = 10 * y + (*x == nil);
    y = 10 * y + (**x == nil);
    y = 10 * y + (***x != nil);
    y = 10 * y + (****x == nil);
    y = 10 * y + (*****x != nil);
    y = 10 * y + (*******************x == nil);
    y = 10 * y + (********************x != nil);
    
    return y;
}
"
        ),
        Err("runtime error: main: tried to dereference a null pointer".into())
    );
}
