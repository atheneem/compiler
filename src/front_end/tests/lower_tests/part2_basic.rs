use super::*;

#[test]
fn break1() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int;

  while 1 {
    if x > 2 {
      break;
    }
    x = x + 1;
  }
  
  return x;
}
"
        ),
        Ok(3)
    );
}

#[test]
fn break2() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int;

  while x < 10 {
    while y <= x {
      y = x;
      break;
    }
    x = x + 1;
  }
  
  return y;
}
"
        ),
        Ok(9)
    );
}

#[test]
fn break3() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int;

  while x < 10 {
    while y <= x {
      y = x;
      break;
      y = 0;
    }
    x = x + 1;
  }
  
  return y;
}
"
        ),
        Ok(9)
    );
}

#[test]
fn continue1() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int;

  y = 5;
  while x < 7 {
    x = x + 1;
    if x > 2 * y {
      continue;
    }
    y = y - 1;
  }
  
  return x * 10 + y;
}
"
        ),
        Ok(71)
    );
}

#[test]
fn continue2() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
  let x: int, y: int;

  while x < 10 {
    while y < x {
      y = x;
      continue;
      y = y + 1;
    }
    x = x + 1;
  }
  
  return y;
}
"
        ),
        Ok(9)
    );
}

#[test]
fn and1() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    let x: int = 3, y: int, acc: int;
    acc = x and y;
    y = 5;
    acc = acc * 10 + (x and y);
    acc = acc * 10 + (y and x);
    x = 0;
    acc = acc * 10 + (x and y);
    return acc;
}
"
        ),
        Ok(530)
    );
}

#[test]
fn or1() {
    assert_eq!(
        lower_and_run(
            r"
fn main() -> int {
    let x: int = 3, y: int, acc: int;
    acc = x or y;
    y = 5;
    acc = acc * 10 + (x or y);
    acc = acc * 10 + (y or x);
    x = 0;
    acc = acc * 10 + (x or y);
    acc = acc * 10 + (y or x);
    y = 0;
    acc = acc * 10 + (x or y);
    return acc;
}
"
        ),
        Ok(335550)
    );
}

// todo: and & or inside other expressions

// these tests check the `and` operator
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
  
  while tortoise != nil and hare != nil and tortoise != hare {
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
  
  while tortoise != nil and hare != nil and tortoise != hare {
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
