// tests for reaching definitions analysis.

use std::collections::BTreeMap as Map;

use collapse::*;

use crate::middle_end::{
    analysis::{reaching_defs, reaching_defs::Env, AbstractEnv, InstId},
    lir::*,
};

fn get_post(result: &Map<InstId, Env>, block: &BasicBlock) -> Env {
    let bb = &block.id;
    let mut r = result
        .iter()
        .rfind(|((bb_, _), _)| bb_ == bb)
        .unwrap()
        .1
        .clone();
    r.analyze_term(&block.term);
    r
}

/*

- single defs/uses

- control flow

- loops

- re-define

- in-class examples

- hw6

*/

#[test]
fn simple_arith() {
    let code = r#"
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
    "#;

    let expected = r#"
    a -> 2
    b -> 0
    c -> 4
    d -> 2
    e -> Top
    f -> Top
    g -> Top
    h -> Top
    i -> Top
    j -> Top
    k -> Top
    l -> Top
    top -> Top
    "#;

    let program = code.parse::<Program>().unwrap().validate().unwrap();

    let result = reaching_defs::analyze(&program, func_id("test"));
    let get_block = |name| &program.0.functions[&func_id("test")].body[&bb_id(name)];
    for ((bb, n), env) in &result.1 {
        println!("{bb}.{n}:\n{env}");
    }
    collapsed_eq!(
        get_post(&result.1, get_block("entry")).to_string().as_str(),
        expected
    );
}

#[test]
fn simple_calldir1() {
    let code = r#"
    fn test() -> _ {
    let a:int, b:int, c:&int, d:&&int
    entry:
      b = $call_dir foo(d) then exit

    exit:
      $ret
    }

    fn foo(p:&&int) -> int {
    entry:
      $ret 42
    }

    fn main() -> int {
        entry:
          $ret 0
        }
    "#;

    let expected = r#"
    a -> 0
    b -> Top
    c -> 0
    d -> 0
    "#;

    let program = code.parse::<Program>().unwrap().validate().unwrap();

    let result = reaching_defs::analyze(&program, func_id("test"));
    let get_block = |name| &program.0.functions[&func_id("test")].body[&bb_id(name)];
    collapsed_eq!(
        get_post(&result.1, get_block("entry")).to_string().as_str(),
        expected
    );
}

#[test]
fn simple_calldir2() {
    let code = r#"
    fn test() -> _ {
    let a:int, b:&int, c:&int, d:&&int
    entry:
      b = $call_dir foo(d) then exit

    exit:
      c = $load d
      $ret
    }

    fn foo(p:&&int) -> &int {
    let r:&int
    entry:
      r = $load p
      $ret r
    }

    fn main() -> int {
        entry:
          $ret 0
        }
    "#;

    let expected = r#"
    a -> 0
    b -> Top
    c -> Top
    d -> 0
    "#;

    let program = code.parse::<Program>().unwrap().validate().unwrap();

    let result = reaching_defs::analyze(&program, func_id("test"));
    let get_block = |name| &program.0.functions[&func_id("test")].body[&bb_id(name)];
    collapsed_eq!(
        get_post(&result.1, get_block("exit")).to_string().as_str(),
        expected
    );
}

#[test]
fn simple_callext() {
    let code = r#"
    extern foo:(&&int) -> int

    fn test() -> _ {
      let a:int, b:int, c:&int, d:&&int
      entry:
        b = $call_ext foo(d)
        $ret
      }

      fn main() -> int {
        entry:
          $ret 0
        }
    "#;

    let expected = r#"
    a -> 0
    b -> Top
    c -> 0
    d -> 0
    "#;

    let program = code.parse::<Program>().unwrap().validate().unwrap();

    let result = reaching_defs::analyze(&program, func_id("test"));
    let get_block = |name| &program.0.functions[&func_id("test")].body[&bb_id(name)];
    collapsed_eq!(
        get_post(&result.1, get_block("entry")).to_string().as_str(),
        expected
    );
}

#[test]
fn simple_callidr() {
    let code = r#"
    @foo:&(&&int) -> int

    fn test() -> _ {
      let a:int, b:int, c:&int, d:&&int
      entry:
        b = $call_idr @foo(d) then exit
  
      exit:
        $ret
      }
  
      fn foo(p:&&int) -> int {
      entry:
        $ret 42
      }

      fn main() -> int {
        entry:
          $ret 0
        }
    "#;

    let expected = r#"
    a -> 0
    b -> Top
    c -> 0
    d -> 0
    "#;

    let program = code.parse::<Program>().unwrap().validate().unwrap();

    let result = reaching_defs::analyze(&program, func_id("test"));
    let get_block = |name| &program.0.functions[&func_id("test")].body[&bb_id(name)];
    collapsed_eq!(
        get_post(&result.1, get_block("entry")).to_string().as_str(),
        expected
    );
}

#[test]
fn simple_cmp() {
    let code = r#"
    fn test(top:int) -> _ {
      let a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int, i:int, j:int, k:int, l:int, m:int, n:int, o:int, p:int, q:int, r:int, s:int, t:int, u:int, v:&int, w:&int, bot:int
      entry:
        bot = $arith div 2 0
        a = $cmp eq 1 1
        b = $cmp neq 1 1
        c = $cmp lt 2 2
        d = $cmp lte 2 4
        m = $cmp gt 2 4
        n = $cmp gte 3 3
        e = $cmp eq top 1
        f = $cmp neq top 1
        g = $cmp lt 1 top
        h = $cmp lte 1 top
        o = $cmp gt top 4
        p = $cmp gte 3 top
        i = $cmp eq bot 1
        j = $cmp neq bot 1
        k = $cmp lt 1 bot
        l = $cmp lte 1 bot
        q = $cmp gt bot 4
        r = $cmp gte 3 bot
        i = $cmp eq bot top
        j = $cmp neq bot top
        k = $cmp lt top bot
        l = $cmp lte top bot
        s = $cmp gt bot top
        t = $cmp gte top bot
        u = $cmp eq v w
        $ret
    }

    fn main() -> int {
        entry:
          $ret 0
        }
    "#;

    let expected = r#"
    a -> 1
    b -> 0
    c -> 0
    d -> 1
    e -> Top
    f -> Top
    g -> Top
    h -> Top
    m -> 0
    n -> 1
    o -> Top
    p -> Top
    top -> Top
    u -> 1
    v -> 0
    w -> 0
    "#;

    let program = code.parse::<Program>().unwrap().validate().unwrap();

    let result = reaching_defs::analyze(&program, func_id("test"));
    let get_block = |name| &program.0.functions[&func_id("test")].body[&bb_id(name)];
    collapsed_eq!(
        get_post(&result.1, get_block("entry")).to_string().as_str(),
        expected
    );
}

#[test]
fn simple_copy() {
    let code = r#"
    fn test() -> _ {
    let a:int
    entry:
      // set to non-bottom.
      a = $copy 10
      a = $copy 42
      $ret
    }

    fn main() -> int {
        entry:
          $ret 0
        }
    "#;

    let expected = r#"a -> 42"#;

    let program = code.parse::<Program>().unwrap().validate().unwrap();

    let result = reaching_defs::analyze(&program, func_id("test"));
    let get_block = |name| &program.0.functions[&func_id("test")].body[&bb_id(name)];
    collapsed_eq!(
        get_post(&result.1, get_block("entry")).to_string().as_str(),
        expected
    );
}

#[test]
fn simple_load() {
    let code = r#"
    fn test() -> _ {
    let a:int, b:&int
    entry:
      // set to non-bottom.
      a = $copy 10
      a = $load b
      $ret
    }

    fn main() -> int {
        entry:
          $ret 0
        }
    "#;

    let expected = r#"a -> Top b -> 0"#;

    let program = code.parse::<Program>().unwrap().validate().unwrap();

    let result = reaching_defs::analyze(&program, func_id("test"));
    let get_block = |name| &program.0.functions[&func_id("test")].body[&bb_id(name)];
    collapsed_eq!(
        get_post(&result.1, get_block("entry")).to_string().as_str(),
        expected
    );
}

#[test]
fn simple_store() {
    let code = r#"
    fn test() -> _ {
    let a:int, b:&int, c:&int, d:int
    entry:
      // set to non-bottom.
      d = $copy 3
      $store c 0
      $ret
    }

    fn main() -> int {
        entry:
          $ret 0
        }
    "#;

    let expected = r#"
    a -> 0
    b -> 0
    c -> 0
    d -> 3
    "#;

    let program = code.parse::<Program>().unwrap().validate().unwrap();

    let result = reaching_defs::analyze(&program, func_id("test"));
    let get_block = |name| &program.0.functions[&func_id("test")].body[&bb_id(name)];
    collapsed_eq!(
        get_post(&result.1, get_block("entry")).to_string().as_str(),
        expected
    );
}

#[test]
fn control_flow() {
    let code = r#"
    fn test() -> _ {
    let a:int, b:int, c:int, d:int
    entry:
      $jump begin

    begin:
      a = $copy 1
      b = $copy 2
      c = $copy 3
      $branch a tt ff

    tt:
      b = $copy 4
      c = $copy 5
      $jump join

    ff:
      c = $copy 6
      $jump join

    join:
      d = $copy 7
      $jump loop_hdr

    loop_hdr:
      $branch d loop exit

    loop:
      d = $arith add d 1
      $jump loop_hdr

    exit:
      $ret
    }

    fn main() -> int {
        entry:
          $ret 0
        }
    "#;

    let expected_entry = r#"
    a -> 0
    b -> 0
    c -> 0
    d -> 0
    "#;

    let expected_begin = r#"
    a -> 1
    b -> 2
    c -> 3
    d -> 0
    "#;

    let expected_tt = r#"
    a -> 1
    b -> 4
    c -> 5
    d -> 0
    "#;

    let expected_ff = r#"
    a -> 1
    b -> 2
    c -> 6
    d -> 0
    "#;

    let expected_join = r#"
    a -> 1
    b -> Top
    c -> Top
    d -> 7
    "#;

    let expected_loop_hdr = r#"
    a -> 1
    b -> Top
    c -> Top
    d -> Top
    "#;

    let expected_loop = r#"
    a -> 1
    b -> Top
    c -> Top
    d -> Top
    "#;

    let expected_exit = r#"
    a -> 1
    b -> Top
    c -> Top
    d -> Top
    "#;

    let program = code.parse::<Program>().unwrap().validate().unwrap();

    let result = reaching_defs::analyze(&program, func_id("test"));
    let get_block = |name| &program.0.functions[&func_id("test")].body[&bb_id(name)];
    collapsed_eq!(
        get_post(&result.1, get_block("entry")).to_string().as_str(),
        expected_entry
    );
    collapsed_eq!(
        get_post(&result.1, get_block("begin")).to_string().as_str(),
        expected_begin
    );
    collapsed_eq!(
        get_post(&result.1, get_block("tt")).to_string().as_str(),
        expected_tt
    );
    collapsed_eq!(
        get_post(&result.1, get_block("ff")).to_string().as_str(),
        expected_ff
    );
    collapsed_eq!(
        get_post(&result.1, get_block("join")).to_string().as_str(),
        expected_join
    );
    collapsed_eq!(
        get_post(&result.1, get_block("loop")).to_string().as_str(),
        expected_loop
    );
    collapsed_eq!(
        get_post(&result.1, get_block("loop_hdr"))
            .to_string()
            .as_str(),
        expected_loop_hdr
    );
    collapsed_eq!(
        get_post(&result.1, get_block("exit")).to_string().as_str(),
        expected_exit
    );
}
