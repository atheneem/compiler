// Basic tests for the inlining pass.

use crate::{
    commons::Valid,
    middle_end::{lir::*, optimization::inlining::*},
};
use std::collections::{BTreeMap as Map, BTreeSet as Set};

// SECTION: NameGenerator tests

#[test]
fn name_generator() {
    let code = r#"
    fn main() -> int {
    entry:
      $ret 0
    }

    fn test(bb.foo.x.0:int, bb.foo.x.1:int) -> _ {
      let bb.foo.x.3:&int, bb.foo.x.4:&(int) -> int
      entry:
        $jump bb.foo.bb2.1
      bb.foo.bb2.1:
        $jump bb.foo.bb2.3
      bb.foo.bb2.3:
        $ret
    }
    "#;

    let program: Program = code.parse().unwrap();
    program.check_valid().unwrap();

    let main = &program.functions[&func_id("test")];
    let mut name_generator = NameGenerator::new(main);
    println!("{:#?}", name_generator.declared_vars);

    let int = int_ty();
    let intp = ptr_ty(int.clone());
    let scope = Some(main.id.clone());
    let var1 = var_id("x", int.clone(), Some(func_id("foo")));
    let var2 = var_id("x", intp.clone(), Some(func_id("foo")));
    let bb = bb_id("bb");

    let int_vars = (0..5)
        .map(|_| name_generator.mangle_var(&bb, &var1))
        .collect::<Vec<VarId>>();

    assert_eq!(
        int_vars,
        vec![
            var_id("bb.foo.x.2", int.clone(), scope.clone()),
            var_id("bb.foo.x.5", int.clone(), scope.clone()),
            var_id("bb.foo.x.6", int.clone(), scope.clone()),
            var_id("bb.foo.x.7", int.clone(), scope.clone()),
            var_id("bb.foo.x.8", int.clone(), scope.clone()),
        ]
    );

    let intp_vars = (0..5)
        .map(|_| name_generator.mangle_var(&bb, &var2))
        .collect::<Vec<VarId>>();

    assert_eq!(
        intp_vars,
        vec![
            var_id("bb.foo.x.9", intp.clone(), scope.clone()),
            var_id("bb.foo.x.10", intp.clone(), scope.clone()),
            var_id("bb.foo.x.11", intp.clone(), scope.clone()),
            var_id("bb.foo.x.12", intp.clone(), scope.clone()),
            var_id("bb.foo.x.13", intp.clone(), scope.clone()),
        ]
    );

    let bb_ids = (0..5)
        .map(|_| name_generator.mangle_bb(&bb, &func_id("foo"), &bb_id("bb2")))
        .collect::<Vec<BbId>>();

    assert_eq!(
        bb_ids,
        vec![
            bb_id("bb.foo.bb2.2"),
            bb_id("bb.foo.bb2.4"),
            bb_id("bb.foo.bb2.5"),
            bb_id("bb.foo.bb2.6"),
            bb_id("bb.foo.bb2.7"),
        ]
    );
}

// SECTION: End-to-end inlining tests

#[test]
fn inline_no_calls() {
    let code = r#"
    fn f(x:int) -> int {
      entry:
        $ret x
    }

    fn main() -> int {
      let x:int
      entry:
        $ret 0
    }
    "#;

    let program: Program = code.parse().unwrap();
    let p = program.clone().validate().unwrap();

    assert_eq!(inline_leaf_functions(p).0.to_string(), program.to_string());
}

#[test]
fn dont_rename_globals() {
    let code = r#"
    @foo:int

    fn f() -> int {
      let x: int
      entry:
        x = $arith mul @foo 2
        $ret x
    }

    fn main() -> int {
      let x:int, foo:int
      entry:
        x = $call_dir f() then exit
      exit:
        $ret x
    }
    "#;

    let inlined = r#"
    @foo:int

    fn f() -> int {
    let x: int
    entry:
      x = $arith mul @foo 2
      $ret x
    }

    fn main() -> int {
    let foo:int, x:int, entry.f.x.1:int
    entry.f.entry.1:
      entry.f.x.1 = $arith mul @foo 2
      x = $copy entry.f.x.1
      $jump exit

    entry:

      $jump entry.f.entry.1

    exit:

      $ret x
    }
    "#;

    let program: Program = code.parse().unwrap();

    let inlined_program: Program = inlined.parse().unwrap();
    inlined_program.check_valid().unwrap();

    assert_eq!(
        inline_call_sites(
            &program,
            &Map::from([(func_id("main"), Set::from([bb_id("entry")]))])
        )
        .to_string(),
        inlined_program.to_string(),
    );
}

#[test]
fn inline_direct_calls() {
    let code = r#"
    @unknown:&() -> _
    fn f(a:int) -> int {
      let x: int
      entry:
        x = $arith mul a 2
        $ret x
    }

    fn g(a:int) -> _ {
      entry:
        $ret
    }

    fn h() -> int {
      let x: int
      entry:
        $call_idr @unknown() then exit
      exit:
        x = $copy 3
        $ret x
    }

    fn main() -> int {
      let x:int, y:int
      entry:
        x = $call_dir f(3) then bb1
      bb1:
        $call_dir g(x) then bb2
      bb2:
        y = $call_dir h() then exit
      exit:
        $ret x
    }
    "#;

    let inlined = r#"
    @unknown:&() -> _
    fn f(a:int) -> int {
      let x: int
      entry:
        x = $arith mul a 2
        $ret x
    }

    fn g(a:int) -> _ {
      entry:
        $ret
    }

    fn h() -> int {
      let x: int
      entry:
        $call_idr @unknown() then exit
      exit:
        x = $copy 3
        $ret x
    }

    fn main() -> int {
    let x:int, entry.f.a.1:int, entry.f.x.1:int, bb1.g.a.1:int, y:int
    bb1.g.entry.1:
      bb1.g.a.1 = $copy x
      $jump bb2

    entry.f.entry.1:
      entry.f.a.1 = $copy 3
      entry.f.x.1 = $arith mul entry.f.a.1 2
      x = $copy entry.f.x.1
      $jump bb1

    bb1:

      $jump bb1.g.entry.1

    bb2:

      y = $call_dir h() then exit

    entry:

      $jump entry.f.entry.1

    exit:

      $ret x
    }
    "#;

    let program: Program = code.parse().unwrap();
    let p = program.clone().validate().unwrap();

    let inlined_program: Program = inlined.parse().unwrap();
    inlined_program.check_valid().unwrap();

    assert_eq!(
        inline_leaf_functions(p).0.to_string(),
        inlined_program.to_string()
    );
}

#[test]
fn inline_only_leaf_calls() {
    let code = r#"
    fn wont_be_inlined(a:int) -> int {
      let x: int
      entry:
        x = $call_dir will_be_inlined(a) then exit
      exit:
        $ret x
    }

    fn will_be_inlined(a:int) -> int {
      entry:
        a = $arith add a 1
        $ret a
    }

    fn main() -> int {
      let x:int
      entry:
        x = $call_dir will_be_inlined(3) then bb1
      bb1:
        x = $call_dir wont_be_inlined(x) then exit
      exit:
        $ret x
    }
    "#;

    let inlined = r#"
    fn main() -> int {
    let entry.will_be_inlined.a.1:int, x:int
    bb1:

      x = $call_dir wont_be_inlined(x) then exit

    entry:

      $jump entry.will_be_inlined.entry.1

    entry.will_be_inlined.entry.1:
      entry.will_be_inlined.a.1 = $copy 3
      entry.will_be_inlined.a.1 = $arith add entry.will_be_inlined.a.1 1
      x = $copy entry.will_be_inlined.a.1
      $jump bb1

    exit:

      $ret x
    }

    fn will_be_inlined(a:int) -> int {

    entry:
      a = $arith add a 1
      $ret a
    }

    fn wont_be_inlined(a:int) -> int {
    let entry.will_be_inlined.a.1:int, x:int
    entry:

      $jump entry.will_be_inlined.entry.1

    entry.will_be_inlined.entry.1:
      entry.will_be_inlined.a.1 = $copy a
      entry.will_be_inlined.a.1 = $arith add entry.will_be_inlined.a.1 1
      x = $copy entry.will_be_inlined.a.1
      $jump exit

    exit:

      $ret x
    }
    "#;

    let program: Program = code.parse().unwrap();
    let p = program.clone().validate().unwrap();

    let inlined_program: Program = inlined.parse().unwrap();
    inlined_program.check_valid().unwrap();

    assert_eq!(
        inline_leaf_functions(p).0.to_string(),
        inlined_program.to_string(),
    );
}

#[test]
fn rewrite_vars_in_all_insts() {
    let code = r#"
    struct foo {
      f1: int
    }

    @unknown:&(int) -> int

    extern foo:(int, &int, int) -> int

    fn f(a:int) -> int {
      let x: int, y: &int, z: &foo, x.1: int, x.2: int
      entry:
        a = $arith add a 1
        x = $copy a
        x = $cmp lt x 3
        a = $copy x
        z = $alloc 10 [_1]
        z = $gep z 2
        y = $gfp z f1
        $store y a
        x = $load y
        x = $phi(x.1, x.2)
        x = $call_ext foo(x, y, a)
        $branch x bb1 bb2
      bb1:
        $jump exit
      bb2:
        x = $copy 0
        $jump exit
      exit:
        $ret x
    }

    fn main() -> int {
      let x:int
      entry:
        x = $call_dir f(x) then exit
      exit:
        $ret x
    }
    "#;

    let inlined = r#"
    struct foo {
      f1:int
    }

    @unknown:&(int) -> int

    extern foo:(int,&int,int) -> int

    fn f(a:int) -> int {
    let x:int, x.1:int, x.2:int, y:&int, z:&foo
    bb1:

      $jump exit

    bb2:
      x = $copy 0
      $jump exit

    entry:
      a = $arith add a 1
      x = $copy a
      x = $cmp lt x 3
      a = $copy x
      z = $alloc 10 [_1]
      z = $gep z 2
      y = $gfp z f1
      $store y a
      x = $load y
      x = $phi(x.1, x.2)
      x = $call_ext foo(x, y, a)
      $branch x bb1 bb2

    exit:

      $ret x
    }

    fn main() -> int {
    let entry.f.a.1:int, entry.f.x.1:int, entry.f.x.1.1:int, entry.f.x.2.1:int, entry.f.y.1:&int, entry.f.z.1:&foo, x:int
    entry:

      $jump entry.f.entry.1

    entry.f.bb1.1:

      $jump entry.f.exit.1

    entry.f.bb2.1:
      entry.f.x.1 = $copy 0
      $jump entry.f.exit.1

    entry.f.entry.1:
      entry.f.a.1 = $copy x
      entry.f.a.1 = $arith add entry.f.a.1 1
      entry.f.x.1 = $copy entry.f.a.1
      entry.f.x.1 = $cmp lt entry.f.x.1 3
      entry.f.a.1 = $copy entry.f.x.1
      entry.f.z.1 = $alloc 10 [entry.._1.1]
      entry.f.z.1 = $gep entry.f.z.1 2
      entry.f.y.1 = $gfp entry.f.z.1 f1
      $store entry.f.y.1 entry.f.a.1
      entry.f.x.1 = $load entry.f.y.1
      entry.f.x.1 = $phi(entry.f.x.1.1, entry.f.x.2.1)
      entry.f.x.1 = $call_ext foo(entry.f.x.1, entry.f.y.1, entry.f.a.1)
      $branch entry.f.x.1 entry.f.bb1.1 entry.f.bb2.1

    entry.f.exit.1:
      x = $copy entry.f.x.1
      $jump exit

    exit:

      $ret x
    }
    "#;

    let program: Program = code.parse().unwrap();

    let inlined_program: Program = inlined.parse().unwrap();
    inlined_program.check_valid().unwrap();

    assert_eq!(
        inline_call_sites(
            &program,
            &Map::from([(func_id("main"), Set::from([bb_id("entry")])),])
        )
        .to_string(),
        inlined_program.to_string(),
    );
}

#[test]
fn multiple_calls_to_same_func() {
    let code = r#"
    fn f(a:int) -> int {
      let x: int
      entry:
        x = $arith mul a 2
        $ret x
    }

    fn main() -> int {
      let x:int, y:int
      entry:
        x = $call_dir f(3) then bb1
      bb1:
        x = $call_dir f(x) then exit
      exit:
        $ret x
    }
    "#;

    let inlined = r#"
    fn f(a:int) -> int {
    let x:int
    entry:
      x = $arith mul a 2
      $ret x
    }

    fn main() -> int {
    let bb1.f.a.1:int, bb1.f.x.1:int, entry.f.a.1:int, entry.f.x.1:int, x:int, y:int
    bb1:

      $jump bb1.f.entry.1

    bb1.f.entry.1:
      bb1.f.a.1 = $copy x
      bb1.f.x.1 = $arith mul bb1.f.a.1 2
      x = $copy bb1.f.x.1
      $jump exit

    entry:

      $jump entry.f.entry.1

    entry.f.entry.1:
      entry.f.a.1 = $copy 3
      entry.f.x.1 = $arith mul entry.f.a.1 2
      x = $copy entry.f.x.1
      $jump bb1

    exit:

      $ret x
    }
    "#;

    let program: Program = code.parse().unwrap();
    program.check_valid().unwrap();

    let inlined_program: Program = inlined.parse().unwrap();
    inlined_program.check_valid().unwrap();

    assert_eq!(
        inline_call_sites(
            &program,
            &Map::from([(func_id("main"), Set::from([bb_id("entry"), bb_id("bb1"),])),])
        )
        .to_string(),
        inlined_program.to_string(),
    );
}
