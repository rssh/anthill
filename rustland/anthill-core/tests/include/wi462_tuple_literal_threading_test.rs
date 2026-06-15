//! WI-462: TUPLE-LITERAL element threading parity with the Pair-CONSTRUCTOR.
//!
//! `operation split(xs: List) -> Option[(xs.T, List[T = xs.T])] = match xs case nil ->
//! none case cons(h, t) -> some((h, t))` failed: the positional tuple `(h, t)` (lowered
//! to a `Constructor{TupleLiteral}` with `_1`/`_2` fields) did not receive the expected
//! component types, so `h` stayed a free `?_` and the some-branch did not conform — while
//! the Pair-CONSTRUCTOR `pair(h, t)` threaded (its constructor build seeds the expected).
//! The fix pushes the constructor's expected down into a tuple-literal field value and
//! threads each component in `check_tuple_literal_constructor` (unify against the expected
//! component, then walk) — the tuple-literal twin of the constructor's expected-seed. A
//! CONCRETE element that genuinely mismatches the declared component is still rejected.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// The headline: `split` with a positional tuple `(h, t)` threaded through `some(...)`
/// against the declared `Option[(xs.T, List[T = xs.T])]` typechecks.
#[test]
fn tuple_literal_threads_in_some() {
    let ok = r#"
namespace test.wi462.ok
  import anthill.prelude.{List, Option}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons, nil}
  operation split(xs: List) -> Option[T = (xs.T, List[T = xs.T])] =
    match xs
      case nil() -> none
      case cons(h, t) -> some((h, t))
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "the positional tuple (h, t) must thread the expected components like pair(h, t); \
         got: {:?}",
        load_errors(&[ok]),
    );
}

/// PARITY: the Pair-CONSTRUCTOR form (`some(pair(h, t))`) and the tuple-literal form
/// (`some((h, t))`) both typecheck — the threading reaches the tuple literal too.
#[test]
fn tuple_literal_parity_with_pair_constructor() {
    let pair_form = r#"
namespace test.wi462.pairform
  import anthill.prelude.{List, Option, Pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Pair.{pair}
  operation split(xs: List) -> Option[T = Pair[A = xs.T, B = List[T = xs.T]]] =
    match xs
      case nil() -> none
      case cons(h, t) -> some(pair(h, t))
end
"#;
    let tuple_form = r#"
namespace test.wi462.tupleform
  import anthill.prelude.{List, Option}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons, nil}
  operation split(xs: List) -> Option[T = (xs.T, List[T = xs.T])] =
    match xs
      case nil() -> none
      case cons(h, t) -> some((h, t))
end
"#;
    assert!(load_errors(&[pair_form]).is_empty(), "pair form must load (baseline)");
    assert!(
        load_errors(&[tuple_form]).is_empty(),
        "tuple form must reach parity with the pair form; got: {:?}",
        load_errors(&[tuple_form]),
    );
}

/// Soundness: a CONCRETE element that genuinely mismatches the declared component is still
/// rejected — `xs : List[T = Int64]` makes `h : Int64`, so declaring `(String, …)` fails.
#[test]
fn tuple_concrete_wrong_component_rejected() {
    let wrong = r#"
namespace test.wi462.concwrong
  import anthill.prelude.{List, Option, String, Int64}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons, nil}
  operation split(xs: List[T = Int64]) -> Option[T = (String, List[T = Int64])] =
    match xs
      case nil() -> none
      case cons(h, t) -> some((h, t))
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        errs.iter().any(|e| e.contains("Int64") && e.contains("String")),
        "a concrete Int64 head declared as String must be rejected; got: {errs:?}",
    );
}

/// EVAL: `split` runs end-to-end — `split([7, 8, 9])` is `some((7, [8, 9]))`, so the
/// extracted head is `7` (the tuple value round-trips through the threaded type).
#[test]
fn tuple_split_evals() {
    let src = r#"
namespace test.wi462.eval
  import anthill.prelude.{List, Option, Int64}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons, nil}
  operation split(xs: List) -> Option[T = (xs.T, List[T = xs.T])] =
    match xs
      case nil() -> none
      case cons(h, t) -> some((h, t))
  operation head_of() -> Int64 =
    match split([7, 8, 9])
      case some((h, t)) -> h
      case none() -> 0 - 1
end
"#;
    assert!(
        load_errors(&[src]).is_empty(),
        "the split eval fixture must typecheck; got: {:?}",
        load_errors(&[src]),
    );
    let mut interp = crate::common::interp_for(src);
    assert_eq!(
        run_int(&mut interp, "test.wi462.eval.head_of"),
        7,
        "split([7,8,9]) is some((7, [8,9])); the head must be 7",
    );
}
