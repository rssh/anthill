//! WI-445 — NAMED sub-patterns in constructor match patterns now BIND and
//! MATCH. `case Box(v: some(x)) -> x` previously failed with
//! `UnresolvedName(x)` (the named sub-pattern was silently dropped at load:
//! the `pattern_constructor` load handler read only the positional `args` and
//! ignored the parse term's `named_args`), while the positional
//! `case Box(some(x))` bound fine.
//!
//! The fix preserves named sub-patterns through load as a
//! `constructor_pattern.named: List[NamedPattern]` field (the loader does NOT
//! resolve field→position, since the entity may be declared *after* the
//! operation), and resolves each named sub-pattern BY FIELD NAME in the typer
//! (`extend_env_from_pattern`) and eval (`match_constructor_pattern`), where
//! the entity's fields are always registered. Order-independent throughout.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Load stdlib + `src`, returning any load/type errors as strings.
fn load_errors(src: &str) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let s = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&s).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(src).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// Call a nullary op, expect an Int result.
fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// THE ticket shape: a named single-field sub-pattern binds `x` and both arms
/// evaluate. Pre-WI-445 this failed to load with `UnresolvedName(x)`.
#[test]
fn named_single_field_binds_and_evals_both_arms() {
    let src = r#"
namespace wi445.single
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}

  entity Box(v: Option[T = Int64])

  operation get(b: Box) -> Int64 =
    match b
      case Box(v: some(x)) -> x
      case Box(v: none()) -> 0 - 1

  operation mk_some() -> Box = Box(v: some(9))
  operation mk_none() -> Box = Box(v: none())
  operation t_some() -> Int64 = get(mk_some())
  operation t_none() -> Int64 = get(mk_none())
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "named sub-pattern must load and type-check: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi445.single.t_some"), 9, "named some(x) binds x=9");
    assert_eq!(run_int(&mut interp, "wi445.single.t_none"), -1, "named none() arm fires");
}

/// Named sub-patterns bind BY FIELD NAME — robust to order: a pattern listing
/// the fields out of declaration order (`Pair(b: y, a: x)`) binds each to the
/// right field, so `x - y` reads `a - b`.
#[test]
fn named_multifield_reordered_binds_by_name() {
    let src = r#"
namespace wi445.reorder
  import anthill.prelude.Int64

  entity Pair(a: Int64, b: Int64)

  operation diff(p: Pair) -> Int64 =
    match p
      case Pair(b: y, a: x) -> x - y

  operation t() -> Int64 = diff(Pair(a: 10, b: 3))
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "reordered named pattern must load: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi445.reorder.t"), 7, "a - b = 10 - 3 = 7 (bound by name, not order)");
}

/// A MIXED pattern: a leading positional sub-pattern (fills field `a`) plus a
/// named one (`b: y`). Both bind, against a value built either way.
#[test]
fn mixed_positional_and_named_binds() {
    let src = r#"
namespace wi445.mixed
  import anthill.prelude.Int64

  entity Pair(a: Int64, b: Int64)

  operation f(p: Pair) -> Int64 =
    match p
      case Pair(x, b: y) -> x - y

  operation t_named_ctor() -> Int64 = f(Pair(a: 10, b: 3))
  operation t_pos_ctor() -> Int64 = f(Pair(10, 3))
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "mixed positional+named pattern must load: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi445.mixed.t_named_ctor"), 7, "x=a=10, y=b=3");
    assert_eq!(run_int(&mut interp, "wi445.mixed.t_pos_ctor"), 7, "named pattern matches positionally-built value");
}

/// Order independence at LOAD: the entity is declared AFTER the operation that
/// destructures it with a named sub-pattern. The loader can't resolve
/// field→position at that point — which is exactly why resolution is deferred
/// to the typer/eval. Pre-WI-445 (and any normalize-at-load approach) this
/// would fail.
#[test]
fn entity_declared_after_op_still_binds() {
    let src = r#"
namespace wi445.order
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}

  operation get(b: BoxLate) -> Int64 =
    match b
      case BoxLate(v: some(x)) -> x
      case BoxLate(v: none()) -> 0 - 1

  entity BoxLate(v: Option[T = Int64])

  operation t() -> Int64 = get(BoxLate(v: some(4)))
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "named sub-pattern over a later-declared entity must load: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi445.order.t"), 4, "binds despite entity declared after op");
}

/// The positional form is unchanged (no regression) and interoperates with the
/// named form in sibling arms.
#[test]
fn positional_and_named_arms_coexist() {
    let src = r#"
namespace wi445.coexist
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}

  entity Box(v: Option[T = Int64])

  operation get(b: Box) -> Int64 =
    match b
      case Box(some(x)) -> x
      case Box(v: none()) -> 0 - 1

  operation t_pos() -> Int64 = get(Box(v: some(8)))
  operation t_named() -> Int64 = get(Box(v: none()))
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "mixed positional/named arms must load: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi445.coexist.t_pos"), 8, "positional arm still binds");
    assert_eq!(run_int(&mut interp, "wi445.coexist.t_named"), -1, "named none arm fires");
}
