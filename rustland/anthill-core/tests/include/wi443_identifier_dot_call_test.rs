//! WI-443 — identifier-receiver dot calls: `args.find(...)` where `args` is
//! a local binding (op param / let / lambda / match binder), without the `?`
//! sigil the WI-278/279 value-receiver form required.
//!
//! The scope-blind converter flattens `args.find(...)` into the single
//! dotted functor `"args.find"` (indistinguishable at parse time from a
//! sort-companion call like `Stream.find(...)`). The loader — which knows
//! the scope — re-routes it to the same `Expr::DotApply` the `?x.m(...)`
//! form produces (`load.rs try_identifier_dot_call`), dispatched by the
//! typer on the receiver's sort. Locals are checked first, so a binder
//! shadows a same-named sort; a head naming nothing stays the loud
//! unknown-functor error.
//!
//! WI-443 also moved DotApply arg typing INTO the synthesized call: args are
//! no longer pre-typed hintless at the DotApply frame, so a lambda argument
//! gets the callee's param-type hint (`xs.find(lambda n -> n > 2)` works).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Call a nullary op and expect an Int result.
fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

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

/// THE acceptance shape: `xs.find(is_big)` on a bare List param typechecks
/// and EVALS equal to `find(xs, is_big)` — both the named-op and the inline
/// LAMBDA predicate (the lambda types via the callee's hint inside the
/// synthesized call).
#[test]
fn identifier_dot_call_evals_like_plain_find() {
    let src = r#"
namespace wi443.eval
  import anthill.prelude.{List, Int64, Option, Bool}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Iterable.{find}

  operation is_big(n: Int64) -> Bool = n > 2

  operation unwrap(o: Option[T = Int64]) -> Int64 =
    match o
      case some(x) -> x
      case none() -> 0 - 1

  operation dot_named(xs: List[T = Int64]) -> Option[T = Int64] = xs.find(is_big)
  operation dot_lambda(xs: List[T = Int64]) -> Option[T = Int64] =
    xs.find(lambda n -> n > 2)
  operation plain(xs: List[T = Int64]) -> Option[T = Int64] = find(xs, is_big)

  operation t_named() -> Int64 = unwrap(dot_named([1, 2, 3, 4]))
  operation t_lambda() -> Int64 = unwrap(dot_lambda([1, 2, 3, 4]))
  operation t_plain() -> Int64 = unwrap(plain([1, 2, 3, 4]))
  operation t_none() -> Int64 = unwrap(dot_named([1, 2]))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi443.eval.t_plain"), 3);
    assert_eq!(run_int(&mut interp, "wi443.eval.t_named"), 3);
    assert_eq!(run_int(&mut interp, "wi443.eval.t_lambda"), 3);
    assert_eq!(run_int(&mut interp, "wi443.eval.t_none"), -1);
}

/// The dot form needs NO import: the member resolves by the receiver's sort
/// (provided-spec fallback), not lexical scope — the ergonomic win over the
/// imported short name.
#[test]
fn identifier_dot_call_needs_no_import() {
    let src = r#"
namespace wi443.noimport
  import anthill.prelude.{List, Int64, Option, Bool}
  import anthill.prelude.Option.{some, none}

  operation is_big(n: Int64) -> Bool = n > 2
  operation unwrap(o: Option[T = Int64]) -> Int64 =
    match o
      case some(x) -> x
      case none() -> 0 - 1
  operation t() -> Int64 = unwrap([1, 2, 3, 4].find(is_big))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "literal-receiver dot call must load; got: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi443.noimport.t"), 3);
}

/// A LET-bound local as the dot receiver (the `lookup_local_name` arm of the
/// binder check, vs the op-param arm).
#[test]
fn identifier_dot_call_let_bound_receiver() {
    let src = r#"
namespace wi443.letrecv
  import anthill.prelude.{List, Int64, Option, Bool}
  import anthill.prelude.Option.{some, none}

  operation is_big(n: Int64) -> Bool = n > 2
  operation unwrap(o: Option[T = Int64]) -> Int64 =
    match o
      case some(x) -> x
      case none() -> 0 - 1
  operation t() -> Int64 =
    let ys = [1, 2, 3, 4]
    unwrap(ys.find(is_big))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi443.letrecv.t"), 3);
}

/// SHADOWING pin (the WI-411 hazard in reverse): a param named like a sort
/// in scope prefers the LOCAL binding, like every binder language. A param
/// named `Pair` (the prelude sort is imported) typed `Box`: `Pair.grab()`
/// dot-dispatches `grab(param)` on Box — it is NOT a `anthill.prelude.Pair`
/// companion lookup (which has no `grab` and would fail loudly).
#[test]
fn identifier_dot_param_shadows_sort_companion() {
    let src = r#"
namespace wi443.shadow
  import anthill.prelude.{Int64, Pair}

  sort Box
    import anthill.prelude.{Int64}
    entity box(value: Int64)
    operation grab(b: Box) -> Int64 = 7
  end

  operation use_it(Pair: Box) -> Int64 = Pair.grab()
  operation t() -> Int64 = use_it(box(1))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(
        run_int(&mut interp, "wi443.shadow.t"),
        7,
        "a param named like a sort must shadow the sort companion in dot position",
    );
}

/// A head naming NEITHER a binder nor a sort keeps the existing loud
/// diagnostic — no silent fallback.
#[test]
fn identifier_dot_unknown_head_stays_loud() {
    let src = r#"
namespace wi443.unknown
  import anthill.prelude.{List, Int64, Option, Bool}
  import anthill.prelude.Iterable.{find}
  operation is_big(n: Int64) -> Bool = n > 2
  operation boom(xs: List[T = Int64]) -> Option[T = Int64] = nosuch.find(is_big)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "a dot call on an unknown head must stay a loud load error",
    );
}
