//! WI-605: a bare `pattern -> body` in an operation-body expression position
//! is NOT a lambda — the infix `->` desugars (pratt) to an arrow-type term,
//! so its left-hand binder names used to load as unresolved value refs and
//! the typer cascaded a misleading `UnresolvedName` per binder ("type
//! mismatch in x.name: expected resolved name, got unresolved"). A lambda
//! requires the `lambda` keyword (kernel-language.md §Lambda, proposal 018 —
//! deliberate: the keyword keeps call-argument commas unambiguous).
//!
//! The fix is a targeted load-blocking diagnostic
//! (`LoadError::ArrowTermInExprPosition`) at the arrow term itself — exactly
//! ONE error, no follow-on cascade (the poisoned body is not stored, so the
//! typer never sees the recovery Bottom). The gate is pratt PROVENANCE
//! (WI-618, `SimpleTermStore::is_minted`): only a desugared infix `->`
//! fires, so a genuine call to something the user named `arrow` keeps its
//! meaning and its own accurate diagnostics.

/// The marker phrase of the targeted diagnostic (shared with wi618 — both
/// diagnostics end in `load::LAMBDA_KEYWORD_HINT`).
use crate::common::LAMBDA_HINT as HINT;

fn load_errors(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

/// WI-784: the lambda cases here are DRIVEN, not merely loaded — the callback
/// arity defect they sit on was invisible to `load_errors`.
fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// The WI-605 minimal repro: a keyword-less `(x, acc) -> …` as a higher-order
/// argument. Must produce EXACTLY the targeted lambda-keyword hint — one
/// error, no per-binder `UnresolvedName` cascade, no follow-on Bottom noise.
#[test]
fn bare_arrow_in_op_body_is_single_targeted_error() {
    let errs = load_errors(
        r#"
namespace test.wi605.bare
  import anthill.prelude.{List, nil, cons, Int64}

  operation sum_inc(xs: List[T=Int64]) -> List[T=Int64] =
    List.foldRight(xs, nil, (x, acc) -> cons(head: x + 1, tail: acc))
end
"#,
    );
    assert_eq!(
        errs.len(),
        1,
        "bare `(x, acc) -> …` must produce exactly the one targeted error; got: {errs:?}",
    );
    assert!(
        errs[0].contains(HINT) && errs[0].contains("arrow-type"),
        "the one error must be the lambda-keyword hint; got: {errs:?}",
    );
}

/// The single-binder misuse (`x -> x + 1`): the pratt desugar builds
/// `add(arrow(x, x), 1)` (`->` binds tighter than `+`), and the inner arrow
/// term errs with the same single hint.
#[test]
fn bare_single_param_arrow_is_single_targeted_error() {
    let errs = load_errors(
        r#"
namespace test.wi605.single
  import anthill.prelude.{List, Int64}

  operation incs(xs: List[T=Int64]) -> List[T=Int64] =
    xs.map(x -> x + 1)
end
"#,
    );
    assert_eq!(errs.len(), 1, "expected exactly the targeted error; got: {errs:?}");
    assert!(errs[0].contains(HINT), "expected the lambda-keyword hint; got: {errs:?}");
}

/// The keyword form of the SAME body loads clean — the WI's hypothesized
/// "lambda params not entered into a resolution scope" gap does not exist;
/// binder resolution in an op-body argument position works.
///
/// WI-784: also DRIVEN. Loading clean was never the interesting half — the
/// multi-binder lambda `List.foldRight` applies as `f(h, …)` trapped at eval
/// until the closure arm learned to gather its arguments.
#[test]
fn lambda_keyword_form_resolves_params() {
    let src = r#"
namespace test.wi605.keyword
  import anthill.prelude.{List, nil, cons, Int64}

  operation sum_inc(xs: List[T=Int64]) -> List[T=Int64] =
    List.foldRight(xs, nil, lambda (x, acc) -> cons(head: x + 1, tail: acc))

  operation drive() -> Int64 = List.length(sum_inc(cons(1, cons(2, nil))))
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "`lambda (x, acc) -> …` in an op-body argument position must load clean; got: {errs:?}",
    );
    assert_eq!(
        run_int(&mut crate::common::interp_for(src), "test.wi605.keyword.drive"),
        2,
        "the multi-binder lambda callback must actually APPLY, not just load",
    );
}

/// The effectful bare form (`x -> body @ e`, pratt-minted `arrow_effect/3`)
/// gets the same single targeted hint.
#[test]
fn bare_effectful_arrow_is_single_targeted_error() {
    let errs = load_errors(
        r#"
namespace test.wi605.effectful
  import anthill.prelude.{List, Int64}

  operation incs(xs: List[T=Int64]) -> List[T=Int64] =
    xs.map(x -> x + 1 @ pure)
end
"#,
    );
    assert_eq!(errs.len(), 1, "expected exactly the targeted error; got: {errs:?}");
    assert!(errs[0].contains(HINT), "expected the lambda-keyword hint; got: {errs:?}");
}

/// A function-typed op PARAM named `arrow`, legitimately applied — the
/// foldLeft `f(init, h)` pattern. `arrow(x, y)` is WRITTEN as a call (not
/// pratt-minted), so the provenance gate never fires on working code.
///
/// WI-784: this case is DRIVEN, not merely loaded. It describes itself as the
/// foldLeft pattern, and that pattern trapped at eval for a lambda callback
/// while passing for an operation — a load-only assertion could not see it.
/// Both spellings are evaluated here and must agree.
#[test]
fn function_typed_param_named_arrow_still_applies() {
    let src = r#"
namespace test.wi605.paramarrow
  import anthill.prelude.{Int64}

  operation apply2(arrow: (a: Int64, b: Int64) -> Int64, x: Int64, y: Int64) -> Int64 =
    arrow(x, y)

  operation sub2(a: Int64, b: Int64) -> Int64 = a - b

  operation drive_op() -> Int64 = apply2(sub2, 3, 10)
  operation drive_lambda() -> Int64 = apply2(lambda (a, b) -> a - b, 3, 10)
end
"#;
    assert!(
        load_errors(src).is_empty(),
        "applying a function-typed param named `arrow` must load clean; got: {:?}",
        load_errors(src),
    );
    let via_op = run_int(&mut crate::common::interp_for(src), "test.wi605.paramarrow.drive_op");
    let via_lambda =
        run_int(&mut crate::common::interp_for(src), "test.wi605.paramarrow.drive_lambda");
    assert_eq!(via_op, -7, "the operation spelling is the control");
    assert_eq!(
        via_lambda, via_op,
        "the lambda and operation callbacks of the same call must agree",
    );
}

/// An operation the user actually NAMED `arrow` is a genuine (written, not
/// minted) call and keeps the normal Apply path.
#[test]
fn user_defined_arrow_operation_still_callable() {
    let errs = load_errors(
        r#"
namespace test.wi605.userarrow
  import anthill.prelude.{Int64}

  operation arrow(a: Int64, b: Int64) -> Int64 = a + b
  operation use_arrow() -> Int64 = arrow(1, 2)
end
"#,
    );
    assert!(
        errs.is_empty(),
        "a user-defined `arrow` operation must remain callable; got: {errs:?}",
    );
}

/// A symbol named `arrow` in scope (here a sort) changes nothing: the typo
/// term is pratt-minted, so it still gets the targeted hint — an unrelated
/// name collision must not silently restore the old cascade.
#[test]
fn non_callable_arrow_symbol_does_not_disable_hint() {
    let errs = load_errors(
        r#"
namespace test.wi605.sortarrow
  import anthill.prelude.{List, nil, cons, Int64}

  sort arrow = ?

  operation sum_inc(xs: List[T=Int64]) -> List[T=Int64] =
    List.foldRight(xs, nil, (x, acc) -> cons(head: x + 1, tail: acc))
end
"#,
    );
    assert_eq!(
        errs.len(),
        1,
        "a sort named `arrow` must not suppress the diagnostic; got: {errs:?}",
    );
    assert!(errs[0].contains(HINT), "expected the lambda-keyword hint; got: {errs:?}");
}

/// An explicit call to an undefined `arrow` was WRITTEN as a call (not
/// pratt-minted) — it keeps the normal path's accurate unresolved-functor
/// diagnostics, not wrong advice about a `->` the user never typed.
#[test]
fn explicit_wrong_arity_arrow_call_keeps_normal_diagnostics() {
    let errs = load_errors(
        r#"
namespace test.wi605.arity
  import anthill.prelude.{Int64}

  operation use_it() -> Int64 = arrow(1, 2, 3)
end
"#,
    );
    assert!(
        !errs.is_empty(),
        "an undefined `arrow(1, 2, 3)` call must still error",
    );
    assert!(
        !errs.iter().any(|e| e.contains(HINT)),
        "a 3-arg call is not the pratt shape — no lambda hint; got: {errs:?}",
    );
}

/// An AMBIGUOUS genuine call: two wildcard imports both exporting an `arrow`
/// operation make the written call `arrow(1, 2)` ambiguous, and the user must
/// get the accurate ambiguity diagnostic — not the lambda hint (there is no
/// `->` anywhere in the call).
#[test]
fn ambiguous_arrow_call_reports_ambiguity_not_lambda_hint() {
    let liba = r#"
namespace test.wi605.liba
  import anthill.prelude.{Int64}
  operation arrow(a: Int64, b: Int64) -> Int64 = a + b
end
"#;
    let libb = r#"
namespace test.wi605.libb
  import anthill.prelude.{Int64}
  operation arrow(a: Int64, b: Int64) -> Int64 = a - b
end
"#;
    let main = r#"
namespace test.wi605.amb
  import test.wi605.liba.*
  import test.wi605.libb.*
  import anthill.prelude.{Int64}

  operation use_it() -> Int64 = arrow(1, 2)
end
"#;
    let errs = crate::common::try_load_kb_with_files(&[liba, libb, main])
        .err()
        .unwrap_or_default();
    assert!(
        !errs.iter().any(|e| e.contains(HINT)),
        "an ambiguous genuine call must not get the lambda hint; got: {errs:?}",
    );
    assert!(
        errs.iter().any(|e| e.to_lowercase().contains("ambiguous")),
        "expected the ambiguity diagnostic; got: {errs:?}",
    );
}
