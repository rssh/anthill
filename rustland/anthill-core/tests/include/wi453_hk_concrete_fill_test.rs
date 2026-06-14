//! WI-453 (§5.4) — HIGHER-KINDED CONCRETE FILL at a use-site, via
//! requirement-discharge.
//!
//! With the marked carrier `F` var-backed (WI-452), an EXTERNAL call to a spec op
//! FILLS `F` from the call context — `F[T=A] ≟ Option[T=X]` ⟹ `F := Option` — for
//! both the ARG-carrier (`flatMap(o: Option, …)`) and the RESULT-carrier
//! (`unit(42) : Option`, where `F` is only in the return). The σ-walk grounds
//! `F[T=A]` to `Option[T=A]` (the §5.4 injective-application `F := List`
//! decomposition). Dispatch routes through `dispatch_spec_op_cached`: the SLD
//! discharge against the WI-431 instance fact confirms `Option` provides `CpsMonad`
//! AND yields the bound impl (`unit ↦ optionUnit`). A carrier with no instance is a
//! LOUD error (the undischarged obligation), never a silent accept.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// The §5.4 `CpsMonad` spec in the marked enclosing-list form + the `Option`
/// instance fact, shared by the cases below (with `$BODY` appended).
fn cps_src(body: &str) -> String {
    format!(
        r#"namespace test.wi453
  import anthill.prelude.{{Option, Int64}}

  sort CpsMonad[F[T]]
    operation unit[A](a: A) -> F[T = A]
    operation flatMap[A, B](fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
  end

  operation optionUnit[A](a: A) -> Option[T = A] = some(a)
  operation optionFlatMap[A, B](fa: Option[T = A], f: (A) -> Option[T = B]) -> Option[T = B] =
    match fa
      case some(x) -> f(x)
      case none() -> none
  fact CpsMonad[F = Option, unit = optionUnit, flatMap = optionFlatMap]

{body}
end
"#
    )
}

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

/// RESULT-carrier (`F` only in the return) typechecks: `unit(42)` fills `F := Option`
/// from the expected type.
#[test]
fn result_carrier_fill_typechecks() {
    let src = cps_src("  operation useResult() -> Option[T = Int64] = unit(42)");
    let errs = load_errors(&src);
    assert!(errs.is_empty(), "unit(42) : Option should fill F := Option and typecheck: {errs:?}");
}

/// ARG-carrier (`F` in the argument) typechecks: `flatMap(o : Option, …)` fills
/// `F := Option` from the argument's base.
#[test]
fn arg_carrier_fill_typechecks() {
    let src = cps_src(
        "  operation mkSome(n: Int64) -> Option[T = Int64] = some(n)\n  \
         operation useArg(o: Option[T = Int64]) -> Option[T = Int64] = flatMap(o, mkSome)",
    );
    let errs = load_errors(&src);
    assert!(errs.is_empty(), "flatMap(o:Option, mkSome) should fill F := Option and typecheck: {errs:?}");
}

/// The fill is TYPE-CHECKED: `unit(42)` grounds to `Option[T = Int64]`, so a wrong
/// declared return `Option[T = String]` is rejected (not blindly accepted).
#[test]
fn fill_is_type_checked_wrong_type_rejected() {
    let src = cps_src(
        "  import anthill.prelude.String\n  \
         operation wrong() -> Option[T = String] = unit(42)",
    );
    let errs = load_errors(&src);
    assert!(
        errs.iter().any(|e| e.contains("wrong") && e.contains("Option")),
        "unit(42):Option[Int64] must be rejected against declared Option[String]: {errs:?}"
    );
}

/// A carrier with NO instance is a LOUD error (the undischarged `Spec[F = C]`
/// obligation), never a silent accept: `MyBox` has no `fact CpsMonad[F = MyBox]`.
#[test]
fn no_instance_carrier_is_loud() {
    let src = cps_src(
        "  sort MyBox[T]\n    entity mybox(v: T)\n  end\n  \
         operation noInst() -> MyBox[T = Int64] = unit(42)",
    );
    let errs = load_errors(&src);
    assert!(
        errs.iter().any(|e| e.contains("noInst") || e.contains("dispatch") || e.contains("unit")),
        "unit(42):MyBox with no CpsMonad instance must be a loud no-instance/dispatch error: {errs:?}"
    );
}

// ── Eval: the discharge dispatches to the instance's bound impl ──────────────

/// RESULT-carrier dispatch: `unit(42)` (annotated `: Option`) dispatches to the
/// instance's `optionUnit` ⟹ `some(42)`; unwrapped to `42`. The carrier is only in
/// the return, so value-directed eval CANNOT classify it — the typer-resolved
/// instance dispatch is the route.
#[test]
fn result_carrier_dispatches_to_instance_impl() {
    let src = cps_src(
        "  operation runResult() -> Int64 =\n    \
         let o: Option[T = Int64] = unit(42)\n    \
         match o\n      case some(x) -> x\n      case none() -> 0",
    );
    let mut interp = crate::common::interp_for(&src);
    match interp.call("test.wi453.runResult", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 42,
            "unit(42) must dispatch to optionUnit ⟹ some(42) ⟹ 42; got {n}"
        ),
        other => panic!("runResult should dispatch unit via the instance fact; got {other:?}"),
    }
}

/// ARG-carrier dispatch: `flatMap(some(5), mkSome)` dispatches to `optionFlatMap`
/// ⟹ `mkSome(5)` ⟹ `some(5)`; unwrapped to `5`.
#[test]
fn arg_carrier_dispatches_to_instance_impl() {
    let src = cps_src(
        "  operation mkSome(n: Int64) -> Option[T = Int64] = some(n)\n  \
         operation runArg() -> Int64 =\n    \
         let o: Option[T = Int64] = some(5)\n    \
         let r: Option[T = Int64] = flatMap(o, mkSome)\n    \
         match r\n      case some(x) -> x\n      case none() -> 0",
    );
    let mut interp = crate::common::interp_for(&src);
    match interp.call("test.wi453.runArg", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 5,
            "flatMap(some(5), mkSome) must dispatch to optionFlatMap ⟹ some(5) ⟹ 5; got {n}"
        ),
        other => panic!("runArg should dispatch flatMap via the instance fact; got {other:?}"),
    }
}
