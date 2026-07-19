//! WI-783 — NAMED arguments at a function-VALUE application must bind by the
//! arrow's DECLARED binder names, not by the order they are written in.
//!
//! `check_apply_iter`'s Path 1 (a call to a known operation) checks named-arg
//! coverage and then reorders the labelled args into the callee's parameter
//! order (`reorder_named_args_in_apply`), because eval's `start_apply` DISCARDS
//! the labels and binds what remains positionally. Path 2 — the callee is a
//! variable of arrow type — did neither: it computed the return type and
//! effects and returned the occurrence untouched.
//!
//! So the labels were inert and every argument bound by WRITTEN ORDER. Measured
//! on the pre-fix tree with `sub2(a, b) = a - b` passed as `(acc, x) -> Int64`:
//! `f(x: 10, acc: 3)` evaluated to 7 and `f(acc: 3, x: 10)` to -7 — the same
//! call, spelled two ways, giving two answers, with no trap and no diagnostic.
//! An unknown label (`f(bogus: 10, acc: 3)`) was accepted just as silently.
//! That is strictly worse than a loud failure, hence the end-to-end drives here:
//! nothing about this bug is visible at load time.
//!
//! Binding by the DECLARED names stays sound under WI-775, which lets the actual
//! callee's own binder names differ from the arrow's (`sub2(a, b)` is a legal
//! argument for `(acc, x)`): an arrow's parameter list is applied POSITIONALLY,
//! so declared slot i IS the callee's slot i. Resolving label → slot against the
//! static type and handing eval a positional call therefore composes exactly.
//!
//! Where the arrow type records NO binder names the labels are rejected instead
//! (`arrow_declared_param_list` → `None`), since they can be neither ordered nor
//! validated. That covers a ONE-parameter arrow — `(v: Int64) -> Int64` keeps
//! only `Int64`, the name `v` is dropped when the type is built — and the
//! `Function[A, B]` surface, whose `A` is one tuple-typed ARGUMENT rather than a
//! parameter list (WI-775).

use crate::common::{interp_for, try_load_kb_with};

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// Assert the program is refused with a located named-argument diagnostic that
/// names the offending LABEL — not merely "some error", which a typo in the
/// fixture would also satisfy.
fn assert_named_arg_rejected(src: &str, label: &str, expected_reason: &str) {
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("must NOT load: named argument '{label}' is unresolvable here"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains(&format!("named argument '{label}'"))
            && e.contains(expected_reason)),
        "rejection must name label '{label}' and say {expected_reason:?}; got: {errs:?}",
    );
}

/// A non-commutative body, so a swapped binding is a DIFFERENT number rather
/// than an accidentally-equal one. Declared binder names (`acc`, `x`)
/// deliberately differ from the callee's own (`a`, `b`) — the WI-775 freedom
/// this fix must keep.
const SUB2: &str = r#"
  operation sub2(a: Int64, b: Int64) -> Int64
    = a - b
"#;

/// THE acceptance criterion: the same call spelled in both orders must agree.
/// Driven end-to-end — at load both spellings were (and still are) clean, so a
/// load-only assertion would not see this bug at all.
#[test]
fn both_orderings_agree_end_to_end() {
    let src = format!(
        r#"
namespace test.wi783agree
  import anthill.prelude.{{Int64}}
{SUB2}
  operation apply_written(f: (acc: Int64, x: Int64) -> Int64) -> Int64
    = f(x: 10, acc: 3)
  operation apply_swapped(f: (acc: Int64, x: Int64) -> Int64) -> Int64
    = f(acc: 3, x: 10)
  operation drive_written() -> Int64
    = apply_written(sub2)
  operation drive_swapped() -> Int64
    = apply_swapped(sub2)
end
"#
    );
    let mut interp = interp_for(&src);
    let written = run_int(&mut interp, "test.wi783agree.drive_written");
    let swapped = run_int(&mut interp, "test.wi783agree.drive_swapped");
    assert_eq!(
        written, swapped,
        "`f(x: 10, acc: 3)` and `f(acc: 3, x: 10)` name the same binding and must \
         evaluate alike; got {written} vs {swapped} (pre-fix: 7 vs -7)",
    );
    // Pin WHICH binding, not merely that the two agree: `acc: 3` is slot 0 and
    // `x: 10` slot 1, so the callee computes 3 - 10. Agreement alone would also
    // hold if both spellings bound wrongly but identically.
    assert_eq!(written, -7, "labels must bind by NAME (acc=3, x=10 ⇒ 3-10), not by written order");
}

/// The label must reach the DECLARED slot even when the callee's own parameter
/// names differ (WI-775: an arrow's parameter list aligns positionally, so
/// binder names need not agree). Here `acc`/`x` are the arrow's; `a`/`b` the
/// callee's. A fix that resolved labels against the *callee's* names instead
/// would fail this.
#[test]
fn declared_binder_names_win_over_callee_names() {
    let src = format!(
        r#"
namespace test.wi783decl
  import anthill.prelude.{{Int64}}
{SUB2}
  operation apply2(f: (acc: Int64, x: Int64) -> Int64) -> Int64
    = f(x: 10, acc: 3)
  operation drive() -> Int64
    = apply2(sub2)
end
"#
    );
    let mut interp = interp_for(&src);
    assert_eq!(run_int(&mut interp, "test.wi783decl.drive"), -7);
}

/// An unknown label must be a LOUD located error, matching what a direct call to
/// a named operation already gives ("names no parameter of this operation").
/// Pre-fix this loaded clean and evaluated to 7.
#[test]
fn unknown_label_rejected() {
    let src = format!(
        r#"
namespace test.wi783unknown
  import anthill.prelude.{{Int64}}
{SUB2}
  operation apply2(f: (acc: Int64, x: Int64) -> Int64) -> Int64
    = f(bogus: 10, acc: 3)
  operation drive() -> Int64
    = apply2(sub2)
end
"#
    );
    assert_named_arg_rejected(&src, "bogus", "names no parameter of this function value's type");
}

/// A label that re-binds a parameter already filled POSITIONALLY. Without the
/// coverage check the stray label sorts last in the reorder and eval rebinds it
/// to the leftover slot — the WI-426 failure mode, here on the arrow path.
#[test]
fn label_duplicating_a_positional_arg_rejected() {
    let src = format!(
        r#"
namespace test.wi783dup
  import anthill.prelude.{{Int64}}
{SUB2}
  operation apply2(f: (acc: Int64, x: Int64) -> Int64) -> Int64
    = f(3, acc: 10)
  operation drive() -> Int64
    = apply2(sub2)
end
"#
    );
    assert_named_arg_rejected(&src, "acc", "binds a parameter already given");
}

/// A ONE-parameter arrow drops its binder name when the type is built —
/// `(v: Int64) -> Int64` extracts as param `Int64`, with no `v` anywhere. There
/// is nothing to match a label against, so a label here is rejected rather than
/// waved through: at arity 1 a WRONG label (`f(zzz: 7)`) is indistinguishable
/// from a right one, and silently accepting it is the very inertness this ticket
/// is about. Both spellings below are refused identically.
#[test]
fn label_rejected_when_arrow_records_no_parameter_names() {
    let mk = |label: &str| {
        format!(
            r#"
namespace test.wi783noname{label}
  import anthill.prelude.{{Int64}}
  operation neg(v: Int64) -> Int64
    = 0 - v
  operation apply1(f: (v: Int64) -> Int64) -> Int64
    = f({label}: 7)
  operation drive() -> Int64
    = apply1(neg)
end
"#
        )
    };
    let reason = "records no parameter names";
    // The label that MATCHES the source-level binder name is refused too — the
    // name is genuinely absent from the type, so accepting it would be luck.
    assert_named_arg_rejected(&mk("v"), "v", reason);
    assert_named_arg_rejected(&mk("zzz"), "zzz", reason);
}

/// The boundary the fix must not cross, part 1: a POSITIONAL function-value
/// application is untouched — no labels, nothing to resolve. Includes the mixed
/// form, where the sole label fills the slot the positional arg left open.
#[test]
fn positional_and_mixed_applications_unaffected() {
    let src = format!(
        r#"
namespace test.wi783pos
  import anthill.prelude.{{Int64}}
{SUB2}
  operation all_positional(f: (acc: Int64, x: Int64) -> Int64) -> Int64
    = f(3, 10)
  operation mixed(f: (acc: Int64, x: Int64) -> Int64) -> Int64
    = f(3, x: 10)
  operation drive_positional() -> Int64
    = all_positional(sub2)
  operation drive_mixed() -> Int64
    = mixed(sub2)
end
"#
    );
    let mut interp = interp_for(&src);
    assert_eq!(run_int(&mut interp, "test.wi783pos.drive_positional"), -7, "f(3, 10)");
    assert_eq!(run_int(&mut interp, "test.wi783pos.drive_mixed"), -7, "f(3, x: 10)");
}

/// The boundary the fix must not cross, part 2: the stdlib's higher-order
/// callbacks, which are exactly the arrow-typed parameters this path types.
/// `foldLeft`'s `f` is declared `(acc, x)` and receives a two-param op's eta
/// arrow `(_1, _2)` — the WI-775 positional-alignment case. It is applied
/// positionally, so the new label handling must not see it at all.
#[test]
fn stdlib_higher_order_callbacks_still_run() {
    let src = r#"
namespace test.wi783stdlib
  import anthill.prelude.{Int64, List}
  import anthill.prelude.FiniteCollection.{foldLeft}
  operation shift(acc: Int64, x: Int64) -> Int64
    = acc * 10 + x
  operation fold_it() -> Int64
    = foldLeft([1, 2, 3], 0, shift)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi783stdlib.fold_it"), 123);
}

/// The boundary the fix must not cross, part 3: `Function[A, B]`. WI-775 settled
/// that `A` is the ARGUMENT's data type — one tuple-typed argument, not a
/// two-slot parameter list — so a named-tuple `A` must NOT be read as binder
/// names. The call below passes a single tuple VALUE positionally and must keep
/// working; reading `A`'s field names as a parameter list would re-conflate the
/// two positions WI-775 split apart.
#[test]
fn function_sort_tuple_argument_still_applies() {
    let src = r#"
namespace test.wi783fn
  import anthill.prelude.{Int64, Function}
  operation fst(t: (acc: Int64, x: Int64)) -> Int64
    = t.acc
  operation apply_tuple(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64
    = f((acc: 3, x: 10))
  operation drive() -> Int64
    = apply_tuple(fst)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi783fn.drive"), 3);
}
