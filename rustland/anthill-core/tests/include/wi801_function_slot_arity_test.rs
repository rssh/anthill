//! WI-801 — the typer and eval agree on ONE spread-vs-whole rule.
//!
//! THE DEFECT. Three sites decided how many values a callable is handed, each
//! from a different quantity: the typer's argument check
//! (`positional_arg_expectations`) from `A`'s COMPONENT COUNT, eval
//! (`spread_eta_args` / `gather_closure_arg`) from the CALLEE's OWN ARITY, and the
//! conformance check (`arrow_function_compatible`) from neither — it read no arity
//! at all at a `Function[A, B, E]` slot. Nothing checked the three against each
//! other, and two independent load-clean-then-trap holes fell out. Both are
//! measured below as they were:
//!
//!   1. A CALLBACK THAT FITS NEITHER READING WAS ADMITTED. `lambda (p, q, r) -> p`
//!      at a 2-component `A` loaded clean and trapped
//!      `ArityMismatch { expected: 3, got: 2 }`. Only the LAMBDA spelling: an op
//!      reference's eta arrow carries its parameter list as a CONCRETE tuple type,
//!      so a wrong count already failed the param comparison, while an unannotated
//!      lambda ADOPTS the expected `A` as its param type — so its param matches by
//!      construction and its arity was the one quantity left, free-floating and
//!      unread. "A `Function` states no arity" is true, and had been taken to mean
//!      nothing about arity is decidable; it only means the check is a SET rather
//!      than an equality.
//!
//!   2. THE SPREAD CALL FORM TRAPPED AGAINST A WHOLE-`A` CALLEE. `f(1, 2)` inside
//!      a `Function[A = (a: Int64, b: Int64), B]` slot, given `lambda t -> t.a`,
//!      loaded clean and trapped `ArityMismatch { expected: 1, got: 2 }` — even
//!      though the spec makes both call forms legal at the slot and arity 1 is the
//!      CANONICAL inhabitant of the type. The whole-tuple form worked in every
//!      cell; only the spread form was broken, and only against an arity-1 callee.
//!
//! THE RULE (docs/kernel-language.md §"the equivalence is not exact"): a
//! `Function[(A, B), R]` "accepts either" a single-tuple-argument callback OR a
//! two-parameter one. So a slot whose `A` has `n` components admits exactly the
//! arities {1, n} — and reaches exactly the call counts {1, n}. Note this is
//! NARROWER than the ticket's own phrasing ("a callback whose binder count differs
//! from A's arity is a load error"): that would refuse arity 1, which is simply
//! what `(X, Y) -> B` means.
//!
//! THE FIX, in one owner. `kb/call_form.rs` states the rule once
//! (`classify_application`); the conformance gate, the call-site check and both of
//! eval's adapters read it. Hole 1 becomes a load error. Hole 2 is removed at the
//! TYPER, not at eval, and that asymmetry is forced: a gather needs `A`'s component
//! LABELS, which are erased before eval runs. The typer rewrites the spread call
//! into its whole-`A` form, so eval sees ONE argument and both admitted arities
//! take the identical path — its existing spread adapters, which were already the
//! tested ones.

use crate::common::{interp_for, try_load_kb_with};

fn run_int(src: &str, op: &str) -> i64 {
    // A FRESH interpreter per call — reusing one after a trapped call returns a
    // bogus Internal on every later call.
    let mut interp = interp_for(src);
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

fn load_errs(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

// ── hole 1: a callback fitting neither reading is refused at LOAD ──

/// THE headline program for hole 1. Pre-fix this loaded clean and trapped
/// `ArityMismatch { expected: 3, got: 2 }`.
#[test]
fn a_callback_fitting_neither_reading_is_refused_at_load() {
    let msg = load_errs(
        r#"
namespace test.wi801.neither
  import anthill.prelude.{Int64, Function}
  operation ap(f: Function[A = (Int64, Int64), B = Int64]) -> Int64
    = f(1, 2)
  operation drive() -> Int64
    = ap(lambda (p, q, r) -> p)
end
"#,
    )
    .join(" | ");
    assert!(
        msg.contains("callback of 3 parameters"),
        "the diagnostic must name the callback's OWN arity (3); got: {msg}",
    );
    assert!(
        msg.contains("1 parameter") && msg.contains("2 (its components spread)"),
        "and BOTH admissible readings (1, or A's 2 components spread), since a \
         `Function` admits two and the reader needs to know which were open; got: {msg}",
    );
}

/// The same refusal reaches the ANNOTATED spelling. Measured pre-fix as loading
/// clean too, which is what shows the param comparison could never have caught
/// this: `param_type` comes from the CONTEXT either way, so the arrow's param is
/// `A` and only its arity disagrees.
#[test]
fn an_annotated_callback_is_refused_on_arity_too() {
    let msg = load_errs(
        r#"
namespace test.wi801.annotated
  import anthill.prelude.{Int64, Function}
  operation ap(f: Function[A = (Int64, Int64), B = Int64]) -> Int64
    = f(1, 2)
  operation drive() -> Int64
    = ap(lambda (p: Int64, q: Int64, r: Int64) -> p)
end
"#,
    )
    .join(" | ");
    assert!(msg.contains("callback of 3 parameters"), "got: {msg}");
}

/// A NON-tuple `A` is ONE indivisible value, so only arity 1 can take it. This is
/// the case a rule stated as "arity 1 or |A|" gets wrong if `Spread`'s obligation
/// is not discharged against `A`: `classify_application(2, 1)` IS a spread, and it
/// is admissible only because `A` really has 2 components — which here it has not.
#[test]
fn a_scalar_argument_type_admits_only_a_one_parameter_callback() {
    let msg = load_errs(
        r#"
namespace test.wi801.scalar
  import anthill.prelude.{Int64, Function}
  operation ap(f: Function[A = Int64, B = Int64]) -> Int64
    = f(7)
  operation drive() -> Int64
    = ap(lambda (p, q) -> p)
end
"#,
    )
    .join(" | ");
    assert!(
        msg.contains("no components to spread"),
        "a scalar `A` must say WHY only arity 1 fits, rather than offering a \
         spread reading that does not exist; got: {msg}",
    );
}

/// EVERY channel that can render this disagreement must render it as ITSELF.
///
/// The remedy was first installed at the op-arg channel only, and `/code-review`
/// caught that the other two still shipped the exact string the fix exists to
/// remove — `expected Function[A = (_1: Int64, _2: Int64), B = Int64], got (_1:
/// Int64, _2: Int64) -> Int64`. That is the WI-790 failure mode (half-consolidating
/// is worse than not) and the WI-792 one (the other channel had the same hole):
/// the defect is fixed on the path the tests exercise and left standing beside it.
///
/// The negative assertion is the load-bearing one — the positive text could be
/// satisfied while the raw mismatch ALSO fired somewhere.
#[test]
fn every_channel_names_the_arity_rather_than_printing_both_sides_alike() {
    let cases = [
        (
            "op-arg",
            r#"
namespace test.wi801.chan.oparg
  import anthill.prelude.{Int64, Function}
  operation ap(f: Function[A = (Int64, Int64), B = Int64]) -> Int64 = f(1, 2)
  operation drive() -> Int64 = ap(lambda (p, q, r) -> p)
end
"#,
        ),
        (
            "let-annotation",
            r#"
namespace test.wi801.chan.letann
  import anthill.prelude.{Int64, Function}
  operation drive() -> Int64 =
    let f: Function[A = (Int64, Int64), B = Int64] = lambda (p, q, r) -> p
    1
end
"#,
        ),
        (
            "op-return",
            r#"
namespace test.wi801.chan.opret
  import anthill.prelude.{Int64, Function}
  operation mk() -> Function[A = (Int64, Int64), B = Int64] = lambda (p, q, r) -> p
end
"#,
        ),
    ];
    for (channel, src) in cases {
        let msg = load_errs(src).join(" | ");
        assert!(
            msg.contains("callback of 3 parameters"),
            "{channel}: must name the callback's arity; got: {msg}",
        );
        assert!(
            !msg.contains("-> Int64"),
            "{channel}: must NOT fall back to rendering the two arrow types, which \
             print alike here because the lambda ADOPTS `A` as its param; got: {msg}",
        );
    }
}

/// A GENERIC `A` states no component count and must stay unconstrained — a count
/// is exactly what instantiation supplies. THE CONTROL for every refusal above:
/// the gate must fire on a known `A`, never on an unknown one.
#[test]
fn a_rigid_argument_type_is_not_gated() {
    let src = r#"
namespace test.wi801.rigid
  import anthill.prelude.{Int64, Function}
  operation ap[T](f: Function[A = T, B = T], x: T) -> T
    = f(x)
  operation drive() -> Int64
    = ap(lambda t -> t, 5)
end
"#;
    assert!(try_load_kb_with(src).is_ok(), "a rigid `A` must not be arity-gated");
    assert_eq!(run_int(src, "test.wi801.rigid.drive"), 5);
}

// ── hole 2: both call forms x both admitted arities ────────────

/// THE MATRIX, and the point of the ticket: {positional `A`, named `A`} x
/// {whole-tuple callee, spread callee} x {whole call, spread call}.
///
/// Pre-fix the two `1binder`+`spread` cells trapped
/// `ArityMismatch { expected: 1, got: 2 }` while their six siblings evaluated. The
/// callee's arity and `A`'s component count are exactly the two quantities WI-801
/// found disagreeing, so driving every combination is what pins that they no
/// longer can.
#[test]
fn every_call_form_reaches_every_admitted_callback_arity() {
    // A running cell index, NOT a hash of the cell's strings: `a.len() + kind.len()
    // + form.len()` collided (two of the eight cells both summed to 43) while
    // claiming to be distinct. Harmless only because `run_int` builds a fresh KB
    // per cell — but a comment asserting an invariant the code does not hold is
    // exactly what a later shared-KB refactor would trust.
    let mut cell = 0;
    for (a, whole, fst) in [
        ("(Int64, Int64)", "(1, 2)", "_1"),
        ("(a: Int64, b: Int64)", "(a: 1, b: 2)", "a"),
    ] {
        for (kind, callee, want) in [
            ("whole-tuple callee", format!("lambda t -> t.{fst}"), 1),
            ("spread callee", "lambda (p, q) -> p - q".to_string(), -1),
        ] {
            for (form, call) in [("whole call", whole), ("spread call", "1, 2")] {
                cell += 1;
                let ns = format!("test.wi801.m{cell}");
                let src = format!(
                    r#"
namespace {ns}
  import anthill.prelude.{{Int64, Function}}
  operation ap(f: Function[A = {a}, B = Int64]) -> Int64
    = f({call})
  operation drive() -> Int64
    = ap({callee})
end
"#
                );
                assert_eq!(
                    run_int(&src, &format!("{ns}.drive")),
                    want,
                    "A = {a}, {kind}, {form}: both call forms must reach both \
                     admitted callback arities",
                );
            }
        }
    }
}

/// The OPERATION spelling of the same widening — WI-784's interchangeability
/// invariant, extended to the cell it did not cover. A ONE-parameter operation at
/// a `Function` slot called in the SPREAD form trapped
/// `ArityMismatch { op: "function-value application", expected: 1, got: 2 }`
/// pre-fix, the same defect as the lambda's through the other adapter.
#[test]
fn a_one_parameter_operation_also_takes_the_spread_form() {
    let src = r#"
namespace test.wi801.opspread
  import anthill.prelude.{Int64, Function}
  operation takeT(t: (Int64, Int64)) -> Int64 = t._1
  operation ap(f: Function[A = (Int64, Int64), B = Int64]) -> Int64
    = f(1, 2)
  operation drive() -> Int64
    = ap(takeT)
end
"#;
    assert_eq!(run_int(src, "test.wi801.opspread.drive"), 1);
}

/// The UNIT slot, at BOTH admitted arities. `f()` is the ZERO-argument spread
/// form, so a 1-parameter callback there is the same hole as `f(1, 2)` against a
/// 1-parameter one — it reached eval as a gather of zero arguments and trapped.
/// The nullary half is the CONTROL: `prelude/delay.anthill`'s thunk rides it, and
/// the normalization must not disturb it.
#[test]
fn a_unit_slot_reaches_both_admitted_arities() {
    for (i, (lam, what)) in
        [("lambda () -> 5", "the nullary thunk"), ("lambda t -> 5", "a whole-unit callback")]
            .into_iter()
            .enumerate()
    {
        let ns = format!("test.wi801.unit{i}");
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Function}}
  operation force(f: Function[A = (), B = Int64]) -> Int64
    = f()
  operation drive() -> Int64 = force({lam})
end
"#
        );
        assert_eq!(run_int(&src, &format!("{ns}.drive")), 5, "{what} at a unit slot");
    }
}

/// The normalization must compose with the WI-408 some-coercion, which indexes
/// the ORIGINAL argument children: a coerced argument has to be wrapped BEFORE it
/// becomes a tuple component, or the `some(...)` lands on the wrong node — or on
/// none, leaving a bare value in memory whose type says `Option[T]`.
#[test]
fn a_coerced_argument_is_wrapped_before_it_becomes_a_component() {
    let src = r#"
namespace test.wi801.coerce
  import anthill.prelude.{Int64, Option, Function, some, none}
  operation pick(t: (o: Option[T = Int64], d: Int64)) -> Int64 =
    match t.o
      case none() -> t.d
      case some(v) -> v
  operation ap(f: Function[A = (o: Option[T = Int64], d: Int64), B = Int64]) -> Int64
    = f(7, 3)
  operation drive() -> Int64
    = ap(pick)
end
"#;
    assert_eq!(
        run_int(src, "test.wi801.coerce.drive"),
        7,
        "the bare `7` must reach the callee as `some(7)`, not as a bare Int",
    );
}
