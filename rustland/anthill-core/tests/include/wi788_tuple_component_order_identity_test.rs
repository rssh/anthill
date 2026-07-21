//! WI-788 — a named tuple's component ORDER is part of its type identity, and a
//! `Function[A, B]` slot CHECKS its arguments.
//!
//! THE DEFECT, measured end-to-end: `operation ap(f: Function[A = (a: Int64, b:
//! String), B = Int64]) -> Int64 = f((b: "ess", a: 3))` with `ap(lambda (p, q) ->
//! p)` LOADED CLEAN and returned `Str("ess")` from an operation declared
//! `-> Int64`. Two independent causes had to meet, and each is fixed here:
//!
//!   1. ORDER WAS NOT IDENTITY. `align_named_tuple_fields` (kb/typing.rs) related
//!      two named tuples by an order-insensitive NAME lookup, so a permuted
//!      literal conformed. But the value carrier keeps SOURCE order (WI-786) and a
//!      destructuring binder list reads it POSITIONALLY (WI-785), so binder `i`
//!      received the value's `i`-th component while the typer had given it the
//!      type of the DECLARED `i`-th field.
//!
//!   2. THE `Function` SLOT CHECKED NOTHING. `arrow_positional_param_slots`
//!      returns `None` for `Function[A, B, E]` — correctly, since it states no
//!      arity and WI-775 settled that `f(3, 10)` and `f((3, 10))` are both legal
//!      there — and "no count can be REQUIRED" had been taken to mean "nothing can
//!      be checked". The `A` binding was read for the lambda's binder types and
//!      then discarded at the application. This was NOT a permutation gap:
//!      `f((a: "ess", b: 3))` (in order, wrong types) and `f(true)` loaded clean
//!      too, which `function_slot_*` below pins.
//!
//! THE RULE. A component is identified by its NAME and its POSITION together, so
//! tuple types align SLOT BY SLOT with the names required to agree at each slot —
//! the same correspondence `TupleAlign::ParamList` already performed for arrow
//! parameter lists (WI-782), one rule for both as the ticket asked.
//! `(a: Int64, b: String)` therefore differs from `(b: String, a: Int64)` (the
//! positions disagree) AND from `(Int64, String)` (the names disagree, proposal
//! 004 rule 4 — pinned by `positional_tuple_does_not_conform_to_a_named_one`).
//! Numbering components `_1.._n` by definition order is a way to SEE that
//! position counts; it is not a normalization, and read literally it would erase
//! names and collapse `(a: A)` into `(_1: A)`.
//!
//! WHY NOT "align by the consumer's read discipline" (the direction originally
//! proposed): it is not decidable where the permutation is admitted. `t.x` reads
//! by name and a binder list reads by position, but a value flows through a
//! `Function[A, B]` PARAMETER to a consumer chosen at a different call site, so
//! the site relating the literal to `A` cannot know which reader it will meet.
//!
//! WIDTH survives as a PREFIX: dropping a TRAILING component leaves every
//! retained component's canonical position unchanged, whereas dropping a MIDDLE
//! one renumbers everything after it. `width_*` below pins both halves.

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

fn assert_refused(src: &str, what: &str) {
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("mismatch")),
        "{what} must be refused at load with a type mismatch; got: {errs:?}",
    );
}

/// Build `ap(f) = f(<lit>)` over a `Function[A = <ty>, B = Int64]` and drive it
/// with `<lam>` — the shape every `Function`-slot case here shares. Same builder
/// as `wi786_tuple_component_order_test`'s, which pins the carrier invariant this
/// ticket's rule rests on.
fn fn_slot_case(ns: &str, imports: &str, ty: &str, lit: &str, lam: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{{imports}}}
  operation ap(f: Function[A = {ty}, B = Int64]) -> Int64
    = f({lit})
  operation drive() -> Int64
    = ap({lam})
end
"#
    )
}

// ── THE REGRESSION, driven end-to-end ──────────────────────────

/// THE headline program. Pre-fix this loaded clean and `drive()`, declared
/// `-> Int64`, evaluated to `Str("ess")` — a wrong-TYPED value, not merely a
/// wrong one, with no trap anywhere.
#[test]
fn permuted_literal_at_a_function_slot_is_refused() {
    assert_refused(
        &fn_slot_case(
            "test.wi788.headline",
            "Int64, String, Function",
            "(a: Int64, b: String)",
            r#"(b: "ess", a: 3)"#,
            "lambda (p, q) -> p",
        ),
        "a permuted tuple literal against a declared (a: Int64, b: String)",
    );
}

/// The ALL-Int64 variant, which carries no type signal at all: every component
/// type matches under the old by-name lookup, so nothing downstream could notice.
/// It returned 7 where the declared order (a, b) implies -7.
#[test]
fn permuted_literal_with_uniform_types_is_refused() {
    assert_refused(
        &fn_slot_case(
            "test.wi788.uniform",
            "Int64, Function",
            "(a: Int64, b: Int64)",
            "(b: 10, a: 3)",
            "lambda (p, q) -> p - q",
        ),
        "a permuted all-Int64 tuple literal",
    );
}

// ── order is identity at every tuple position ──────────────────

/// A plain operation ARGUMENT. Pre-fix this loaded clean and even returned the
/// RIGHT answer (3), because `t.a` reads by NAME — which is precisely why the
/// by-name relation looked sound and why it could not be gated on the reader:
/// the same admitted permutation is a silent wrong answer once the reader is a
/// binder list instead.
#[test]
fn permuted_operation_argument_is_refused() {
    assert_refused(
        r#"
namespace test.wi788.oparg
  import anthill.prelude.{Int64, String}
  operation take(t: (a: Int64, b: String)) -> Int64 = t.a
  operation drive() -> Int64 = take((b: "ess", a: 3))
end
"#,
        "a permuted tuple passed as an operation argument",
    );
}

/// An operation RETURN — the dual position, same rule.
#[test]
fn permuted_operation_return_is_refused() {
    assert_refused(
        r#"
namespace test.wi788.opret
  import anthill.prelude.{Int64, String}
  operation mk() -> (a: Int64, b: String) = (b: "ess", a: 3)
  operation drive() -> Int64 = mk().a
end
"#,
        "a permuted tuple returned from an operation",
    );
}

/// Names still take part, so this is NOT a raw positional zip: a POSITIONAL tuple
/// does not conform to a NAMED one of the same component types (proposal 004
/// rule 4 — no subtyping between named and positional).
#[test]
fn positional_tuple_does_not_conform_to_a_named_one() {
    assert_refused(
        r#"
namespace test.wi788.posvsnamed
  import anthill.prelude.{Int64, String}
  operation take(t: (a: Int64, b: String)) -> Int64 = t.a
  operation drive() -> Int64 = take((3, "ess"))
end
"#,
        "a positional tuple against a named tuple type",
    );
}

// ── width subtyping: prefix yes, middle-drop no ────────────────

/// PREFIX width survives. Dropping a TRAILING component leaves every retained
/// component's canonical position unchanged, so `(a: Int64, b: String)` still
/// conforms to `(a: Int64)`.
#[test]
fn width_prefix_still_conforms() {
    let src = r#"
namespace test.wi788.widthok
  import anthill.prelude.{Int64, String}
  operation narrow(t: (a: Int64)) -> Int64 = t.a
  operation drive() -> Int64 = narrow((a: 3, b: "ess"))
end
"#;
    assert_eq!(run_int(src, "test.wi788.widthok.drive"), 3);
}

/// A MIDDLE drop does NOT. Removing `b` renumbers `c` from `_3` to `_2`, which is
/// a different type — the boundary that distinguishes this rule from the looser
/// "expected names appear in order" (subsequence) reading.
#[test]
fn width_middle_drop_is_refused() {
    assert_refused(
        r#"
namespace test.wi788.widthmid
  import anthill.prelude.{Int64, String, Bool}
  operation narrow(t: (a: Int64, c: Bool)) -> Int64 = t.a
  operation drive() -> Int64 = narrow((a: 3, b: "ess", c: true))
end
"#,
        "dropping a MIDDLE component, which renumbers the ones after it",
    );
}

// ── the Function slot checks its arguments at all ──────────────

/// NOT a permutation: the components are in the DECLARED order and merely have
/// the wrong TYPES. Pre-fix this loaded clean and returned `Str("ess")` from
/// `-> Int64`, which is what shows the `Function` slot was checking nothing
/// rather than checking order too loosely.
#[test]
fn function_slot_checks_in_order_argument_types() {
    assert_refused(
        &fn_slot_case(
            "test.wi788.fnslottypes",
            "Int64, String, Function",
            "(a: Int64, b: String)",
            r#"(a: "ess", b: 3)"#,
            "lambda (p, q) -> p",
        ),
        "an in-order tuple with the component types swapped",
    );
}

/// The same hole at its widest: an argument that is not a tuple at all. Pre-fix
/// this loaded clean and trapped in the MATCHER at eval.
#[test]
fn function_slot_checks_a_non_tuple_argument() {
    assert_refused(
        &fn_slot_case(
            "test.wi788.fnslotscalar",
            "Int64, String, Bool, Function",
            "(a: Int64, b: String)",
            "true",
            "lambda (p, q) -> p",
        ),
        "a scalar passed where the function's A is a 2-component tuple",
    );
}

/// WI-775's INTERCHANGEABILITY must survive: a `Function` states no arity, so
/// both application forms stay legal at the slot. This is the invariant that
/// forbids REQUIRING a count here — the check only OBSERVES the count at the call
/// and relates each argument to `A` or to `A`'s components accordingly.
///
/// The whole-tuple half doubles as THE CONTROL for the permutation tests above:
/// the same program written in the DECLARED order loads and computes the
/// declared-order answer, so what those refuse is the permutation, not the shape.
#[test]
fn function_slot_admits_both_application_forms() {
    let ty = "(a: Int64, b: Int64)";
    let lam = "lambda (p, q) -> p - q";
    let whole = fn_slot_case("test.wi788.formwhole", "Int64, Function", ty, "(a: 3, b: 10)", lam);
    let spread = fn_slot_case("test.wi788.formspread", "Int64, Function", ty, "3, 10", lam);
    assert_eq!(run_int(&whole, "test.wi788.formwhole.drive"), -7);
    assert_eq!(run_int(&spread, "test.wi788.formspread.drive"), -7);
}

/// A LABELLED argument at a `Function` slot must report the LABEL, not a count.
/// The count check compares `A`'s components against the POSITIONAL count while
/// the diagnostic renders the TOTAL, so counting labelled arguments produced a
/// self-contradictory "expected … or 2 …, got 2 arguments" AND preempted the
/// accurate error. Found by `/code-review` on this ticket's own change.
#[test]
fn labelled_argument_at_a_function_slot_reports_the_label() {
    let msg = load_errs(&fn_slot_case(
        "test.wi788.fnlabel",
        "Int64, Function",
        "(a: Int64, b: Int64)",
        "a: 1, b: 2",
        "lambda (p, q) -> p - q",
    ))
    .join(" | ");
    assert!(
        msg.contains("named argument"),
        "a label at a `Function` slot must be reported as a label; got: {msg}",
    );
    assert!(
        !msg.contains("got 2 arguments"),
        "must NOT report a count that equals the expected count — the \
         expected-X-got-X shape this check reintroduced; got: {msg}",
    );
}

/// PREFIX width stops short of the unit type. `()` has exactly one value, which a
/// 2-component tuple is not — but an empty expected list zips to nothing and every
/// name test passes vacuously, so this conformed and then trapped at eval against
/// a nullary pattern. Also found by `/code-review` here.
#[test]
fn a_wider_tuple_does_not_conform_to_unit() {
    assert_refused(
        r#"
namespace test.wi788.unitwidth
  import anthill.prelude.{Int64, String}
  operation takeUnit(t: ()) -> Int64 = 1
  operation drive() -> Int64 = takeUnit((a: 3, b: "ess"))
end
"#,
        "a 2-component tuple against the unit type",
    );
}

/// The CONTROL for the guard above: unit still relates to unit, so a nullary
/// thunk keeps working. The guard must refuse a WIDER tuple, not empty-vs-empty.
#[test]
fn nullary_thunk_still_applies() {
    let src = r#"
namespace test.wi788.nullary
  import anthill.prelude.{Int64, Function}
  operation force(f: Function[A = (), B = Int64]) -> Int64
    = f()
  operation drive() -> Int64 = force(lambda () -> 5)
end
"#;
    assert_eq!(run_int(src, "test.wi788.nullary.drive"), 5);
}

/// A spread call whose count cannot match `A`'s components is refused at LOAD,
/// with both counts named. No arity is REQUIRED of the `Function` — the whole-
/// tuple form remains legal, which is why the diagnostic offers both.
#[test]
fn function_slot_refuses_an_unspreadable_argument_count() {
    let errs = load_errs(
        r#"
namespace test.wi788.spreadcount
  import anthill.prelude.{Int64, Function}
  operation ap(f: Function[A = (a: Int64, b: Int64), B = Int64]) -> Int64
    = f(1, 2, 3)
  operation drive() -> Int64
    = ap(lambda (p, q) -> p - q)
end
"#,
    );
    let msg = errs.join(" | ");
    assert!(
        msg.contains("2") && msg.contains("3"),
        "the diagnostic must name A's component count (2) and the supplied count (3); \
         got: {msg}",
    );
}
