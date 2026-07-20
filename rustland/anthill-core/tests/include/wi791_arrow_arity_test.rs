//! WI-791 — an arrow records its PARAMETER-LIST ARITY, so a one-tuple-parameter
//! operation is no longer the same type as an n-parameter one.
//!
//! An arity-1 parameter list collapsed to its parameter's bare type, so
//! `(t: (a: A, b: B)) -> R` and `(a: A, b: B) -> R` built the IDENTICAL term.
//! Each was accepted where the other was required, and the program then trapped
//! at eval — the load-clean-then-trap shape WI-782 exists to remove, left open
//! there as its case 3.
//!
//! THE FIX is one ground child on the arrow: `arity`. That placement is the
//! whole lesson. WI-782 first tried the encoding INSIDE the param slot (wrap an
//! arity-1 list whose parameter is itself a tuple) and reverted it: the wrap was
//! decided from the SPELLING at mint time but read back AFTER substitution, so a
//! type variable bound to the slot picked it up and `apply1(get_a, (a: 1, b: 2))`
//! — a working program — broke. A count sibling is not a type σ acts on, so
//! substitution can neither introduce nor erase it. `type_parameter_instantiated
//! _at_a_tuple_still_applies` below is that exact program, kept green.
//!
//! Recording arity also settles WHICH RELATION the param slot gets, which is
//! what repays the cost WI-782 knowingly paid:
//!
//!   * arity ≠ 1 — the slot IS the parameter list, applied positionally: equal
//!     arity, index zip, no permutation and no width (WI-782's rules, unchanged;
//!     they live in `wi782_param_list_alignment_test.rs`);
//!   * arity 1 — the slot is the sole parameter's TYPE. A tuple there is DATA,
//!     read by name, so a permuted or narrower one conforms again (the two
//!     `*_tuple_typed_parameter_still_applies` tests in that same file).
//!
//! Every rejection below is paired with a neighbouring program that must still
//! load AND EVALUATE — a fix that merely rejected more would satisfy the
//! rejections alone. All of them were measured on the parent commit in an
//! isolated worktree: the five rejections all loaded clean there and trapped (or,
//! for `two_parameter_operation_is_refused_for_a_tuple_argument_arrow`, evaluated
//! through eval's tuple-spread), and every control already passed.

use crate::common::{interp_for, load_kb_with, try_load_kb_with};

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// Assert the program is refused AND that the diagnostic names both arrow
/// spellings adjacently, in the loader's own `expected …, got …` phrasing.
///
/// Pinning the exact text matters more here than elsewhere: before WI-791 the
/// two spellings RENDERED IDENTICALLY, so a message-agnostic assertion would
/// pass on a fix that rejected the program while still reporting
/// `expected (a: Int64, b: Int64) -> Int64, got (a: Int64, b: Int64) -> Int64`
/// — restating the confusion it is reporting. The extra parens in the expected
/// text are the one-tuple-parameter spelling.
fn assert_refused_naming(src: &str, expected: &str, got: &str) {
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!(
            "must NOT load: `{got}` and `{expected}` take a different number of parameters"
        ),
        Err(errs) => errs,
    };
    let wanted = format!("expected {expected}, got {got}");
    assert!(
        errs.iter().any(|e| e.contains("type mismatch") && e.contains(&wanted)),
        "rejection must be a type mismatch reading `{wanted}`; got: {errs:?}",
    );
}

// ── the ticket's two repros ────────────────────────────────────

/// REPRO 1. `get_a` takes ONE tuple-typed parameter; the annotation declares TWO
/// parameters. Measured on the parent commit: loaded clean, then trapped
/// `Internal("field_access: tuple has no component 'a'")` — `f((7, 8))` passed
/// the positional pair as the single tuple `t`, whose components are `_1`/`_2`,
/// so `t.a` found nothing.
#[test]
fn one_tuple_parameter_operation_is_refused_for_a_two_parameter_arrow() {
    assert_refused_naming(
        r#"
namespace test.wi791.repro1
  import anthill.prelude.{Int64}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = let f: (_1: Int64, _2: Int64) -> Int64 = get_a
      f((7, 8))
end
"#,
        "(_1: Int64, _2: Int64) -> Int64",
        "((a: Int64, b: Int64)) -> Int64",
    );
}

/// REPRO 2, the DUAL. A 2-parameter operation into a one-tuple-parameter
/// annotation. Measured on the parent commit: loaded clean, then trapped
/// `ArityMismatch { expected: 2, got: 1 }`.
#[test]
fn two_parameter_operation_is_refused_for_a_one_tuple_parameter_arrow() {
    assert_refused_naming(
        r#"
namespace test.wi791.repro2
  import anthill.prelude.{Int64}
  operation two(a: Int64, b: Int64) -> Int64
    = a - b
  operation drive() -> Int64
    = let f: (t: (a: Int64, b: Int64)) -> Int64 = two
      f((a: 7, b: 8))
end
"#,
        "((a: Int64, b: Int64)) -> Int64",
        "(_1: Int64, _2: Int64) -> Int64",
    );
}

// ── the two spellings WI-782's name gate could not catch ───────

/// BYPASS 1, the IDIOMATIC spelling. A positionally-written tuple type mints its
/// components `_1, _2` (`intern_positional_label`), which is exactly the
/// synthetic shape WI-782's admissibility gate ADMITS — so the shorter and more
/// common way to write a 2-parameter callback disarmed the gate. Measured on the
/// parent commit: loaded clean, trapped `ArityMismatch { expected: 1, got: 2 }`.
/// It is not refused by a better name test; it is refused because 1 ≠ 2.
#[test]
fn positionally_spelled_two_parameter_callback_is_refused() {
    assert_refused_naming(
        r#"
namespace test.wi791.bypass1
  import anthill.prelude.{Int64}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation take2(f: (Int64, Int64) -> Int64) -> Int64
    = f(1, 2)
  operation drive() -> Int64
    = take2(get_a)
end
"#,
        "(_1: Int64, _2: Int64) -> Int64",
        "((a: Int64, b: Int64)) -> Int64",
    );
}

/// BYPASS 2, LEADING ZEROS. `parse::<usize>()` accepts `_01`, so the gate read
/// `(_01: Int64, _02: Int64)` as the synthetic convention and admitted the zip —
/// while eval's `is_synthetic_positional_label` calls `_01` a USER label
/// (WI-786's `leading_zero_label_is_not_synthetic`), the cross-boundary
/// divergence WI-789/WI-790 predict. Measured on the parent commit: loaded
/// clean, trapped `ArityMismatch { expected: 1, got: 2 }`.
///
/// The divergence itself is NOT fixed here and does not need to be: this refusal
/// never consults a name. That is the point — the gate stopped being what decides
/// whether a tuple is a parameter list.
#[test]
fn leading_zero_component_names_do_not_make_a_parameter_list() {
    assert_refused_naming(
        r#"
namespace test.wi791.bypass2
  import anthill.prelude.{Int64}
  operation get_a(t: (_01: Int64, _02: Int64)) -> Int64
    = t._01
  operation take2(f: (p: Int64, q: Int64) -> Int64) -> Int64
    = f(1, 2)
  operation drive() -> Int64
    = take2(get_a)
end
"#,
        "(p: Int64, q: Int64) -> Int64",
        "((_01: Int64, _02: Int64)) -> Int64",
    );
}

/// The BEHAVIOR CHANGE this fix knowingly makes, pinned so it is a decision
/// rather than a surprise. Measured on the parent commit, this LOADED and
/// EVALUATED to -1: eval's `spread_eta_args` spreads a single POSITIONAL tuple
/// argument across a multi-parameter operation (the WI-275 convention), so
/// `f((10, 3))` reached `minus(10, 3)`.
///
/// It is refused now because the two types genuinely differ — `((Int64, Int64))
/// -> Int64` takes one tuple, `minus` takes two scalars — and because accepting
/// it is the SAME relation as repro 2 above, which the ticket requires refusing.
/// The two only looked different: repro 2 trapped solely because its tuple is
/// NAME-keyed and so has nothing in `.pos` for the spread to find. Leaving the
/// relation to depend on how a caller happens to build its tuple is the
/// incoherence this ticket removes.
///
/// The spread convention itself is untouched and still reachable — through the
/// `Function` spelling (see `function_spelling_states_no_arity_and_still_bridges`)
/// and through a direct positional call.
#[test]
fn two_parameter_operation_is_refused_for_a_tuple_argument_arrow() {
    assert_refused_naming(
        r#"
namespace test.wi791.spread
  import anthill.prelude.{Int64}
  operation minus(a: Int64, b: Int64) -> Int64
    = a - b
  operation take(f: ((Int64, Int64)) -> Int64) -> Int64
    = f((10, 3))
  operation drive() -> Int64
    = take(minus)
end
"#,
        "((_1: Int64, _2: Int64)) -> Int64",
        "(_1: Int64, _2: Int64) -> Int64",
    );
}

// ── what must keep working ─────────────────────────────────────

/// THE program the reverted in-slot encoding broke, and the reason `arity` is a
/// sibling of `param` rather than something inside it. `apply1`'s callback slot
/// is written `(x: T) -> Int64`, so its arity is 1 at the mint and stays 1 after
/// `T := (a: Int64, b: Int64)`; the sibling `v: T` therefore still sees the plain
/// tuple. Under the wrapper, `T` bound to the WRAPPED param and `v` was rejected
/// with `expected (_1: (a: Int64, b: Int64)), got (a: Int64, b: Int64)`.
#[test]
fn type_parameter_instantiated_at_a_tuple_still_applies() {
    let src = r#"
namespace test.wi791.typaram
  import anthill.prelude.{Int64}
  operation apply1[T](f: (x: T) -> Int64, v: T) -> Int64
    = f(v)
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = apply1(get_a, (a: 7, b: 8))
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi791.typaram.drive"), 7);
}

/// The same generic shape in the MULTI-parameter direction: a 2-parameter
/// callback slot taking a 2-parameter operation, driven to a value. Without this,
/// a fix that refused every generic callback would pass the test above.
#[test]
fn generic_two_parameter_callback_still_applies() {
    let src = r#"
namespace test.wi791.generic2
  import anthill.prelude.{Int64}
  operation apply2[T](f: (x: T, y: T) -> Int64, v: T, w: T) -> Int64
    = f(v, w)
  operation minus(a: Int64, b: Int64) -> Int64
    = a - b
  operation drive() -> Int64
    = apply2(minus, 10, 3)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi791.generic2.drive"), 7);
}

/// A one-tuple-parameter arrow APPLIED, so the spelling this ticket makes
/// distinct is shown to be usable and not merely rejectable. `get_a` reads `t.a`,
/// so this also proves the tuple reaching the callee is NAME-keyed.
#[test]
fn one_tuple_parameter_arrow_applies_end_to_end() {
    let src = r#"
namespace test.wi791.onetuple
  import anthill.prelude.{Int64}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = let f: ((a: Int64, b: Int64)) -> Int64 = get_a
      f((a: 7, b: 8))
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi791.onetuple.drive"), 7);
}

/// WHY there is no arity check on the `arrow`-vs-`Function` arm, shown rather
/// than asserted in a comment. `Function[A, B, E]` states no arity and cannot:
/// its `A` is the ONE argument `apply(f, x: A)` passes, yet `Function[(T, T), R]`
/// has ALSO denoted a 2-parameter operation's eta arrow since WI-775 — which is
/// what this drives. Demanding arity 1 of the arrow side would break it;
/// demanding a MATCH would need a count `Function` does not have.
///
/// Contrast `two_parameter_operation_is_refused_for_a_tuple_argument_arrow`: the
/// same program in the ARROW spelling is refused. That residual disagreement
/// between the two spellings is recorded in the spec's `Function` note.
#[test]
fn function_spelling_states_no_arity_and_still_bridges() {
    let src = r#"
namespace test.wi791.fnspelling
  import anthill.prelude.{Int64, Function}
  operation minus(a: Int64, b: Int64) -> Int64
    = a - b
  operation take(f: Function[A = (Int64, Int64), B = Int64]) -> Int64
    = f((10, 3))
  operation drive() -> Int64
    = take(minus)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi791.fnspelling.drive"), 7);
}

// ── the representation, observed through the printer ───────────

/// The two spellings must PRINT differently, and each printing must reparse to
/// the arrow it came from. Both halves are load-bearing:
///
///   * DISTINCT — the diagnostics above depend on it, and before WI-791 both
///     rendered `(a: Int64, b: Int64) -> Int64`;
///   * STABLE — the reverted in-slot encoding gained a wrapper layer per
///     print/reparse round until the third generation no longer parsed. Here the
///     wrap is decided by `arity`, and reparsing `((a: Int64, b: Int64)) -> R`
///     yields a ONE-parameter list again, so nothing accumulates. The test does a
///     full second generation to say so rather than assert it.
#[test]
fn the_two_arrow_spellings_print_distinctly_and_round_trip() {
    fn printed_params(src: &str) -> Vec<String> {
        let kb = load_kb_with(src);
        ["test.wi791.print.one", "test.wi791.print.two"]
            .iter()
            .map(|name| {
                let sym = kb.try_resolve_symbol(name).expect("op symbol");
                let info = anthill_core::kb::op_info::lookup_operation_info(&kb, sym)
                    .expect("op info");
                let (_, ty) = info.params.first().expect("callback param");
                match ty {
                    anthill_core::eval::Value::Term { id, .. } => {
                        anthill_core::persistence::print::TermPrinter::new(&kb).print_term(*id)
                    }
                    other => panic!("callback param should be a ground type, got {other:?}"),
                }
            })
            .collect()
    }

    // `one` takes a callback of ONE tuple-typed parameter; `two` takes a callback
    // of TWO parameters. Same components, different arity.
    let gen1 = printed_params(
        r#"
namespace test.wi791.print
  import anthill.prelude.{Int64}
  operation one(f: ((a: Int64, b: Int64)) -> Int64) -> Int64
    = f((a: 1, b: 2))
  operation two(f: (a: Int64, b: Int64) -> Int64) -> Int64
    = f(1, 2)
end
"#,
    );
    assert_eq!(
        gen1,
        vec!["((a: Int64, b: Int64)) -> Int64", "(a: Int64, b: Int64) -> Int64"],
        "the one-tuple-parameter and two-parameter spellings must render differently",
    );

    // Second generation: feed each printing back through the parser in the same
    // position and print again. Identical output ⇒ the encoding is a fixpoint.
    let gen2 = printed_params(&format!(
        r#"
namespace test.wi791.print
  import anthill.prelude.{{Int64}}
  operation one(f: {}) -> Int64
    = f((a: 1, b: 2))
  operation two(f: {}) -> Int64
    = f(1, 2)
end
"#,
        gen1[0], gen1[1]
    ));
    assert_eq!(gen2, gen1, "printing must be a fixpoint — no layer may accumulate");
}

// ── a KNOWN GAP this ticket does not close, pinned ─────────────

/// A callback argument to a TYPE-PARAMETERIZED operation is not conformance-
/// checked at all, so an arity mismatch there is still load-clean-then-trap.
/// MEASURED IDENTICAL on the parent commit — this is PRE-EXISTING and is not a
/// hole in the arity child: the same program written non-generically
/// (`positionally_spelled_two_parameter_callback_is_refused`) IS refused.
///
/// TRACKED AS WI-792, as a second locus of the same family — that ticket's own
/// case is the APPLICATION site (calling a function value), this one is the
/// ARGUMENT-PASSING site. When it closes, this test SHOULD fail; replace it with
/// a load-rejection assertion.
///
/// ROOT CAUSE, for whoever closes it: `validate_arg_against_param`
/// (`kb/typing.rs`) gates on `resolved_type_is_ground` for BOTH sides, and a
/// declared `(x: T, y: T) -> Int64` is non-ground while `T` is free, so the full
/// `types_compatible` — where the arity check lives — never runs. The non-ground
/// path delegates to `validate_arrow_param_result`, which checks param and result
/// COMPONENT-WISE and only where each component is itself ground.
///
/// Arity is the one component that check could always decide: it is a ground
/// `Const(Int)` no matter how polymorphic the types are, so the groundness
/// discipline that defers the rest does not apply to it. It is deliberately not
/// done here because it also refuses the DUAL — a 2-parameter op into a generic
/// `(x: T) -> R` slot — which works today only because eval spreads a single
/// POSITIONAL tuple argument. That is the same trade
/// `two_parameter_operation_is_refused_for_a_tuple_argument_arrow` takes at the
/// conformance rung, and it should be a stated decision there rather than a side
/// effect here.
#[test]
fn known_gap_generic_callback_arrow_is_not_conformance_checked() {
    let src = r#"
namespace test.wi791.knowngap
  import anthill.prelude.{Int64}
  operation apply2[T](f: (x: T, y: T) -> Int64, v: T, w: T) -> Int64
    = f(v, w)
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = apply2(get_a, 7, 8)
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "known gap: a generic op's callback arrow is still not checked, so this loads",
    );
    let mut interp = interp_for(src);
    let err = interp
        .call("test.wi791.knowngap.drive", &[])
        .expect_err("known gap: this program is expected to TRAP at eval");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("ArityMismatch"),
        "the gap should surface as the eval-time arity trap; got: {msg}",
    );
}
