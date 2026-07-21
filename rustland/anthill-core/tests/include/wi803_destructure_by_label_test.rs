//! WI-803 — destructuring binds by LABEL, and data-tuple `<:` drops the order
//! interim.
//!
//! This is the ticket WI-788 was really about. WI-788 found a permuted tuple
//! literal type-checking by NAME while a destructuring binder list read the value
//! by SLOT, so an operation declared `-> Int64` returned a `String` on a clean
//! load. It fixed the RELATION — component order became part of a tuple's type
//! identity at every position — and the pre-WI-788 spec had already said that was
//! the wrong half: "Permutation and width are subtyping rules for data tuples
//! whose components are read by NAME … (A data tuple read by DESTRUCTURING is
//! also positional; aligning such a reader by name is a known open defect)."
//! WI-804 restored name-keyed width and recorded the remaining order requirement
//! as an explicit INTERIM. This ticket fixes the READER and retires the interim.
//!
//! The reader now binds by label: `extend_env_from_pattern` (kb/typing.rs) records
//! WHICH component name each binder takes, read off the pattern's expected
//! named-tuple type into `Pattern::Tuple.labels`, and `match_tuple_pattern`
//! (eval/pattern.rs) fetches that component by name instead of by slot — through
//! `TupleComponents::by_label`, the same reader `t.x` uses, so the relation and
//! the two readers cannot disagree.
//!
//! WHY THE READER AND NOT THE RELATION, which WI-788 established by measurement:
//! "align by the consumer's read discipline" is not decidable at the site that
//! admits the permutation, because the value flows through a `Function[A, B]`
//! PARAMETER to a consumer chosen at a DIFFERENT call site (`ap(lambda (p, q) -> p)`
//! versus `ap(lambda t -> t.a)`). A by-label fetch needs no such knowledge — it is
//! correct for whichever reader turns up.
//!
//! Order remains a tuple's IDENTITY (`TupleAlign::EQUALITY`, and a parameter list
//! under `TupleAlign::PARAM_LIST`); what changed is only that `<:` between DATA
//! tuples no longer carries the rule across. `identity_*` below pins that split.

use crate::common::{interp_for, try_load_kb_with};

fn load_errs(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

fn assert_loads(src: &str, what: &str) {
    let errs = load_errs(src);
    assert!(errs.is_empty(), "{what} must load; got: {errs:?}");
}

fn assert_refused(src: &str, what: &str) {
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("mismatch")),
        "{what} must be refused at load with a type mismatch; got: {errs:?}",
    );
}

/// Drive `op` and expect an `Int64`. A FRESH interpreter per call — reusing one
/// after a trapped call returns a bogus `Internal` on every later call.
fn run_int(src: &str, op: &str) -> i64 {
    let mut interp = interp_for(src);
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// `ap(f) = f(<lit>)` over a `Function[A = <ty>, B = Int64]`, driven with `<lam>`.
/// The same builder `wi788_tuple_component_order_identity_test` uses, so the
/// programs there and here are comparable line for line.
fn fn_slot_case(ns: &str, imports: &str, ty: &str, lit: &str, lam: &str) -> String {
    crate::common::function_slot_case(ns, imports, ty, lit, lam)
}

// ── THE HEADLINE REPRO, driven end-to-end ──────────────────────

/// THE program this cluster has been about since WI-788. Before WI-788 it loaded
/// clean and returned `Str("ess")` from an operation declared `-> Int64`; WI-788
/// refused it at load; now it loads AND returns 3 — the `Int64` component, which
/// is the one the typer typed `p` from.
///
/// That is the acceptance criterion in full: the answer, not merely the absence of
/// an error.
#[test]
fn permuted_literal_at_a_function_slot_binds_by_label() {
    let src = fn_slot_case(
        "test.wi803.headline",
        "Int64, String, Function",
        "(a: Int64, b: String)",
        r#"(b: "ess", a: 3)"#,
        "lambda (p, q) -> p",
    );
    assert_loads(&src, "a permuted literal at a Function slot");
    assert_eq!(
        run_int(&src, "test.wi803.headline.drive"),
        3,
        "`p` takes the DECLARED first component `a`, whatever slot the literal put it in",
    );
}

/// The ALL-Int64 variant, which carries no type signal at all — every component
/// type matches, so nothing downstream could ever have noticed a swap. Declared
/// `(a, b)` with the literal written `(b: 10, a: 3)`, so `p - q` is `3 - 10`.
///
/// This is the case that pins the fix as a REORDERING and not merely a
/// type-agreement check: with types alone there is nothing to check.
#[test]
fn permuted_literal_with_uniform_types_binds_by_label() {
    let src = fn_slot_case(
        "test.wi803.uniform",
        "Int64, Function",
        "(a: Int64, b: Int64)",
        "(b: 10, a: 3)",
        "lambda (p, q) -> p - q",
    );
    assert_loads(&src, "a permuted all-Int64 literal");
    assert_eq!(
        run_int(&src, "test.wi803.uniform.drive"),
        -7,
        "declared order (a, b) means p=3, q=10 — the source order (b, a) would give 7",
    );
}

/// A three-component scramble, so the fix cannot be a two-element swap.
/// Declared `(a, b, c)`, written `(c: 3, a: 1, b: 2)`; `p*100 + q*10 + r` is 123
/// by declared order and would be 312 read by slot.
#[test]
fn three_component_scramble_binds_by_label() {
    let src = fn_slot_case(
        "test.wi803.scramble",
        "Int64, Function",
        "(a: Int64, b: Int64, c: Int64)",
        "(c: 3, a: 1, b: 2)",
        "lambda (p, q, r) -> p * 100 + q * 10 + r",
    );
    assert_loads(&src, "a three-component scramble");
    assert_eq!(run_int(&src, "test.wi803.scramble.drive"), 123);
}

// ── every destructuring form, not just the lambda ──────────────

/// `let (p, q) = …` over a permuted value. The three surface forms reach
/// `extend_env_from_pattern` through three DIFFERENT typer frames
/// (`LambdaBody`, `LetFinal`, `MatchFinal`), and each has to thread the relabelled
/// pattern into its own `reassemble` — a frame that dropped it would leave that
/// form silently binding by slot while the other two were fixed.
#[test]
fn let_destructuring_binds_by_label() {
    let src = r#"
namespace test.wi803.letform
  import anthill.prelude.{Int64}
  operation mk() -> (a: Int64, b: Int64) = (b: 10, a: 3)
  operation drive() -> Int64 =
    let (p, q) = mk()
    p - q
end
"#;
    assert_loads(src, "a permuted value destructured by let");
    assert_eq!(run_int(src, "test.wi803.letform.drive"), -7);
}

/// `case (p, q) ->` over a permuted value — the `MatchFinal` frame's half.
#[test]
fn match_case_destructuring_binds_by_label() {
    let src = r#"
namespace test.wi803.matchform
  import anthill.prelude.{Int64}
  operation mk() -> (a: Int64, b: Int64) = (b: 10, a: 3)
  operation drive() -> Int64 =
    match mk()
      case (p, q) -> p - q
end
"#;
    assert_loads(src, "a permuted value destructured by a match case");
    assert_eq!(run_int(src, "test.wi803.matchform.drive"), -7);
}

/// A tuple binder list NESTED inside a constructor pattern
/// (`case some((p, q)) ->`). The constructor arm of `extend_env_from_pattern`
/// recurses, so it too has to reassemble from the relabelled sub-patterns rather
/// than passing the written ones through.
#[test]
fn nested_tuple_pattern_under_a_constructor_binds_by_label() {
    let src = r#"
namespace test.wi803.nested
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}
  operation mk() -> Option[T = (a: Int64, b: Int64)] = some((b: 10, a: 3))
  operation drive() -> Int64 =
    match mk()
      case some((p, q)) -> p - q
      case none() -> 0
end
"#;
    assert_loads(src, "a permuted value destructured under a constructor pattern");
    assert_eq!(run_int(src, "test.wi803.nested.drive"), -7);
}

// ── width reaches the destructuring reader now ─────────────────

/// WIDTH plus PERMUTATION together. `(c: 9, b: "ess", a: 3)` conforms to
/// `(a: Int64, b: String)` — `c` dropped from the FRONT, `a` and `b` swapped —
/// and the binder list still gets `a` and `b`.
///
/// Under WI-804's interim this was refused for the permutation. Under WI-788 it
/// was refused twice over. A by-label fetch does not care about either.
#[test]
fn width_and_permutation_together_bind_by_label() {
    let src = fn_slot_case(
        "test.wi803.widthperm",
        "Int64, String, Function",
        "(a: Int64, b: String)",
        r#"(c: 9, b: "ess", a: 3)"#,
        "lambda (p, q) -> p",
    );
    assert_loads(&src, "a wider AND permuted literal");
    assert_eq!(run_int(&src, "test.wi803.widthperm.drive"), 3);
}

/// WIDTH ALONE at a destructuring binder list. This is the half WI-804 admitted
/// in the RELATION while knowing it broke the READER: the extra component changes
/// the binder COUNT, so the old positional matcher failed its arity test and
/// raised. It was tolerated because it failed LOUDLY rather than silently.
///
/// A by-label fetch ignores components it was not asked for, so the loud half
/// retires with the silent one and the program simply runs.
#[test]
fn width_alone_no_longer_traps_the_binder_list() {
    let src = fn_slot_case(
        "test.wi803.widthonly",
        "Int64, Function",
        "(a: Int64, b: Int64)",
        "(a: 3, b: 10, c: 99)",
        "lambda (p, q) -> p - q",
    );
    assert_loads(&src, "a wider in-order literal");
    assert_eq!(
        run_int(&src, "test.wi803.widthonly.drive"),
        -7,
        "the unasked-for `c` is not observed — pre-WI-803 this raised on the binder count",
    );
}

// ── what did NOT change: order is still IDENTITY ───────────────

/// A PARAMETER LIST still refuses a permutation (`TupleAlign::PARAM_LIST`). It is
/// applied POSITIONALLY by eval — there is no label to fetch by — so this is not
/// an interim like the data-tuple rule was, it is the rule.
#[test]
fn identity_permuted_parameter_list_is_still_refused() {
    let src = r#"
namespace test.wi803.paramlist
  import anthill.prelude.{Int64, Bool}
  operation impl_yx(y: Bool, x: Int64) -> Int64 = x
  operation take(f: (x: Int64, y: Bool) -> Int64) -> Int64 = f(7, true)
  operation drive() -> Int64 = take(impl_yx)
end
"#;
    assert_refused(src, "a permuted PARAMETER LIST");
}

/// A positional tuple still does not conform to a named one — names participate,
/// so this is not a raw by-name free-for-all (proposal 004 rule 4).
#[test]
fn identity_positional_tuple_does_not_conform_to_a_named_one() {
    let src = fn_slot_case(
        "test.wi803.posnamed",
        "Int64, Function",
        "(a: Int64, b: Int64)",
        "(3, 10)",
        "lambda (p, q) -> p - q",
    );
    assert_refused(&src, "a POSITIONAL literal against a NAMED tuple type");
}

/// A positional tuple destructures positionally, as it always did: its labels are
/// the synthetic `_1.._n`, whose order IS the positional order, so the by-label
/// fetch and the by-slot read agree by construction.
#[test]
fn identity_positional_tuple_still_binds_in_order() {
    let src = fn_slot_case(
        "test.wi803.positional",
        "Int64, Function",
        "(Int64, Int64)",
        "(3, 10)",
        "lambda (p, q) -> p - q",
    );
    assert_loads(&src, "a positional literal against a positional tuple type");
    assert_eq!(run_int(&src, "test.wi803.positional.drive"), -7);
}

/// Component ACCESS was already name-keyed and order-independent (WI-638), and
/// still is. This is the reader that made the by-name relation look sound in the
/// first place; it is now reached through the same `by_label` owner the matcher
/// uses.
#[test]
fn identity_field_access_stays_name_keyed() {
    let src = r#"
namespace test.wi803.access
  import anthill.prelude.{Int64, String}
  operation take(t: (a: Int64, b: String)) -> Int64 = t.a
  operation drive() -> Int64 = take((b: "ess", a: 3))
end
"#;
    assert_loads(src, "a permuted argument read by name");
    assert_eq!(run_int(src, "test.wi803.access.drive"), 3);
}

// ── the arity guard the positional path still owns ─────────────

/// A binder list whose COUNT disagrees with the tuple it is typed against is
/// still refused — and, since WI-801, at LOAD rather than at the match. Two
/// binders over a 3-component `A` names neither the whole argument (1) nor its
/// components spread (3).
///
/// What this pins for WI-803 is that the by-label read did not swallow the
/// disagreement. It easily could have: a by-label fetch ignores components it was
/// not asked for, so had `extend_env_from_pattern` recorded labels for a
/// mismatched list, `p` and `q` would have quietly taken `a` and `b` and the
/// extra `c` would have gone unnoticed — an accepted program where there had been
/// a loud one. Labels are recorded only at EQUAL arity precisely to leave this
/// case to the checks that own it.
#[test]
fn arity_mismatch_is_still_refused_and_not_swallowed_by_the_label_read() {
    let src = r#"
namespace test.wi803.arity
  import anthill.prelude.{Int64, Function}
  operation ap(f: Function[A = (a: Int64, b: Int64, c: Int64), B = Int64]) -> Int64
    = f((a: 1, b: 2, c: 3))
  operation drive() -> Int64 = ap(lambda (p, q) -> p - q)
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("1 parameter") && e.contains("2 parameters")),
        "the diagnostic must name the binder count against the component count, \
         not accept the shape; got: {errs:?}",
    );
}

/// The same disagreement where no type resolves the labels, so the POSITIONAL
/// path and its COUNT test are the only guard. `mk`'s declared 3-component return
/// meets a 2-binder `let`, which is refused before it can bind two of the three.
#[test]
fn arity_mismatch_without_a_function_slot_is_refused_too() {
    let src = r#"
namespace test.wi803.arity2
  import anthill.prelude.{Int64}
  operation mk() -> (a: Int64, b: Int64, c: Int64) = (a: 1, b: 2, c: 3)
  operation drive() -> Int64 =
    let (p, q) = mk()
    p - q
end
"#;
    let errs = load_errs(src);
    if errs.is_empty() {
        let mut interp = interp_for(src);
        let result = interp.call("test.wi803.arity2.drive", &[]);
        assert!(
            result.is_err(),
            "a 2-binder let over a 3-component tuple must raise, not silently bind \
             two of the three; got {result:?}",
        );
    }
}

// ── the duplicate-label disagreement, closed as a side effect ──

/// WI-805's program. `(a: 1, b: 2, a: "ess")` used to conform to
/// `(b: Int64, a: String)` because the relation's cursor resumed AFTER the `b`
/// match and so took the SECOND `a` (a `String`), while `t.a` read the FIRST
/// (an `Int64`) — an operation declared `-> String` returned `Int(1)` on a clean
/// load.
///
/// The `TupleOrder::Free` walk looks each name up from the START, which is
/// `field_access`' own rule, so the relation and the reader now pick the same
/// component and the program is REFUSED. Recorded here as the observable it is:
/// WI-805's own fix — refusing a duplicate label where the tuple is BUILT — is a
/// separate and still-open ticket, and this test does not stand in for it.
#[test]
fn duplicate_label_no_longer_conforms_on_the_second_occurrence() {
    let src = r#"
namespace test.wi803.dup
  import anthill.prelude.{Int64, String}
  operation take(t: (b: Int64, a: String)) -> String = t.a
  operation drive() -> String = take((a: 1, b: 2, a: "ess"))
end
"#;
    assert_refused(
        src,
        "a duplicate-label tuple whose FIRST `a` is the one `t.a` reads",
    );
}

// ── the three holes /code-review found in the first cut ────────

// NOTE on where the SYNTHETIC-LABEL and QUALIFIED-LABEL guards are pinned, and
// why not here. Both were added after a /code-review of the first cut, and the
// end-to-end fixtures written for them were CONTROL-RUN with each guard removed
// and PASSED — they were blind:
//
//  * synthetic labels only reach the by-label reader when the VALUE is name-keyed
//    while the expected TYPE is a positional tuple, and proposal 004 rule 4 keeps
//    those apart in any program spellable here (an all-named relation row is the
//    shape that makes it reachable in principle);
//  * a QUALIFIED `_N` label needs a tuple type whose field symbols intern
//    qualified, which nothing in this corpus produces.
//
// Both are therefore DEFENSIVE, and are pinned at the reader instead, in
// `eval::value::tests::wi803_by_label_reader` — which does discriminate
// (control-run: the qualified-label test fails against the raw-label version). A
// blind end-to-end test asserting neither was deleted rather than kept for
// appearances; `identity_positional_tuple_still_binds_in_order` above already
// covers the ordinary positional path.

/// A tuple type whose components carry the SAME name must not serve one component
/// to two binders.
///
/// By-label resolution takes the FIRST match, so without a double-cover guard both
/// binders receive component `a`'s first occurrence — while the component the
/// SECOND binder was TYPED from goes unread. The typer types `q` from the second
/// `a` (a `String`), so a matcher that hands it the first (an `Int64`) produces a
/// wrong-TYPED value from an operation declared `-> String`: the WI-788 family
/// again, reached through duplicate labels rather than order.
///
/// `match_constructor_pattern` has guarded double cover since WI-445; the by-label
/// tuple arm did not until /code-review found it.
///
/// NOTE the fixture is `-> q`, not `-> p`. An earlier version of this test drove
/// `-> p` and asserted `is_err() || Ok(Int(3))` — which the BUGGY matcher also
/// satisfies, since `p` legitimately takes the first `a`. Control-run with the
/// guard removed, it passed. Only the SECOND binder can observe the collision.
#[test]
fn duplicate_component_names_do_not_bind_one_component_twice() {
    let src = r#"
namespace test.wi803.dupty
  import anthill.prelude.{Int64, String, Function}
  operation ap(f: Function[A = (a: Int64, a: String), B = String]) -> String
    = f((a: 3, a: "ess"))
  operation drive() -> String = ap(lambda (p, q) -> q)
end
"#;
    assert!(
        load_errs(src).is_empty(),
        "the duplicate-label TYPE loads today — refusing it where the tuple is \
         BUILT is WI-805, still open; got: {:?}",
        load_errs(src),
    );
    let mut interp = interp_for(src);
    match interp.call("test.wi803.dupty.drive", &[]) {
        // The loud outcome: `q`'s label resolves to the component `p` already
        // took, so the match is refused rather than binding one component twice.
        Err(_) => {}
        Ok(anthill_core::eval::Value::Str(_)) => {}
        other => panic!(
            "an operation declared `-> String` must not yield a non-String: `q` was \
             typed from the SECOND `a` and must not be handed the first. Got: {other:?}",
        ),
    }
}

/// The by-label reader resolves a label by SHORT name, so it must normalize BOTH
/// sides consistently — including on the synthetic `_N` branch.
///
/// The first cut normalized the component side and passed the RAW label to the
/// `_N` reader, justifying the normalization on the grounds that a label read off
/// a TYPE's field list can arrive qualified. If that is true it is true of a
/// positional tuple's `_N` fields too, so the two branches disagreed. This drives
/// a positional tuple through both readers (`t._1` field access and a binder list)
/// and requires them to agree.
#[test]
fn positional_component_resolves_the_same_by_access_and_by_destructuring() {
    let src = r#"
namespace test.wi803.posagree
  import anthill.prelude.{Int64}
  operation mk() -> (Int64, Int64) = (3, 10)
  operation by_access() -> Int64 = mk()._1
  operation by_destructure() -> Int64 =
    let (p, q) = mk()
    p
end
"#;
    assert_loads(src, "a positional tuple read both ways");
    assert_eq!(run_int(src, "test.wi803.posagree.by_access"), 3);
    assert_eq!(
        run_int(src, "test.wi803.posagree.by_destructure"),
        3,
        "`t._1` and the first binder must name the same component",
    );
}
