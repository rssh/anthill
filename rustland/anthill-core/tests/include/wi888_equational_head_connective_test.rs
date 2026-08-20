//! WI-888 — `<=>` IS THE EQUATIONAL-HEAD CONNECTIVE, AND THE LOADER NOW AGREES.
//!
//! THE DIVERGENCE. kernel-language.md §5.3 said an equational rule's head connective is
//! `<=>` and **not** `=`, and the loader accepted both: `is_equational_head` classifies
//! through `is_equality_connective_functor`, which matches the `eq` symbol OR the
//! `unify` one. Driven across all four (connective × attribute) combinations on one
//! shape (WI-884), the answer tracked the `[simp]` ATTRIBUTE alone — `=` fired, and
//! `<=>` without the tag was dead. The cost was not hypothetical: WI-884 read §5.3,
//! concluded `Bool.ite`'s dead reduction was CAUSED by `bool.anthill` spelling its case
//! laws with `=`, and wrote that into two files before driving refuted it.
//!
//! THE DECISION, AND WHY IT IS THE SPEC THAT STANDS. The three named readers of
//! `is_equality_connective_functor` — the resolver's eq/non-eq candidate triage,
//! `simp_equation_rids`, and WI-139's cite-required unindexing — are INDIFFERENT: each
//! asks a head-SHAPE question that keeps its answer whichever spelling loads, so
//! nothing downstream wanted `=` admitted. What decided it is proposal 049, which is a
//! rule and not a history: §"simp and equational rules: radius-3 migration" says "every
//! `is_equation` rule head migrates `=` → `<=>`", build step 6 is WI-526, and
//! `is_equality_connective_functor`'s own doc records that it matches both "while
//! WI-526's `=`→`<=>` relabel is in flight". WI-526 delivered 40 heads and left 44 in
//! the stdlib. WI-1090 had already moved the same table row one connective over: `===`
//! and `=` are the spec's TEST column, `<=>` alone is the BIND column, and a bodyless
//! `===` head is refused. Accepting `=` from that same row was the last inconsistency.
//!
//! WHAT MOVED: `pratt::EQUATION_FUNCTORS` is `unify` alone, so a bodyless `=` head
//! reaches WI-1090's existing refusal seam; the stdlib's 44 heads and the corpus's
//! fixtures are relabelled; §5.3 states the rule instead of disclaiming it.
//!
//! WHAT DID NOT MOVE, deliberately, and each has a row here:
//!
//!   * the GUARDED `=` equation (`lhs = rhs :- guard`). Proposal 049 draws its
//!     migration boundary at the EMPTY BODY ("the loader's existing `is_equation`
//!     classification"), and WI-526 delivered it that way — `map.anthill:119` writes one
//!     directly beneath its `<=>` siblings. Refusing it would be a second decision.
//!   * `=` in a BODY GOAL, a contract or a constraint. That is where §5.3's
//!     test-vs-bind distinction actually holds, and it is untouched.
//!   * the KB-side `is_equality_connective_functor`, which still answers for `eq`
//!     because WI-139 unindexing reads the head SHAPE and the guarded form still has
//!     that shape. The parse list and the KB predicate are now in CONTAINMENT rather
//!     than equality — pinned by `load::wi888_connective_agreement_tests`.
//!
//! AND ONE DEFECT THE MIGRATION SURFACED, which is why [`a_local_unify_declaration_does_not_capture_the_connective`]
//! is here: `reflect.anthill` declares its own `unify(a: Term, b: Term, kb: KB)`
//! (proposal 049's term-level face), so the three `fact_monotonicity` rules rewritten in
//! that namespace resolved their MINTED connective through the scope ladder to
//! `anthill.reflect.unify` and filed three clauses under a 3-ary reflect operation. They
//! loaded clean and stopped firing. The `=` spelling had worked only because
//! `anthill.reflect` declares no `eq`.
//!
//! THE CONTROLS.
//!
//!   * BACK OUT WI-888 — `EQ_FUNCTOR` back into `pratt::EQUATION_FUNCTORS`. FOUR fail
//!     here: `a_bodyless_eq_head_is_refused_and_names_the_substitute`,
//!     `a_tagged_eq_head_is_refused_for_the_same_reason`,
//!     `a_bodyless_eq_fact_head_is_refused_too`, and
//!     `a_folded_guard_is_still_an_empty_body`. THREE more fail elsewhere, and they are
//!     the rows other tickets carry rather than duplicates of these:
//!     `load::wi888_connective_agreement_tests::eq_is_an_equality_connective_that_does_not_define`
//!     (the two-sides pin), `wi884_sibling_backing_test::the_connective_admits_the_-
//!     equation_and_the_attribute_fires_it` (the inverted four-row matrix) and
//!     `wi902_dot_rule_macro_test::a_unify_spelled_dot_rule_fires_and_an_eq_spelled_-
//!     one_is_refused`. MEASURED, not predicted.
//!   * BACK OUT THE CONNECTIVE OVERRIDE — `remap_functor` delegating to `remap_symbol`
//!     unconditionally. TWO fail:
//!     `a_local_unify_declaration_does_not_capture_the_connective` here, and
//!     `wi666_monotonicity_test::reflection_index_functors_are_constant` — the STDLIB
//!     row, which is the one that says this is not a fixture's problem. Both fail the
//!     way the stdlib did: the load stays clean and the rule does not fire.
//!   * PASS EITHER WAY, BY DESIGN, and each says so at its site:
//!     `a_guarded_eq_head_still_loads` (the boundary WI-888 did not move) and
//!     `an_eq_goal_in_a_rule_body_is_still_a_test` (the position §5.3's distinction is
//!     actually about).

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// One `pick` shape, spelled with whichever connective and attribute a row wants.
fn pick_source(ns: &str, connective: &str, attribute: &str) -> String {
    format!(
        r#"
namespace test.wi888.{ns}
  import anthill.prelude.{{Int64, Bool}}
  sort C
    import anthill.prelude.{{Int64, Bool}}
    operation pick(cond: Bool, then: Int64, else: Int64) -> Int64
    rule pick(true, ?t, ?_) {connective} ?t{attribute}
    operation drive(n: Int64) -> Int64 = pick(true, 10, 20)
  end
end
"#
    )
}

fn refusal_of(src: &str) -> String {
    try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("this source must be refused at load:\n{src}"))
        .join("\n")
}

/// THE REFUSAL, and what it owes the author. Nothing went wrong at run time — this rule
/// FIRED before WI-888 — so the message is not a diagnosis: it is the rule, the reason
/// the spelling moved, and the substitute, named on the author's own subject.
#[test]
fn a_bodyless_eq_head_is_refused_and_names_the_substitute() {
    let msg = refusal_of(&pick_source("bare", "=", ""));
    assert!(
        msg.contains("`pick(…) <=> …`"),
        "the remedy must name the SUBJECT and the substitute spelling, got: {msg}",
    );
    assert!(
        msg.contains("semantic equality TEST"),
        "…and say what `=` is, which is why it cannot head an equation: {msg}",
    );
    // The one thing an author cannot see from here: `===`'s second remedy ("give it a
    // body goal") is WRONG for `=`, because a guarded equation is read by no firing
    // site. A message that offered it would trade a working rule for a dead one.
    assert!(
        msg.contains("Adding a body goal is NOT the alternative"),
        "the `===` remedy must be withheld for `=`: {msg}",
    );
}

/// The `[simp]` tag has NO bearing on the refusal, which is the half a reader of the
/// pre-WI-888 matrix would get backwards: the attribute decided everything there, and
/// it decides nothing here. `reflect.anthill` and `bool.anthill` both shipped this exact
/// combination — `[simp]` on an `=` head — which §5.3 said could not exist.
#[test]
fn a_tagged_eq_head_is_refused_for_the_same_reason() {
    let msg = refusal_of(&pick_source("tagged", "=", " [simp]"));
    assert!(
        msg.contains("`pick(…) <=> …`"),
        "a `[simp]` tag does not admit the spelling: {msg}",
    );
}

/// A FACT is a rule with an empty body (§6.1), so `fact lhs = rhs` is the same
/// refusal one keyword away. WI-1090 found this arm by review after its rule-side
/// refusal shipped alone; WI-888 inherits it by widening the shared reader rather than
/// by remembering the second site.
#[test]
fn a_bodyless_eq_fact_head_is_refused_too() {
    let msg = refusal_of(
        r#"
namespace test.wi888.factform
  import anthill.prelude.Int64
  sort C
    import anthill.prelude.Int64
    entity boxp(v: Int64)
    fact boxp(v: 1) = boxp(v: 2)
  end
end
"#,
    );
    assert!(
        msg.contains("<=>"),
        "a `fact lhs = rhs` is a bodyless head too: {msg}",
    );
}

/// EMPTINESS IS READ AFTER GUARD FOLDING, so a rule whose only body goal was a folded
/// `Spec[T]` bound is a definition here — the same emptiness every equation reader uses.
/// This is the WI-582 typed-pattern spelling, and it is the row most likely to look like
/// an exemption: it is WRITTEN with a `:-`.
#[test]
fn a_folded_guard_is_still_an_empty_body() {
    let msg = refusal_of(
        r#"
namespace test.wi888.folded
  import anthill.prelude.{Int64, Bool, Eq}

  sort Summable
    sort T = ?
    requires Eq[T]
  end

  fact Summable[T = Int64]

  sort Lib
    sort A = ?
    operation keep(x: A, y: A) -> A
    rule keep_id: keep[T](?x: T, ?y) = ?x :- Summable[T] [simp]
  end
end
"#,
    );
    assert!(
        msg.contains("`keep(…) <=> …`"),
        "a folded `Spec[T]` guard leaves the body EMPTY, so the head still defines: {msg}",
    );
}

/// THE BOUNDARY WI-888 DID NOT MOVE. A GUARDED equation keeps its `=` spelling —
/// proposal 049 draws the migration line at the empty body, and `map.anthill:119` writes
/// one directly beneath its `<=>` siblings.
///
/// PASSES WITH AND WITHOUT WI-888, by design: it is here to say what the refusal must
/// NOT reach, so a widening of the gate is caught as a failure rather than shipped as a
/// tidier rule.
#[test]
fn a_guarded_eq_head_still_loads() {
    let src = r#"
namespace test.wi888.guarded
  import anthill.prelude.{Int64, Bool}
  sort C
    import anthill.prelude.{Int64, Bool}
    entity c(v: Int64)
    operation pick(a: Int64, b: Int64) -> Int64
    rule pick(?a, ?b) = ?a :- Int64.gt(?a, ?b)
  end
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "a guarded `=` equation keeps its spelling: {:?}",
        try_load_kb_with(src).err(),
    );
}

/// `=` IN A BODY GOAL IS UNTOUCHED — the position §5.3's test-vs-bind distinction is
/// actually about. The goal below is a TEST over two bound values and the rule answers
/// only when they agree.
///
/// PASSES WITH AND WITHOUT WI-888, by design. Its job is to bound the change: the
/// refusal keys on the HEAD, and a gate that leaked into body goals would take the
/// language's ordinary equality test away.
#[test]
fn an_eq_goal_in_a_rule_body_is_still_a_test() {
    let src = r#"
namespace test.wi888.bodygoal
  import anthill.prelude.{Int64, Bool}
  entity item(k: Int64, v: Int64)
  fact item(k: 1, v: 1)
  fact item(k: 2, v: 9)
  rule same(?k) :- item(k: ?k, v: ?v), ?k = ?v
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "a body-position `=` is a test and stays legal: {:?}",
        try_load_kb_with(src).err(),
    );
}

/// A VARIADIC CAPTURE ON AN `=` HEAD STILL REACHES THIS REFUSAL, and does not die at
/// parse with a message about where it was already correctly placed.
///
/// FOUND BY REVIEW, not by the suite, because nothing in the corpus writes the shape.
/// `convert::equation_lhs` feeds `claim_rule_head_captures`, which is handed only the
/// heads and the meta block and NEVER the body — so asking it "does this connective
/// DEFINE" made it answer for two questions at once, and narrowing
/// `EQUATION_FUNCTORS` took the `...?args` claim away from every `=` head. The marker
/// then reached `refuse_stray_rest_args`, whose message says a capture "may appear only
/// as the LAST positional argument of a `[simp]` rule head's left-hand side" — which is
/// exactly where it was. Worse, that error is at PARSE stage, so the load never ran and
/// WI-888's substitute-naming refusal was never reached.
///
/// This is the WI-1090 defect one reader over: that ticket split
/// `collect_rule_tvar_names` off the defining predicate for this reason and wrote the
/// lesson down. The repair is the same — `equation_lhs` asks the SHAPE question
/// (`is_equality_family_functor`), because "where do the operands sit" answers alike
/// for every family member.
///
/// The GUARDED row is the one that makes this a regression rather than a bad message:
/// WI-888 leaves a guarded `=` equation alone, and with the narrow predicate it became
/// a hard parse error.
///
/// BACK OUT the widening (`equation_lhs` on `is_equation_functor` again) and both rows
/// fail — the first on the message, the second on loading at all.
#[test]
fn a_variadic_capture_on_an_eq_head_reaches_the_wi888_refusal() {
    const BODYLESS: &str = r#"
namespace test.wi888.capture
  import anthill.prelude.Int64
  sort C
    import anthill.prelude.Int64
    operation fixup[R](r: Int64, ...args: R) -> Int64 = r
    operation target(r: Int64, n: Int64) -> Int64 = r
    rule fixup(?r, ...?args) = target(?r, 1) [simp]
  end
end
"#;
    let msg = refusal_of(BODYLESS);
    assert!(
        msg.contains("`fixup(…) <=> …`"),
        "the capture must not divert the head's own refusal to the stray-rest sweep, \
         which would report the `...` as misplaced where the author placed it right: {msg}",
    );

    // The GUARDED form: WI-888 does not move it, so it must still convert. Its capture
    // is claimed exactly as before.
    const GUARDED: &str = r#"
namespace test.wi888.captureguarded
  import anthill.prelude.{Int64, Bool}
  sort C
    import anthill.prelude.{Int64, Bool}
    operation fixup[R](r: Int64, ...args: R) -> Int64 = r
    operation target(r: Int64, n: Int64) -> Int64 = r
    rule fixup(?r, ...?args) = target(?r, 1) :- Int64.gt(?r, 0) [simp]
  end
end
"#;
    assert!(
        try_load_kb_with(GUARDED).is_ok(),
        "a guarded `=` head keeps its capture and its spelling: {:?}",
        try_load_kb_with(GUARDED).err(),
    );
}

/// THE DEFECT THE MIGRATION SURFACED. A namespace that declares its OWN `unify` must not
/// capture the minted `<=>` connective — `<=>` is structural-only and never dispatches
/// (proposal 049's Invariant), so a same-named symbol in scope is a collision, not an
/// override.
///
/// This is `reflect.anthill`'s shape reduced to one file: a local
/// `unify(a: Int64, b: Int64, c: Int64)` beside a `[simp]` equation, and the equation
/// must still FIRE. Backing out the override (`remap_functor` → `remap_symbol`) makes
/// this fail the way the stdlib did — the load stays clean and `drive` traps with
/// `OperationBodyMissing`, because the clause went to the 3-ary local operation.
///
/// The second half is the limit: the local operation is still CALLABLE by name from
/// inside its own namespace, because a written `unify(a, b, c)` call is not minted
/// (WI-948) and keeps the ordinary ladder. An override that captured the call site too
/// would have made the declaration unusable.
#[test]
fn a_local_unify_declaration_does_not_capture_the_connective() {
    const SRC: &str = r#"
namespace test.wi888.localunify
  import anthill.prelude.{Int64, Bool}
  sort C
    import anthill.prelude.{Int64, Bool}
    operation unify(a: Int64, b: Int64, c: Int64) -> Int64 = a
    operation pick(cond: Bool, then: Int64, else: Int64) -> Int64
    rule pick(true, ?t, ?_) <=> ?t [simp]
    operation drive(n: Int64) -> Int64 = pick(true, 10, 20)
    operation callLocal(n: Int64) -> Int64 = unify(7, 8, 9)
  end
end
"#;
    let mut interp = interp_for(SRC);
    match interp.call("test.wi888.localunify.C.drive", &[Value::Int(0)]) {
        Ok(Value::Int(10)) => {}
        other => panic!(
            "the `<=>` equation must fire even beside a local `unify` declaration; got {other:?}"
        ),
    }
    match interp.call("test.wi888.localunify.C.callLocal", &[Value::Int(0)]) {
        Ok(Value::Int(7)) => {}
        other => panic!("a WRITTEN `unify(a, b, c)` call still reaches the local op; got {other:?}"),
    }
}
