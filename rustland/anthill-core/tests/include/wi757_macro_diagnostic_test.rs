//! WI-757 (the WI-722 macro contract) — a compile-time MACRO's DIAGNOSTIC channel.
//!
//! A macro that cannot expand had exactly one outcome before this: it DECLINED.
//! `try_expand_macro` mapped its `Err` to `None`, the `[simp]` template call was
//! kept, and the author read whatever downstream type error the residual produced.
//! That is the right contract for a macro that is merely not applicable — but
//! WI-730 made "this row lambda is not goal-expressible" a DEFINITIVE, user-caused
//! macro failure, and there the residual's error (`guarded_of.r (op-arg): expected
//! NodeOccurrence, got Relation[…]`) names neither the offending condition nor the
//! reason, while the compiler's own "cannot translate" text is discarded.
//!
//! So a macro now has TWO negative outcomes: DECLINE (unchanged — kept template,
//! downstream error) and REJECT (`EvalError::MacroRejected` → `MacroRejection` →
//! `LoadError::MacroRejected`, reported at the sub-expression the macro named).
//! These tests pin both, and the split between them.

use crate::common::try_load_kb_with;

/// The rendered load errors for `src`, which MUST fail to load.
fn load_errors(src: &str) -> Vec<String> {
    try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected this source to fail loading:\n{src}"))
}

/// The rejection text a `LoadError::MacroRejected` renders with — the one marker
/// that distinguishes it from every OTHER way a bad `where` could fail to load
/// (in particular from the residual-template type error it replaces).
///
/// `pub(crate)` (with [`rejections`]) so the WI-902 dot-site suite pins the SAME
/// marker rather than re-spelling the literal: both suites assert the marker's
/// ABSENCE to prove a decline, and a re-spelled copy would pass vacuously if the
/// rendering ever changed. Same-binary reuse across `wi_tests` submodules, as
/// `wi424_iterable_members_test::load_errors` established.
pub(crate) const REJECTION_MARKER: &str = "cannot expand this expression";

pub(crate) fn rejections(errs: &[String]) -> Vec<&String> {
    errs.iter()
        .filter(|e| e.contains(REJECTION_MARKER))
        .collect()
}

/// The WI-702/054 effectful-rewrite gate's marker — the refusal the macro
/// exemption below is carved out of. Owned here, beside the three tests that
/// assert it PRESENT, so the WI-903 suite (which asserts it ABSENT, to prove the
/// exemption now covers a case it used to miss) cannot pass vacuously on a
/// re-spelled literal — the same hazard [`REJECTION_MARKER`] names.
pub(crate) const EFFECTFUL_REWRITE_MARKER: &str = "an effectful operation is not equational";

// ── REJECT: the macro's own words, at the offending sub-expression ──────────

const UNTRANSLATABLE: &str = r#"
namespace test.wi757untranslatable
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  sort Person
    entity person(name: String, age: Int64)
    operation alwaysTrue() -> Bool = true
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation p() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> Person.alwaysTrue()).takeN(5)
end
"#;

/// The whole point of the channel: the message is the MACRO's, naming the macro,
/// the offending head, and the reason — not the residual template's `op-arg`
/// mismatch on a parameter (`guarded_of.r`) the author never wrote.
#[test]
fn rejection_carries_the_macros_own_words() {
    let errs = load_errors(UNTRANSLATABLE);
    let [rejection] = rejections(&errs)[..] else {
        panic!("expected exactly one macro rejection, got: {errs:?}");
    };
    for fragment in [
        // WHICH macro refused — the `[simp]` RHS head behind `where`.
        "compile-time macro `anthill.prelude.Relation.guarded_of`",
        // WHAT it needed.
        "a goal-expressible predicate",
        // WHAT it found — the author's own name, which the residual error never
        // mentioned.
        "test.wi757untranslatable.Person.alwaysTrue",
        // WHY, and the spelling that works instead.
        "it has no meaning as a query goal",
        "compute it with `.map` on the stream instead",
    ] {
        assert!(
            rejection.contains(fragment),
            "missing {fragment:?} in: {rejection}"
        );
    }
    assert!(
        !errs.iter().any(|e| e.contains("op-arg")),
        "the residual `guarded_of` template's op-arg type error must no longer be \
         what the author reads, got: {errs:?}",
    );
}

/// Located at the CONDITION, not at the `where` call and not at the operation.
/// The macro holds the argument occurrences, so it can point at the one atom that
/// does not translate — and it must, since the enclosing call is fine.
#[test]
fn rejection_is_located_at_the_offending_condition() {
    let errs = load_errors(UNTRANSLATABLE);
    let [rejection] = rejections(&errs)[..] else {
        panic!("expected exactly one macro rejection, got: {errs:?}");
    };
    // `person_row.where(lambda c -> Person.alwaysTrue()).takeN(5)` — the column of
    // `Person`, computed from the source rather than written as a constant so an
    // edit to the fixture cannot silently un-anchor the assertion.
    let body_line = UNTRANSLATABLE
        .lines()
        .position(|l| l.contains("person_row.where"))
        .expect("the fixture has the `where` line")
        + 1;
    let line_text = UNTRANSLATABLE.lines().nth(body_line - 1).unwrap();
    let cond_col = line_text.find("Person.alwaysTrue").unwrap() + 1;
    let where_col = line_text.find("where").unwrap() + 1;
    assert!(
        rejection.starts_with(&format!("{body_line}:{cond_col}:")),
        "expected the rejection at the condition ({body_line}:{cond_col}), not the \
         `where` call ({body_line}:{where_col}), got: {rejection}",
    );
}

/// One genuine failure, one error. A macro can be ATTEMPTED more than once (the
/// `[simp]` engine fires bottom-up and re-visits a rewritten node, and a
/// re-entrant expansion is capped, not forbidden), so a rejection reported by a
/// buffer would need a dedup key. It is instead reported by the FIRE's caller and
/// aborts that node's typing, which makes the count structural.
#[test]
fn one_rejection_is_reported_once() {
    let errs = load_errors(UNTRANSLATABLE);
    assert_eq!(
        rejections(&errs).len(),
        1,
        "a single untranslatable condition must be reported once, got: {errs:?}",
    );
}

/// A rejection is per-REDEX: a sibling `where` whose condition IS goal-expressible
/// still expands, so the failure does not spread and — the converse of the stale-
/// error hazard — a macro attempt that succeeds leaves nothing behind. (The
/// expansion of the good one is asserted end-to-end by the WI-730 suite; here the
/// point is that exactly ONE of the two is reported.)
#[test]
fn a_rejection_does_not_condemn_a_sibling_where() {
    const SRC: &str = r#"
namespace test.wi757sibling
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
    operation alwaysTrue() -> Bool = true
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation good() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> eq(c.name, "alice")).takeN(5)
  operation bad() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> Person.alwaysTrue()).takeN(5)
end
"#;
    let errs = load_errors(SRC);
    let [rejection] = rejections(&errs)[..] else {
        panic!("expected exactly one macro rejection, got: {errs:?}");
    };
    assert!(
        rejection.contains("alwaysTrue"),
        "the reported rejection must be the bad `where`, got: {rejection}",
    );
}

/// A bare column PROJECTION is an operand form, never a condition — and the
/// refusal must say which spelling works. `is_err()` alone was satisfied by the
/// residual template's `expected NodeOccurrence, got Relation[…]`, which told the
/// author nothing about the column they wrote.
#[test]
fn bare_column_projection_rejection_names_the_working_spelling() {
    const SRC: &str = r#"
namespace test.wi757bare
  import anthill.prelude.{String, List, Bool}
  import anthill.prelude.Relation.{where}
  sort Person
    entity person(name: String, ok: Bool)
  end
  fact person(name: "alice", ok: true)
  rule person_row(?name, ?ok) :- person(name: ?name, ok: ?ok)
  operation p() -> List[(name: String, ok: Bool)] effects Error =
    person_row.where(lambda c -> c.ok).takeN(5)
end
"#;
    let errs = load_errors(SRC);
    let [rejection] = rejections(&errs)[..] else {
        panic!("expected exactly one macro rejection, got: {errs:?}");
    };
    assert!(
        rejection.contains("COMPARE the column")
            && rejection.contains("bare column projection in condition position"),
        "expected the macro's own bare-projection text, got: {rejection}",
    );
}

/// The channel is not `where`-specific: `join`'s macro (`conjoin_of`) is a second
/// caller of the same condition compiler and reports through the same channel,
/// naming ITSELF.
#[test]
fn the_join_macro_reports_through_the_same_channel() {
    const SRC: &str = r#"
namespace test.wi757join
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{join}
  sort Person
    entity person(name: String, age: Int64)
    operation alwaysTrue() -> Bool = true
  end
  sort Membership
    entity member(who: String, dept: String)
  end
  fact person(name: "alice", age: 30)
  fact member(who: "alice", dept: "eng")
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  rule member_row(?who, ?dept) :- member(who: ?who, dept: ?dept)
  operation p() -> List[(name: String, age: Int64, who: String, dept: String)] effects Error =
    person_row.join(member_row, lambda (c, q) -> Person.alwaysTrue()).takeN(5)
end
"#;
    let errs = load_errors(SRC);
    let [rejection] = rejections(&errs)[..] else {
        panic!("expected exactly one macro rejection, got: {errs:?}");
    };
    assert!(
        rejection.contains("compile-time macro `anthill.prelude.Relation.conjoin_of`")
            && rejection.contains("it has no meaning as a query goal"),
        "expected `join`'s macro to reject through the same channel, got: {rejection}",
    );
}

// ── REJECT from anthill: a macro raises ────────────────────────────────────

/// An anthill-WRITTEN macro reaches the same channel by RAISING (proposal 043.1
/// §3.6). `Error.raise`'s payload renders into the rejection's text through the
/// shared `render_raised_payload` — the same words the CLI prints for an unhandled
/// top-level raise.
///
/// This is only reachable because the WI-702 / proposal 054 rewrite gate exempts a
/// MACRO at the `[simp]` RHS head (see the two narrowness tests below). Without
/// that exemption `wrap`'s `effects Error[…]` was refused at the rule naming it, so
/// 043.1 §6's "a macro that raises `Error` becomes a compile-time diagnostic" could
/// never fire and the channel was host-only.
#[test]
fn an_anthill_macro_rejects_by_raising() {
    const SRC: &str = r#"
namespace test.wi757raise
  import anthill.prelude.{Int64, String}
  import anthill.prelude.Numeric.{add}
  import anthill.reflect.{NodeOccurrence}

  sort NotAllowed
    entity not_allowed(why: String)
  end

  operation wrap(x: NodeOccurrence) -> NodeOccurrence effects Error[NotAllowed] =
    Error.raise(not_allowed(why: "trigger takes a column, not a literal"))

  operation trigger(x: Int64) -> Int64 = x
  rule trigger(?x) <=> wrap(?x) [simp]

  operation consumer() -> Int64 = add(trigger(5), 1)
end
"#;
    let errs = load_errors(SRC);
    let [rejection] = rejections(&errs)[..] else {
        panic!("expected exactly one macro rejection, got: {errs:?}");
    };
    assert!(
        rejection.contains("compile-time macro `test.wi757raise.wrap`")
            && rejection.contains(r#"not_allowed(why: "trigger takes a column, not a literal")"#),
        "expected the raised payload rendered as the rejection text, got: {rejection}",
    );
    // `raise` carries a payload and NO occurrence, so the location is the redex —
    // `trigger(5)`, the call the rule fired on, not `wrap`'s own body.
    let body_line = SRC
        .lines()
        .position(|l| l.contains("add(trigger(5)"))
        .unwrap()
        + 1;
    let line_text = SRC.lines().nth(body_line - 1).unwrap();
    let redex_col = line_text.find("trigger(5)").unwrap() + 1;
    assert!(
        rejection.starts_with(&format!("{body_line}:{redex_col}:")),
        "expected the raised rejection at the redex ({body_line}:{redex_col}), got: {rejection}",
    );
}

/// The exemption is for the MACRO, not for `[simp]` rules in general. An ORDINARY
/// effectful operation at the RHS head is still refused by WI-702 / 054 — its call
/// SURVIVES the rewrite into the program, so firing really can duplicate, reorder
/// or drop it.
#[test]
fn the_rewrite_gate_still_refuses_an_effectful_non_macro() {
    const SRC: &str = r#"
namespace test.wi757ordinary
  import anthill.prelude.{Int64, String}
  import anthill.prelude.Numeric.{add}
  sort Boom
    entity boom(why: String)
  end
  operation risky(x: Int64) -> Int64 effects Error[Boom] = Error.raise(boom(why: "no"))
  operation trigger(x: Int64) -> Int64 = x
  rule trigger(?x) <=> risky(?x) [simp]
  operation consumer() -> Int64 = add(trigger(5), 1)
end
"#;
    let errs = load_errors(SRC);
    assert!(
        errs.iter().any(|e| e.contains("test.wi757ordinary.risky")
            && e.contains(EFFECTFUL_REWRITE_MARKER)),
        "an effectful NON-macro rewrite must stay refused, got: {errs:?}",
    );
}

/// …and not for a macro the typer's expander does NOT fire. `[unfold]` is fired by
/// the RESOLVER (`fire_simp_equation`), which substitutes the RHS template verbatim
/// and never macro-expands — so the effectful call really is rewritten into the
/// program, exactly the hazard WI-702 exists for.
///
/// This was a live hole: with the exemption keyed on `is_macro` alone, this source
/// LOADED CLEAN. `macro_expanded_rhs_head` ties the exemption to `try_fire`'s own
/// firing conditions so it cannot outrun the expansion that justifies it.
#[test]
fn the_rewrite_gate_still_refuses_an_effectful_macro_the_typer_never_expands() {
    const SRC: &str = r#"
namespace test.wi757unfold
  import anthill.prelude.{Int64, String}
  import anthill.prelude.Numeric.{add}
  import anthill.reflect.{NodeOccurrence}
  sort Boom
    entity boom(why: String)
  end
  operation m(x: NodeOccurrence) -> NodeOccurrence effects Error[Boom] =
    Error.raise(boom(why: "nope"))
  operation trigger(x: Int64) -> Int64 = x
  rule trigger(?x) <=> m(?x) [unfold]
  operation consumer() -> Int64 = add(trigger(5), 1)
end
"#;
    let errs = load_errors(SRC);
    assert!(
        errs.iter()
            .any(|e| e.contains("test.wi757unfold.m") && e.contains(EFFECTFUL_REWRITE_MARKER)),
        "an effectful macro under `[unfold]` is never expanded, so it must stay \
         refused, got: {errs:?}",
    );
}

/// The exemption skips the macro's SYMBOL, so it also lifts the gate off that macro
/// written elsewhere in the same rule. That is safe only because every such spelling
/// is refused AHEAD of the gate — this pins the case that is not obvious: a macro in
/// a rule-body GOAL, which is not an operation call at all and so cannot be caught
/// by the occurrence-vs-value parameter mismatch. WI-583 refuses it: an
/// occurrence-returning op has no relational reading.
#[test]
fn a_macro_in_a_body_goal_is_refused_ahead_of_the_gate() {
    const SRC: &str = r#"
namespace test.wi757bodygoal
  import anthill.prelude.{Int64, String}
  import anthill.prelude.Numeric.{add}
  import anthill.reflect.{NodeOccurrence}
  sort Boom
    entity boom(why: String)
  end
  operation m(x: NodeOccurrence) -> NodeOccurrence effects Error[Boom] =
    Error.raise(boom(why: "nope"))
  operation trigger(x: Int64) -> Int64 = x
  rule trigger(?x) <=> m(?x) :- m(?x) [simp]
  operation consumer() -> Int64 = add(trigger(5), 1)
end
"#;
    let errs = load_errors(SRC);
    assert!(
        errs.iter()
            .any(|e| e.contains("test.wi757bodygoal.m") && e.contains("rule-body goal position")),
        "a macro cited as a body goal must be refused for having no relational \
         reading, got: {errs:?}",
    );
}

/// …and not for an effectful operation the macro is merely APPLIED TO. Only the
/// RHS HEAD is evaluated away at compile time; an argument rides into the spliced
/// result, so it keeps the gate.
#[test]
fn the_rewrite_gate_still_refuses_an_effectful_macro_argument() {
    const SRC: &str = r#"
namespace test.wi757nested
  import anthill.prelude.{Int64, String}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Numeric.{add}
  import anthill.reflect.{NodeOccurrence, make_apply}
  sort Boom
    entity boom(why: String)
  end
  operation risky(x: Int64) -> Int64 effects Error[Boom] = Error.raise(boom(why: "no"))
  operation wrapped(v: Int64) -> Int64 = add(v, 100)
  operation wrap(x: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi757nested.wrapped", cons(x, nil()), x)
  operation trigger(x: Int64) -> Int64 = x
  rule trigger(?x) <=> wrap(risky(?x)) [simp]
  operation consumer() -> Int64 = add(trigger(5), 1)
end
"#;
    let errs = load_errors(SRC);
    assert!(
        errs.iter()
            .any(|e| e.contains("test.wi757nested.risky") && e.contains(EFFECTFUL_REWRITE_MARKER)),
        "an effectful macro ARGUMENT must stay refused, got: {errs:?}",
    );
}

// ── DECLINE: the WI-722 contract, unchanged ────────────────────────────────

/// A macro that is NOT APPLICABLE still DECLINES quietly: its `[simp]` template
/// call is kept and the residual's own type-check is what the author reads. This
/// is the WI-722 contract, and WI-757 must not have collapsed the two negative
/// outcomes into one.
///
/// The decline here is `try_expand_macro`'s own structural gate: a macro is
/// called on the matched pattern-var occurrences POSITIONALLY, so a template
/// carrying NAMED arguments (`wrap(x: ?x)`) is outside the surface and is left
/// alone. `wrap` is then typed as an ordinary call, whose `NodeOccurrence`
/// parameter meets the value type `Int64` — the loud downstream error the kept
/// template is supposed to produce, at the redex.
///
/// (This pins the "not applicable" half of the split. The other decline — a macro
/// whose EVALUATION fails with something that is neither a host rejection nor a
/// raise — is `try_expand_macro`'s `Err(e) => Ok(None)` arm: a `Suspended` flounder
/// is "not yet", and an unrelated evaluator error is not the author's to read.)
#[test]
fn a_macro_that_is_not_applicable_still_declines_quietly() {
    const SRC: &str = r#"
namespace test.wi757decline
  import anthill.prelude.{Int64}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Numeric.{add}
  import anthill.reflect.{NodeOccurrence, make_apply}

  operation wrapped(v: Int64) -> Int64 = add(v, 100)
  operation wrap(x: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi757decline.wrapped", cons(x, nil()), x)

  operation trigger(x: Int64) -> Int64 = x
  rule trigger(?x) <=> wrap(x: ?x) [simp]

  operation consumer() -> Int64 = add(trigger(5), 1)
end
"#;
    let errs = load_errors(SRC);
    assert!(
        rejections(&errs).is_empty(),
        "a macro that is merely not applicable must DECLINE, not reject: {errs:?}",
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("wrap.x (op-arg)")
                && e.contains("expected NodeOccurrence, got Int64")),
        "the kept template's own type-check is what must surface, got: {errs:?}",
    );
}
