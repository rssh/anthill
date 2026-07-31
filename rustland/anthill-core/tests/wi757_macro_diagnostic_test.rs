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

mod common;

use common::try_load_kb_with;

/// The rendered load errors for `src`, which MUST fail to load.
fn load_errors(src: &str) -> Vec<String> {
    try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected this source to fail loading:\n{src}"))
}

/// The rejection text a `LoadError::MacroRejected` renders with — the one marker
/// that distinguishes it from every OTHER way a bad `where` could fail to load
/// (in particular from the residual-template type error it replaces).
const REJECTION_MARKER: &str = "cannot expand this expression";

fn rejections(errs: &[String]) -> Vec<&String> {
    errs.iter().filter(|e| e.contains(REJECTION_MARKER)).collect()
}

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
        assert!(rejection.contains(fragment), "missing {fragment:?} in: {rejection}");
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
/// (This pins the "not applicable" half of the split, which is what the acceptance
/// names. The other decline — a macro whose EVALUATION fails with something that
/// is not a rejection — is `try_expand_macro`'s `Err(e) => Ok(None)` arm, left
/// untouched: WI-757 only added an arm ahead of it.)
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
        errs.iter().any(|e| e.contains("wrap.x (op-arg)")
            && e.contains("expected NodeOccurrence, got Int64")),
        "the kept template's own type-check is what must surface, got: {errs:?}",
    );
}
