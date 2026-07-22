//! WI-809 — a named-argument list may not repeat a LABEL.
//!
//! Found while measuring WI-808 and recorded there before being fixed. MEASURED on a
//! well-formed entity — DISTINCT fields, so WI-808's declaration rule does not apply:
//!
//! ```anthill
//! sort S
//!   entity mk(a: Int64, b: Int64)
//! end
//! operation by_a() -> Int64 = mk(a: 1, a: 2).a     -- loaded clean, returned Int(1)
//! ```
//!
//! The value it built had TWO `a` fields and NO `b`: `.a` read the first, a positional
//! pattern saw the second `a` occupying `b`'s slot, and `.b` raised
//! `Internal("field_access: entity has no field 'b'")` at RUN TIME. So writing one label
//! twice silently filled an unrelated field and left the intended one unbound.
//!
//! THE CHECK EXISTED AND ENTITIES DID NOT USE IT. The identical spelling against an
//! OPERATION was already refused by `named_arg_coverage_errors` ("binds a parameter
//! already given"); entity construction, facts and rule-body atoms never route through
//! it.
//!
//! FIXED AT THE SYNTAX LAYER rather than by teaching the typer a fourth callee shape,
//! because whether one argument list repeats a label needs NO type information. One rule
//! at `push_fn_term` / `push_dot_method_call` covers every callee at once — operation, entity
//! constructor, fact, rule-body atom, function value, dot call — which is what stops this
//! from being the same half-covered rule a third time (WI-805's lesson).
//!
//! `named_arg_coverage_errors` KEEPS BOTH ITS OWN REASONS, neither of which is syntactic:
//! an UNKNOWN label, and a label colliding with a parameter already filled POSITIONALLY
//! (`f(3, acc: 10)` — WI-783, still its own test). Only the two-named-args spelling moved
//! earlier.
//!
//! EXTENDED TO TWO MORE PRODUCTIONS after a `/code-review` pass refused the first cut's
//! producer list — the same lesson, a third time:
//!
//!  * CONSTRUCTOR PATTERNS (`case mk(a: p, a: q)`, the `named_pattern_field` production).
//!    The first cut left these out, claiming they were "already loud at run time" via
//!    `match_constructor_pattern`'s WI-445 double-cover guard. THAT WAS MEASURED ON THE
//!    WRONG FIXTURE. It raises `MatchFailed` only when no other case follows; with a
//!    fallback — the common shape — the malformed arm simply never matches and the
//!    fallback wins, so `case mk(a: p, a: q) -> 111` under `case _ -> 999` loaded clean
//!    and returned 999. A silently dead arm, which is the failure mode this codebase
//!    ranks below a loud error.
//!  * PROOF-STRATEGY arguments (`by z3(logic: "LRA", logic: "QF_NRA")`), which share the
//!    very `named_arg` node this rule keys on. Leaving them out produced an indefensible
//!    asymmetry: the NESTED spelling `z3(tactic: smt(logic: …, logic: …))` was refused,
//!    because its value routes through `convert_term`, while the top-level one was not.
//!    `prove.rs` reads these last-wins AND pushes both into the proof-cache canon, so the
//!    duplicate silently changed both what was proved and what was cached.
//!
//! The `named_arg` grammar node reaches exactly three productions — `fn_term`,
//! `tuple_literal` (WI-805) and `proof_strategy` — and all three are now covered, plus
//! the pattern twin.

use crate::common::{interp_for, parse_errs, parses_clean, try_load_kb_with};

const ENTITY: &str = "  sort S\n    entity mk(a: Int64, b: Int64)\n  end\n";

fn assert_dup_refused(src: &str, what: &str) {
    let errs = parse_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("duplicate named argument `a`")),
        "{what} must refuse a repeated label, naming it; got: {errs:?}",
    );
}

/// THE REPORTED CASE: value-position construction of an entity.
#[test]
fn duplicate_label_in_entity_construction_is_refused() {
    let src = format!(
        "namespace test.wi809.val\n  import anthill.prelude.Int64\n{ENTITY}  \
         operation d() -> Int64 = mk(a: 1, a: 2).a\nend\n"
    );
    assert_dup_refused(&src, "entity construction");
}

/// A FACT — the same corruption through a door the typer's check never saw.
#[test]
fn duplicate_label_in_a_fact_is_refused() {
    let src = format!(
        "namespace test.wi809.fact\n  import anthill.prelude.Int64\n{ENTITY}  \
         fact mk(a: 1, a: 2)\nend\n"
    );
    assert_dup_refused(&src, "a fact");
}

/// A RULE-BODY atom. Worth its own case because a repeated label there might have been
/// read as "match this field against two patterns" — it never was: it builds an atom
/// with two `a` arguments, which can only match an equally malformed fact.
#[test]
fn duplicate_label_in_a_rule_body_atom_is_refused() {
    let src = format!(
        "namespace test.wi809.rule\n  import anthill.prelude.Int64\n{ENTITY}  \
         rule r(?x, ?y) :- mk(a: ?x, a: ?y)\nend\n"
    );
    assert_dup_refused(&src, "a rule-body atom");
}

/// An OPERATION call — already refused before this change, by the typer. Kept to pin
/// that the rule now fires for it too, one stage earlier, so the guarantee is uniform
/// across callees rather than per-callee.
#[test]
fn duplicate_label_in_an_operation_call_is_refused() {
    let src = "namespace test.wi809.op\n  import anthill.prelude.Int64\n  \
               operation take(a: Int64, b: Int64) -> Int64 = a\n  \
               operation d() -> Int64 = take(a: 1, a: 2)\nend\n";
    assert_dup_refused(src, "an operation call");
}

/// The DOT-CALL form is a second argument-list producer (`push_dot_method_call`), not the same
/// code path as `push_fn_term`. Both were wired; this is the one that would silently stay
/// open if only the obvious site had been patched.
#[test]
fn duplicate_label_in_a_dot_call_is_refused() {
    let src = format!(
        "namespace test.wi809.dot\n  import anthill.prelude.Int64\n{ENTITY}  \
         operation on(s: S, a: Int64, b: Int64) -> Int64 = a\n  \
         operation d() -> Int64 = mk(1, 2).on(a: 1, a: 2)\nend\n"
    );
    assert_dup_refused(&src, "a dot call");
}

// ── what the rule must NOT catch ───────────────────────────────

/// DISTINCT labels still work, end to end — including reading the field that the bug
/// used to leave unbound. Without this the tests above pass against a guard that refuses
/// every named argument.
#[test]
fn distinct_labels_still_construct_and_read() {
    let src = format!(
        "namespace test.wi809.ok\n  import anthill.prelude.Int64\n{ENTITY}  \
         operation d() -> Int64 = mk(a: 1, b: 2).b\nend\n"
    );
    let errs = try_load_kb_with(&src).err().unwrap_or_default();
    assert!(errs.is_empty(), "a distinct-label construction must load; got: {errs:?}");
    let mut interp = interp_for(&src);
    match interp.call("test.wi809.ok.d", &[]).expect("d") {
        anthill_core::eval::Value::Int(2) => {}
        other => panic!("`.b` must read the `b` field (2) — the slot the bug left unbound; got {other:?}"),
    }
}

/// The label set is PER ARGUMENT LIST, not per expression or per file: two separate
/// calls may each use `a`, and a nested call may reuse an outer label. A check keyed on
/// anything wider would reject ordinary code.
#[test]
fn labels_do_not_collide_across_separate_argument_lists() {
    parses_clean(
        "namespace test.wi809.sep\n  import anthill.prelude.Int64\n  \
         sort S\n    entity mk(a: Int64, b: Int64)\n  end\n  \
         operation d() -> Int64 = mk(a: 1, b: 2).a + mk(a: 3, b: 4).b\nend\n",
    );
    parses_clean(
        "namespace test.wi809.nest\n  import anthill.prelude.Int64\n  \
         operation inner(a: Int64) -> Int64 = a\n  \
         operation outer(a: Int64, b: Int64) -> Int64 = a\n  \
         operation d() -> Int64 = outer(a: inner(a: 1), b: 2)\nend\n",
    );
}

// ── the two producers the first cut missed ────────────────

/// A CONSTRUCTOR PATTERN, in the shape that made the "already loud" claim false: with a
/// following case, the malformed arm was silently dead rather than loud.
#[test]
fn duplicate_label_in_a_constructor_pattern_is_refused() {
    let src = format!(
        "namespace test.wi809.pat\n  import anthill.prelude.Int64\n{ENTITY}  \
         operation d() -> Int64 =\n    match mk(1, 2)\n      \
         case mk(a: p, a: q) -> 111\n      case _ -> 999\nend\n"
    );
    let errs = parse_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("duplicate named pattern field `a`")),
        "a constructor pattern must refuse a repeated field label; got: {errs:?}",
    );
}

/// A PROOF STRATEGY's argument list — the third `named_arg` production. Its nested twin
/// was already refused via `convert_term`, which is what made the gap indefensible rather
/// than merely incomplete.
#[test]
fn duplicate_label_in_a_proof_strategy_is_refused() {
    let src = "namespace test.wi809.ps\n  import anthill.prelude.Int64\n  \
               proof p by z3(logic: \"LRA\", logic: \"QF_NRA\") end\nend\n";
    let errs = parse_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("duplicate proof strategy argument `logic`")),
        "a proof strategy must refuse a repeated argument label; got: {errs:?}",
    );
}

/// CONTROL for the strategy case: distinct strategy arguments still parse.
#[test]
fn distinct_proof_strategy_arguments_still_parse() {
    parses_clean(
        "namespace test.wi809.ps2\n  import anthill.prelude.Int64\n  \
         proof p by z3(logic: \"LRA\", model: true) end\nend\n",
    );
}

/// A label may coincide with a POSITIONAL argument's value or with the callee name —
/// only two NAMED labels collide.
#[test]
fn a_named_label_does_not_collide_with_positional_arguments() {
    parses_clean(
        "namespace test.wi809.pos\n  import anthill.prelude.Int64\n  \
         operation take(a: Int64, b: Int64, c: Int64) -> Int64 = a\n  \
         operation d() -> Int64 = take(1, b: 2, c: 3)\nend\n",
    );
}
