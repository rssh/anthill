//! WI-20260830-DQD5W — a SPEC OPERATION'S bare goal DECIDES, where before it was a
//! silent no-solutions goal.
//!
//! `isEmpty(?xs)` / `nonEmpty(?xs)` are `anthill.prelude.Iterable` operations with
//! DEFAULT BODIES, reached by `List`'s provision; `contains(?xs, ?x)` is `List`'s own.
//! All three import cleanly and none is a name error — but only `contains` had any
//! clauses to try, so the other two answered ZERO SOLUTIONS. A goal with no clauses is
//! FALSE, not an error, so a `constraint c :- Verdict(labels: ?ls) -: nonEmpty(?ls)`
//! LOADS and then fires on every well-formed row, indistinguishably from a constraint
//! that works. That is how this was found (`examples/guardians`, measured.md C11).
//!
//! THREE CAUSES, each measured, and NONE is the one the ticket guessed (it guessed the
//! derivation keys on the carrier's own clause; it does not — it keys on the SPELLED
//! functor, which is fine here). Only the first two are about SPEC OPERATIONS; the
//! third is measured with `List.contains`, the ticket's own control:
//!
//!   1. `bare_bodied_bool_relation`'s effect gate read `!sig.effects.is_empty()`.
//!      `Iterable.isEmpty(c: C) -> Bool effects E` declares a row PARAMETER — its sort
//!      declares `effects E = ?` — so the row has one member that names no effect, and
//!      `List` instantiates it to `{}`. The gate answered a question about the SPEC's
//!      abstraction where the goal asks one about the CALL. Now the row's MEMBERS are
//!      read, via WI-1049's `effect_member_is_parametric`.
//!
//!   2. With the goal routed, the eval bridge still suspended: `resolve_bridge_
//!      requirements` tried to RESOLVE the `EffectsRuntime[Effects = Iterable.E]`
//!      kind-anchor `effects E = ?` synthesizes, and its (correct, for every other
//!      slot) "fully pinned or residualize" gate refused a row parameter no argument
//!      type can pin. WI-857 names three readers that must agree the anchor is a
//!      STRUCTURAL LEAF holding its slot; this was a fourth that did not.
//!
//!   3. And a goal written directly in a CONSTRAINT GUARD body still could not
//!      decide, for a reason with nothing to do with spec ops: `lower_query` hands the
//!      resolver a hash-consed `Value::Term` where a rule body carries an occurrence,
//!      and `reduce_op_value` folds only a `Value::Node`. So `no ?ls: Box(items: ?ls)
//!      -: contains(?ls, "z")` LOADED CLEAN over `fact Box(items: ["z"])` — the
//!      ticket's stated consequence, with its stated control equally inert. The Bool
//!      hook now rebuilds its operand on the occurrence carrier, which is what the
//!      arity+1 hook beside it already did and says it does.
//!
//! A FOURTH FIX RIDES WITH (3) BECAUSE THE WIDENING ENLARGES ITS POPULATION: the Bool
//! hook was not ARITY-GATED, though §5.3 has always said the routing applies "at the
//! operation's declared arity". A 3-ary goal on a 2-param op was wrapped in
//! `eq(…, true)`, the extra column dropped by arg-place lookup, and the goal answered
//! ONE DEFINITE solution with the result variable FREE. `contains(?ls, "a", ?r)`
//! measured it on `main`; `Iterable.isEmpty(?ls, ?r)` would have joined it under
//! cause (1). Gated, such a goal falls to the arity+1 view, which BINDS the result.
//!
//! WHAT FAILS WHEN EACH IS BACKED OUT — the causes are independent and each has its own
//! row here:
//!
//!   * back out (1) alone (restore `if !sig.effects.is_empty() { return false }`):
//!     `spec_op_bare_goal_decides` and `spec_op_bare_goal_is_not_a_residual` fail —
//!     zero solutions, the ticket's symptom verbatim.
//!   * back out (2) alone (drop the `is_effects_runtime` arm in
//!     `resolve_bridge_requirements`): `spec_op_bare_goal_decides` fails and
//!     `spec_op_bare_goal_is_not_a_residual` fails LOUDER — the goal is now routed but
//!     the bridge suspends, so each `Box` comes back as an INDEFINITE solution. That
//!     asymmetry is why the residual row exists: `definite_unary` alone cannot tell
//!     "no clauses" from "suspended", and cause (2) turns the first into the second.
//!   * back out (3) alone (drop the `Value::Term` materialization):
//!     `a_constraint_guard_body_takes_the_relational_view` and
//!     `a_quantified_constraint_over_a_spec_op_holds_for_well_formed_rows` fail; the
//!     four rule-body rows pass, which is what attributes it to the GUARD carrier.
//!   * back out the arity gate (drop the `declared_arity == …` conjunct):
//!     `an_arity_mismatched_bool_goal_takes_the_functional_relation_view` fails alone.
//!
//! CONTROLS — each passes with the change backed out either way, and each is here
//! because it is what the widening could plausibly have broken:
//!
//!   * `carriers_own_operation_still_decides` — `contains`, `List`'s own bodied,
//!     effect-free operation. It is the row the ticket names as passing today
//!     (`wi939_contains_rename_test::list_contains_as_a_rule_body_goal` is its
//!     sibling); if it moved, the change reached past the parametric-row class.
//!   * `an_unground_spec_op_goal_still_suspends` — the WI-519 residual the ticket
//!     requires to keep suspending. The relational view is a sound CHECKER, not a
//!     generator (WI-580 §5), and admitting a parametric row must not turn it into one.
//!   * `a_concretely_effectful_bool_op_is_still_refused` — a bodied `Bool` operation
//!     declaring a REAL effect (`Modify`) keeps zero solutions. `effect_member_is_
//!     parametric` is HEAD-only by design, so `Modify[c]` stays a concrete effect; this
//!     is the row that says the gate was WIDENED and not DELETED.

use anthill_core::eval::Value;

use crate::common::{definite_unary, load_kb_with, query_unary, try_load_kb_with};

/// The ticket's fixture, one file, one `List`, with the head carrying the `Box`'s own
/// items so a solution names WHICH box answered — an `empty(1)` head would count right
/// while pointing at either row.
const SRC: &str = r#"
namespace dqd5w
  import anthill.prelude.{List, String, Bool}
  import anthill.prelude.List.{contains}
  import anthill.prelude.Iterable.{isEmpty, nonEmpty}

  sort Box
    entity Box(items: List[T = String])
  end

  fact Box(items: ["a", "b"])
  fact Box(items: [])

  rule has_a(?ls) :- Box(items: ?ls), contains(?ls, "a")
  rule empty(?ls) :- Box(items: ?ls), isEmpty(?ls)
  rule full(?ls)  :- Box(items: ?ls), nonEmpty(?ls)
end
"#;

/// Render a solution list as `["a", "b"]`-ish text, so a row can say which `Box` it got
/// rather than only how many.
fn answers(kb: &mut anthill_core::kb::KnowledgeBase, qn: &str) -> Vec<String> {
    definite_unary(kb, qn)
        .iter()
        .map(|v| format!("{v:?}"))
        .collect()
}

/// THE ACCEPTANCE ROW. `isEmpty` yields the empty `Box` and `nonEmpty` the other one —
/// one solution each, and DIFFERENT ones, so a predicate that answered everything (or
/// nothing) fails whichever way it is wrong.
#[test]
fn spec_op_bare_goal_decides() {
    let mut kb = load_kb_with(SRC);
    let empty = answers(&mut kb, "dqd5w.empty");
    let full = answers(&mut kb, "dqd5w.full");
    assert_eq!(
        empty.len(),
        1,
        "`isEmpty(?ls)` must decide for exactly one Box; got {empty:?}"
    );
    assert_eq!(
        full.len(),
        1,
        "`nonEmpty(?ls)` must decide for exactly one Box; got {full:?}"
    );
    assert_ne!(
        empty[0], full[0],
        "`isEmpty` and `nonEmpty` picked the SAME Box — the two goals are not \
         inverses, which a count-only assertion would have missed"
    );
    // And WHICH one, by the only structural fact available without decoding the term:
    // the empty list's rendering is shorter than the two-element one's.
    assert!(
        empty[0].len() < full[0].len(),
        "`isEmpty` must select the EMPTY Box, not merely a different one: \
         isEmpty={empty:?} nonEmpty={full:?}"
    );
}

/// The same two goals counted with residuals INCLUDED. Cause (2) is invisible to the
/// row above — with only cause (1) fixed both goals produce two INDEFINITE solutions
/// apiece, which `definite_unary` filters to zero and reports identically to the
/// original "no clauses at all". This row separates them.
#[test]
fn spec_op_bare_goal_is_not_a_residual() {
    let mut kb = load_kb_with(SRC);
    for qn in ["dqd5w.empty", "dqd5w.full"] {
        let all = query_unary(&mut kb, qn);
        assert_eq!(
            all.len(),
            1,
            "`{qn}` must produce exactly one solution — two means the goal routed but \
             the bridge SUSPENDED on every Box (cause 2); got {all:?}"
        );
        assert!(
            all[0].1,
            "`{qn}`'s solution must be DEFINITE, not a floundered residual; got {all:?}"
        );
    }
}

/// CONTROL — the carrier's OWN bodied, effect-free operation. Passes with either cause
/// backed out; it is here so a regression in `contains` is attributed to the widening
/// rather than to the spec-op route.
#[test]
fn carriers_own_operation_still_decides() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(
        definite_unary(&mut kb, "dqd5w.has_a").len(),
        1,
        "`contains(?ls, \"a\")` is List's own operation and decided before this ticket"
    );
}

/// CONTROL — the WI-519 residual. An UNGROUND receiver has nothing to decide about, and
/// the relational view is a sound checker rather than a generator (WI-580 §5), so the
/// goal must SUSPEND: solutions may exist, but none definite. Passes either way.
#[test]
fn an_unground_spec_op_goal_still_suspends() {
    let src = r#"
namespace dqd5w_ung
  import anthill.prelude.{List, String, Bool}
  import anthill.prelude.Iterable.{isEmpty}
  fact mark(1)
  rule gen(?m) :- mark(?m), isEmpty(?ls)
end
"#;
    let mut kb = load_kb_with(src);
    assert_eq!(
        definite_unary(&mut kb, "dqd5w_ung.gen").len(),
        0,
        "an unground `isEmpty(?ls)` must not GENERATE — it suspends to a residual"
    );
}

/// CONTROL — a bodied `Bool` operation whose declared row names a REAL effect keeps its
/// refusal, and a byte-identical one with the row REMOVED decides. Two rows in one
/// fixture, differing only in the axis the predicate is about, because a single
/// effectful op answering zero is also what an un-drivable fixture answers.
/// `effect_member_is_parametric` reads the row member's HEAD, so a concrete effect sort
/// is not a parameter; without this pair the change reads as "the effect gate was
/// deleted".
#[test]
fn a_concretely_effectful_bool_op_is_still_refused() {
    let src = r#"
namespace dqd5w_eff
  import anthill.prelude.{Bool, Int64, Error}

  operation pure_flag(x: Int64) -> Bool = x === 1
  operation loud_flag(x: Int64) -> Bool effects Error = x === 1

  fact mark(1)
  rule pure_fires(?m) :- mark(?m), pure_flag(1)
  rule loud_fires(?m) :- mark(?m), loud_flag(1)
end
"#;
    let mut kb = load_kb_with(src);
    assert_eq!(
        definite_unary(&mut kb, "dqd5w_eff.pure_fires").len(),
        1,
        "the effect-free twin must decide — otherwise the row below measures an          un-drivable fixture rather than the effect gate"
    );
    assert_eq!(
        definite_unary(&mut kb, "dqd5w_eff.loud_fires").len(),
        0,
        "a CONCRETE effect row (`Error`) must keep the operation out of the relational \
         view — the DQD5W widening is for row PARAMETERS only"
    );
}

/// THE CONSEQUENCE THE TICKET WAS FOUND BY, driven rather than described. A
/// QUANTIFIED constraint over `nonEmpty` — the enforced form (WI-023) — is what
/// `examples/guardians` wanted to write for "a verdict must say something". With the
/// goal inert it LOADED and then fired on EVERY row, well-formed ones included,
/// because the `-:` body could never hold; from the acceptance test's side that is
/// indistinguishable from a constraint that works.
///
/// Two arms, and the second is what makes the first mean anything: a corpus of
/// well-formed rows must LOAD, and a corpus containing a violating row must be
/// REFUSED naming the constraint. Before the change the first arm failed and the
/// second passed — a constraint that rejects the whole world passes any test that
/// only checks that violations are caught.
///
/// THIS ROW NEEDS ALL THREE FIXES, which is why it is not the acceptance row: the
/// effect-row widening routes the goal, the kind-anchor leaf lets it decide, and the
/// `Value::Term` materialization is what makes any of it reach a GUARD body at all.
/// Backing out the materialization alone fails it —
/// `a_constraint_guard_body_takes_the_relational_view` is the row that attributes that
/// third one, and it does so with `contains` rather than a spec op.
#[test]
fn a_quantified_constraint_over_a_spec_op_holds_for_well_formed_rows() {
    let corpus = |extra: &str| {
        format!(
            r#"
namespace dqd5w_con
  import anthill.prelude.{{List, String, Bool}}
  import anthill.prelude.Iterable.{{nonEmpty}}

  sort Box
    entity Box(items: List[T = String])
  end

  constraint labels_are_not_empty:
    forall ?ls: Box(items: ?ls) -: nonEmpty(?ls)

  fact Box(items: ["a"])
  fact Box(items: ["b", "c"])
{extra}
end
"#
        )
    };
    let ok = try_load_kb_with(&corpus(""));
    assert!(
        ok.is_ok(),
        "every Box here HAS labels, so the constraint must hold — it fired on all of \
         them while `nonEmpty(?ls)` had no clauses to try: {:?}",
        ok.err()
    );
    let violated = try_load_kb_with(&corpus("  fact Box(items: [])"));
    let errs = violated.err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("labels_are_not_empty")),
        "the CONTROL: an empty Box must be refused NAMING the constraint, or the arm \
         above is passing over a guard that enforces nothing; got {errs:?}"
    );
}

// ── Two defects found while verifying the above, both at the Bool view's own hook ──
//
// Neither is about spec ops: each is measured with `List.contains`, this ticket's OWN
// CONTROL, which decided in a rule body before any of this. They are fixed here rather
// than filed because the first is ENLARGED by the widening above (a change whose note
// says it "costs a reduction attempt, never a wrong answer" may not ship one) and the
// second is the ticket's stated CONSEQUENCE, which the widening alone did not close.

/// THE HOOK IS ARITY-GATED, per §5.3's own words ("the gating applies only in goal
/// position and at the operation's declared arity"). It was not, and the cost was a
/// WRONG ANSWER: the rewrite wrapped a 3-ary goal on a 2-param operation in
/// `eq(…, true)`, `reduce_op_value` read its arguments BY ARG PLACE and dropped the
/// extra column, and the goal answered ONE DEFINITE solution with `?r` still free.
/// The `"z"` twin answered 0, so the pair read exactly like a working 3-place relation.
///
/// WHAT FAILS WHEN BACKED OUT (drop the `declared_arity == …` conjunct): both rows —
/// `?r` comes back a free `Var` for `"a"` and the `"z"` row answers nothing at all.
///
/// AND THE GATE IS WHY THEY ANSWER *CORRECTLY* NOW, which is the part a reader should
/// not have to infer: the un-gated Bool hook was SHADOWING the arity+1 hook below it,
/// which is the view a 3-ary goal on a 2-param op actually wants. With the Bool hook
/// declining, WI-938's functional-relation view takes the goal and BINDS `?r`.
#[test]
fn an_arity_mismatched_bool_goal_takes_the_functional_relation_view() {
    let src = r#"
namespace dqd5w_ar
  import anthill.prelude.{List, String, Bool}
  import anthill.prelude.List.{contains}

  sort Box
    entity Box(items: List[T = String])
  end

  fact Box(items: ["a"])

  rule present(?r) :- Box(items: ?ls), contains(?ls, "a", ?r)
  rule absent(?r)  :- Box(items: ?ls), contains(?ls, "z", ?r)
end
"#;
    let mut kb = load_kb_with(src);
    for (qn, want) in [("dqd5w_ar.present", true), ("dqd5w_ar.absent", false)] {
        let got = definite_unary(&mut kb, qn);
        assert_eq!(got.len(), 1, "`{qn}` must answer exactly once; got {got:?}");
        assert!(
            matches!(got[0], Value::Bool(b) if b == want),
            "`{qn}` must BIND the result column to {want}; a free `Var` here is the \
             un-gated Bool hook reporting a definite answer it never computed. Got {:?}",
            got[0]
        );
    }
}

/// A CONSTRAINT GUARD takes the relational view too — the ticket's stated consequence,
/// and the half the effect-row widening alone did NOT close.
///
/// `lower_query` hands the resolver a hash-consed `Value::Term` goal where a rule body
/// carries an occurrence, and `reduce_op_value` folds only a `Value::Node` — so the
/// guard body could never hold. Measured on `main`: `no ?ls: Box(items: ?ls) -:
/// contains(?ls, "z")` LOADED CLEAN over `fact Box(items: ["z"])`.
///
/// `contains` IS THE ROW THAT PROVES THIS IS NOT THE SPEC-OP DEFECT — it is the
/// operation the ticket names as working — so both are driven, and each in both
/// polarities so a guard that fired on everything (or nothing) fails either way.
///
/// WHAT FAILS WHEN BACKED OUT (drop the `Value::Term` materialization): the two
/// `SHOULD fire` arms — the file loads clean where a constraint must refuse it.
#[test]
fn a_constraint_guard_body_takes_the_relational_view() {
    let case = |items: &str, goal: &str| {
        format!(
            r#"
namespace dqd5w_gd
  import anthill.prelude.{{List, String, Bool}}
  import anthill.prelude.List.{{contains}}
  import anthill.prelude.Iterable.{{isEmpty}}

  sort Box
    entity Box(items: List[T = String])
  end

  constraint none_bad:
    no ?ls: Box(items: ?ls) -: {goal}

  fact Box(items: {items})
end
"#
        )
    };
    for (label, items, goal, must_fire) in [
        (
            "contains, witness present",
            r#"["z"]"#,
            r#"contains(?ls, "z")"#,
            true,
        ),
        (
            "contains, no witness",
            r#"["a"]"#,
            r#"contains(?ls, "z")"#,
            false,
        ),
        ("isEmpty, witness present", "[]", "isEmpty(?ls)", true),
        ("isEmpty, no witness", r#"["a"]"#, "isEmpty(?ls)", false),
    ] {
        let errs = try_load_kb_with(&case(items, goal))
            .err()
            .unwrap_or_default();
        let fired = errs.iter().any(|e| e.contains("none_bad"));
        assert_eq!(
            fired,
            must_fire,
            "{label}: expected the guard to {} — got {errs:?}",
            if must_fire { "REFUSE the load" } else { "hold" }
        );
    }
}

/// THE WIDENING'S FULL ADMITTED CLASS, driven — because the comment this ticket
/// DELETED named `Stream.isEmpty` as the example of what the effect gate refuses, and a
/// reader of the diff alone would not learn that it is now admitted (raised by
/// /code-review).
///
/// `Stream.isEmpty(s: Stream) -> Bool effects s.E` is the row's OTHER parametric
/// spelling: a path-dependent PROJECTION of a receiver's effect parameter, not a bare
/// parameter. `effect_member_is_parametric` treats both as parametric and its own doc
/// names these two spellings, so admitting one admits the other; this row says so with
/// a measurement instead of leaving it to be inferred.
///
/// Driven in BOTH polarities over one `List` (which provides `Stream` with `E = {}`),
/// so a predicate that answered everything fails as loudly as one that answered
/// nothing. Fails when the effect widening is backed out.
#[test]
fn the_projected_row_spelling_is_admitted_too() {
    let src = r#"
namespace dqd5w_str
  import anthill.prelude.{List, String, Bool}
  import anthill.prelude.Stream.{isEmpty, nonEmpty}

  sort Box
    entity Box(items: List[T = String])
  end

  fact Box(items: ["a", "b"])
  fact Box(items: [])

  rule empty(?ls) :- Box(items: ?ls), isEmpty(?ls)
  rule full(?ls)  :- Box(items: ?ls), nonEmpty(?ls)
end
"#;
    let mut kb = load_kb_with(src);
    let empty = definite_unary(&mut kb, "dqd5w_str.empty");
    let full = definite_unary(&mut kb, "dqd5w_str.full");
    assert_eq!(
        empty.len(),
        1,
        "`Stream.isEmpty`'s `{{s.E}}` row is a PROJECTION of a parameter, so the goal \
         must decide; got {empty:?}"
    );
    assert_eq!(full.len(), 1, "and so must its inverse; got {full:?}");
    assert_ne!(
        format!("{:?}", empty[0]),
        format!("{:?}", full[0]),
        "`isEmpty` and `nonEmpty` picked the SAME Box"
    );
}
