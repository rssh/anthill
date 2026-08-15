//! WI-1104 — the rule-body arity tolerance is scoped to the position it was always
//! about, and the relational goal's RESULT COLUMN is type-checked.
//!
//! WI-1100 made a call's argument count a load error and carried ONE tolerance: in a rule
//! body a call at the operation's arity + 1 is admitted, because that is the FUNCTIONAL-
//! RELATION view (kernel §5.3, WI-938) — `vec_add(a, b, ?c)` resolves as
//! `unify(vec_add(a, b), ?c)`. It is not optional, and that is RE-MEASURED here rather
//! than cited: with `relational_result_column` forced to `None`, **21** tests fail — the
//! 17 across `wi1026` (5) / `wi1035` (1) / `wi1043` (7) / `wi1044` (3) / `wi1100` (1) that
//! WI-1100 counted, plus 4 of this file's own. Re-measuring it is the point: those 17 are
//! written in the GOAL spelling, so their staying green is what says the new threading
//! actually delivers `NodePos::RuleBodyGoal` to the position the tolerance lives at.
//!
//! **THE DEFECT: the tolerance was POSITION-BLIND.** It was gated on
//! `TypingEnv::rule_body_dispatch`, a PER-RULE flag, while the distinction it wants is
//! GOAL-vs-VALUE — which is `BodyPos`, and `BodyPos` lives in the rule-body walk
//! (`dispatch_calls_in_occ`), not in the typing env. So the +1 was admitted in a VALUE
//! position too, and this is a live program rather than a hypothetical:
//!
//! ```anthill
//! rule r(?y) :- leaf().describe(?d), ?y = concat("a", "b", "c")   -- loaded clean
//! ```
//!
//! `concat` is binary. The three-argument call sits in the right-hand side of an `=`
//! goal, which loads as a call on the body-less `PartialEq.eq` and so is type-checked as
//! one whole atom with the rule-body flag set. An operation body carrying the same
//! expression is refused. One program, two verdicts, decided by where it is written.
//!
//! **THE FIX: `NodePos` rides the typer's work-stack frame.** Beside `expected` and
//! `fuel`, which are per-node for the same reason — an env flag is inherited by nested
//! calls and separates nothing. `dispatch_calls_in_occ` is the one thing in the language
//! that knows the answer (it owns goal descent), so it tells `type_check_node_at`; from
//! there `NodePos::Value` is the default every CHILD visit takes, and only a re-Visit that
//! REPLACES a node (a `[simp]` fire's RHS, the call a dot lowers to, a WI-411 spec-op
//! redirect) inherits the goal position — a rewrite of the goal is still the goal.
//!
//! **THE SECOND HALF, same site and same cause.** The extra column was admitted but never
//! TYPE-checked: the positional validation loop reads `written_params.get(i)`, so an
//! argument past the declared list is skipped. Nothing anywhere related it to the
//! operation's declared return — the goal's shape is decided at resolution
//! (`functional_relation_arity` / `dispatched_relation_arity`, kb/resolve.rs), which reads
//! the arity and never the return. `Desc.describe(leaf(), "not an int")` against
//! `-> Int64` loaded clean and answered nothing: a dead goal indistinguishable from one
//! with no solutions, which is exactly the deferral WI-1100 exists to remove. Once the
//! position is known at the check, the column IS the operation's return and is validated
//! (`relational_result_column` / `result_column_error`, kb/typing.rs).
//!
//! **NOT quite "like any argument", and both differences were review-found.** Which
//! argument is the column is decided at the arity verdict, but the COMPARISON waits for
//! `proj_return_type` — a projection return (`-> b.T`) is discharged against the
//! receiver ~150 lines later, and comparing against the written spelling refused the
//! correct `box(v: 3).get(3)` with `expected b.T, got Int64`. And the relation is
//! two-directional: an argument flows IN, so `actual <: declared` is its whole question,
//! while a column is a UNIFICATION target the resolver coerces nothing into — under the
//! argument direction alone a column WIDER than a named-tuple return loaded clean, since
//! more fields is a subtype of fewer.
//!
//! WHAT FAILS IF EACH PIECE IS BACKED OUT — MEASURED, four reverts, four runs. The last
//! two pieces are review findings, each kept as its own column because each was a
//! separate way for a check that "passes its own test" to be wrong:
//!
//! | test | position gate | column check | σ-eliminated return | reverse direction |
//! |---|---|---|---|---|
//! | `a_value_position_call_over_the_arity_is_refused` | **FAILS** | ok | ok | ok |
//! | `a_value_position_dot_over_the_arity_is_refused` | **FAILS** | ok | ok | ok |
//! | `a_result_column_contradicting_the_return_is_refused` | ok | **FAILS** | ok | ok |
//! | `a_projection_return_column_is_checked_against_the_eliminated_type` | ok | — | **FAILS** | ok |
//! | `a_column_that_cannot_unify_is_refused_in_either_width_direction` | ok | — | ok | **FAILS** |
//! | `a_goal_position_relational_column_still_loads_and_answers` | ok | ok | ok | ok |
//! | `a_ground_well_typed_result_column_still_loads` | ok | ok | ok | ok |
//! | `a_value_position_call_at_the_declared_arity_still_loads` | ok | ok | ok | ok |
//! | `wi1100…::a_rule_body_relational_goal_still_loads` | ok | ok | ok | ok |
//! | `wi1100…::a_rule_body_goal_two_over_the_arity_is_still_refused` | ok | ok | ok | ok |
//!
//! Each of the two review columns was run over the WHOLE `wi_tests` binary, not just this
//! file: **exactly one** test fails in each (2804 passed / 1 failed), so neither fix is
//! paying for itself with someone else's coverage. A `—` is not "ok": with the column
//! check gone those two rows are vacuous, since there is nothing left to be wrong.
//!
//! The last five pass either way BY DESIGN — they are the false-positive half, and four
//! of them are what would break if the threading leaked or dropped: the driven goal (the
//! qualified spelling), `wi1100`'s pair (which drives the DOTTED spelling too, whose
//! position must survive the DotApply → synthesized-`Apply` lowering), and the
//! exact-arity value call (which must not be swept up by the narrowing). The
//! whole-tolerance revert above is the further column that measures them.
//!
//! WHAT THE CORPUS SAYS, MEASURED rather than predicted — an `anthill load` sweep over
//! all thirteen `.anthill` projects in the repo, instrumented at the arity check:
//!
//! | project | rule-body GOAL calls | rule-body VALUE calls |
//! |---|---|---|
//! | stdlib + host bindings | 44 | 40 |
//! | `anthill-todo` | 22 | 20 |
//! | `examples/webots-modelling/lf1` | 106 | 122 |
//!
//! **Every project still loads clean.** Two readings, and both matter. The gate is NOT
//! inert — 40 rule-body calls in stdlib alone are decided differently by it, having
//! carried the tolerance until this ticket. And no shipped program was RELYING on the
//! tolerance in a value position, so the narrowing refuses nothing that exists: the
//! defect it closes is a hole, not a used feature.
//!
//! The RESULT-COLUMN check is reached **zero** times across that same corpus, and **93**
//! times across the `wi_tests` binary — **85 of them DECIDABLE** (both the column's type
//! and the return ground, so the check fires rather than deferring), over 47 distinct
//! callees including the stdlib's own `Numeric.add` (22), `Numeric.mul` and
//! `PartialOrd.gt`. Both halves of that are worth stating. A corpus zero is not coverage
//! (WI-1034/WI-1063) — no shipped `.anthill` program writes the shape, because it needs a
//! callee with a SIGNATURE at the goal, which today means a spec op or a dot (a plain
//! operation named as a goal is a `CallDispatch::Subgoal` and never reaches
//! `check_apply_iter`). But 85 decided sites in the suite is the real exposure: a wrong
//! check here would refuse programs those five sibling tickets exist to keep working —
//! and it is why both review findings were re-measured over the whole binary, not here.
//!
//! REFERENCE: WI-1100; WI-1058 (`BodyPos`); WI-1043; WI-1026; WI-938; kernel §5.3.

use crate::common::try_load_kb_with;

/// SIBLING-MODULE REUSE, the house pattern in this cluster: the `Desc`/`Leaf` fixture and
/// the goal DRIVER are `wi1026`'s, so this file's controls exercise the same program whose
/// answers that ticket measured rather than a look-alike copy of it.
use crate::wi1026_rule_body_spec_op_dispatch_test::{answer, program, TWO_LEAF};

fn refusal(src: &str) -> String {
    match try_load_kb_with(src) {
        Ok(_) => panic!("expected a load refusal, but the program loaded clean\n{src}"),
        Err(errs) => errs.join(" | "),
    }
}

fn loads(src: &str) {
    if let Err(errs) = try_load_kb_with(src) {
        panic!("expected a clean load, got: {}\n{src}", errs.join(" | "));
    }
}

/// The ticket's own program, verbatim. `concat` is binary and the three-argument call is
/// the right-hand side of an `=` goal — a VALUE inside a goal, not a goal.
const VALUE_POSITION_CONCAT: &str = r#"
namespace test.wi1104.value
  import anthill.prelude.String.{concat}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    operation describe(x: Leaf) -> Int64 = 7
    provides Desc[T = Leaf]
  end

  rule r(?y) :- leaf().describe(?d), ?y = concat("a", "b", "c")
end
"#;

// ── half 1: the tolerance is a GOAL's, not a rule's ─────────────────────────

/// THE HEADLINE. Refused now, and the diagnostic is WI-1100's own — the declared arity,
/// the count given, and the callee — because the position gate changes WHO the tolerance
/// covers, not what the refusal says.
#[test]
fn a_value_position_call_over_the_arity_is_refused() {
    let msg = refusal(VALUE_POSITION_CONCAT);
    assert!(
        msg.contains("expected 2 arguments") && msg.contains("got 3 arguments"),
        "the diagnostic must state the declared arity AND the count given; got: {msg}",
    );
    assert!(
        msg.contains("anthill.prelude.String.concat"),
        "and name the operation; got: {msg}",
    );
}

/// The VALUE-position CONTROL: the same program at the declared arity still loads. This is
/// what says the refusal above is about the count and not about the position itself.
#[test]
fn a_value_position_call_at_the_declared_arity_still_loads() {
    loads(&VALUE_POSITION_CONCAT.replace(r#"concat("a", "b", "c")"#, r#"concat("a", "b")"#));
}

/// The DOT spelling of the same defect, and the reason it is a separate column: a dot
/// reaches the arity check through a DIFFERENT path — `DotApply` resolves the member and
/// re-Visits a SYNTHESIZED `Apply`, so the position must survive that lowering. Here it is
/// a value (the right-hand side of an `=`), so arity + 1 is refused; the goal spelling of
/// the very same lowering is `wi1100`'s `a_rule_body_relational_goal_still_loads`, which
/// must keep loading.
#[test]
fn a_value_position_dot_over_the_arity_is_refused() {
    let msg = refusal(
        r#"
namespace test.wi1104.valuedot
  import anthill.prelude.Int64

  sort Box
    entity box(v: Int64)
    operation get(b: Box) -> Int64 = b.v
  end

  rule r(?y) :- ?y = box(v: 1).get(2)
end
"#,
    );
    assert!(
        msg.contains("expected 1 argument") && msg.contains("got 2 arguments"),
        "got: {msg}",
    );
}

// ── half 2: the result column is the operation's RETURN ─────────────────────

/// THE SECOND HALF. `describe` returns `Int64`; the goal writes a `String` in the column
/// that receives that result, so the goal can never unify and the rule silently answers
/// nothing. Refused at load, naming the operation's RETURN — the column fills no
/// parameter, so naming one would point the author at the wrong thing.
#[test]
fn a_result_column_contradicting_the_return_is_refused() {
    let msg = refusal(&program(
        "test.wi1104.badcol",
        TWO_LEAF,
        "",
        "  rule answer(?r) :- Desc.describe(leaf(), \"not an int\")\n",
    ));
    assert!(
        msg.contains("describe") && msg.contains("return"),
        "the diagnostic must name the operation's return; got: {msg}",
    );
    assert!(
        msg.contains("Int64") && msg.contains("String"),
        "and both types; got: {msg}",
    );
}

/// THE CONTROL FOR IT, DRIVEN: the ordinary spelling — an unbound `?r` — is exactly the
/// shape the check must not touch (its type is not ground, so it is left to resolution),
/// and the rule still ANSWERS. Loading clean is not enough here: this is the delivered
/// feature the whole tolerance exists for, so it is resolved, not merely accepted.
#[test]
fn a_goal_position_relational_column_still_loads_and_answers() {
    let ns = "test.wi1104.okcol";
    let src = program(
        ns,
        TWO_LEAF,
        "",
        "  rule answer(?r) :- Desc.describe(leaf(), ?r)\n",
    );
    assert_eq!(
        answer(ns, &src),
        7,
        "the carrier's own member supplies the answer through the relational column",
    );
}

/// …and a GROUND, well-typed column loads too — the half of the check that fires and
/// PASSES. Without this, a check that refused every ground column would look identical to
/// a correct one from the refusal test alone.
#[test]
fn a_ground_well_typed_result_column_still_loads() {
    loads(&program(
        "test.wi1104.groundcol",
        TWO_LEAF,
        "",
        "  rule answer(?r) :- Desc.describe(leaf(), 7)\n",
    ));
}

// ── the two review findings, each with the program that found it ────────────

/// A PROJECTION RETURN (`-> b.T`), and the reason the comparison happens where it does.
/// The first cut read `op.return_type` at the arity verdict, where the return is still
/// the un-discharged `b.T`; that spelling is DETERMINED, so the check fired and refused
/// this correct program with `expected b.T, got Int64` — a type the author never wrote.
/// Comparing against `proj_return_type` — the return after WI-376 discharges the
/// projection against the receiver's argument — both accepts it and CHECKS it: the
/// mismatched twin below names `Int64`, the eliminated type, not `b.T`.
///
/// Both halves matter. Skipping a projection return would have passed the accepting half
/// alone, so the refusal is what says the fix restored coverage rather than dropping it.
#[test]
fn a_projection_return_column_is_checked_against_the_eliminated_type() {
    let src = |col: &str| {
        format!(
            r#"
namespace test.wi1104.proj
  import anthill.prelude.Int64

  sort Box
    sort T = ?
    entity box(v: T)
    operation get(b: Box) -> b.T = b.v
  end

  rule r() :- box(v: 3).get({col})
end
"#
        )
    };
    loads(&src("3"));
    loads(&src("?c"));
    let msg = refusal(&src("\"s\""));
    assert!(
        msg.contains("expected Int64") && msg.contains("got String"),
        "the diagnostic must name the ELIMINATED return, not the `b.T` projection; got: {msg}",
    );
}

/// A column is a UNIFICATION TARGET, so it is checked in BOTH directions — the second
/// review finding, and its two halves are exact mirrors. Under the argument direction
/// alone (`column <: return`) the NARROW column was refused and the WIDE one loaded
/// clean, because a named tuple with more fields is a subtype of one with fewer. Neither
/// can ever unify with the returned tuple, so admitting one of them was the check
/// producing the very defect it exists to remove.
#[test]
fn a_column_that_cannot_unify_is_refused_in_either_width_direction() {
    let src = |goal: &str| {
        format!(
            r#"
namespace test.wi1104.width
  import anthill.prelude.Int64

  sort Rec
    entity mk(v: Int64)
    operation pair(r: Rec) -> (a: Int64, b: Int64) = (a: 1, b: 2)
    operation triple(r: Rec) -> (a: Int64, b: Int64, c: Int64) = (a: 1, b: 2, c: 3)
  end

  rule w() :- {goal}
end
"#
        )
    };
    let wide = refusal(&src("mk(v: 0).pair((a: 1, b: 2, c: 3))"));
    assert!(
        wide.contains("expected (a: Int64, b: Int64)")
            && wide.contains("got (a: Int64, b: Int64, c: Int64)"),
        "a column WIDER than the return; got: {wide}",
    );
    let narrow = refusal(&src("mk(v: 0).triple((a: 1, b: 2))"));
    assert!(
        narrow.contains("expected (a: Int64, b: Int64, c: Int64)")
            && narrow.contains("got (a: Int64, b: Int64)"),
        "a column NARROWER than the return; got: {narrow}",
    );
    // The control that keeps this from being "refuse every tuple column".
    loads(&src("mk(v: 0).pair((a: 1, b: 2))"));
    loads(&src("mk(v: 0).pair(?t)"));
}
