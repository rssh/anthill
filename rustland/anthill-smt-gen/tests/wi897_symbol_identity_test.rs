//! WI-897 — WHAT AN OPERATION MEANS TO SMT-GEN IS ITS SYMBOL, NOT ITS PRINTED NAME.
//!
//! Every `map_*_op` table in `lib.rs` used to decide an operation's SMT-LIB meaning by
//! comparing `qualified_name_of(functor)` against literal strings, each spelling a
//! fully-qualified / sort-qualified / bare TRIPLE — `"anthill.prelude.Numeric.add" |
//! "Numeric.add" | "add"`. WI-680 recorded what the loose arms cost: a user's own
//! same-named operation is indistinguishable from the prelude's and is silently
//! reinterpreted as the SMT builtin. `SMT_BUILTINS` is now resolved against the KB once
//! and matched by `Symbol`, so a name no longer decides anything.
//!
//! WHAT DRIVES THE COLLISION HERE. A user's op has to actually PRINT as one of the
//! dropped spellings, or the test measures nothing — `test.wi897.add` never matched
//! those tables in the first place. A TOP-LEVEL `sort Numeric` is how: the stdlib's own
//! `sort anthill.prelude.Numeric` shows a sort is a top-level item with its own
//! qualified name, so an undotted one qualifies its members as `Numeric.add` exactly —
//! the middle arm of the old triple, verbatim.
//!
//! CONTROL, MEASURED by reverting `lib.rs` and re-running this file: exactly the three
//! collision tests FAIL, and the emitted SMT names the damage —
//!
//!     (define-fun var_1 () Real (+ var_0 1.0))                  <- the user's Numeric.add
//!     (define-fun var_1 () Real (ite (<= var_0 1.0) 1.0 0.0))   <- the user's Ord.lte
//!     (define-fun var_1 () Real (ite (= var_0 1.0) 1.0 0.0))    <- the user's Widget.eq
//!
//! — three operations that answer their first argument, `false`, and `true` respectively,
//! each silently replaced by the SMT builtin that shares its short name.
//! `no_prelude_op_regressed` PASSES in that same revert, and passes now: it is the other
//! direction, and it is what stops a "fix" that simply recognised nothing from satisfying
//! this file.

use super::common::load_kb_with;

use anthill_smt_gen::{emit_satisfiability_check, lift_rule_to_implication_clause};

/// Three user sorts with an operation that is deliberately NOT what SMT would make of
/// it: `Numeric.add` answers its FIRST argument, `Ord.lte` answers `false` for every
/// pair, `Widget.eq` answers `true` for every pair.
///
/// The first two are named exactly as the prelude spec sorts whose members the old
/// tables spelled sort-qualified. `Widget` is not, and does not need to be:
/// `is_eq_functor` matched the SHORT name `eq`, so any sort at all collided with it.
const COLLIDING_SRC: &str = r#"
sort Numeric
  import anthill.prelude.{Float}
  operation add(a: Float, b: Float) -> Float = a
end

sort Ord
  import anthill.prelude.{Float, Bool}
  operation lte(a: Float, b: Float) -> Bool = false
end

sort Widget
  import anthill.prelude.{Float, Bool}
  operation eq(a: Float, b: Float) -> Bool = true
end

namespace test.wi897
  import anthill.prelude.{Float, Bool}
  import anthill.prelude.PartialOrd.{lt}
  import anthill.prelude.Bool.{ite}

  -- Expression position — the `map_arith_op` reader.
  rule user_add(?w)
    :- ?w = Numeric.add(?x, 1.0),
       lt(?w, 0.0)

  -- Condition position — the `map_inequality_op` reader.
  rule user_lte(?w)
    :- ?w = ite(Ord.lte(?x, 1.0), 1.0, 0.0),
       lt(?w, 0.0)

  -- Condition position — the `is_eq_functor` reader, which matched a bare short
  -- name and so did not even need the sort to be spelled `PartialEq`.
  rule user_eq(?w)
    :- ?w = ite(Widget.eq(?x, 1.0), 1.0, 0.0),
       lt(?w, 0.0)
end
"#;

/// The prelude's own operations, reached by import, in the same two positions.
const PRELUDE_SRC: &str = r#"
namespace test.wi897.prelude_side
  import anthill.prelude.{Float, Bool}
  import anthill.prelude.Numeric.{add}
  import anthill.prelude.PartialOrd.{lt, lte}
  import anthill.prelude.Bool.{ite}

  rule prelude_add(?w)
    :- ?w = add(?x, 1.0),
       lt(?w, 0.0)

  rule prelude_lte(?w)
    :- ?w = ite(lte(?x, 1.0), 1.0, 0.0),
       lt(?w, 0.0)
end
"#;

/// A user's `Numeric.add` is NOT SMT `+`. Backed out, this emits `(+ var_0 1.0)`.
#[test]
fn a_user_sorts_add_is_not_smt_addition() {
    let kb = load_kb_with(COLLIDING_SRC);
    assert!(
        kb.has_qualified_name("Numeric.add"),
        "the fixture must actually mint the colliding qualified name `Numeric.add`, \
         or this test is measuring nothing"
    );
    let err = match emit_satisfiability_check(&kb, "test.wi897.user_add") {
        Err(e) => e.message,
        Ok(smt) => {
            panic!("a user's own `Numeric.add` must not be lowered at all — smt-gen gave:\n{smt}")
        }
    };
    assert!(
        err.contains("Numeric.add"),
        "the refusal must name the operation it does not know — got {err:?}"
    );
}

/// A user's `Ord.lte` is NOT SMT `<=`. Backed out, this emits `(<= var_0 1.0)`.
#[test]
fn a_user_sorts_lte_is_not_smt_comparison() {
    let kb = load_kb_with(COLLIDING_SRC);
    assert!(
        kb.has_qualified_name("Ord.lte"),
        "the fixture must actually mint the colliding qualified name `Ord.lte`, \
         or this test is measuring nothing"
    );
    let err = match emit_satisfiability_check(&kb, "test.wi897.user_lte") {
        Err(e) => e.message,
        Ok(smt) => {
            panic!("a user's own `Ord.lte` must not be lowered at all — smt-gen gave:\n{smt}")
        }
    };
    assert!(
        err.contains("Ord.lte"),
        "the refusal must name the operation it does not know — got {err:?}"
    );
}

/// A user's `Widget.eq` is NOT SMT equality. Backed out, this emits `(= var_0 1.0)`.
#[test]
fn a_user_sorts_eq_is_not_smt_equality() {
    let kb = load_kb_with(COLLIDING_SRC);
    let err = match emit_satisfiability_check(&kb, "test.wi897.user_eq") {
        Err(e) => e.message,
        Ok(smt) => {
            panic!("a user's own `Widget.eq` must not be lowered at all — smt-gen gave:\n{smt}")
        }
    };
    assert!(
        err.contains("Widget.eq"),
        "the refusal must name the operation it does not know — got {err:?}"
    );
}

/// THE OTHER DIRECTION, and the reason the three above are not satisfied by an emitter
/// that recognises nothing: the prelude's `Numeric.add` and `PartialOrd.lte`, reached
/// by import, still lower to `(+ …)` and `(<= …)`. Passes either way by design.
#[test]
fn no_prelude_op_regressed() {
    let kb = load_kb_with(PRELUDE_SRC);
    let add = emit_satisfiability_check(&kb, "test.wi897.prelude_side.prelude_add")
        .unwrap_or_else(|e| panic!("emit prelude_add: {}", e.message));
    assert!(
        add.contains("(+ "),
        "the prelude's `Numeric.add` must still lower to SMT `+` — got:\n{add}"
    );
    let lte = emit_satisfiability_check(&kb, "test.wi897.prelude_side.prelude_lte")
        .unwrap_or_else(|e| panic!("emit prelude_lte: {}", e.message));
    assert!(
        lte.contains("(<= "),
        "the prelude's `PartialOrd.lte` must still lower to SMT `<=` — got:\n{lte}"
    );
}

/// WI-897 follow-through — AN ABSTRACT LIFT MUST NOT DROP A PREMISE IT CANNOT LOWER.
///
/// `lift_rule_to_implication_clause` runs `abstract_mode`, whose job is to leave a RULE
/// CALL unexpanded (chasing it would condition a universal claim on facts the consumer
/// never quoted). It used to skip whatever reached it, rule call or not — so a premise
/// this table does not recognise vanished, and the lemma spliced into the consumer's
/// SMT as `(=> true <conclusion>)`: a conditional claim silently promoted to an
/// unconditional axiom, which is a FALSE "proved", not a missing feature.
///
/// `String.lte` is the sharpest witness: it is a real, resolvable, legal comparison
/// that this Real-typed emitter deliberately refuses (a lexicographic order is not
/// `(<= …)` over Reals — see `SMT_BUILTINS`), and it has no program clauses, so it can
/// only be the not-a-rule case. CONTROL: with the guard removed this returns `Ok`, and
/// the clause it returns contains `(=> true` — the premise gone.
#[test]
fn an_unlowerable_premise_is_refused_by_the_lift_not_dropped() {
    let kb = load_kb_with(
        r#"
namespace test.wi897.lift
  import anthill.prelude.{Float, String, Bool}
  import anthill.prelude.PartialOrd.{lte}

  rule leaks_a_premise: lte(?d, 100.0)
    :- String.lte(?name, "z"),
       lte(?d, 5.0)
end
"#,
    );
    let err = match lift_rule_to_implication_clause(&kb, "test.wi897.lift.leaks_a_premise") {
        Err(e) => e.message,
        Ok(clauses) => panic!(
            "a premise smt-gen cannot lower must refuse the lift, not vanish from it — \
             got:\n{}",
            clauses.join("\n")
        ),
    };
    assert!(
        err.contains("String.lte"),
        "the refusal must name the premise it could not lower — got {err:?}"
    );
}
