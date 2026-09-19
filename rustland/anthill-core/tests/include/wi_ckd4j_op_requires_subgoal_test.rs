//! WI-20260918-CKD4J (prerequisite, fixed inline) — an OPERATION-level `requires`
//! answers a conditional provision's SUB-goal.
//!
//! `eq(a, b)` over `Pair[A = X, B = X]` resolves to `Pair`'s conditional provision
//! `provides PartialEq[Pair] :- PartialEq[A], PartialEq[B]`, whose sub-goal is
//! `PartialEq[X]`. Written on the operation (`… requires PartialEq[X] = eq(a, b)`),
//! that requirement was INVISIBLE to the sub-goal: the resolver's scope held only the
//! sort half of the frame chain (WI-822 LEG 1), so the call was refused at load with
//! `PartialEq.eq.dispatch … unresolved: PartialEq[T = <term#…>]` — while the
//! SORT-level spelling of the same program loaded. The sub-goal now resolves
//! `FromScope` into the op half of the frame chain
//! (`typing::ResolutionScope::sub_goal_requires`); the call's OWN goal still does
//! not, which is WI-822's decision.
//!
//! This is what the conditional `Eq`/`PartialEq` rows CKD4J derives for `Option` and
//! `List` need: a generic operation that compares containers of its own element.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ──────────────────────────────
//!
//! Backing out the sub-goal lookup in `resolve_inner` (or passing `&[]` for
//! `sub_goal_requires` at the call-site dispatch) fails
//! `an_op_level_requires_answers_the_conditional_subgoal` with the load refusal quoted
//! above. Backing out only the emission change in `classify_pin_or_apply_within`
//! (naming the tree off the sort chain) panics the same test in debug with
//! "WI-829: cross-sort constructing tree for eq failed to emit a dispatch dict".
//!
//! PASS EITHER WAY BY DESIGN: `without_the_requires_the_call_is_still_refused` (the
//! control that the lookup did not become a wildcard), and
//! `a_stronger_requires_does_not_answer_the_weaker_subgoal` (a pinned, pre-existing
//! gap shared with the sort-level spelling).

use anthill_core::eval::value::Value;

const PROGRAM: &str = r#"
namespace wickd4j.opreq
  import anthill.prelude.{Bool, Int64, Pair, PartialEq}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.PartialEq.{eq}
  sort D
    operation same[X](a: Pair[A = X, B = X], b: Pair[A = X, B = X]) -> Bool
      requires PartialEq[X] = eq(a, b)
    operation yes(n: Int64) -> Int64 =
      if same(pair(fst: 1, snd: 2), pair(fst: 1, snd: 2)) then 1 else 0
    -- The negative twin: a `same` that answered `true` vacuously would fail here.
    operation no(n: Int64) -> Int64 =
      if same(pair(fst: 1, snd: 2), pair(fst: 1, snd: 3)) then 1 else 0
  end
end
"#;

fn eval_int(src: &str, op: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(op, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{op}: expected an Int, got {other:?}"),
    }
}

fn refusals(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

#[test]
fn an_op_level_requires_answers_the_conditional_subgoal() {
    assert_eq!(
        refusals(PROGRAM),
        Vec::<String>::new(),
        "`requires PartialEq[X]` on the operation must answer `Pair`'s `PartialEq[A]` \
         sub-goal"
    );
    assert_eq!(eval_int(PROGRAM, "wickd4j.opreq.D.yes"), 1);
    assert_eq!(eval_int(PROGRAM, "wickd4j.opreq.D.no"), 0);
}

#[test]
fn without_the_requires_the_call_is_still_refused() {
    let src = r#"
namespace wickd4j.noreq
  import anthill.prelude.{Bool, Pair}
  import anthill.prelude.PartialEq.{eq}
  sort D
    operation same[X](a: Pair[A = X, B = X], b: Pair[A = X, B = X]) -> Bool = eq(a, b)
  end
end
"#;
    let errs = refusals(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("PartialEq.eq.dispatch") && e.contains("unresolved")),
        "nothing in scope answers `PartialEq[X]`, so the op-half lookup must not have \
         become a wildcard; got {errs:?}"
    );
}

/// A PINNED GAP, not this change's: `requires Eq[X]` does not answer the `PartialEq[X]`
/// sub-goal, although `Eq` provides `PartialEq`. The SORT-level spelling
/// (`sort E { sort X = ?  requires Eq[X] … }`) is refused identically, so the op
/// half is held to exactly the sort half's bar — the scope lookup is a direct cover,
/// with no projection path to follow a conversion.
#[test]
fn a_stronger_requires_does_not_answer_the_weaker_subgoal() {
    let op_level = r#"
namespace wickd4j.eqop
  import anthill.prelude.{Bool, Pair, Eq}
  import anthill.prelude.PartialEq.{eq}
  sort D
    operation same[X](a: Pair[A = X, B = X], b: Pair[A = X, B = X]) -> Bool
      requires Eq[X] = eq(a, b)
  end
end
"#;
    let sort_level = r#"
namespace wickd4j.eqsort
  import anthill.prelude.{Bool, Pair, Eq}
  import anthill.prelude.PartialEq.{eq}
  sort E
    sort X = ?
    requires Eq[X]
    operation same(a: Pair[A = X, B = X], b: Pair[A = X, B = X]) -> Bool = eq(a, b)
  end
end
"#;
    for (spelling, src) in [("operation", op_level), ("sort", sort_level)] {
        let errs = refusals(src);
        assert!(
            errs.iter().any(|e| e.contains("PartialEq.eq.dispatch")),
            "{spelling}-level `requires Eq[X]` is refused today at the `PartialEq[X]` \
             sub-goal; got {errs:?}"
        );
    }
}
