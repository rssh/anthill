//! WI-20260820-MH90F — `not` is a resolver primitive, and it is now filed with them.
//!
//! `anthill.kernel`'s own header says "resolver primitives"; it held `push_choice`,
//! `unify`, `struct_eq`, `cut` and the derived `or`. Negation-as-failure passed every
//! test they pass — a reified goal in, `-> Bool` naming the test outcome, behaviour that
//! is an effect on the search rather than a value computed from the argument — and sat
//! in `anthill.reflect`, the TERM-LEVEL namespace whose members return data about a
//! program. `kernel.unify`'s own doc comment states the convention it was violating:
//! "`-> Bool` names the test outcome; the substitution it really produces is the
//! term-level `anthill.reflect.unify` face."
//!
//! ## The move is a MOVE — no alias
//!
//! Nothing in the tree spelled the qualified name: every NAF site writes bare `not` and
//! reaches it through `PRELUDE_QUALIFIED`, or through an `import ….{not}` line that this
//! change retargets. So an alias would have had no users — and it would have had to live
//! in `anthill.reflect`, i.e. a SECOND symbol named `not` reachable from reflect's own
//! rule bodies, which is the `AmbiguousSymbol(not, [reflect.not, reflect.not])` scaland
//! hit in WI-212. `no_alias_left_behind` drives that decision rather than documenting it.
//!
//! ## What actually changes at load
//!
//! `stdlib/anthill/reflect/typing.anthill` writes bare `not(...)` from inside
//! `anthill.reflect.typing`. Before the move that resolved by SCOPE — the enclosing
//! `anthill.reflect` namespace held `not`, and scope resolution sits ABOVE the
//! implicit-prelude fallback. After it, the same source has no `not` in any enclosing
//! scope and must reach the primitive through the fallback instead.
//!
//! ## Which test fails when what is backed out — MEASURED, one piece at a time
//!
//! Three pieces ship: (A) the declaration moves to `kernel.anthill`, (B)
//! `register_builtin_tag` names `anthill.kernel.not`, (C) `PRELUDE_QUALIFIED` names it.
//!
//! **Back out (C) alone → THE STDLIB DOES NOT LOAD**, and all four tests fail through
//! `load_stdlib_kb`: `UndefinedRuleBodyGoal { functor: "not" }` at
//! `anthill.reflect.typing`. Worth recording because the opposite was the expectation —
//! a fallback pointing at a name nobody defines reads like the silent-skip class, and it
//! is not: WI-1034's rule-body-goal check refuses it at load. The dangling entry has a
//! guard, so no test here has to be the one that notices.
//!
//! **Back out (B) alone → `kernel_not_is_the_naf_primitive` and `no_alias_left_behind`
//! FAIL; both NAF rows PASS.** `register_builtin_tag`'s define arm re-mints
//! `anthill.reflect.not` in the reflect scope, so the fixture namespace reaches a tagged
//! `not` by ENCLOSING SCOPE — the exact path the move retires — and negation keeps
//! working through it. That is why the two symbol-identity tests are here at all: the
//! behavioural rows cannot tell the two paths apart, because both of them work.
//!
//! `naf_over_a_provable_goal_finds_no_solution` is the control and reads 0 under every
//! column by design: NAF over a goal that SUCCEEDS must find nothing, so it can never
//! discriminate. It is here to prove the fixture's negand really is provable, which is
//! what makes the 1 in the row above it mean negation rather than an accident.
//!
//! REFERENCE: `stdlib/anthill/kernel/kernel.anthill`; `PRELUDE_QUALIFIED` (load.rs);
//! `KnowledgeBase::POSITION_DIRECTED_BOOLEANS` (mod.rs); docs/kernel-language.md §6.6;
//! proposal 052 §Open questions 7 (why the two readings stay two symbols).

/// A namespace nested INSIDE `anthill.reflect`, so the goal `not` in it is the resolution
/// path the move changed: an enclosing-scope hit before, the implicit-prelude fallback
/// after. `mh90fEmpty` holds of nothing, so `not(mh90fEmpty(?x))` must SUCCEED and the
/// rule must answer once per `mh90fLeft` fact.
const REFLECT_SUBTREE: &str = "\
namespace anthill.reflect.mh90f
  fact mh90fLeft(1)
  fact mh90fEmpty(99)
  rule mh90fNafHolds(?x) :- mh90fLeft(?x), not(mh90fEmpty(?x))
  rule mh90fNafFails(?x) :- mh90fLeft(?x), not(mh90fLeft(?x))
end
";

/// The primitive answers at its new qualified name, and it is the NAF BUILTIN there and
/// not merely a declared operation: a goal built on the symbol classifies as
/// [`BuiltinTag::Not`], which is what `step_naf` dispatches on. Asserting only that the
/// name resolves would keep passing if `register_builtin_tags` still tagged the old one.
#[test]
fn kernel_not_is_the_naf_primitive() {
    use anthill_core::kb::resolve::BuiltinTag;
    use anthill_core::kb::term::{Literal, Term};
    use smallvec::SmallVec;

    let mut kb = crate::common::load_stdlib_kb();
    let not_sym = kb
        .try_resolve_symbol("anthill.kernel.not")
        .expect("`anthill.kernel.not` is the NAF primitive");

    // `not(true)` — the argument is irrelevant to the classification, which keys on the
    // functor; what is being read is that the TAG travelled with the symbol.
    let inner = kb.alloc(Term::Const(Literal::Bool(true)));
    let goal = kb.alloc(Term::Fn {
        functor: not_sym,
        pos_args: SmallVec::from_elem(inner, 1),
        named_args: SmallVec::new(),
    });
    assert_eq!(
        kb.get_builtin_view(&goal),
        Some(BuiltinTag::Not),
        "the builtin tag must be registered on the moved symbol"
    );
}

/// The "no deprecated alias" half of the decision, driven. `anthill.reflect.not` must
/// resolve to NOTHING — an alias, or a stale `register_builtin_tag` line, or a leftover
/// `operation not(...)` in reflect.anthill each put a second `not` back in reflect's own
/// scope, which is what WI-212 measured as an ambiguity rather than a convenience.
#[test]
fn no_alias_left_behind() {
    let kb = crate::common::load_stdlib_kb();
    assert!(
        kb.try_resolve_symbol("anthill.reflect.not").is_none(),
        "the move left an `anthill.reflect.not` behind"
    );
}

/// Bare `not` written from inside the `anthill.reflect` subtree — the source position
/// whose resolution PATH this change alters, from an enclosing-scope hit to the
/// implicit-prelude fallback — still performs negation-as-failure. Driven on the row
/// where NAF must SUCCEED, the only row that discriminates: a `not` reaching an
/// unclaused predicate answers 0, and so does a working `not` over a provable goal.
///
/// It survives both single-piece back-outs (see the module header), by design and not by
/// weakness: (C) is caught earlier and louder, at stdlib load, and (B) leaves the OLD
/// path working. What it pins is that the fallback route reaches a primitive that
/// actually negates — the claim neither symbol-identity test makes.
#[test]
fn naf_answers_from_inside_the_reflect_subtree() {
    let (mut kb, _) = crate::common::load_stdlib_kb_with_source(REFLECT_SUBTREE);
    let sols = crate::common::query_unary(&mut kb, "anthill.reflect.mh90f.mh90fNafHolds");
    assert_eq!(
        sols.len(),
        1,
        "`not(mh90fEmpty(?x))` must succeed — its goal has no solutions"
    );
}

/// The control for the row above, and it is a control precisely because it reads 0 either
/// way: `mh90fLeft(1)` IS provable, so NAF over it must find nothing. What it rules out is
/// a fixture where the negand was unprovable for some unrelated reason, which would make
/// the 1 above meaningless.
#[test]
fn naf_over_a_provable_goal_finds_no_solution() {
    let (mut kb, _) = crate::common::load_stdlib_kb_with_source(REFLECT_SUBTREE);
    let sols = crate::common::query_unary(&mut kb, "anthill.reflect.mh90f.mh90fNafFails");
    assert!(
        sols.is_empty(),
        "`not(mh90fLeft(?x))` must fail — its goal is provable"
    );
}
