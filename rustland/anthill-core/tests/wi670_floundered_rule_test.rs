//! WI-670: a rule delayed on a caller var by the open-time whole-rule
//! pre-check must be REFUTED (not residualized into a spurious solution) when
//! one of its other conjuncts is already unsatisfiable — but an honest,
//! still-satisfiable delayed rule must keep residualizing. Three cases pin the
//! boundary:
//!   1. dead rule (a refuting conjunct) → 0 solutions;
//!   2. genuine stuck builtin → 1 residual solution (kept);
//!   3. honest delayed rule (satisfiable other conjunct) → 1 residual solution
//!      (kept — the case a naive "drop any un-opened rule-goal residual" fix
//!      would wrongly discard).

mod common;

use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term, Var};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use smallvec::SmallVec;

#[test]
fn floundered_rule_with_hard_failing_conjunct_yields_zero() {
    // p(?x, ?y) :- q(?x), anthill.reflect.nonvar(?y)
    //   q has NO facts → q(a) hard-fails → whole rule is refutable.
    //   nonvar(?y) delays on the unbound caller var ?y, so the open-time
    //   pre-check delays the ENTIRE rule before its body opens, and q(a)
    //   never runs to refute the branch. The residual is then yielded as a
    //   spurious solution under the default definite_only:false.
    let source = r#"
namespace test.wi670
  sort Thing
    entity a
  end

  rule p(?x, ?y)
    :- q(?x), anthill.reflect.nonvar(?y)
end
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let parsed = parse::parse(source).expect("parse failed");
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Build p(a, ?s) with ?s an unbound query var.
    let a_term = kb.resolve_qualified_name_term("test.wi670.Thing.a");
    let s_sym = kb.intern("s");
    let s_vid = kb.fresh_var(s_sym);
    let s_term = kb.alloc(Term::Var(Var::Global(s_vid)));
    let p_sym = kb.try_resolve_symbol("test.wi670.p")
        .or_else(|| kb.try_resolve_symbol("p"))
        .expect("p symbol");
    let goal = kb.alloc(Term::Fn {
        functor: p_sym,
        pos_args: SmallVec::from_slice(&[a_term, s_term]),
        named_args: SmallVec::new(),
    });

    let config = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
    let results = kb.resolve(&[goal], &config);
    assert_eq!(
        results.len(),
        0,
        "p(a, ?s) must have 0 solutions: q(a) has no facts and hard-fails; \
         got {} (residual-as-solution flounder bug)",
        results.len()
    );
}

/// Boundary control: an HONEST delayed rule must STILL residualize. Here the
/// rule's other conjunct `is_thing(?a)` IS satisfiable (a fact `is_thing(42)`
/// exists), so `check(?a)` — delayed by `nonvar(?a)` on the unbound caller var
/// — is genuinely pending, not dead. The WI-670 refutation must NOT fire (a
/// non-delayed conjunct with a discrim WILDCARD arg keeps ≥1 candidate), so the
/// residual survives. This is the exact case a naive "drop any un-opened
/// rule-goal residual" fix wrongly discards.
#[test]
fn honest_delayed_rule_with_satisfiable_conjunct_still_residualizes() {
    let source = r#"
namespace test.wi670b
  sort Thing
    entity a
  end

  fact is_thing(name: "hello")

  rule check(?x)
    :- anthill.reflect.nonvar(?x), is_thing(name: ?x)
end
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let parsed = parse::parse(source).expect("parse failed");
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // check(?s) with ?s an unbound query var → delayed on nonvar, but the
    // is_thing conjunct is satisfiable, so it honestly residualizes.
    let s_sym = kb.intern("s");
    let s_vid = kb.fresh_var(s_sym);
    let s_term = kb.alloc(Term::Var(Var::Global(s_vid)));
    let check_sym = kb.try_resolve_symbol("test.wi670b.check")
        .or_else(|| kb.try_resolve_symbol("check"))
        .expect("check symbol");
    let goal = kb.alloc(Term::Fn {
        functor: check_sym,
        pos_args: SmallVec::from_elem(s_term, 1),
        named_args: SmallVec::new(),
    });

    let config = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
    let results = kb.resolve(&[goal], &config);
    assert_eq!(
        results.len(),
        1,
        "check(?s) must keep its honest residual (is_thing is satisfiable); got {}",
        results.len()
    );
    assert!(
        !results[0].residual.is_empty(),
        "the honest delayed check(?s) carries a residual goal"
    );
}

/// Boundary control: the WI-670 fix drops ONLY an openable rule-goal residual.
/// A genuine STUCK-BUILTIN residual (`nonvar(?s)` alone — no rule to expand,
/// honestly "holds if ?s becomes bound") must STILL count as a residual
/// solution under the default (non-definite) mode. Guards against over-dropping.
#[test]
fn genuine_stuck_builtin_residual_still_counts() {
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();

    // anthill.reflect.nonvar(?s) with ?s unbound → floundered stuck builtin.
    let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");
    let s_sym = kb.intern("s");
    let s_vid = kb.fresh_var(s_sym);
    let s_term = kb.alloc(Term::Var(Var::Global(s_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: nonvar_sym,
        pos_args: SmallVec::from_elem(s_term, 1),
        named_args: SmallVec::new(),
    });

    let config = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
    let results = kb.resolve(&[goal], &config);
    assert_eq!(results.len(), 1, "a stuck-builtin residual must still be a solution");
    assert_eq!(
        results[0].residual.len(),
        1,
        "the honest residual carries the stuck nonvar(?s) goal"
    );
}
