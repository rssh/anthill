//! WI-537 / proposal 050 — local-interpretation Γ substrate + resolver bridge.
//!
//! The acceptance: Γ carries `neq(b, 0)` inside the then-branch of
//! `if neq(b, 0)`, and the resolver bridge proves it from Γ, while a *symbolic*
//! `neq(b, 0)` (no Γ fact) stays undischarged via floundering — the open-world
//! soundness guard (048 §"Discharge is constructive refutation, not NAF").
//!
//! These exercise the NEW primitives directly: the logical storage `FlowEnv`
//! (`assume` / `is_empty`, a discrimination-tree Γ index) and the resolver
//! bridge (`prove_from_gamma` / `refute_guard`). The bridge does NOT re-implement
//! resolution — it hands Γ to the *existing* SLD resolver as its `gamma` overlay
//! (consulted like a frame's `assumed_facts`), so a goal is decided over KB ∪ Γ
//! in one search. A parameter is a non-ground logic variable (a real op
//! parameter skolemizes to `Var::Rigid`, also non-ground), so a guard over it
//! flounders — only a Γ fact discharges it. The `if`-fork narrowing that
//! *populates* Γ from a branch condition is additive (read only by WI-067
//! discharge) and is covered by the full suite staying green.

mod common;

use anthill_core::eval::value::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence, Pattern};
use anthill_core::kb::term::{Literal, Term, Var};
use anthill_core::kb::typing::{match_arm_gamma_facts, prove_from_gamma, refute_guard, FlowEnv};
use anthill_core::kb::KnowledgeBase;
use anthill_core::span::{SourceId, SourceSpan};
use std::rc::Rc;

/// `f(args)` as a transient goal `Value` (an `Entity`, the carrier
/// `make_goal_value` uses internally) — the shape the typer puts into Γ.
fn goal(functor: Symbol, args: Vec<Value>) -> Value {
    Value::Entity {
        functor,
        pos: Rc::from(args),
        named: Rc::from(Vec::new()),
    }
}

/// An op parameter as a `Value` — a fresh non-ground flex `Var::Global`. Two
/// properties are load-bearing, and BOTH hold:
///  - open-world (R1): a guard `eq(b, 0)` over the parameter is satisfiable (a
///    caller could pass 0), so `eq`/`neq` flounder on a flex var — `neq(b, 0)`
///    is NOT provable without a Γ fact. (A `Var::Rigid` skolem would instead
///    read `b ≠ 0` as definite, proving `neq(b,0)` with no Γ fact — the wrong,
///    closed-world reading — and it also carries forall distinctness semantics,
///    so it is not interchangeable here.)
///  - per-parameter (R3): a Γ fact about `b` discharges only `b`, never a
///    different parameter `c` — enforced by the identity-aware Γ match in
///    `gamma_candidates_for` (the bare discrim query alone would wildcard-match;
///    see `gamma_fact_over_one_parameter_does_not_discharge_another`).
fn param(kb: &mut KnowledgeBase, name: &str) -> Value {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    Value::Term(kb.alloc(Term::Var(Var::Global(vid))))
}

fn neq_sym(kb: &mut KnowledgeBase) -> Symbol {
    kb.try_resolve_symbol("anthill.prelude.Eq.neq").expect("neq")
}

#[test]
fn flow_env_assume_is_copy_on_write() {
    // The logical storage: `assume` extends Γ, returning a narrowed env; the
    // parent FlowEnv is unchanged (the per-Visit clone of the iterative typer
    // must not see a sibling branch's narrowing).
    let mut kb = common::load_kb_with("namespace wi537.cow\nend\n");
    let neq = neq_sym(&mut kb);
    let fact = goal(neq, vec![Value::Int(7), Value::Int(0)]);

    let flow = FlowEnv::empty();
    assert!(flow.is_empty(), "Γ₀ starts empty");

    let narrowed = flow.assume(&kb, fact);
    assert!(!narrowed.is_empty(), "assume extends Γ");
    assert!(flow.is_empty(), "assume is copy-on-write — parent Γ unchanged");
}

#[test]
fn prove_from_gamma_proves_a_fact_in_gamma_over_a_symbolic_parameter() {
    // Γ = { neq(b, 0) } with `b` a symbolic parameter. The bridge resolves
    // `neq(b, 0)` over KB ∪ Γ; the Γ fact is found as an `Assumption` candidate
    // by the SLD resolver — the then-branch case.
    let mut kb = common::load_kb_with("namespace wi537.gamma\nend\n");
    let neq = neq_sym(&mut kb);
    let b = param(&mut kb, "?b");
    let neq_b_0 = goal(neq, vec![b, Value::Int(0)]);

    let flow = FlowEnv::empty().assume(&kb, neq_b_0.clone());
    assert!(
        prove_from_gamma(&mut kb, &flow, &neq_b_0),
        "neq(b,0) ∈ Γ ⊢ neq(b,0)"
    );
}

#[test]
fn gamma_fact_over_one_parameter_does_not_discharge_another() {
    // Per-parameter soundness (R3): Γ = { neq(b, 0) } must NOT prove neq(c, 0)
    // for a DISTINCT parameter c. The discrim query alone unifies the goal var as
    // a wildcard (it would over-match); `gamma_candidates_for`'s identity filter
    // (`views_structurally_equal`) closes that, so a fact about `b` discharges
    // only `b`. With no Γ match, neq(c,0) → not(eq(c,0)) flounders → unproven.
    let mut kb = common::load_kb_with("namespace wi537.distinct\nend\n");
    let neq = neq_sym(&mut kb);
    let b = param(&mut kb, "?b");
    let c = param(&mut kb, "?c");
    let flow = FlowEnv::empty().assume(&kb, goal(neq, vec![b, Value::Int(0)]));
    assert!(
        !prove_from_gamma(&mut kb, &flow, &goal(neq, vec![c, Value::Int(0)])),
        "neq(b,0) ∈ Γ must NOT prove neq(c,0) for a distinct parameter c"
    );
}

#[test]
fn symbolic_goal_with_empty_gamma_stays_unproven_via_floundering() {
    // No Γ fact, `b` symbolic: `neq(b, 0)` → `not(eq(b, 0))`, eq(b,0) is
    // non-ground, so NAF flounders and `definite_only` drops it — UNPROVEN.
    // This is the soundness guard: failure-to-prove never becomes a "drop".
    let mut kb = common::load_kb_with("namespace wi537.flounder\nend\n");
    let neq = neq_sym(&mut kb);
    let b = param(&mut kb, "?b");
    let neq_b_0 = goal(neq, vec![b, Value::Int(0)]);

    assert!(
        !prove_from_gamma(&mut kb, &FlowEnv::empty(), &neq_b_0),
        "a symbolic neq(b,0) with empty Γ must stay unproven (floundering)"
    );
}

#[test]
fn refute_guard_discharges_an_eq_guard_from_a_neq_fact() {
    // The 048 discharge shape: a guarded effect `Error :- eq(b, 0)` at a call
    // under `if neq(b, 0)`. Γ = { neq(b, 0) }; refuting the guard eq(b, 0)
    // proves its negation neq(b, 0) from Γ (eq ⇄ neq functor swap, open Q C).
    let mut kb = common::load_kb_with("namespace wi537.refute\nend\n");
    let eq_sym = kb.eq_functor();
    let neq = neq_sym(&mut kb);
    let b = param(&mut kb, "?b");

    let guard = goal(eq_sym, vec![b.clone(), Value::Int(0)]);
    let neq_fact = goal(neq, vec![b, Value::Int(0)]);

    let flow = FlowEnv::empty().assume(&kb, neq_fact);
    assert!(
        refute_guard(&mut kb, &flow, &guard),
        "neq(b,0) ∈ Γ refutes the guard eq(b,0)"
    );
}

#[test]
fn refute_guard_keeps_the_effect_when_the_guard_is_symbolic() {
    // Same guard, but no Γ fact: eq(b, 0) cannot be refuted over a symbolic b,
    // so the effect is conservatively KEPT (refute returns false).
    let mut kb = common::load_kb_with("namespace wi537.keep\nend\n");
    let eq_sym = kb.eq_functor();
    let b = param(&mut kb, "?b");
    let guard = goal(eq_sym, vec![b, Value::Int(0)]);

    assert!(
        !refute_guard(&mut kb, &FlowEnv::empty(), &guard),
        "an unrefutable symbolic guard must keep the effect"
    );
}

// ── the `match`-arm Γ producer (`match_arm_gamma_facts`) ────────
//
// These exercise the producer side of the proposal-050 `match` rule: each arm's
// pattern fact eq(s, p) plus the negations neq(s, pⱼ) of earlier ground,
// unguarded arms. The bridge (above) is the consumer; here we check the facts
// the typer threads into each arm's Γ, and that they round-trip through the
// bridge (a negation proves, an `eq` guard refutes).

fn span() -> SourceSpan {
    SourceSpan::new(SourceId::from_raw(0), 0, 0)
}

fn lit_pat(n: i64) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_pattern(Pattern::Literal { value: Literal::Int(n) }, span(), None)
}

fn wildcard_pat() -> Rc<NodeOccurrence> {
    NodeOccurrence::new_pattern(Pattern::Wildcard, span(), None)
}

fn var_pat(name: Symbol) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_pattern(Pattern::Var { name, type_ann: None }, span(), None)
}

#[test]
fn match_case_0_carries_neq_into_the_wildcard_arm() {
    // `match s case 0 -> … case _ -> div(a, s)` — proposal 050's canonical
    // discharge case. Arm 0 (`case 0`) carries the pattern fact eq(s, 0); the
    // wildcard arm carries the earlier-arm negation neq(s, 0), which refutes a
    // later `div`'s eq(s, 0) guard straight from Γ — no branch test written.
    let mut kb = common::load_kb_with("namespace wi537.match0\nend\n");
    let s = param(&mut kb, "?s");
    let arms = vec![(lit_pat(0), false), (wildcard_pat(), false)];
    let facts = match_arm_gamma_facts(&mut kb, &s, &arms, &[]);

    assert_eq!(facts[0].len(), 1, "case 0 ⇒ one pattern fact eq(s,0)");
    assert_eq!(facts[1].len(), 1, "the wildcard arm ⇒ neq(s,0) from the earlier case 0");

    // Round-trip the wildcard arm's Γ through the bridge: the negation proves,
    // and it refutes the div guard eq(s,0).
    let mut flow = FlowEnv::empty();
    for f in &facts[1] {
        flow = flow.assume(&kb, f.clone());
    }
    assert!(prove_from_gamma(&mut kb, &flow, &facts[1][0]), "neq(s,0) ∈ Γ ⊢ neq(s,0)");
    let eq_sym = kb.eq_functor();
    let guard = goal(eq_sym, vec![s.clone(), Value::Int(0)]);
    assert!(refute_guard(&mut kb, &flow, &guard), "the wildcard arm refutes the guard eq(s,0)");
}

#[test]
fn match_negation_indexes_a_node_scrutinee() {
    // The real typer passes the scrutinee OCCURRENCE (a `Value::Node`), not a
    // bare var, into the facts. A simple `Expr::Ref` scrutinee heads as `Ref`
    // (indexable), so the negation it forms is stored and matched — this pins
    // that the `Value::Node` carrier the producer actually uses round-trips
    // (the existing bridge tests use a bare `Var::Global`).
    let mut kb = common::load_kb_with("namespace wi537.matchnode\nend\n");
    let b = kb.intern("b");
    let scrutinee = Value::Node(NodeOccurrence::new_expr(
        anthill_core::kb::node_occurrence::Expr::Ref(b),
        span(),
        None,
    ));
    let arms = vec![(lit_pat(0), false), (wildcard_pat(), false)];
    let facts = match_arm_gamma_facts(&mut kb, &scrutinee, &arms, &[]);
    assert_eq!(facts[1].len(), 1, "wildcard arm ⇒ neq(node(b), 0)");

    let flow = FlowEnv::empty().assume(&kb, facts[1][0].clone());
    assert!(
        prove_from_gamma(&mut kb, &flow, &facts[1][0]),
        "a Node(Ref) scrutinee's neq is indexable and proves from Γ"
    );
}

#[test]
fn match_negation_indexes_a_varref_scrutinee() {
    // The REAL typer scrutinee for `match b` (b a let / lambda / op-param binder)
    // is an `Expr::VarRef` — which headed `Opaque` before the fix, so `assume`
    // silently DROPPED every match/if Γ fact over a plain variable (the common
    // case). It now reads as its reflect term twin `var_ref(name: Ref(name))`
    // (head `Functor{var_ref}`, one `name` child) → indexable. (This is the test
    // the `Ref`-scrutinee one above should have been: a `Ref` is always
    // indexable, so it never exercised the binder path that was actually dead.)
    let mut kb = common::load_kb_with("namespace wi537.varref\nend\n");
    let b = kb.intern("b");
    let scrutinee =
        Value::Node(NodeOccurrence::new_expr(Expr::VarRef { name: b }, span(), None));
    let arms = vec![(lit_pat(0), false), (wildcard_pat(), false)];
    let facts = match_arm_gamma_facts(&mut kb, &scrutinee, &arms, &[]);
    assert_eq!(facts[1].len(), 1, "wildcard arm ⇒ neq(varref(b), 0)");

    let flow = FlowEnv::empty().assume(&kb, facts[1][0].clone());
    assert!(
        prove_from_gamma(&mut kb, &flow, &facts[1][0]),
        "a VarRef (binder) scrutinee's neq must be indexable and prove from Γ"
    );
}

#[test]
fn match_guarded_earlier_arm_contributes_no_negation() {
    // `case 0 | g -> …` matches only when g holds, so a later arm cannot
    // conclude s ≠ 0 — a guarded earlier arm excludes nothing. The wildcard arm
    // therefore carries NO negation.
    let mut kb = common::load_kb_with("namespace wi537.matchguarded\nend\n");
    let s = param(&mut kb, "?s");
    let arms = vec![(lit_pat(0), true), (wildcard_pat(), false)];
    let facts = match_arm_gamma_facts(&mut kb, &s, &arms, &[]);
    assert!(
        facts[1].is_empty(),
        "a guarded earlier arm contributes no negation to a later arm"
    );
}

#[test]
fn match_nullary_ctor_arms_accumulate_negations() {
    // `case red -> … case green -> … case _ -> …` over an enum. A `Var`-pattern
    // whose name is in the scrutinee's constructor set is a nullary constructor
    // (the `collect_covered_entities` disambiguation), so each arm narrows the
    // next: green's arm knows s ≠ red, and the wildcard arm knows s ∉ {red,green}.
    let mut kb = common::load_kb_with("namespace wi537.matchenum\nend\n");
    let red = kb.intern("red");
    let green = kb.intern("green");
    let s = param(&mut kb, "?s");
    let arms = vec![
        (var_pat(red), false),
        (var_pat(green), false),
        (wildcard_pat(), false),
    ];
    let facts = match_arm_gamma_facts(&mut kb, &s, &arms, &[red, green]);

    assert_eq!(facts[0].len(), 1, "red arm: eq(s,red)");
    assert_eq!(facts[1].len(), 2, "green arm: neq(s,red) + eq(s,green)");
    assert_eq!(facts[2].len(), 2, "wildcard arm: neq(s,red) + neq(s,green)");

    let mut flow = FlowEnv::empty();
    for f in &facts[2] {
        flow = flow.assume(&kb, f.clone());
    }
    for f in &facts[2] {
        assert!(prove_from_gamma(&mut kb, &flow, f), "each wildcard-arm negation proves from Γ");
    }
}

#[test]
fn match_binding_arm_contributes_no_fact_or_negation() {
    // `case x -> …` (a bare binding, not a constructor) matches anything and
    // denotes no value, so it adds no pattern fact and narrows no later arm.
    let mut kb = common::load_kb_with("namespace wi537.matchbind\nend\n");
    let x = kb.intern("x");
    let s = param(&mut kb, "?s");
    // `x` is NOT in the (empty) constructor set ⇒ a binding.
    let arms = vec![(var_pat(x), false), (lit_pat(0), false)];
    let facts = match_arm_gamma_facts(&mut kb, &s, &arms, &[]);
    assert!(facts[0].is_empty(), "a binding arm adds no pattern fact");
    assert_eq!(
        facts[1].len(),
        1,
        "the literal arm carries only its own eq(s,0) — the binding arm negates nothing"
    );
}
