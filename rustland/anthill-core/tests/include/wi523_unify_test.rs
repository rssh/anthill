//! WI-523 — `<=>` (`anthill.kernel.unify`) RESOLVES: the resolver's structural
//! unification builtin (proposal 049).
//!
//! `builtin_unify` is the bind-counterpart of `eq`: the same structural walk,
//! but a flex var head BINDS to the other side (an occurs-checked frame effect)
//! and a functor match recurses binding sub-vars on either side. `<=>` is the
//! object-level surface (and `let ?v = e` its directed sugar); `reflect.unify`
//! / `KnowledgeBase::unify_terms` is the term-level DATA face over the same
//! core. Also covers `<=>`-headed empty-body rules being recognized as
//! equations (`is_equation`) and fired by the resolver's `apply_eq_rules`.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Literal, Var};
use anthill_core::kb::term_view::views_structurally_equal;
use anthill_core::eval::value::Value;
use anthill_core::parse;
use smallvec::SmallVec;

/// Mint a fresh global logic variable and return its `Term::Var` carrier — the
/// query-side var whose binding the assertions inspect via `kb.reify`.
fn fresh_var_term(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

fn load_capturing_errors(extra: &str) -> (KnowledgeBase, Vec<LoadError>) {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => (kb, vec![]),
        Err(errs) => (kb, errs),
    }
}

fn load_ok(extra: &str) -> KnowledgeBase {
    let (kb, errs) = load_capturing_errors(extra);
    assert!(
        errs.is_empty(),
        "clean load expected; got:\n{}",
        errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
    );
    kb
}

/// Resolve `functor_qn(args...)` and return the solutions.
fn resolve(kb: &mut KnowledgeBase, functor_qn: &str, args: &[TermId]) -> Vec<anthill_core::kb::resolve::Solution> {
    let functor = kb.resolve_symbol(functor_qn);
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
    kb.resolve(&[goal], &cfg)
}

fn int_term(kb: &mut KnowledgeBase, n: i64) -> TermId {
    kb.alloc(Term::Const(Literal::Int(n)))
}

/// Assert a query var binds to integer `n` after `<=>` — carrier-agnostically.
/// A rule-body literal rides as a `Value::Node` occurrence, so unify binds the
/// var to that Node (carrier-faithful); compare structurally against a term `n`.
fn assert_binds_int(kb: &KnowledgeBase, reified: &Value, n: i64, expected_term: TermId) {
    assert!(
        views_structurally_equal(kb, reified, &Value::term(expected_term)),
        "expected binding to {n}, got {reified:?}"
    );
}

// ── 1. `<=>` binds a flex var to the other side ─────────────────────────

#[test]
fn unify_binds_flex_var_to_scalar() {
    // `go(?v) :- ?v <=> 7` — the body lowers to `unify(?v, 7)`. Queried with a
    // fresh var, `?v` must come back bound to 7 (the relaxed caller-var pre-check
    // lets the body run rather than residualizing on the bare-var first operand).
    let src = r#"
        namespace wi523.bind
          rule go(?v)
            :- ?v <=> 7
        end
    "#;
    let mut kb = load_ok(src);
    let v_term = fresh_var_term(&mut kb, "_q");
    let sols = resolve(&mut kb, "wi523.bind.go", &[v_term]);
    assert_eq!(sols.len(), 1, "unify(?v, 7) succeeds once");
    let reified = kb.reify(v_term, &sols[0].subst);
    let seven = int_term(&mut kb, 7);
    assert_binds_int(&kb, &reified, 7, seven);
}

// ── 2. functor match recurses, binding sub-vars on either side ──────────

#[test]
fn unify_recurses_and_binds_subvar() {
    // `some(?x) <=> some(3)` — functors match, recurse `?x <=> 3`, bind `?x ↦ 3`
    // (the case today's `eq` instead FAILS — unify is the honest substrate).
    let src = r#"
        namespace wi523.rec
          rule go(?x)
            :- some(?x) <=> some(3)
        end
    "#;
    let mut kb = load_ok(src);
    let x_term = fresh_var_term(&mut kb, "_x");
    let sols = resolve(&mut kb, "wi523.rec.go", &[x_term]);
    assert_eq!(sols.len(), 1, "some(?x) <=> some(3) succeeds once");
    let reified = kb.reify(x_term, &sols[0].subst);
    let three = int_term(&mut kb, 3);
    assert_binds_int(&kb, &reified, 3, three);
}

// ── 3. occurs-check: `?v <=> f(?v)` is a loud failure, not a cyclic term ──

#[test]
fn unify_occurs_check_fails() {
    // `go(?v) :- ?v <=> some(?v)` — `?v` occurs in `some(?v)`, so the bind is
    // rejected (no infinite term). The goal fails: zero solutions.
    let src = r#"
        namespace wi523.occurs
          rule go(?v)
            :- ?v <=> some(?v)
        end
    "#;
    let mut kb = load_ok(src);
    let v_term = fresh_var_term(&mut kb, "_q");
    let sols = resolve(&mut kb, "wi523.occurs.go", &[v_term]);
    assert_eq!(sols.len(), 0, "occurs-check rejects ?v <=> some(?v)");
}

// ── 4. mismatch fails; the chase sees a binding made earlier in the unify ──

#[test]
fn unify_chase_then_mismatch_fails() {
    // `go(?x) :- ?x <=> some(1), ?x <=> none` — first binds `?x ↦ some(1)`;
    // the second chases `?x` to `some(1)` and unifies it with `none` (functor
    // mismatch) ⇒ fail. Exercises the working-subst read-through.
    let src = r#"
        namespace wi523.clash
          rule go(?x)
            :- ?x <=> some(1), ?x <=> none
        end
    "#;
    let mut kb = load_ok(src);
    let x_term = fresh_var_term(&mut kb, "_x");
    let sols = resolve(&mut kb, "wi523.clash.go", &[x_term]);
    assert_eq!(sols.len(), 0, "some(1) does not unify with none");
}

// ── 5. `let ?v = expr` is directed sugar over `?v <=> expr` ─────────────

#[test]
fn let_sugar_binds() {
    // `go(?out) :- let ?out = 42` lowers to `unify(?out, 42)`.
    let src = r#"
        namespace wi523.lets
          rule go(?out)
            :- let ?out = 42
        end
    "#;
    let mut kb = load_ok(src);
    let out_term = fresh_var_term(&mut kb, "_o");
    let sols = resolve(&mut kb, "wi523.lets.go", &[out_term]);
    assert_eq!(sols.len(), 1, "let ?out = 42 binds once");
    let reified = kb.reify(out_term, &sols[0].subst);
    let fortytwo = int_term(&mut kb, 42);
    assert_binds_int(&kb, &reified, 42, fortytwo);
}

// ── 6. `<=>`-headed empty-body rule is recognized + fired as an equation ──
//
// Built via the KB API under the canonical `unify_functor()` — the same head
// shape the loader produces for a `<=>` rule once `unify` resolves to
// `anthill.kernel.unify`. (Making a bare-namespace `<=>` *source* head resolve
// to the kernel symbol rather than a fresh local Goal shadow is the radius-3
// migration's loader concern, WI-526; WI-523 delivers the recognition machinery
// these tests pin directly, with no loader-resolution coupling.)

#[test]
fn unify_headed_fact_is_recognized_as_equation() {
    // `is_equation` must accept a `unify`-headed empty-body 2-positional-arg rule
    // (the `<=>` head, proposal 049) type-independently — the bind-side peer of
    // its long-standing `eq` recognition — and the rule must index under
    // `unify_functor()`, where `apply_eq_rules` / the typer's `try_fire` select it.
    let mut kb = KnowledgeBase::new();
    let sort = kb.make_name_term("Thing");
    let domain = kb.make_name_term("test");
    let unify_sym = kb.unify_functor();
    let a = int_term(&mut kb, 1);
    let b = int_term(&mut kb, 2);
    let head = kb.alloc(Term::Fn {
        functor: unify_sym,
        pos_args: SmallVec::from_slice(&[a, b]),
        named_args: SmallVec::new(),
    });
    let rid = kb.assert_fact(head, sort, domain, None);
    assert!(kb.is_equation(rid), "a `unify`-headed empty-body 2-arg rule is an equation");
    assert!(
        kb.rules_by_functor(unify_sym).contains(&rid),
        "the equation must be indexed under `unify_functor()` for discrim selection"
    );
}

#[test]
fn unify_headed_equation_fires_in_apply_eq_rules() {
    // The resolver's equational fallback (`apply_eq_rules`) now selects under
    // `unify` too: a `unify`-headed empty-body equation rewrites L→R, so
    // `unify(1, 2)` makes `simplify(1)` rewrite to `2`. (A ground equation
    // isolates selection-under-`unify`; the resolver path does not open a rule's
    // De Bruijn vars — a pre-existing trait shared with `=`.)
    let mut kb = KnowledgeBase::new();
    let sort = kb.make_name_term("Thing");
    let domain = kb.make_name_term("test");
    let unify_sym = kb.unify_functor();
    let one = int_term(&mut kb, 1);
    let two = int_term(&mut kb, 2);
    let head = kb.alloc(Term::Fn {
        functor: unify_sym,
        pos_args: SmallVec::from_slice(&[one, two]),
        named_args: SmallVec::new(),
    });
    kb.assert_fact(head, sort, domain, None);
    let simplified = kb.simplify(one);
    assert_eq!(
        kb.get_term(simplified),
        &Term::Const(Literal::Int(2)),
        "the `unify`-headed equation `unify(1, 2)` must rewrite 1 → 2"
    );
}

// ── 7. term-level DATA face: `KnowledgeBase::unify_terms` ────────────────

fn fresh_kb() -> KnowledgeBase {
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    kb
}

#[test]
fn unify_terms_data_face() {
    // The honest signature shared by `reflect.unify` and `<=>`: return the mgu
    // as data. `f(?x, 2) <=> f(1, ?y)` → Some(σ) binding `?x ↦ 1`, `?y ↦ 2`.
    let mut kb = fresh_kb();
    let f = kb.intern("f");
    let x_term = fresh_var_term(&mut kb, "_x");
    let y_term = fresh_var_term(&mut kb, "_y");
    let one = int_term(&mut kb, 1);
    let two = int_term(&mut kb, 2);
    let a = kb.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_slice(&[x_term, two]), named_args: SmallVec::new() });
    let b = kb.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_slice(&[one, y_term]), named_args: SmallVec::new() });

    let sigma = kb.unify_terms(a, b).expect("f(?x,2) unifies with f(1,?y)");
    let xb = kb.reify(x_term, &sigma).expect_term();
    let yb = kb.reify(y_term, &sigma).expect_term();
    assert_eq!(kb.get_term(xb), &Term::Const(Literal::Int(1)), "?x ↦ 1");
    assert_eq!(kb.get_term(yb), &Term::Const(Literal::Int(2)), "?y ↦ 2");
}

#[test]
fn unify_terms_mismatch_is_none() {
    // `f(1)` vs `g(1)` — functor mismatch ⇒ no unifier.
    let mut kb = fresh_kb();
    let f = kb.intern("f");
    let g = kb.intern("g");
    let one = int_term(&mut kb, 1);
    let one2 = int_term(&mut kb, 1);
    let fa = kb.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_slice(&[one]), named_args: SmallVec::new() });
    let gb = kb.alloc(Term::Fn { functor: g, pos_args: SmallVec::from_slice(&[one2]), named_args: SmallVec::new() });
    assert!(kb.unify_terms(fa, gb).is_none(), "f(1) and g(1) do not unify");
}

#[test]
fn unify_terms_occurs_check_is_none() {
    // `?x` vs `f(?x)` — occurs-check ⇒ no unifier (data face).
    let mut kb = fresh_kb();
    let f = kb.intern("f");
    let x_term = fresh_var_term(&mut kb, "_x");
    let fx = kb.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_slice(&[x_term]), named_args: SmallVec::new() });
    assert!(kb.unify_terms(x_term, fx).is_none(), "?x and f(?x) fail occurs-check");
}

#[test]
fn unify_rigid_var_is_reflexive() {
    // A rigid (skolem) var unifies reflexively — `!k <=> !k` and `f(!k) <=> f(!k)`
    // succeed (matching `eq` / `views_structurally_equal`, WI-108); `unify_concrete`
    // must not drop the same-skolem case to Fail. Distinct skolems do NOT unify
    // (a skolem never binds). Reachable via the forall/Skolem path and the data face.
    let mut kb = fresh_kb();
    let f = kb.intern("f");
    let s = kb.intern("_k");
    let r = kb.fresh_var(s);
    let rigid = kb.alloc(Term::Var(Var::Rigid(r)));
    assert!(kb.unify_terms(rigid, rigid).is_some(), "!k <=> !k must unify (reflexivity)");
    let fr = kb.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_slice(&[rigid]), named_args: SmallVec::new() });
    assert!(kb.unify_terms(fr, fr).is_some(), "f(!k) <=> f(!k) must unify");

    let r2 = kb.fresh_var(s);
    let other = kb.alloc(Term::Var(Var::Rigid(r2)));
    assert!(kb.unify_terms(rigid, other).is_none(), "distinct skolems !k <=> !j must NOT unify");
}
