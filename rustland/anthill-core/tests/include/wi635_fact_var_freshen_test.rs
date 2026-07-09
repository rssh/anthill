//! WI-635 — a bodyless arity-0 fact with a live `Var::Global` in its stored head
//! (the loader's omitted-field fill, an explicit `fact p(?x)`, or a value fact
//! whose children carry Globals) must freshen that head var PER MATCH, not
//! raw-bind its persistent `VarId`. Raw-binding was the arity-0 remnant of the
//! WI-624 fact fast-path leak — two goals matching the same fact aliased the one
//! stored vid, so constraining them differently spuriously failed. The fix
//! routes such facts through `with_fresh_vars`' arity-0 legacy path, which is now
//! carrier-neutral (seeds from the cached `head_vars`, reads no term-only
//! `rule_head`) so a value-`Entity` head — e.g. an `OperationInfo` whose
//! `type_params` carry Globals — freshens instead of panicking.
//!
//! Tests: the omitted-field aliasing repro, the single-match baseline, the
//! `fact p(?x)` ≡ bodyless-`rule` consistency (the ticket's 2nd failure mode),
//! and the value-`Entity` OperationInfo carrier-neutral no-panic guard.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

const SRC: &str = r#"
    namespace test.wi635
      import anthill.prelude.Int64
      sort Item
        entity item(id: Int64, note: Int64)
      end
      fact item(id: 42)
    end
"#;

/// `item(id: 42, note: <note_var>)` — the `id` is pinned so both goals hit the
/// single stored `fact item(id: 42)` whose `note` is the omitted→fresh fill.
fn item_goal(kb: &mut KnowledgeBase, note_var: TermId) -> TermId {
    let item_sym = kb.try_resolve_symbol("test.wi635.Item.item").unwrap();
    let id_field = kb.intern("id");
    let note_field = kb.intern("note");
    let v42 = kb.alloc(Term::Const(Literal::Int(42)));
    kb.alloc(Term::Fn {
        functor: item_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(id_field, v42), (note_field, note_var)]),
    })
}

/// `unify(a, b)` — the `<=>` builtin (`anthill.kernel.unify`).
fn unify_goal(kb: &mut KnowledgeBase, a: TermId, b: TermId) -> TermId {
    let unify_sym = kb.try_resolve_symbol("anthill.kernel.unify").unwrap();
    kb.alloc(Term::Fn {
        functor: unify_sym,
        pos_args: SmallVec::from_slice(&[a, b]),
        named_args: SmallVec::new(),
    })
}

#[test]
fn omitted_field_var_freshens_per_match() {
    // Conjunction: item(id:42, note:?n1), item(id:42, note:?n2), ?n1<=>1, ?n2<=>2.
    // Both item goals match the ONE stored `fact item(id: 42)` (note omitted →
    // stored `note: <freshGlobal V>`). If V is raw-bound into σ per match, ?n1
    // and ?n2 both alias V; ?n1<=>1 then pins V=1 and ?n2<=>2 unifies 1 with 2 →
    // spurious FAILURE. Freshening V per match keeps ?n1, ?n2 independent → the
    // conjunction has exactly one solution with ?n1=1, ?n2=2.
    let mut kb = crate::common::load_kb_with(SRC);

    let n1_name = kb.intern("n1");
    let n1_vid = kb.fresh_var(n1_name);
    let n1 = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(n1_vid)));

    let n2_name = kb.intern("n2");
    let n2_vid = kb.fresh_var(n2_name);
    let n2 = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(n2_vid)));

    let g1 = item_goal(&mut kb, n1);
    let g2 = item_goal(&mut kb, n2);
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let two = kb.alloc(Term::Const(Literal::Int(2)));
    let g3 = unify_goal(&mut kb, n1, one);
    let g4 = unify_goal(&mut kb, n2, two);

    let sols = kb.resolve(&[g1, g2, g3, g4], &ResolveConfig::default());
    assert_eq!(
        sols.len(),
        1,
        "two goals matching one omitted-field fact must bind the field \
         independently (freshened per match), not alias the fact's stored vid"
    );

    let b1 = kb.reify(n1, &sols[0].subst);
    let b2 = kb.reify(n2, &sols[0].subst);
    assert!(
        reifies_to_int(&kb, &b1, 1) && reifies_to_int(&kb, &b2, 2),
        "?n1 must bind 1 and ?n2 must bind 2 (got {b1:?}, {b2:?})"
    );
}

#[test]
fn single_match_omitted_field_still_answers_unbound() {
    // Baseline: a single goal against the omitted-field fact leaves `note`
    // unbound (an omitted field is genuinely unspecified). Freshening must not
    // regress this — exactly one solution, `note` an unbound variable.
    let mut kb = crate::common::load_kb_with(SRC);
    let n_name = kb.intern("n");
    let n_vid = kb.fresh_var(n_name);
    let n = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(n_vid)));
    let g = item_goal(&mut kb, n);
    let sols = kb.resolve(&[g], &ResolveConfig::default());
    assert_eq!(sols.len(), 1, "item(id:42, note:?n) matches the one fact");
    let bound = kb.reify(n, &sols[0].subst);
    assert!(
        matches!(bound, anthill_core::eval::Value::Term { id, .. }
            if matches!(kb.get_term(id), Term::Var(_))),
        "omitted field stays an unbound variable, got {bound:?}"
    );
}

#[test]
fn explicit_var_fact_matches_bodyless_rule_behavior() {
    // The ticket's SECOND failure mode: post-WI-624 an explicit-var `fact p(?x)`
    // (arity-0, raw-bound persistent vid) diverged from a bodyless `rule q(?x)`
    // (arity-1, freshened per match via with_fresh_vars) for the same meaning.
    // After WI-635 both freshen, so the two-goal differing-constraint scenario
    // yields ONE solution for each — they behave identically. `fact p(?x)` is the
    // general (universally-quantified) form of the omitted-field fill and loads
    // through the same arity-0 Var::Global path (explicit var, not loader fill).
    let src = r#"
        namespace test.wi635b
          import anthill.prelude.Int64
          sort P
            entity p(x: Int64)
          end
          sort Q
            entity q(x: Int64)
          end
          fact p(?x)
          rule q(?y)
        end
    "#;
    for (ctor, one_val, two_val) in [("test.wi635b.P.p", 1, 2), ("test.wi635b.Q.q", 3, 4)] {
        let mut kb = crate::common::load_kb_with(src);
        let ctor_sym = kb.try_resolve_symbol(ctor).unwrap();
        let x_field = kb.intern("x");
        let a_sym = kb.intern("a");
        let a_vid = kb.fresh_var(a_sym);
        let a = kb.alloc(Term::Var(Var::Global(a_vid)));
        let b_sym = kb.intern("b");
        let b_vid = kb.fresh_var(b_sym);
        let b = kb.alloc(Term::Var(Var::Global(b_vid)));
        let g1 = kb.alloc(Term::Fn {
            functor: ctor_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(x_field, a)]),
        });
        let g2 = kb.alloc(Term::Fn {
            functor: ctor_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(x_field, b)]),
        });
        let one = kb.alloc(Term::Const(Literal::Int(one_val)));
        let two = kb.alloc(Term::Const(Literal::Int(two_val)));
        let g3 = unify_goal(&mut kb, a, one);
        let g4 = unify_goal(&mut kb, b, two);
        let sols = kb.resolve(&[g1, g2, g3, g4], &ResolveConfig::default());
        assert_eq!(
            sols.len(),
            1,
            "{ctor}: two goals over one var-headed declaration must freshen \
             independently (fact and bodyless rule behave identically)"
        );
    }
}

#[test]
fn value_entity_operation_info_resolves_without_panic() {
    // Carrier-neutral guard (agent-1's live crash). A stdlib op with a denoted
    // `-Modify[x]` effect (combinators `map`/`filter`, …) is stored as a value
    // fact whose `Value::Entity` head carries a `type_params` cons-list of
    // `Var::Global`s. WI-635 routes such a non-ground arity-0 fact through
    // `with_fresh_vars`' arity-0 legacy path; that path must be carrier-neutral
    // (seed from the cached `head_vars`, read NO term-only `rule_head`) — else
    // reaching this candidate panics "rule_head: head is not a Term carrier".
    let mut kb = crate::common::load_kb_with("namespace test.wi635z\nend\n");
    let op_info = kb.try_resolve_symbol("anthill.reflect.OperationInfo").unwrap();

    // Confirm the value-Entity OperationInfo population actually exists in the
    // loaded KB, so this test genuinely exercises the carrier-neutral path.
    let entity_headed = kb
        .rules_by_functor(op_info)
        .iter()
        .filter(|&&rid| !matches!(kb.rule_head_value(rid), Value::Term { .. }))
        .count();
    assert!(
        entity_headed > 0,
        "expected value-Entity OperationInfo facts (denoted-effect ops) in stdlib"
    );

    // An all-var OperationInfo goal matches every fact, so the resolver drives
    // each Entity-headed candidate through the legacy freshening path. A broken
    // (term-only) path panics here; a correct one resolves every fact.
    let total = kb.rules_by_functor(op_info).len();
    let fields = [
        "name", "params", "return_type", "effects", "requires", "ensures",
        "type_params", "meta",
    ];
    let named_args: SmallVec<[(Symbol, TermId); 2]> = fields
        .iter()
        .map(|f| {
            let key = kb.intern(f);
            let v = kb.fresh_var(key);
            (key, kb.alloc(Term::Var(Var::Global(v))))
        })
        .collect();
    let goal = kb.alloc(Term::Fn {
        functor: op_info,
        pos_args: SmallVec::new(),
        named_args,
    });
    let cfg = ResolveConfig { max_solutions: total + 16, ..ResolveConfig::default() };
    let sols = kb.resolve(&[goal], &cfg);
    assert!(
        sols.len() >= entity_headed,
        "every OperationInfo fact (incl. {entity_headed} value-Entity) must \
         resolve through the carrier-neutral legacy path; got {} of {total}",
        sols.len()
    );
}

fn reifies_to_int(kb: &KnowledgeBase, v: &anthill_core::eval::Value, n: i64) -> bool {
    match v {
        anthill_core::eval::Value::Int(i) => *i == n,
        anthill_core::eval::Value::Term { id, .. } => {
            matches!(kb.get_term(*id), Term::Const(Literal::Int(i)) if *i == n)
        }
        _ => false,
    }
}
