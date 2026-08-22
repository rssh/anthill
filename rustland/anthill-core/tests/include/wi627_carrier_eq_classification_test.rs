//! WI-627 — equation classification keys on the RESOLVED symbol, not the short
//! name. A carrier's OWN `eq` operation (the WI-350/WI-444 short-name override
//! the semantic `=`/`eq` dispatch resolves against) is a DIFFERENT symbol than
//! the canonical `anthill.prelude.Eq.eq` it merely shares a short name with.
//! Before this fix, `is_equation` / `is_equational_head` matched by short name,
//! so a carrier's bodyless 2-ary `eq` base case (`rule eq(red(), red())`) was
//! misclassified as a WI-139 cite-required equational LAW — unindexed and
//! silently dropped from SLD candidates, so the base case never fired.
//!
//! These tests use a SELF-CONTAINED carrier (`Bag`, with its own `eq`) so they
//! do not depend on any stdlib carrier's equality shape. They pin: (1) the
//! bodyless carrier-`eq` base case fires as an ordinary SLD rule; (2)
//! `is_equation` / `is_equational_head` are false for a carrier `eq` head but
//! true for a genuine connective law; (3) WI-139 leaves a genuine law cite-required
//! while keeping the carrier's `eq` rules indexed.
//!
//! WI-888 CHANGED WHICH CONNECTIVE THE POSITIVE ARM IS WRITTEN WITH, and the fixture
//! now carries TWO laws rather than one so nothing is lost. A bodyless `=` head is a
//! load error now (`<=>` is the only defining connective), so `my_law` is spelled
//! `<=>` and heads on `anthill.kernel.unify`. The `anthill.prelude.PartialEq.eq` arm —
//! the one that makes "keys on the RESOLVED symbol" a real claim against `Bag.eq`'s
//! short name — is kept by `bodied_law`, a GUARDED `=` equation, which WI-888
//! deliberately leaves spelled `=` (proposal 049 draws its boundary at the empty body).
//! So both connectives are still exercised, and the pair also pins WI-888's boundary:
//! same head SHAPE, same WI-139 unindexing, and only the bodyless one is an equation.

use anthill_core::eval::Value;
use anthill_core::kb::load::is_equational_head;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// `Bag` declares its OWN `eq` (head resolves to `test.wi627.Bag.eq`, distinct
/// from `anthill.prelude.Eq.eq`) with a BODYLESS base case `eq(red(), red())` —
/// the exact short-name trap WI-627 fixes. `my_law` and `bodied_law` are genuine
/// top-level connective laws (heads resolving to `anthill.kernel.unify` and
/// `anthill.prelude.PartialEq.eq`) for contrast — one per connective, see the module
/// doc for why it takes two.
const SRC: &str = r#"
    namespace test.wi627
      import anthill.prelude.{Int64, Eq}
      sort Bag
        entity red
        entity blue
        operation eq(a: Bag, b: Bag) -> Bool
        rule eq(red(), red()) :- true
        rule eq(blue(), blue()) :- true
      end
      rule my_law: foo(?a, ?b) <=> foo(?b, ?a)
      rule bodied_law: bar(?a) = bar(?a) :- Int64.gt(1, 0)
    end
"#;

fn load_kb() -> KnowledgeBase {
    crate::common::load_kb_with(SRC)
}

fn fn_term(kb: &mut KnowledgeBase, qualified: &str, args: &[TermId]) -> TermId {
    let sym = kb
        .try_resolve_symbol(qualified)
        .unwrap_or_else(|| panic!("symbol {qualified} not in KB"));
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

/// The acceptance criterion: the bodyless `rule eq(red(), red())` on a carrier
/// fires as an SLD base case. With the short-name misclassification it would be
/// dropped from candidates and yield zero solutions.
#[test]
fn carrier_bodyless_eq_base_case_fires_as_sld_rule() {
    let mut kb = load_kb();
    let red1 = fn_term(&mut kb, "test.wi627.Bag.red", &[]);
    let red2 = fn_term(&mut kb, "test.wi627.Bag.red", &[]);
    let goal = fn_term(&mut kb, "test.wi627.Bag.eq", &[red1, red2]);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        sols.len(),
        1,
        "Bag.eq(red(), red()) must resolve via the bodyless base-case rule"
    );

    // A non-matching pair has no base case and correctly yields nothing.
    let red = fn_term(&mut kb, "test.wi627.Bag.red", &[]);
    let blue = fn_term(&mut kb, "test.wi627.Bag.blue", &[]);
    let goal_ne = fn_term(&mut kb, "test.wi627.Bag.eq", &[red, blue]);
    assert_eq!(
        kb.resolve(&[goal_ne], &ResolveConfig::default()).len(),
        0,
        "Bag.eq(red(), blue()) has no rule and must not resolve"
    );
}

/// Find every live rule whose head functor has the given qualified name.
fn rules_with_head_qn(kb: &KnowledgeBase, qn: &str) -> Vec<anthill_core::kb::RuleId> {
    let Some(sym) = kb.try_resolve_symbol(qn) else {
        return Vec::new();
    };
    kb.live_rule_ids()
        .into_iter()
        .filter(|&rid| {
            let Value::Term { id: head, .. } = *kb.rule_head_value(rid) else {
                return false;
            };
            matches!(kb.get_term(head), Term::Fn { functor, .. } if *functor == sym)
        })
        .collect()
}

/// `is_equation` / `is_equational_head` classify by RESOLVED symbol: a carrier
/// `Bag.eq` head is NOT the canonical equality connective, so neither flags it;
/// a genuine `anthill.prelude.Eq.eq` law head IS flagged by both.
#[test]
fn classification_keys_on_resolved_symbol_not_short_name() {
    let kb = load_kb();

    // Carrier `Bag.eq` rules: normal (bodyless) rules, never equational laws.
    let bag_eq_rules = rules_with_head_qn(&kb, "test.wi627.Bag.eq");
    assert_eq!(
        bag_eq_rules.len(),
        2,
        "expected both bodyless Bag.eq base cases"
    );
    for rid in &bag_eq_rules {
        assert!(
            !kb.is_equation(*rid),
            "Bag.eq rule {rid:?} must NOT classify as an equation (different symbol than Eq.eq)"
        );
        let Value::Term { id: head, .. } = *kb.rule_head_value(*rid) else {
            continue;
        };
        assert!(
            !is_equational_head(&kb, head),
            "Bag.eq rule {rid:?} must NOT classify as an equational head"
        );
    }

    // The genuine `foo(?a,?b) <=> foo(?b,?a)` law: head is `anthill.kernel.unify`, so it
    // IS an equation and IS an equational head (cite-required by WI-139).
    let my_law = rules_with_head_qn(&kb, "anthill.kernel.unify")
        .iter()
        .copied()
        .find(|&rid| {
            kb.rule_label(rid)
                .map(|l| kb.local_name_of(l) == "my_law")
                .unwrap_or(false)
        })
        .expect("my_law must load with head functor anthill.kernel.unify");
    assert!(kb.is_equation(my_law), "a genuine `<=>` law is an equation");
    let Value::Term { id: law_head, .. } = *kb.rule_head_value(my_law) else {
        panic!("law head is a term")
    };
    assert!(
        is_equational_head(&kb, law_head),
        "a genuine `<=>` law is an equational head"
    );

    // The `=` half, and the one that keeps this test honest about "RESOLVED symbol":
    // `bodied_law`'s head IS `anthill.prelude.PartialEq.eq`, the very symbol `Bag.eq`
    // shares a short name with, and the two get OPPOSITE verdicts from
    // `is_equational_head` above. It is NOT an equation (WI-888 / proposal 049: a
    // guarded `=` law keeps its spelling and its non-equation status, because
    // `is_equation` requires an empty body) — so the SHAPE question and the EQUATION
    // question part company here, which is exactly the split WI-888 rests on.
    let bodied_law = rules_with_head_qn(&kb, "anthill.prelude.PartialEq.eq")
        .iter()
        .copied()
        .find(|&rid| {
            kb.rule_label(rid)
                .map(|l| kb.local_name_of(l) == "bodied_law")
                .unwrap_or(false)
        })
        .expect("bodied_law must load with head functor anthill.prelude.PartialEq.eq");
    assert!(
        !kb.is_equation(bodied_law),
        "a GUARDED `=` law is not an equation — it has a body"
    );
    let Value::Term { id: bodied_head, .. } = *kb.rule_head_value(bodied_law) else {
        panic!("bodied law head is a term")
    };
    assert!(
        is_equational_head(&kb, bodied_head),
        "…but its HEAD is still the canonical `=` connective, which is what WI-139 reads"
    );
}

/// WI-139 behaviour is unchanged for genuine equations — the bare `foo <=> foo`
/// law is unindexed (cite-required) — while the carrier's `Bag.eq` rules stay
/// indexed in `rules_by_functor` (no longer collateral-unindexed by short name).
///
/// The GUARDED `=` law is checked here too (WI-888): WI-139 keys on the head SHAPE, so
/// a body does not save it from unindexing, and that is precisely why
/// `is_equality_connective_functor` still answers for `eq` after the bodyless spelling
/// was refused. Drop `eq` from that cache and this row is what fails.
#[test]
fn wi139_unchanged_for_law_carrier_eq_stays_indexed() {
    let mut kb = load_kb();

    // Genuine bare law: NOT in the `rules_by_functor(unify)` bucket.
    let unify_sym = kb.unify_functor();
    let my_law = rules_with_head_qn(&kb, "anthill.kernel.unify")
        .iter()
        .copied()
        .find(|&rid| {
            kb.rule_label(rid)
                .map(|l| kb.local_name_of(l) == "my_law")
                .unwrap_or(false)
        })
        .expect("my_law loads");
    assert!(
        !kb.rules_by_functor(unify_sym).contains(&my_law),
        "a bare `<=>` law must be unindexed (WI-139 cite-required)"
    );

    // The guarded `=` law: same treatment, under the OTHER connective's bucket.
    let eq_sym = kb.eq_functor();
    let bodied_law = rules_with_head_qn(&kb, "anthill.prelude.PartialEq.eq")
        .iter()
        .copied()
        .find(|&rid| {
            kb.rule_label(rid)
                .map(|l| kb.local_name_of(l) == "bodied_law")
                .unwrap_or(false)
        })
        .expect("bodied_law loads");
    assert!(
        !kb.rules_by_functor(eq_sym).contains(&bodied_law),
        "a guarded `=` law is unindexed too — WI-139 reads the head SHAPE, not the body"
    );

    // Carrier `Bag.eq` rules: indexed under their own functor.
    let bag_eq_sym = kb
        .try_resolve_symbol("test.wi627.Bag.eq")
        .expect("Bag.eq resolves");
    let indexed = kb.rules_by_functor(bag_eq_sym);
    let all_bag_eq = rules_with_head_qn(&kb, "test.wi627.Bag.eq");
    for rid in &all_bag_eq {
        assert!(
            indexed.contains(rid),
            "Bag.eq rule {rid:?} must stay indexed in rules_by_functor (WI-627)"
        );
    }
}
