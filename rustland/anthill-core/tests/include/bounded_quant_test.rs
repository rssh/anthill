//! Bounded quantification over a collection in rule bodies (WI-027):
//! `(forall ?x in xs: P(?x))` and `(some ?x in xs: P(?x))`.
//!
//! `forall` is a finite CONJUNCTION over the list's elements (`nil` ⇒ vacuously
//! true); `some` is a finite DISJUNCTION (`nil` ⇒ no witness ⇒ fail). The binder
//! is instantiated to each concrete element at resolution time, eliminating a
//! hand-written recursive list walk. A non-ground collection is DELAYed (a
//! floundered residual under WI-519), never silently decided.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::parse;
use smallvec::SmallVec;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p).unwrap();
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

fn resolve_one(kb: &mut KnowledgeBase, goal: TermId) -> bool {
    let cfg = ResolveConfig::default();
    !kb.resolve(&[goal], &cfg).is_empty()
}

fn make_call(kb: &mut KnowledgeBase, qn: &str, args: &[TermId]) -> TermId {
    let sym = kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("symbol {qn} not in KB"));
    kb.alloc(Term::Fn { functor: sym, pos_args: SmallVec::from_slice(args), named_args: SmallVec::new() })
}

/// Build a runtime `cons`/`nil` list of the given elements (the shape a list
/// argument has at resolution time).
fn make_list(kb: &mut KnowledgeBase, elems: &[TermId]) -> TermId {
    let nil_sym = kb.try_resolve_symbol("anthill.prelude.List.nil").expect("List.nil");
    let cons_sym = kb.try_resolve_symbol("anthill.prelude.List.cons").expect("List.cons");
    let head_arg = kb.intern("head");
    let tail_arg = kb.intern("tail");
    let mut list = kb.alloc(Term::Fn { functor: nil_sym, pos_args: SmallVec::new(), named_args: SmallVec::new() });
    for &e in elems.iter().rev() {
        list = kb.alloc(Term::Fn {
            functor: cons_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(head_arg, e), (tail_arg, list)]),
        });
    }
    list
}

/// Shared fixture: an `Item` enum, `good`/`linked` facts, and one rule per
/// scenario. Loaded fresh per test (mirrors the forall_impl suite).
const FIXTURE: &str = r#"
    namespace test.wi027
      enum Item
        entity a
        entity b
        entity c
        entity bad
        entity ugly
        entity z
        entity w
      end

      fact good(a)
      fact good(b)
      fact good(c)

      fact linked(a, z)
      fact linked(b, z)
      fact linked(a, w)

      -- forall: every listed item is good
      rule all_good(?d)        :- (forall ?x in [a, b, c]: good(?x))
      -- forall: a non-good element makes it fail
      rule not_all_good(?d)    :- (forall ?x in [a, bad]: good(?x))
      -- forall over a list passed as the rule argument
      rule all_good_of(?xs)    :- (forall ?x in ?xs: good(?x))

      -- some: at least one good element
      rule some_good(?d)       :- (some ?x in [bad, a]: good(?x))
      -- some: no good element
      rule none_good(?d)       :- (some ?x in [bad, ugly]: good(?x))
      -- some over a list passed as the rule argument
      rule some_good_of(?xs)   :- (some ?x in ?xs: good(?x))

      -- free var ?y threaded across every element (conjunction)
      rule shared(?y)          :- (forall ?x in [a, b]: linked(?x, ?y))

      -- non-ground collection: ?xs is never bound
      rule unground(?d)        :- (forall ?x in ?xs: good(?x))
    end
"#;

fn item(kb: &mut KnowledgeBase, name: &str) -> TermId {
    // Entity value as a `Term::Ref` (matching how source-parsed entity references
    // are stored in facts) — NOT `make_name_term`, which builds a nullary `Fn`
    // that would not unify with the facts' `Ref`.
    let sym = kb.try_resolve_symbol(&format!("test.wi027.Item.{name}"))
        .unwrap_or_else(|| panic!("Item.{name} not found"));
    kb.alloc(Term::Ref(sym))
}

// =================================================================
// Parse + load
// =================================================================

#[test]
fn forall_in_loads_as_forall_in_term() {
    let kb = load_with(FIXTURE);
    // The rule body's sole atom is a `forall_in(...)` occurrence — round-trip it
    // through the printer to confirm surface syntax is recovered.
    let printed = printed_body(&kb, "test.wi027.all_good");
    assert!(printed.contains("(forall "), "expected forall opener: {printed}");
    assert!(printed.contains(" in "), "expected `in`: {printed}");
    assert!(printed.contains("good"), "expected body goal: {printed}");
}

#[test]
fn some_in_round_trips_through_printer() {
    let kb = load_with(FIXTURE);
    let printed = printed_body(&kb, "test.wi027.some_good");
    assert!(printed.contains("(some "), "expected some opener: {printed}");
    assert!(printed.contains(" in "), "expected `in`: {printed}");
}

fn printed_body(kb: &KnowledgeBase, rule_qn: &str) -> String {
    use anthill_core::persistence::print::TermPrinter;
    let sym = kb.try_resolve_symbol(rule_qn).unwrap_or_else(|| panic!("symbol {rule_qn} not found"));
    let rid = kb.rules_by_functor(sym).first().copied()
        .unwrap_or_else(|| panic!("no rule for {rule_qn}"));
    let body = kb.rule_body_nodes(rid);
    let printer = TermPrinter::new(kb);
    printer.print_occurrence(&body[0])
}

// =================================================================
// forall — conjunction
// =================================================================

#[test]
fn forall_succeeds_when_all_elements_hold() {
    let mut kb = load_with(FIXTURE);
    let d = item(&mut kb, "a");
    let goal = make_call(&mut kb, "test.wi027.all_good", &[d]);
    assert!(resolve_one(&mut kb, goal), "forall over [a,b,c] all good must succeed");
}

#[test]
fn forall_fails_when_one_element_fails() {
    let mut kb = load_with(FIXTURE);
    let d = item(&mut kb, "a");
    let goal = make_call(&mut kb, "test.wi027.not_all_good", &[d]);
    assert!(!resolve_one(&mut kb, goal), "forall over [a,bad] must fail (bad is not good)");
}

#[test]
fn forall_over_nil_is_vacuously_true() {
    let mut kb = load_with(FIXTURE);
    let empty = make_list(&mut kb, &[]);
    let goal = make_call(&mut kb, "test.wi027.all_good_of", &[empty]);
    assert!(resolve_one(&mut kb, goal), "forall over [] must hold vacuously");
}

#[test]
fn forall_over_variable_bound_list() {
    let mut kb = load_with(FIXTURE);
    let a = item(&mut kb, "a");
    let b = item(&mut kb, "b");
    let bad = item(&mut kb, "bad");

    let ok = make_list(&mut kb, &[a, b]);
    let ok_goal = make_call(&mut kb, "test.wi027.all_good_of", &[ok]);
    assert!(resolve_one(&mut kb, ok_goal), "forall over a bound [a,b] must succeed");

    let nope = make_list(&mut kb, &[a, bad]);
    let nope_goal = make_call(&mut kb, "test.wi027.all_good_of", &[nope]);
    assert!(!resolve_one(&mut kb, nope_goal), "forall over a bound [a,bad] must fail");
}

#[test]
fn forall_threads_free_var_across_elements() {
    let mut kb = load_with(FIXTURE);
    // shared(?y) :- (forall ?x in [a, b]: linked(?x, ?y))
    // z links BOTH a and b → holds; w links only a → fails for b.
    let z = item(&mut kb, "z");
    let z_goal = make_call(&mut kb, "test.wi027.shared", &[z]);
    assert!(resolve_one(&mut kb, z_goal), "shared(z) must hold — z links both a and b");

    let w = item(&mut kb, "w");
    let w_goal = make_call(&mut kb, "test.wi027.shared", &[w]);
    assert!(!resolve_one(&mut kb, w_goal), "shared(w) must fail — w does not link b");
}

// =================================================================
// some — disjunction
// =================================================================

#[test]
fn some_succeeds_when_one_element_holds() {
    let mut kb = load_with(FIXTURE);
    let d = item(&mut kb, "a");
    let goal = make_call(&mut kb, "test.wi027.some_good", &[d]);
    assert!(resolve_one(&mut kb, goal), "some over [bad,a] must succeed via a");
}

#[test]
fn some_fails_when_no_element_holds() {
    let mut kb = load_with(FIXTURE);
    let d = item(&mut kb, "a");
    let goal = make_call(&mut kb, "test.wi027.none_good", &[d]);
    assert!(!resolve_one(&mut kb, goal), "some over [bad,ugly] must fail");
}

#[test]
fn some_over_nil_fails() {
    let mut kb = load_with(FIXTURE);
    let empty = make_list(&mut kb, &[]);
    let goal = make_call(&mut kb, "test.wi027.some_good_of", &[empty]);
    assert!(!resolve_one(&mut kb, goal), "some over [] must fail — no witness");
}

// =================================================================
// non-ground collection — loud, not silent (WI-519)
// =================================================================

#[test]
fn unground_collection_is_not_a_definite_solution() {
    let mut kb = load_with(FIXTURE);
    let d = item(&mut kb, "a");
    let goal = make_call(&mut kb, "test.wi027.unground", &[d]);
    // definite_only: a floundered residual (the un-ground forall) must NOT count
    // as a definite solution — it is surfaced as undecided, never silently true.
    let cfg = ResolveConfig { definite_only: true, ..ResolveConfig::default() };
    let sols = kb.resolve(&[goal], &cfg);
    assert!(sols.is_empty(), "un-ground forall must not yield a definite solution; got {}", sols.len());
}
