//! WI-20260827-2YHZ3 — an ANSWER binding must be read by deep reification.
//!
//! σ IS NOT FLAT, and the two bind paths disagree about it. A FACT match binds
//! through `bind_compressed`, which re-points the answer link `?a ↦ Var(F)` at
//! the value, so one hop lands on it. A BUILTIN binds through `bind_waking` on
//! the resolver's `SuccessWithBindings` merge, which does NOT compress — both
//! `?a ↦ Var(F)` and `F ↦ 6` stand, and a one-hop `resolve_as_value(?a)` stops
//! at `Var(F)`. That is indistinguishable, at the read, from an answer that
//! bound nothing, so `rule builtin_bound(?x) :- ?x <=> 6` PROVED `?x = 6` and
//! REPORTED `?x` unbound.
//!
//! The defect was in the readers, never in resolution — which is why it hid for
//! so long. `anthill query` showed `?x = ?_` while the ground queries `k(6)` and
//! `k(7)` decided correctly in both directions, a CALLING rule saw the binding,
//! and `common::query_unary` (which reads through `kb.reify`) was green
//! throughout. `KnowledgeBase::answer_binding` is now the one correct read.
//!
//! WHAT FAILS ON A BACK-OUT (revert `answer_binding` to a bare
//! `resolve_as_value`):
//!   * `builtin_bound_head_var_reads_as_its_value` — the headline. `?x` reads
//!     back as an unbound `Var` instead of `6`.
//!   * `nested_binding_resolves_all_the_way_down` — reads `B(v: Var(G))`. This
//!     is the one a TOP-LEVEL CHASE would also fail: only deep reification fixes
//!     it, which is why the fix is `reify_value` and not a var-chase loop.
//!   * `one_hop_read_is_the_defect_being_fixed` — asserts the broken reader is
//!     still broken, so the two are pinned as genuinely different reads rather
//!     than the test passing because both happen to work.
//!   * `relation_column_bound_by_a_builtin_drains_as_its_value` — the second
//!     reader, in the eval bridge.
//!
//! WHAT PASSES EITHER WAY, BY DESIGN (the controls):
//!   * `fact_bound_head_var_was_never_truncated` — the compressed path. Both
//!     readers agree here, and that agreement is exactly why the other path's
//!     truncation went unnoticed.
//!   * `ground_queries_decided_correctly_throughout` — resolution was never
//!     wrong; only the projection was lost.

use anthill_core::eval::value::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Var, VarId};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;

use crate::common::{interp_for, load_kb_with};

const SRC: &str = r#"
namespace probe.wi2yhz3
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.List.{foldLeft}

  sort Box
    entity B(v: Int64)
  end

  fact B(v: 6)

  -- The minimal case: ONE goal, ONE builtin, no operation anywhere in it.
  rule builtin_bound(?x) :- ?x <=> 6
  -- The control: the compressed path, which one hop always read correctly.
  rule fact_bound(?x)    :- B(v: ?x)
  -- The deep case: `?x`'s own CHILD sits behind a second uncompressed link.
  rule nested(?x)        :- ?x <=> B(v: ?y), ?y <=> 6
  -- A LONGER chain. One splice hop is not enough here, at top level or nested.
  rule chain3(?x)        :- ?x <=> ?y, ?y <=> ?z, ?z <=> 6
  rule deep_chain(?x)    :- ?x <=> B(v: ?y), ?y <=> ?z, ?z <=> 6

  -- The eval-bridge reader. A 1-arg rule cited by name IS a `Relation[(x: Int64)]`;
  -- draining it runs `materialize_solution`, which reads each column out of the
  -- answer substitution. Summing is enough to decide the question: a column that
  -- drained as an unbound `Value::Var` cannot sum to 6.
  operation add_col(acc: Int64, row: (x: Int64)) -> Int64 = Int64.add(acc, row.x)
  operation drained_builtin() -> Int64 effects Error =
    foldLeft(builtin_bound.takeN(10), 0, add_col)
  operation drained_fact() -> Int64 effects Error =
    foldLeft(fact_bound.takeN(10), 0, add_col)

  -- A CONSTRUCTOR-valued column on the occurrence carrier — the second way the
  -- old carrier match failed, and in a different reader (`field_access`, not
  -- `numeric_add`).
  rule ctor_bound(?x) :- ?x <=> B(v: 6)
  operation add_field(acc: Int64, row: (x: Box)) -> Int64 = Int64.add(acc, row.x.v)
  operation drained_ctor() -> Int64 effects Error =
    foldLeft(ctor_bound.takeN(10), 0, add_field)
end
"#;

/// Resolve `probe.wi2yhz3.<name>(?x)` and hand back the KB plus the query var, so
/// each test reads the SAME answer two ways. Asserts exactly one definite
/// solution — every rule here is deterministic, and a second answer would mean
/// the fixture, not the reader, moved.
fn one_answer(kb: &mut KnowledgeBase, name: &str) -> (VarId, anthill_core::kb::resolve::Solution) {
    let functor = kb
        .try_resolve_symbol(&format!("probe.wi2yhz3.{name}"))
        .unwrap_or_else(|| panic!("`{name}` did not load"));
    let x_sym = kb.intern("x");
    let vid = kb.fresh_var(x_sym);
    let goal = Value::Entity {
        functor,
        pos: std::rc::Rc::from(vec![Value::Var(Var::Global(vid))]),
        named: std::rc::Rc::from(Vec::new()),
    };
    let mut sols = kb.resolve(&[goal], &ResolveConfig::default());
    sols.retain(|s| s.is_definite());
    assert_eq!(sols.len(), 1, "`{name}` must have exactly one definite answer");
    (vid, sols.pop().unwrap())
}

/// The `Int64` a binding carries, or `None` for anything else — an unbound var
/// included. Deliberately NOT a panic: one test here asserts `None` is exactly
/// what the broken reader produces.
///
/// Read through `TermView`, which is the point rather than a convenience.
/// `answer_binding` is CARRIER-FAITHFUL by contract (WI-348), and a rule body's
/// atoms ride as occurrences (WI-246) — so `?x <=> 6` binds `?x` to a
/// `Value::Node` carrying `6`, while `B(v: ?x)` binds a hash-consed
/// `Value::Term`. Both are the same answer; a carrier-specific read would make
/// this suite pass for one path and fail for the other for reasons that have
/// nothing to do with what it is measuring.
fn as_int(kb: &KnowledgeBase, v: &Value) -> Option<i64> {
    match v.head(kb) {
        ViewHead::Const(Literal::Int(n)) => Some(n),
        _ => None,
    }
}

/// THE HEADLINE. `rule builtin_bound(?x) :- ?x <=> 6` — one goal, one builtin, no
/// operation anywhere in it — and its head variable reads back as `6`.
#[test]
fn builtin_bound_head_var_reads_as_its_value() {
    let mut kb = load_kb_with(SRC);
    let (vid, sol) = one_answer(&mut kb, "builtin_bound");
    let bound = kb
        .answer_binding(vid, &sol.subst)
        .expect("`?x <=> 6` binds ?x");
    assert_eq!(
        as_int(&kb, &bound),
        Some(6),
        "a head var bound by a rule-body builtin must read as its VALUE; got {bound:?}",
    );
}

/// THE PIN THAT MAKES THE TEST ABOVE MEAN SOMETHING. The one-hop read is still
/// truncated — it stops at the uncompressed link and hands back a `Var`. Without
/// this, `builtin_bound_head_var_reads_as_its_value` would keep passing if
/// someone "simplified" `answer_binding` back to `resolve_as_value` on a tree
/// where σ happened to be flat.
#[test]
fn one_hop_read_is_the_defect_being_fixed() {
    let mut kb = load_kb_with(SRC);
    let (vid, sol) = one_answer(&mut kb, "builtin_bound");
    let one_hop = sol
        .subst
        .resolve_as_value(vid)
        .expect("the answer link itself is present — it is where it POINTS that is wrong")
        .clone();
    assert_eq!(
        as_int(&kb, &one_hop),
        None,
        "the one-hop read must still stop at the uncompressed link, or this suite \
         is measuring nothing; got {one_hop:?}",
    );
    assert!(
        matches!(one_hop.head(&kb), ViewHead::Var(Var::Global(_))),
        "and it stops on a VAR — the link `?a -> Var(F)` that sigma never compressed. \
         That is what made the truncation invisible: it is shaped exactly like an \
         answer that bound nothing. Got {one_hop:?}",
    );
}

/// DEEP, NOT A CHASE. `?x <=> B(v: ?y), ?y <=> 6` binds `?x` to a term whose
/// CHILD is behind a second uncompressed link. A top-level var chase reports
/// `B(v: Var(G))` here and passes every other test in this file.
#[test]
fn nested_binding_resolves_all_the_way_down() {
    let mut kb = load_kb_with(SRC);
    let (vid, sol) = one_answer(&mut kb, "nested");
    let bound = kb.answer_binding(vid, &sol.subst).expect("?x binds");
    // Carrier-neutral again: `?x <=> B(v: ?y)` binds an occurrence, so a
    // `Value::Entity`/`Value::Term` match would miss the very shape under test.
    let key = bound
        .named_keys(&kb)
        .into_iter()
        .find(|k| kb.local_name_of(*k) == "v")
        .unwrap_or_else(|| panic!("the answer must be a `B` with a `v` field; got {bound:?}"));
    let field = bound
        .named_arg(&kb, key)
        .map(|c| c.to_value())
        .expect("`v` reads back");
    assert_eq!(
        as_int(&kb, &field),
        Some(6),
        "the NESTED var must resolve too — a top-level chase leaves it a var; got {field:?}",
    );
}

/// THE OTHER SHAPE THE CARRIER MATCH BROKE. A column bound to a CONSTRUCTOR on
/// the occurrence carrier failed in a different reader from the scalar one —
/// `field_access: receiver is not an entity (got Node)`, where the scalar case
/// died in `numeric_add`. Two readers, one cause, and this test says which cause:
/// both READERS were missing an arm, not the drain missing a conversion.
///
/// This paragraph used to end "both are green off the same `value_to_native` call,
/// which is the evidence that it is the boundary and not a pair of special cases",
/// and that reading was WRONG — WI-20260827-3ZNBC measured it. They are green off
/// `reflect_field_access` reading its receiver through `TermView` and `Int64.add`
/// reading its operands through `TermView::literal_int64`; with those in place the
/// drain's conversion had nothing left to fix and was removed, and this row stayed
/// green through the removal. A conversion that every consumer can do without is not
/// a boundary.
#[test]
fn a_constructor_column_on_the_occurrence_carrier_materializes() {
    let mut interp = interp_for(SRC);
    let out = interp
        .call("probe.wi2yhz3.drained_ctor", &[])
        .expect("the constructor-valued relation drains");
    assert_eq!(
        as_int(interp.kb(), &out),
        Some(6),
        "a Node-carried constructor column must materialize as an entity whose \
         field reads back; got {out:?}",
    );
}

/// A CHAIN, NOT A LINK — the case a single splice hop passes and a fixpoint is
/// needed for. `?x <=> ?y, ?y <=> ?z, ?z <=> 6` binds each var to an OCCURRENCE
/// carrying the next var, and `subst_var_leaf`'s `Value::Node` arm used to splice
/// the bound occurrence in WITHOUT re-substituting it — so the walk stopped after
/// one Node→Node hop and `?x` came back as `Var(z)`. Every other test in this file
/// has a chain of length one and passes over that gap; found in review.
#[test]
fn a_chain_of_var_links_resolves_to_a_fixpoint() {
    let mut kb = load_kb_with(SRC);
    let (vid, sol) = one_answer(&mut kb, "chain3");
    let bound = kb.answer_binding(vid, &sol.subst).expect("?x binds");
    assert_eq!(
        as_int(&kb, &bound),
        Some(6),
        "a three-link chain must resolve all the way; got {bound:?}",
    );
}

/// The same chain UNDER a constructor — the two halves of the walk (splice the
/// bound occurrence, recurse into children) have to reach a fixpoint together.
#[test]
fn a_chain_under_a_constructor_resolves_too() {
    let mut kb = load_kb_with(SRC);
    let (vid, sol) = one_answer(&mut kb, "deep_chain");
    let bound = kb.answer_binding(vid, &sol.subst).expect("?x binds");
    let key = bound
        .named_keys(&kb)
        .into_iter()
        .find(|k| kb.local_name_of(*k) == "v")
        .unwrap_or_else(|| panic!("the answer must be a `B` with a `v` field; got {bound:?}"));
    let field = bound
        .named_arg(&kb, key)
        .map(|c| c.to_value())
        .expect("`v` reads back");
    assert_eq!(
        as_int(&kb, &field),
        Some(6),
        "a chain nested under a constructor must resolve too; got {field:?}",
    );
}

/// CONTROL — passes either way BY DESIGN. A fact match binds through
/// `bind_compressed`, which re-points the answer link, so one hop already lands
/// on the value. Both readers agree, and that agreement is why the builtin
/// path's truncation went unnoticed for as long as it did.
#[test]
fn fact_bound_head_var_was_never_truncated() {
    let mut kb = load_kb_with(SRC);
    let (vid, sol) = one_answer(&mut kb, "fact_bound");
    let one_hop = as_int(&kb, &sol.subst.resolve_as_value(vid).expect("bound").clone());
    let deep = kb.answer_binding(vid, &sol.subst).expect("bound");
    assert_eq!(one_hop, Some(6), "the compressed path was always readable");
    assert_eq!(
        as_int(&kb, &deep),
        Some(6),
        "and the correct reader must not change what it says there",
    );
}

/// CONTROL — passes either way BY DESIGN. Resolution was never wrong: a GROUND
/// query decides in both directions, with or without the reader fix, because a
/// ground query has no answer var to project. This is the measurement that
/// separated "the resolver cannot bind" (false) from "the reader cannot read it"
/// (true).
#[test]
fn ground_queries_decided_correctly_throughout() {
    let mut kb = load_kb_with(SRC);
    let functor = kb
        .try_resolve_symbol("probe.wi2yhz3.builtin_bound")
        .expect("loaded");
    let ask = |kb: &mut KnowledgeBase, n: i64| {
        let goal = Value::Entity {
            functor,
            pos: std::rc::Rc::from(vec![Value::Int(n)]),
            named: std::rc::Rc::from(Vec::new()),
        };
        kb.resolve(&[goal], &ResolveConfig::default())
            .iter()
            .filter(|s| s.is_definite())
            .count()
    };
    assert_eq!(ask(&mut kb, 6), 1, "`builtin_bound(6)` is provable");
    assert_eq!(ask(&mut kb, 7), 0, "`builtin_bound(7)` is refuted");
}

/// THE SECOND READER. `materialize_solution` (eval/mod.rs) turns one answer into
/// a relation row, reading each column out of the answer substitution — and read
/// one hop, a column bound by a rule-body builtin came back a `Value::Var`: a
/// typed `Int64` column reporting itself unbound, in the very face built to
/// replace raw substitution walking with typed rows.
///
/// The `drained_fact` half is the CONTROL and passes either way — same drain,
/// same shape, compressed bind path.
#[test]
fn relation_column_bound_by_a_builtin_drains_as_its_value() {
    let mut interp = interp_for(SRC);
    let control = interp
        .call("probe.wi2yhz3.drained_fact", &[])
        .expect("the fact-backed relation drains");
    assert_eq!(
        as_int(interp.kb(), &control),
        Some(6),
        "CONTROL: a fact-bound column always drained correctly; got {control:?}",
    );
    let out = interp
        .call("probe.wi2yhz3.drained_builtin", &[])
        .expect("the builtin-backed relation drains");
    assert_eq!(
        as_int(interp.kb(), &out),
        Some(6),
        "a relation column bound by a rule-body builtin must drain as its VALUE; \
         got {out:?}",
    );
}
