//! WI-650 — `Eq[Map]` is DECLARED (`provides Eq[T = Map]` plus a bodyless `eq`
//! override slot the WI-625 host bridge will fill) but has NO backing: no
//! runnable body and no general SLD clause. A `=`/`eq` comparing two Maps
//! type-checks (`Eq.eq` is a total builtin, so the WI-325/WI-300 requirement
//! passes never flag it) yet would SILENTLY misdecide at resolution
//! (`sem_eq_dispatch` targets the empty override, exhausts, returns "not
//! equal"). `BuiltinResult` has no error channel, so the typer names it loudly
//! at LOAD instead — `check_eq_override_backing` / `TypeError::EqOverrideUnbacked`.
//!
//! Each error case gives the comparison two operands the typer stamps as `Map`:
//! the VAR operands of a rule-body `eq`/`neq` GOAL, typed via the enclosing
//! operation's `Map` parameters (the WI-603 var-leaf stamping the check reads,
//! shared with `check_one_spec_op_requirement`), plus an op BODY `= eq(a, b)` /
//! `= neq(a, b)`. The controls must STILL load clean: structural `===` on maps
//! (never dispatches to the override) and `eq` on `Set`, whose override IS backed
//! by a general `eq(?a, ?b) :- subset(…)` clause. The `wi616_semantic_eq` sibling
//! covers runtime dispatch; this file is load-time only.
//!
//! WI-651 — `neq(map, map)` is flagged identically to `eq(map, map)`. The check
//! matches `Eq.neq` alongside `Eq.eq` (there is no distinct `neq` override — a
//! `neq` dispatches through the carrier's own `eq` override too, so an unbacked
//! `eq` is exactly what makes `neq(map, map)` misdecide). Both operands of a
//! `neq(?a, ?b)` goal over two `Map[…]` params are stamped `Map` by the same
//! WI-603 var-leaf inference `eq` uses (WI-651 investigated an earlier worry that
//! `neq` under-determines its operand to the abstract param `Map.K` and found it
//! false — that `Map.K` was Map's OWN key comparison `neq(?k, ?k2)` in the
//! `get(put(…))` rewrite law, where the operands genuinely ARE keys of type `K`,
//! correctly typed and correctly not flagged). The `map_neq_*` cases below pin it.

/// Assert the load errors include the `Eq[Map] declared but unimplemented`
/// diagnostic. Matches the two stable substrings — the carrier name and the
/// cause phrase — so a wording tweak around them does not break the test.
fn assert_map_eq_unbacked(errs: &[String]) {
    assert!(
        errs.iter()
            .any(|e| e.contains("declared but unimplemented") && e.contains("Map")),
        "expected an `Eq[Map] declared but unimplemented` load error; got:\n{}",
        errs.join("\n"),
    );
}

/// Assert a source loads with no errors (a control that must stay clean).
fn assert_loads_clean(src: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("expected a clean load; got errors:\n{}", errs.join("\n"));
    }
}

// ── The load errors: comparing two Maps ─────────────────────────────────────

#[test]
fn map_eq_in_rule_body_goal_is_a_load_error() {
    // A rule-body `eq` GOAL whose var operands are typed `Map[Int64, Int64]` by
    // the operation `same`'s parameters — the rule-body-goal pass.
    let src = r#"
        namespace mapeq.rulebody
          import anthill.prelude.{Bool, Int64, Map, Eq}
          operation same(a: Map[K = Int64, V = Int64], b: Map[K = Int64, V = Int64]) -> Bool
          rule same(?a, ?b) :- eq(?a, ?b)
        end
    "#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_map_eq_unbacked(&errs);
}

#[test]
fn map_neq_in_rule_body_goal_is_a_load_error() {
    // WI-651 — the `neq` sibling of `map_eq_in_rule_body_goal_is_a_load_error`.
    // Both var operands of `neq(?a, ?b)` are typed `Map[Int64, Int64]` by the
    // operation `differ`'s parameters (the same WI-603 var-leaf stamping `eq`
    // uses), so the check flags them — `neq(map, map)` misdecides through the
    // SAME empty `Map.eq` override, negated.
    let src = r#"
        namespace mapneq.rulebody
          import anthill.prelude.{Bool, Int64, Map, Eq}
          operation differ(a: Map[K = Int64, V = Int64], b: Map[K = Int64, V = Int64]) -> Bool
          rule differ(?a, ?b) :- neq(?a, ?b)
        end
    "#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_map_eq_unbacked(&errs);
}

#[test]
fn map_neq_in_op_body_is_a_load_error() {
    // WI-651 — the `neq` sibling of `map_eq_in_op_body_is_a_load_error`: an
    // operation FUNCTIONAL body comparing its two `Map` params with `neq`.
    let src = r#"
        namespace mapneq.opbody
          import anthill.prelude.{Bool, Int64, Map, Eq}
          operation differ(a: Map[K = Int64, V = Int64], b: Map[K = Int64, V = Int64]) -> Bool
            = neq(a, b)
        end
    "#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_map_eq_unbacked(&errs);
}

#[test]
fn map_eq_in_op_body_is_a_load_error() {
    // An operation FUNCTIONAL body comparing its two `Map` params with `eq` — the
    // WI-325 op-body pass (`op_bodies_iter`), the other driver of the check.
    let src = r#"
        namespace mapeq.opbody
          import anthill.prelude.{Bool, Int64, Map, Eq}
          operation same(a: Map[K = Int64, V = Int64], b: Map[K = Int64, V = Int64]) -> Bool
            = eq(a, b)
        end
    "#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_map_eq_unbacked(&errs);
}

// ── Controls that must STILL load clean ─────────────────────────────────────

#[test]
fn map_struct_eq_loads_clean() {
    // `===` is STRUCTURAL (`struct_eq`, not `Eq.eq`); it never dispatches to the
    // carrier override, so comparing two maps with it is always well-defined and
    // must NOT be flagged.
    let src = r#"
        namespace mapeq.structeq
          import anthill.prelude.{Bool, Int64, Map}
          operation same(a: Map[K = Int64, V = Int64], b: Map[K = Int64, V = Int64]) -> Bool
          rule same(?a, ?b) :- ?a === ?b
        end
    "#;
    assert_loads_clean(src);
}

#[test]
fn set_eq_in_body_loads_clean() {
    // Set's `Eq` override IS backed (`rule eq(?a, ?b) :- subset(…)`, a general
    // all-var head), so a body comparing two Sets with `eq` is fine — WI-650
    // flags only carriers whose own override has no rules and no runnable body.
    let src = r#"
        namespace mapeq.seteq
          import anthill.prelude.{Bool, Int64, Set, Eq}
          operation same(a: Set[T = Int64], b: Set[T = Int64]) -> Bool
          rule same(?a, ?b) :- eq(?a, ?b)
        end
    "#;
    assert_loads_clean(src);
}

// ── WI-652 gap 1: COMPOUND operands ─────────────────────────────────────────
// A rule-body operand that is not a var leaf (`build_map(x)`, `Map.put(…)`)
// carries no WI-603 stamp, so the carrier is read from the operand HEAD's result
// sort (`operand_head_result_carrier`). Both operands here are compound, so the
// original var-leaf channel cannot see them — only the WI-652 head channel does.

#[test]
fn map_eq_compound_operand_in_rule_body_is_a_load_error() {
    // `eq(build_map(?x), other())` — both operands are op applies returning `Map`,
    // NOT var leaves. Neither is stamped, so the compound-head channel (A2) is the
    // only one that reaches them.
    let src = r#"
        namespace mapeq.compound
          import anthill.prelude.{Bool, Int64, Map, Eq}
          operation build_map(x: Int64) -> Map[K = Int64, V = Int64]
          operation other() -> Map[K = Int64, V = Int64]
          operation same(x: Int64) -> Bool
          rule same(?x) :- eq(build_map(?x), other())
        end
    "#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_map_eq_unbacked(&errs);
}

#[test]
fn map_eq_put_empty_compound_operand_is_a_load_error() {
    // The ticket's literal example — `eq(put(empty(), …), empty())` — via qualified
    // `Map.put`/`Map.empty` (the algebra constructors that build a `Map`).
    let src = r#"
        namespace mapeq.putempty
          import anthill.prelude.{Bool, Int64, Map, Eq}
          operation same() -> Bool
          rule same() :- eq(Map.put(Map.empty(), 1, 2), Map.empty())
        end
    "#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_map_eq_unbacked(&errs);
}

// ── WI-652 gap 2: DOT-form `m.eq(n)` ────────────────────────────────────────
// Dot dispatch rewrites `m.eq(n)` to `Map.eq(m, n)`, whose functor is the
// carrier's own `eq` op, not `PartialEq.eq` — so `is_eq_call` misses it. The
// `own_eq_op_carrier` channel reads the carrier straight off that functor.

#[test]
fn map_eq_dot_form_in_op_body_is_a_load_error() {
    let src = r#"
        namespace mapeq.dotop
          import anthill.prelude.{Bool, Int64, Map, Eq}
          operation same(a: Map[K = Int64, V = Int64], b: Map[K = Int64, V = Int64]) -> Bool
            = a.eq(b)
        end
    "#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_map_eq_unbacked(&errs);
}

#[test]
fn map_eq_dot_form_in_rule_body_is_a_load_error() {
    let src = r#"
        namespace mapeq.dotrule
          import anthill.prelude.{Bool, Int64, Map, Eq}
          operation same(a: Map[K = Int64, V = Int64], b: Map[K = Int64, V = Int64]) -> Bool
          rule same(?a, ?b) :- ?a.eq(?b)
        end
    "#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_map_eq_unbacked(&errs);
}

// ── WI-652 gap 3: EVALUATED (quantifier) constraint bodies ──────────────────
// A quantifier constraint is lowered to a real `LogicalQuery` guard (unlike a
// `head :- guard` DENIAL constraint, which is stored as an inert `Constraint`
// fact and never evaluated). A guard carries no stamped operand types, so only
// the compound-head / own-op channels reach it — the same detection the rule/op
// walks use, carried over the untyped `Value` via `TermView`.

#[test]
fn map_eq_compound_in_quantifier_constraint_is_a_load_error() {
    // The body `eq(build_map(?x), build_map(?x))` of a `no ?x -: …` guard is
    // evaluated at load; comparing two `Map`s there would silently misdecide, so
    // the compound-operand head channel flags it.
    let src = r#"
        namespace mapeq.constraint
          import anthill.prelude.{Bool, Int64, Map, Eq}
          operation build_map(x: Int64) -> Map[K = Int64, V = Int64]
          fact num(1)
          constraint c: no ?x: num(?x) -: eq(build_map(?x), build_map(?x))
        end
    "#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_map_eq_unbacked(&errs);
}

// ── Controls: a BACKED carrier's new channels must stay clean ────────────────
// Set's `eq` override IS backed (`eq(?a, ?b) :- subset(…)`), so neither the
// dot-form nor the compound-operand channel may over-fire on it.

#[test]
fn set_eq_dot_form_in_op_body_loads_clean() {
    let src = r#"
        namespace mapeq.setdot
          import anthill.prelude.{Bool, Int64, Set, Eq}
          operation same(a: Set[T = Int64], b: Set[T = Int64]) -> Bool
            = a.eq(b)
        end
    "#;
    assert_loads_clean(src);
}

#[test]
fn set_eq_compound_operand_loads_clean() {
    let src = r#"
        namespace mapeq.setcompound
          import anthill.prelude.{Bool, Int64, Set, Eq}
          operation build_set(x: Int64) -> Set[T = Int64]
          operation same(x: Int64) -> Bool
          rule same(?x) :- eq(build_set(?x), build_set(?x))
        end
    "#;
    assert_loads_clean(src);
}

// The false-positive the `eq_defined` leg guards against — a carrier backing its
// own `eq` via an equational `Carrier.eq(?a,?b) = rhs` that WI-139 unindexes — is
// NOT separately unit-tested here: `is_equational_head` (WI-627) fires only for the
// CANONICAL `PartialEq.eq` head, so the trigger requires an esoteric namespace-level
// equational rule over a carrier's own `eq`, not a realistic user shape. The leg's
// correctness rides on `op_backed_one` parity with `op_backed` (whose `eq_defined`
// leg the provider-operation suite exercises) and on the Map cases above staying a
// load error (Map's `eq` is NOT in `eq_defined`, so the leg does not unmask it).

#[test]
fn abstract_spec_redeclaring_eq_loads_clean() {
    // WI-652 correctness: a USER spec that redeclares a bodyless `eq` (a sort
    // DISTINCT from `PartialEq`) must NOT be flagged by the dot-form / own-op
    // channel — its own `eq` is an abstract requirement satisfied by impls, not an
    // unbacked concrete override. Its default `neq <=> not(eq(…))` rule calls
    // `MyEq.eq`, which (unlike `PartialEq.eq`) survives `carrier_own_op`'s
    // `o != spec_op` filter, so the channel must apply the abstract-spec eligibility
    // filter (shared `unbacked_eq_carrier`) to stay clean rather than spuriously erroring.
    let src = r#"
        namespace mapeq.userspec
          import anthill.reflect.{not}
          import anthill.prelude.Bool
          sort MyEq
            sort T = ?
            operation {
              eq(a: T, b: T) -> Bool
            }
            operation neq2(a: T, b: T) -> Bool = not(eq(a, b))
          end
        end
    "#;
    assert_loads_clean(src);
}

// Two WI-652 gaps are left deliberately OPEN and documented on `check_eq_override_backing`
// (typing.rs), not pinned by a test here — both need a concrete operand sort a
// load-time check cannot see, so no in-source shape reaches them today:
//   - a POLYMORPHIC operand typed by an abstract `T` (`same[T](a, b) = eq(a, b)`)
//     never concretizes to `Map` at load;
//   - a BARE-VAR operand in a constraint (`… -: eq(?m, ?n)`) has no stamped type on
//     the untyped guard `Value` (only the compound/dot channels above reach a guard).
// A DENIAL constraint (`c :- eq(m, m)`) is stored as an inert `Constraint` fact and
// never evaluated, so an unbacked-eq there cannot misdecide — correctly not flagged.
