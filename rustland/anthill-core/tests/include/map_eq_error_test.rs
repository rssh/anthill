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
