//! `List.contains` / `Set.contains` — CONTAINER FIRST, so they dot-dispatch.
//!
//! WHY THE RENAME. `member(x: T, l: List)` took the ELEMENT first, and §6.7 binds a
//! dot receiver to the first parameter — so `l.member(7)` was refused
//! `expected List, got Int64`, measured. Every sibling container question is already
//! spelled the other way (`Map.contains(m, key)`, `String.contains(s, sub)`), so
//! `member` was the odd one out on all three axes at once: a different NAME for the
//! same question, a reversed ORDER, and no dot dispatch as a consequence.
//!
//! `member` was owned by no spec (`IndexedSeq` / `FiniteCollection` / `Iterable`
//! declare no such operation, measured), so the rename was unconstrained.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! Restore `operation member(x: T, l: List)` and every row here fails: the first two
//! on the name, [`list_contains_dot_dispatches`] and [`set_contains_dot_dispatches`]
//! additionally on the ORDER, which is the half a pure rename would not have fixed.
//!
//! One row also fails on a DIFFERENT back-out:
//! [`list_contains_over_a_literal_as_a_rule_body_goal`] needs WI-1096's list-literal
//! lowering. It was deliberately absent while WI-1096 was open —
//! [`list_contains_as_a_rule_body_goal`] uses the `cons` spelling so the rename could
//! be pinned without tripping on that defect — and is the natural home for the literal
//! spelling now that it answers.

use anthill_core::eval::Value;

fn eval_bool(src: &str, op: &str) -> bool {
    let mut interp = crate::common::interp_for(src);
    match interp.call(op, &[]) {
        Ok(Value::Bool(b)) => b,
        Ok(other) => panic!("expected Bool from {op}, got {}", other.type_name()),
        Err(e) => panic!("{op} failed: {e}"),
    }
}

/// THE POINT OF THE RENAME — the receiver is the container, so dot works.
#[test]
fn list_contains_dot_dispatches() {
    let src = r#"
namespace cr1
  import anthill.prelude.{List, Int64, Bool}
  operation yes() -> Bool =
    let l = [1, 2, 3]
    l.contains(2)
  operation no() -> Bool =
    let l = [1, 2, 3]
    l.contains(9)
end
"#;
    assert!(eval_bool(src, "cr1.yes"), "2 IS in [1,2,3]");
    assert!(!eval_bool(src, "cr1.no"), "9 is NOT in [1,2,3]");
}

/// The qualified spelling, which worked before and must keep working — with the
/// arguments now container-first.
#[test]
fn list_contains_qualified() {
    let src = r#"
namespace cr2
  import anthill.prelude.{List, Int64, Bool}
  operation yes() -> Bool = List.contains([1, 2, 3], 2)
  operation no() -> Bool = List.contains([1, 2, 3], 9)
end
"#;
    assert!(eval_bool(src, "cr2.yes"));
    assert!(!eval_bool(src, "cr2.no"));
}

/// The SLD face — a bare goal in a rule body, which is the derived relational view
/// (WI-580). Driven both ways so a predicate that answered everything would fail.
#[test]
fn list_contains_as_a_rule_body_goal() {
    let src = r#"
namespace cr3
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.List.{contains, cons, nil}
  rule yes(1) :- contains(cons(head: 7, tail: nil), 7)
  rule no(1)  :- contains(cons(head: 7, tail: nil), 9)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(crate::common::definite_unary(&mut kb, "cr3.yes").len(), 1);
    assert_eq!(
        crate::common::definite_unary(&mut kb, "cr3.no").len(),
        0,
        "9 is not in [7] — a goal answering here is the WI-1096 shape"
    );
}

/// The same SLD face over the `[…]` LITERAL spelling, which is how a user would
/// actually write it. It is a separate row because it used to answer differently from
/// the `cons`-spelled twin above: the literal stayed a flat `ListLiteral`, `contains`
/// could not destructure it, and `no` came back as an undischarged residual that reads
/// as a solution. WI-1096 lowers the literal at the one conversion site, so the two
/// spellings now answer alike — which is the whole point of the row.
///
/// It fails when WI-1096's default is backed out; the `cons`-spelled twin above passes
/// either way, which is what attributes this one to the spelling.
#[test]
fn list_contains_over_a_literal_as_a_rule_body_goal() {
    let src = r#"
namespace cr3lit
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.List.{contains}
  fact mark(1)
  rule yes(?m) :- mark(?m), contains([7], 7)
  rule no(?m)  :- mark(?m), contains([7], 9)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        crate::common::definite_unary(&mut kb, "cr3lit.yes").len(),
        1,
        "7 IS in [7], and decided — not carried out as a residual"
    );
    assert_eq!(
        crate::common::definite_unary(&mut kb, "cr3lit.no").len(),
        0,
        "9 is not in [7], the literal spelling included (WI-1096)"
    );
}

/// `Set.contains` is CLAUSE-defined (no body), and `Set` is an ABSTRACT typeclass —
/// `empty` / `insert` have no runnable bodies, so its algebra lived in the SLD world over
/// the symbolic `insert`/`empty` normal form.
///
/// SINCE WI-20260926-K4JGC (proposal 068 §2.3) that normal form is UNREDUCED calls, not
/// data: a goal argument is evaluated before its head is matched, `insert(…)` cannot run,
/// and the goal is UNDECIDED — `yes` and `no` alike are one conditional row, neither
/// answered nor refuted. The renamed clauses' composition is re-driven when
/// WI-20260926-QCJ0B gives `Set` a route back. FAILS with K4JGC backed out: `yes` is
/// definite and `no` empty.
#[test]
fn set_contains_answers_over_the_symbolic_algebra() {
    let src = r#"
namespace cr4
  import anthill.prelude.{Set, Int64, Bool}
  import anthill.prelude.Set.{empty, insert, contains}
  rule yes(1) :- contains(insert(insert(empty(), 1), 2), 2)
  rule no(1)  :- contains(insert(insert(empty(), 1), 2), 9)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    for rel in ["cr4.yes", "cr4.no"] {
        let rows = crate::common::query_unary(&mut kb, rel);
        assert!(
            rows.len() == 1 && !rows[0].1,
            "{rel}: one UNDECIDED row over the symbolic algebra; got {rows:?}",
        );
    }
}

/// THE CONTROL FOR THE ALGEBRA: `Set.eq` is defined THROUGH `subset`, and `subset`'s
/// clause calls `contains` — so this was what proved the renamed clauses COMPOSE.
///
/// SINCE WI-20260926-K4JGC it is undecided in both directions, for the reason
/// [`set_contains_answers_over_the_symbolic_algebra`] gives; the composition is re-driven
/// with WI-20260926-QCJ0B. FAILS with K4JGC backed out: `same` is definite and
/// `different` empty.
#[test]
fn set_equality_still_decides_by_membership() {
    let src = r#"
namespace cr5
  import anthill.prelude.{Set, Int64, Bool}
  import anthill.prelude.Set.{empty, insert}
  import anthill.prelude.PartialEq.{eq}
  rule same(1) :- eq(insert(insert(empty(), 1), 2), insert(insert(empty(), 2), 1))
  rule different(1) :- eq(insert(empty(), 1), insert(empty(), 9))
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    for rel in ["cr5.same", "cr5.different"] {
        let rows = crate::common::query_unary(&mut kb, rel);
        assert!(
            rows.len() == 1 && !rows[0].1,
            "{rel}: one UNDECIDED row over the symbolic algebra; got {rows:?}",
        );
    }
}
