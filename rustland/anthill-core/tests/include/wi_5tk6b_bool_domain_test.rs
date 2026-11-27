//! WI-20260911-5TK6B — `Bool` ENUMERATES: its `fill` is derived ONE CLAUSE PER LITERAL, the
//! literal in the head — `Bool.__fill(true)`, `Bool.__fill(false)` — the shape a sort's
//! constructors get (proposal 060 §2.3, "The head decides the mode"; WI-20261115-YR3N7). A bound
//! `Bool` selects its one clause, a check; an unbound one matches both heads, `true` then `false`.
//! Before, `Bool` was a primitive like `Int64`, its `fill` the waiting type check: `?x: Bool` over
//! an unbound `?x` answered one undecided row. `Int64` and `String` keep that check — they are
//! INFINITE, the line `Bool` sits on the other side of (`fill_derive::FINITE_PRIMITIVES`).
//!
//! NO `Bool.domain` (user, 2026-11-27). The value face is superseded by `SortDomain[T].fill`, and
//! every fill reaches `Bool.__fill` through `apply_domain`; the loader mints `<Sort>.domain` only
//! for a face's citation, so it mints none for `Bool`, and a goal or a citation of it names
//! nothing — refused at load. Minted with no clause, it would have answered nothing in silence.
//!
//! BACK-OUT, measured 2026-11-27, each axis a temporary mutation in one build, over this file
//! and `wi743` (30 rows):
//!  * [L] the literal clauses not derived (`Bool` back on the waiting check) — 5 fail:
//!    `an_unbound_bool_column_enumerates_true_then_false`, `a_spine_of_free_bool_cells_fills`,
//!    `a_bool_inside_a_value_enumerates`, `a_rigid_type_variable_at_bool_counts_two` and
//!    `wi743::bool_has_a_derived_domain_and_enumerates`;
//!  * [V] each literal's clause with a VARIABLE head, `__fill(?x) :- unify(?x, true)` (the shape
//!    that proposes each literal to a bound value in turn) — `a_bound_bool_selects_its_one_clause`
//!    alone: the answers are the same, and the `false` clause is asked after the `true` one;
//!  * [M] `Bool.domain` minted as before, and left with no clause — `bool_has_no_value_face`
//!    alone: its goal loads clean and answers nothing.
//!
//! `infinite_primitives_keep_the_waiting_check` and `tiny_sat_over_facts_answers_its_two_models`
//! pass under every axis BY DESIGN: the line the change must not cross, and the tiny-sat whose
//! facts bind every cell before the fill runs.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::{ResolveConfig, ResolveStats};
use anthill_core::kb::KnowledgeBase;

use crate::common::{
    assert_refused_naming, definite_unary, load_errors_of, load_kb_with, query_pattern_term,
    query_unary, show_value,
};

const BOOLS: &str = r#"
namespace t5tk6b
  import anthill.prelude.{Bool, Int64, String, List, Option, Error}
  import anthill.prelude.Bool.{or, and}
  import anthill.reflect.SortDomain

  rule b(?x: Bool) :- true
  rule b2(?x: Bool) :- ?x <=> true
  rule ints(?x: Int64) :- true
  rule strs(?x: String) :- true

  entity Flag(on: Bool)
  rule flags(?f: Flag) :- true
  rule opts(?o: Option[T = Bool]) :- true

  rule cells(vs: List[T = Bool]) :- vs <=> [?p, ?q]

  -- tiny-sat over `Bool`, the formula as TESTS that wait for the cells, so the typed head's fill
  -- is what binds them: (p or not q) and (q or r) and (not p or not r), over `or` and `and` alone
  -- (p or not q is `or(p, q) = p`; not p or not r is `and(p, r) = false`).
  rule model(vs: List[T = Bool])
    :- vs <=> [?p, ?q, ?r], or(?p, ?q) = ?p, or(?q, ?r) = true, and(?p, ?r) = false

  -- tiny-sat as `examples/classic-mini/tiny-sat` writes it, over `Bool` for its `Bit`: the `neg`
  -- facts bind every cell before the fill runs, so the fill only checks.
  fact neg(true, false)
  fact neg(false, true)
  rule or2(?a, ?)  :- ?a <=> true
  rule or2(?a, ?b) :- ?a <=> false, ?b <=> true
  rule factModel(vs: List[T = Bool])
    :- vs <=> [?p, ?q, ?r],
       neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
       or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)

  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- true
  end
  sort Driver
    operation countAt[X]() -> Int64 effects {Error} requires SortDomain[T = X] =
      Wrap[T = X].el.takeN(9).length()
    operation bools() -> Int64 effects {Error} = countAt[X = Bool]()
    operation wrapped() -> Int64 effects {Error} = countAt[X = Wrap[T = Bool]]()
  end
end
"#;

/// The search of `pattern`, drained up to `max_solutions` (0: all): its definite answers and
/// its telemetry.
fn search(kb: &mut KnowledgeBase, pattern: &str, max_solutions: usize) -> (usize, ResolveStats) {
    let goal = query_pattern_term(kb, pattern);
    let config = ResolveConfig {
        max_solutions,
        ..ResolveConfig::default()
    };
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config);
    assert!(!stats.truncated, "`{pattern}` was truncated: {stats:?}");
    (solutions.iter().filter(|s| s.is_definite()).count(), stats)
}

/// Every answer of the unary relation `qn`, rendered, with whether it is definite.
fn rendered(kb: &mut KnowledgeBase, qn: &str) -> Vec<(String, bool)> {
    query_unary(kb, qn)
        .into_iter()
        .map(|(v, definite)| (show_value(kb, &v), definite))
        .collect()
}

fn drive(entry: &str) -> Result<i64, String> {
    let mut interp = crate::common::interp_for(BOOLS);
    match interp.call(&format!("t5tk6b.Driver.{entry}"), &[]).map(|h| h.value) {
        Ok(Value::Int(n)) => Ok(n),
        other => Err(format!("{other:?}")),
    }
}

/// ROW 1: an unbound `?x: Bool` answers its two literals, DEFINITELY, `true` then `false`.
#[test]
fn an_unbound_bool_column_enumerates_true_then_false() {
    let mut kb = load_kb_with(BOOLS);
    assert_eq!(
        rendered(&mut kb, "t5tk6b.b"),
        [("true".to_string(), true), ("false".to_string(), true)],
    );
}

/// ROW 2: a bound `Bool` is CHECKED — it selects the one clause its literal heads, and after the
/// answer the search asks no goal again: no case is tried and refuted behind it. The body's
/// binding (`b2`) and a ground query (`b(true)`, `b(false)`) alike. FAILS under [V]; passes
/// under [L] by design (the waiting check proposes nothing either).
#[test]
fn a_bound_bool_selects_its_one_clause() {
    let mut kb = load_kb_with(BOOLS);
    for q in ["t5tk6b.b2(?x)", "t5tk6b.b(true)", "t5tk6b.b(false)"] {
        let (one, first) = search(&mut kb, q, 1);
        let (all, drained) = search(&mut kb, q, 0);
        assert_eq!((one, all), (1, 1), "{q}");
        assert_eq!(
            first.goals_asked, drained.goals_asked,
            "{q}: goals asked after the answer ({first:?} / {drained:?})"
        );
    }
    assert_eq!(definite_unary(&mut kb, "t5tk6b.b2").len(), 1);
}

/// ROW 3: a `List[T = Bool]` spine with free cells FILLS them — two cells, four lists, each
/// definite — and tiny-sat whose formula waits for its cells answers its two models.
#[test]
fn a_spine_of_free_bool_cells_fills() {
    let mut kb = load_kb_with(BOOLS);
    let mut cells = rendered(&mut kb, "t5tk6b.cells");
    cells.sort();
    assert_eq!(
        cells,
        [
            ("[false, false]".to_string(), true),
            ("[false, true]".to_string(), true),
            ("[true, false]".to_string(), true),
            ("[true, true]".to_string(), true),
        ],
    );
    let mut models = rendered(&mut kb, "t5tk6b.model");
    models.sort();
    assert_eq!(
        models,
        [("[false, false, true]".to_string(), true), ("[true, true, false]".to_string(), true)],
        "(p or not q) and (q or r) and (not p or not r) has the two models t t f and f f t"
    );
}

/// THE CONTROL for row 3: tiny-sat written as the example writes it, over `Bool`, answers its
/// two models with the waiting check too — its `neg` facts bind every cell before the fill.
/// Passes under [L] by design: it is why the row above writes the formula as waiting tests.
#[test]
fn tiny_sat_over_facts_answers_its_two_models() {
    let mut kb = load_kb_with(BOOLS);
    let mut models = rendered(&mut kb, "t5tk6b.factModel");
    models.sort();
    assert_eq!(
        models,
        [("[false, false, true]".to_string(), true), ("[true, true, false]".to_string(), true)],
    );
}

/// A `Bool` INSIDE a typed value is filled the same way: an entity's field, an option's
/// element.
#[test]
fn a_bool_inside_a_value_enumerates() {
    let mut kb = load_kb_with(BOOLS);
    assert_eq!(definite_unary(&mut kb, "t5tk6b.flags").len(), 2, "Flag(true), Flag(false)");
    assert_eq!(definite_unary(&mut kb, "t5tk6b.opts").len(), 3, "none, some(true), some(false)");
}

/// THE RIGID CASE — the reason `<Sort>.domain` is superseded: inside `countAt[X]` the `X` is a
/// name, and the dictionary the caller hands is the only thing that knows its domain.
/// `countAt[X = Bool]` counts `Bool`'s two values through it, and `Wrap[T = Bool]` two wraps.
#[test]
fn a_rigid_type_variable_at_bool_counts_two() {
    assert_eq!(drive("bools"), Ok(2));
    assert_eq!(drive("wrapped"), Ok(2));
}

/// ROW 4: `Int64` and `String` are INFINITE and keep the waiting check — one row, undecided.
/// Passes under every axis, by design: the line the change must not cross.
#[test]
fn infinite_primitives_keep_the_waiting_check() {
    let mut kb = load_kb_with(BOOLS);
    for qn in ["t5tk6b.ints", "t5tk6b.strs"] {
        let answers = query_unary(&mut kb, qn);
        assert_eq!(answers.len(), 1, "{qn}");
        assert!(!answers[0].1, "{qn}: the one row waits on its check");
    }
}

/// `Bool.domain` NAMES NOTHING: a goal of it and a citation of it are refused at load. Its
/// control, `Int64.domain` — an infinite primitive keeps its face until WT8WG retires the
/// faces — still loads.
#[test]
fn bool_has_no_value_face() {
    let goal = load_errors_of(
        "namespace t5tk6b.face\n\
         \x20 import anthill.prelude.{Bool}\n\
         \x20 rule viaFace(?x) :- anthill.prelude.Bool.domain(?x)\n\
         end\n",
    );
    assert_refused_naming(
        &goal,
        &["anthill.prelude.Bool.domain", "names nothing"],
        "a goal of `Bool.domain` names nothing",
    );
    let citation = load_errors_of(
        "namespace t5tk6b.cite\n\
         \x20 import anthill.prelude.{Bool, Int64, Error}\n\
         \x20 operation n() -> Int64 effects Error = Bool.domain.takeN(5).length()\n\
         end\n",
    );
    assert_refused_naming(
        &citation,
        &["Bool.domain.takeN"],
        "a citation of `Bool.domain` names nothing",
    );
    let control = load_errors_of(
        "namespace t5tk6b.intface\n\
         \x20 import anthill.prelude.{Int64}\n\
         \x20 rule viaFace(?x) :- anthill.prelude.Int64.domain(?x)\n\
         end\n",
    );
    assert!(control.is_empty(), "`Int64.domain` keeps its face: {control:#?}");
}
