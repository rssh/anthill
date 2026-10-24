//! WI-20261022-DRGCP — A REFUSED PRECONDITION IS QUOTED AS THE GOAL IT IS, ON EVERY
//! CARRIER.
//!
//! A call decides a precondition's type-level variable from the argument's declared type
//! (WI-9PGCM), and where that type rides an occurrence — a type alias's node, `sort Dirty =
//! Untrusted`, or every sort under `ANTHILL_TEST_NODE_CARRIER=1` — the judged goal is no
//! hash-consed term: an entity a substitution rebuilt, holding the occurrence. The verdict
//! was right on every carrier; the QUOTE was not. The renderer printed a goal that was a term
//! by the term printer and any other by the TYPE renderer, which spells a type context:
//! `flows_to(Untrusted, Public)` for `flows_to(Untrusted[], Public[])` — in a data slot the
//! bare name is the INSTANCE (kernel-language.md §4.4) — `edge[from = …]` for `edge(from:
//! …)`, an arrow without its row; and the pass that rewrote the goal in source spelling read
//! a term only, so a parameter the call left symbolic read `var_ref[name = k]`.
//!
//! The printer now reads every carrier through the view (`persistence::print::PrintView`),
//! so a goal prints one text whatever holds it, and quotes its author's spelling itself
//! (`TermPrinter::quoting_source`). Where it can, a row below takes the quote and writes it as
//! the fact the refusal asks for: the quote is right when that fact discharges the obligation.
//!
//! BACKED OUT, each part alone (measured; the first and the type forms also under
//! `ANTHILL_TEST_NODE_CARRIER=1`). Parts in `persistence/print.rs` unless named.
//!  * `format_precondition_clause` choosing its printer by carrier again (a term by the term
//!    printer, any other by the type renderer): FAIL
//!    `the_quoted_goal_is_the_fact_that_discharges_it`,
//!    `a_named_argument_goal_keeps_its_parentheses`,
//!    `a_parameter_the_call_left_symbolic_is_named_as_written`,
//!    `a_list_in_a_goal_is_written_as_its_literal`, `an_arrow_label_is_written_as_a_type`;
//!    under the switch also the six that found this ticket —
//!    `wi4gbqv_ambient_resource_test::an_entity_in_an_ordinary_type_slot_is_still_a_type`,
//!    `wi9pgcm_type_level_precondition_test::{untrusted_label_into_public_only_sink_is_refused,
//!    existential_witness_does_not_discharge_the_obligation,
//!    a_declared_wrapper_gates_its_own_callers, mixed_conjunct_decided_and_unprovable_is_refused,
//!    mixed_conjunct_declared_discharges_and_still_gates}`.
//!  * the quote printed without `TermPrinter::quoting_source`: FAIL both parameter rows here,
//!    `value_holding_type_readers_test::a_wrapper_is_told_to_declare_a_precondition_at_a_type_holding_a_value`
//!    and five of `wi9pgcm_type_level_precondition_test` —
//!    `rigid_label_obligation_is_decided_and_refused`,
//!    `the_wrapper_no_longer_swallows_the_obligation`,
//!    `the_obligation_propagates_through_two_wrappers`,
//!    `mixed_conjunct_over_a_rigid_label_is_decided_whole`,
//!    `a_guard_still_gates_an_undeclared_wrapper`.
//!  * the source name (`source_name`) taken out of the data walk: FAIL
//!    `a_parameter_the_call_left_symbolic_is_named_as_written` and wi9pgcm's
//!    `a_guard_still_gates_an_undeclared_wrapper`, `mixed_conjunct_over_a_rigid_label_is_decided_whole`;
//!    out of the type walk: FAIL `a_parameter_in_a_type_binding_is_named_as_written`.
//!  * a skolem quoted `!m` (`write_var`): FAIL the value-holding wrapper row and the five wi9pgcm
//!    wrapper rows above.
//!  * the type forms taken out of the data walk (`is_type_form`): FAIL
//!    `an_arrow_label_is_written_as_a_type` and fifteen rows of the type-printing suites the term
//!    printer already had (`wi173_type_print_test` ×10, `wi790` ×2, `wi791`, `wi_tcsgt` ×2) —
//!    its behavior, now on every carrier.
//!  * a bare empty row written by its name: FAIL `a_bare_empty_row_is_written_as_the_row`.
//!  * the parse side's written bracket ignored (`written_bracket`): FAIL
//!    `a_persisted_constructor_type_is_found_by_its_retract_key`.
//!  * a bare type value written without its face's bracket: FAIL
//!    `wi_jb6rs_type_face_test::a_bracket_in_a_rules_compound_expression_is_the_type`; a type
//!    value's binding written as data: FAIL the CLI's
//!    `wi_drgcp_query_answer_spelling_test::a_type_value_answers_as_its_fact_twin`.
//!  * an expression occurrence read through the view rather than its own writer
//!    (`own_spelling`): FAIL the CLI's `an_answer_holding_an_expression_is_written_as_its_source`.
//!  * an opaque value not named by its kind: FAIL
//!    `persistence::print::tests::an_opaque_value_in_a_value_is_named_by_its_kind`.
//!  * the CLI's renderer back to its per-carrier match: FAIL the CLI's
//!    `an_answer_rebuilt_over_a_type_is_written_as_the_type` and
//!    `wi_7fp1m_query_type_names_test::wi7fp1m_direct_query_matches_wrapper_enumeration`.
//!  * `term_to_string` lowering its argument again (`eval/builtins.rs`): FAIL
//!    `term_to_string_prints_an_entity_without_interning`.
//!
//! FAIL NONE, and say so at their sites: the arm for a parameterized type whose base is an
//! occurrence (no row builds the shape), and `print_rule` writing a head that is no term or
//! occurrence by `print_value` rather than a placeholder (a bodied rule's head is never one).
//!
//! PASS EITHER WAY, by design: `a_type_application_in_a_goal_is_written_as_a_type` (the type
//! renderer writes a type application as the data spelling does), and the instance-spelled
//! fact in the first row, which refuses either way — the control that the spelling decides the
//! verdict, which is why the quote must carry it.

use crate::common::load_errors_of;

/// The label lattice, with `Untrusted` reached through an alias so the label rides an
/// occurrence without the node-carrier switch. Each relation a `requires` names holds at
/// `Public` alone; `{facts}` adds clauses, `{calls}` the calls whose preconditions are
/// judged.
fn program(facts: &str, calls: &str) -> String {
    format!(
        r#"
enum test.drgcp.Level
  entity Untrusted
  entity Public
end

enum test.drgcp.Text
  import anthill.prelude.{{String}}
  sort L = ?
  entity mk(raw: String)
end

sort test.drgcp.Box
  sort V = ?
end

namespace test.drgcp
  import anthill.prelude.{{Unit, Int64, Cell, Modify, todo}}
  import test.drgcp.Level.{{Untrusted, Public}}
  import test.drgcp.Text
  import test.drgcp.Box

  sort Dirty = Untrusted

  fact flows_to(Public[], Public[])
  fact edge(from: Public[], to: Public[])
  fact allowed(Public[], 1)
  fact holds(Box[V = Public])
  fact gated(Public[])
  fact among([Public[]])
  fact held_at(Box[V = Int64])
{facts}
  operation fetch() -> Text[L = Dirty] = todo()

  operation send(body: Text[L = ?l]) -> Unit
    requires flows_to(?l, Public[])
    = ()
  operation sink(body: Text[L = ?l]) -> Unit
    requires edge(from: ?l, to: Public[])
    = ()
  operation gate(body: Text[L = ?l], n: Int64) -> Unit
    requires allowed(?l, n)
    = ()
  operation hold(body: Text[L = ?l]) -> Unit
    requires holds(Box[V = ?l])
    = ()
  operation wire(body: Text[L = ?l]) -> Unit
    requires gated(?l)
    = ()
  operation among_of(body: Text[L = ?l]) -> Unit
    requires among([?l, Public[]])
    = ()
  operation need(n: Int64) -> Unit
    requires held_at(Box[V = n])
    = ()

{calls}
end
"#
    )
}

/// The goal the one refusal of `calls` quotes, as written between its backticks.
fn quoted_goal(calls: &str) -> String {
    let errs = load_errors_of(&program("", calls));
    assert_eq!(errs.len(), 1, "one refusal: {errs:#?}");
    let err = &errs[0];
    assert!(err.contains("unsatisfied precondition"), "{err}");
    let quote = err
        .split("precondition `")
        .nth(1)
        .and_then(|rest| rest.split('`').next())
        .unwrap_or_else(|| panic!("a quoted goal: {err}"));
    quote.to_owned()
}

/// The load's errors once `goal` is written as a fact.
fn discharged_by(goal: &str, calls: &str) -> Vec<String> {
    load_errors_of(&program(&format!("  fact {goal}"), calls))
}

#[test]
fn the_quoted_goal_is_the_fact_that_discharges_it() {
    let calls = "  operation leak() -> Unit = send(fetch())";
    let goal = quoted_goal(calls);
    assert_eq!(goal, "flows_to(Untrusted[], Public[])");
    let errs = discharged_by(&goal, calls);
    assert!(errs.is_empty(), "the quoted goal, as a fact, discharges it: {errs:#?}");
    // CONTROL: the instance's spelling, which the type renderer quoted, discharges nothing.
    let errs = discharged_by("flows_to(Untrusted, Public)", calls);
    assert!(
        errs.iter().any(|e| e.contains("unsatisfied precondition")),
        "a fact over the instances is not the obligation: {errs:#?}"
    );
}

#[test]
fn a_named_argument_goal_keeps_its_parentheses() {
    let calls = "  operation leak() -> Unit = sink(fetch())";
    let goal = quoted_goal(calls);
    assert_eq!(goal, "edge(from: Untrusted[], to: Public[])");
    let errs = discharged_by(&goal, calls);
    assert!(errs.is_empty(), "the quoted goal, as a fact, discharges it: {errs:#?}");
}

#[test]
fn a_parameter_the_call_left_symbolic_is_named_as_written() {
    let calls = "  operation leak(k: Int64) -> Unit = gate(fetch(), k)";
    let goal = quoted_goal(calls);
    assert_eq!(goal, "allowed(Untrusted[], k)");
}

#[test]
fn a_type_application_in_a_goal_is_written_as_a_type() {
    let calls = "  operation leak() -> Unit = hold(fetch())";
    let goal = quoted_goal(calls);
    assert_eq!(goal, "holds(Box[V = Untrusted])");
    let errs = discharged_by(&goal, calls);
    assert!(errs.is_empty(), "the quoted goal, as a fact, discharges it: {errs:#?}");
}

/// A list in a goal is written as its literal, the spelling its term twin prints — not as
/// the `cons` cells a substitution rebuilt it into.
#[test]
fn a_list_in_a_goal_is_written_as_its_literal() {
    let calls = "  operation leak() -> Unit = among_of(fetch())";
    let goal = quoted_goal(calls);
    assert_eq!(goal, "among([Untrusted[], Public[]])");
    let errs = discharged_by(&goal, calls);
    assert!(errs.is_empty(), "the quoted goal, as a fact, discharges it: {errs:#?}");
}

/// A label that is a type form of its own — an arrow, whose row names a place and so rides
/// an occurrence — is written as the type its term twin prints, its row included. (Not
/// written back as a fact: a fact cannot name the place, and an arrow written as data in a
/// fact does not meet the arrow type even where the label is a term — measured, apart from
/// this ticket.)
#[test]
fn an_arrow_label_is_written_as_a_type() {
    let calls = "  operation relay(c: Cell[V = Int64], t: Text[L = (x: Int64) -> Unit @ Modify[c]]) \
                 -> Unit =\n    wire(t)";
    let goal = quoted_goal(calls);
    assert_eq!(goal, "gated((Int64) -> Unit @ Modify[T = c])");
}

/// A parameter the call left symbolic is named as written inside a type's binding as well:
/// the quote's source spelling is the printer's, in its type walk as in its data walk.
#[test]
fn a_parameter_in_a_type_binding_is_named_as_written() {
    let calls = "  operation go(k: Int64) -> Unit = need(k)";
    assert_eq!(quoted_goal(calls), "held_at(Box[V = k])");
}

/// The file store keys a fact by its print: of the text on disk, parsed, and of the loaded
/// fact. A fact holding a constructor's TYPE prints `held_type(Untrusted[])` from the
/// knowledge base, its type face; the parse side must print the bracket it read, or the
/// retract misses and the fact stays on disk in silence.
#[test]
fn a_persisted_constructor_type_is_found_by_its_retract_key() {
    use anthill_core::kb::term::Term;
    use anthill_core::kb::{ClauseKind, KnowledgeBase};
    use anthill_core::persistence::file_store::{FileConvention, FileStore};
    use anthill_core::persistence::Store;

    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let mut kb = crate::common::load_kb_with(&program("", ""));
    let untrusted = kb.resolve_symbol("test.drgcp.Level.Untrusted");
    let face = kb.type_context_face(untrusted);
    let arg = kb.alloc(Term::Ref(face));
    let domain = kb.intern("drgcp");
    let mut fact = |kb: &mut KnowledgeBase, name: &str| {
        let f = kb.intern(name);
        let head = kb.alloc(Term::Fn {
            functor: f,
            pos_args: smallvec::SmallVec::from_elem(arg, 1),
            named_args: smallvec::SmallVec::new(),
        });
        (head, kb.assert_fact(head, ClauseKind::Fact, domain, None))
    };
    let (held, held_id) = fact(&mut kb, "held_type");
    let (kept, _) = fact(&mut kb, "kept_type");
    for h in [held, kept] {
        store.persist(&kb, h, ClauseKind::Fact, domain, None).unwrap();
    }
    store.flush(&kb).unwrap();
    let path = dir.path().join("facts.anthill");
    assert!(std::fs::read_to_string(&path).unwrap().contains("held_type(Untrusted[])"));

    assert!(store.retract(&kb, held_id).unwrap(), "retract is buffered");
    kb.retract(held_id);
    store.flush(&kb).unwrap();
    let after = std::fs::read_to_string(&path).unwrap();
    assert!(!after.contains("held_type"), "the retracted fact is found by its key: {after}");
    assert!(after.contains("kept_type(Untrusted[])"), "the other stays: {after}");
}

/// An empty effect row standing alone is written `{}`, as its occurrence was before the
/// printer read it through the view, where it heads as the bare name `empty_row`.
#[test]
fn a_bare_empty_row_is_written_as_the_row() {
    use anthill_core::kb::node_occurrence::{EffectExprNode, NodeOccurrence};
    use anthill_core::persistence::print::TermPrinter;
    use anthill_core::span::{SourceId, SourceSpan};
    let kb = crate::common::load_stdlib_kb();
    let span = SourceSpan::new(SourceId::from_raw(0), 0, 0);
    let occ = NodeOccurrence::new_effect_expr(EffectExprNode::EmptyRow, span, None);
    assert_eq!(TermPrinter::new(&kb).print_occurrence(&occ), "{}");
}

/// `term_to_string` prints a value a program built — an entity — through the view, and
/// interns nothing for it. It lowered the entity into the hash-consed store for want of a
/// printer that read one: a tree a printed row on anthill-todo's path, which
/// WI-20260827-W1YKH's growth rule forbids. The call's own growth is measured with a term
/// argument first, which never interned. A carrier with no term reading still raises.
#[test]
fn term_to_string_prints_an_entity_without_interning() {
    use anthill_core::eval::Value;
    let mut interp = crate::common::interp_for(&program("", ""));
    let mk = interp.kb().resolve_symbol("test.drgcp.Text.mk");
    let raw = interp.kb_mut().intern("raw");
    let text = |v: Result<Value, _>| match v {
        Ok(Value::Str(s)) => s,
        other => panic!("expected a String: {other:?}"),
    };

    let one = interp.kb_mut().alloc(anthill_core::kb::term::Term::Const(
        anthill_core::kb::term::Literal::Int(1),
    ));
    let before = interp.kb().term_store_len();
    let printed = text(interp.call("anthill.reflect.term_to_string", &[Value::term(one)]));
    assert_eq!(printed, "1");
    let call_growth = interp.kb().term_store_len() - before;

    let entity = Value::Entity {
        functor: mk,
        pos: vec![].into(),
        named: vec![(raw, Value::Str("fresh-drgcp-text".into()))].into(),
    };
    let before = interp.kb().term_store_len();
    let printed = text(interp.call("anthill.reflect.term_to_string", &[entity]));
    assert_eq!(printed, "mk(raw: \"fresh-drgcp-text\")");
    let grew = interp.kb().term_store_len() - before;
    assert!(
        grew <= call_growth,
        "printing an entity grew the store by {grew} where the call alone grows it by \
         {call_growth}: `term_to_string` is lowering its argument"
    );

    // `Unit` is the tuple of no components, a term (WI-20261011-7G99A); an operation
    // reference has no term reading, and raises.
    let printed = text(interp.call("anthill.reflect.term_to_string", &[Value::Unit]));
    assert_eq!(printed, "()");
    let op_ref = Value::OpRef {
        op_reqs: None,
        spread_labels: None,
        op: mk,
        dict: None,
        named: None,
    };
    let refused = interp.call("anthill.reflect.term_to_string", &[op_ref]);
    assert!(refused.is_err(), "a value with no term reading raises: {refused:?}");
}
