//! WI-930 — a DECLARATION RECORD is held to its declared fields like any other fact
//! (kernel-language.md §6.3, *A `Symbol` slot of a clause holds a NAME*).
//!
//! WI-928 made the loader's records reachable from the fact check and skipped them
//! there (`is_metadata_functor`): every record naming a constructor was refused. A
//! `Symbol` is stored as the `Ref` of what it names, and since WI-20260902-JB6RS a
//! constructor's name is the same term as its nullary instance, so `SortInfo(name:
//! Duration)` read as an instance of `Duration` in a `Symbol` slot. MEASURED on
//! d3438cf4, stdlib + the Rust host bindings, skip removed:
//!
//! ```text
//! 270 MemberInfo.name   266 EntityInfo.name   131 SortInfo.constructors (as "SortInfo.head")
//!  79 SortInfo.name      10 DescriptionInfo.target                        = 756
//! ```
//!
//! (the `Term` classes the ticket listed were gone already: WI-946). With the rule a
//! `Symbol` slot reads a `Ref` by, 6 were left: `MemberInfo` / `EntityInfo` named the
//! three reflect collection forms by `TupleLiteral()` — their EMPTY LITERAL, which the
//! nullary canon keeps apart from the name — where `SortInfo.name` writes `Ref`.
//!
//! The rule is a clause's (`typing::reflect_slot_admits`): a fact's field, a rule head,
//! a goal of a rule's own term, a construction inside any of them. An operation body
//! evaluates `red` to the instance, and is held to the value's type.
//!
//! BACK-OUT LEDGER, measured on a selected run of this file, `wi928_…` and the recipe
//! guard (each part alone, and the two pairs a part needs to leave the stdlib loading):
//!   * B1, the rule in the fact check (`check_value_against_type`) → EVERY row fails: the
//!     stdlib's own load is refused, 756 reports (wi928's `control_the_stdlib_loads_clean`
//!     names them). B1+B2 → `a_symbol_field_holds_a_constructor_name`, the `List` and
//!     `Option` arms of `a_symbol_slot_of_a_clause_holds_a_name_wherever_it_is_written`,
//!     and B2's row.
//!   * B2, the skip restored (the reflect / realization prefixes in
//!     `checkable_field_types`) → `a_handwritten_declaration_record_is_held_to_its_fields`.
//!   * B3, the record writers back on `make_name_term_from_sym` → EVERY row fails: the
//!     stdlib's load is refused, 6 reports. B2+B3 →
//!     `the_reflect_forms_records_name_them_by_their_name`, and B2's row.
//!   * B4, `describe`'s writer back on `name_to_sort_term` → `describing_a_reflect_form_
//!     names_it` (its load is refused).
//!   * B5, the clause walk's arguments back on the `Term` conversion alone
//!     (`constrain_arg`, `argument_fits_field`, `constrain_occurrence_at`) → every arm of
//!     `a_symbol_slot_of_a_clause_…`.
//!   * B6, the field tested before it is walked through the clause's bindings → its
//!     `List` and `Option` arms.
//!   * B7, a rule's own term typed without the rule (`clause_slot_admits`) → its goal arm.
//!   * B8, value heads skipped whole again (`check_entity_fact`) →
//!     `a_value_headed_fact_is_held_to_its_term_fields`.
//!   * B10, `OperationInfo.requires` / `ensures` declared `List[NodeOccurrence]` again
//!     (reflect.anthill, and the bridge's carrier) →
//!     `an_operation_contract_of_a_construction_is_recorded`; found by the first full
//!     gate (`kb_operations_surfaces_requires_ensures_and_meta`), not by the stdlib.
//!   * the `control_…` rows pass under every part that leaves the stdlib loading — B2,
//!     B4–B8, B10, B1+B2, B2+B3 — by design: a literal, a construction, the empty literal, a
//!     const, an operation body's and a fragment's instance are refused in a `Symbol` slot
//!     with the rule and without it, and a well-typed record loads with the skip and
//!     without it. The const one also passes with `reflect_slot_admits` admitting a
//!     const's `Ref` (measured): the loader folds a const before any slot reads it, so
//!     the predicate does not exclude one.

use crate::common::{load_errors_of, load_kb_with, load_stdlib_kb_untyped, query_unary};
use anthill_core::eval::Value;
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::typing::{type_check_sorts_typed, TypeError, TypeErrorContext};
use anthill_core::kb::{ClauseKind, KnowledgeBase};

const HOLDER: &str = "
namespace test.wi930
  import anthill.prelude.{Int64, List, Option}
  import anthill.prelude.Option.{some}
  import anthill.reflect.{Symbol, MemberInfo}

  sort Colour
    entity red
    entity rgb(r: Int64)
  end

  entity Holder(s: Symbol)
  entity L(xs: List[T = Symbol])
  entity O(x: Option[T = Symbol])
  entity Outer(h: Holder)
  fact r(1)
  const k: Int64 = 3
";

fn holder(rest: &str) -> String {
    format!("{HOLDER}\n{rest}\nend\n")
}

/// The qualified name each definite answer of `qn(?r)` denotes.
fn names(kb: &mut KnowledgeBase, qn: &str) -> Vec<String> {
    query_unary(kb, qn)
        .into_iter()
        .map(|(v, definite)| {
            assert!(definite, "`{qn}`: an indefinite answer {v:?}");
            let id = match v {
                Value::Term { id, .. } => id,
                other => panic!("`{qn}`: expected a term, got {other:?}"),
            };
            match kb.get_term(id) {
                Term::Ref(s) => kb.qualified_name_of(*s).to_owned(),
                other => panic!("`{qn}`: expected a name, got {other:?}"),
            }
        })
        .collect()
}

/// The `field` of every fact of the reflect record `record`, as stored.
fn slot_in(kb: &KnowledgeBase, record: &str, field: &str) -> Vec<Term> {
    let functor = kb.try_resolve_symbol(record).expect("reflect is loaded");
    kb.rules_by_functor(functor)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .filter_map(|rid| kb.fact_head_named_args(rid))
        .filter_map(|named| {
            named
                .iter()
                .find(|(f, _)| kb.local_name_of(*f) == field)
                .map(|(_, v)| kb.get_term(*v).clone())
        })
        .collect()
}

/// The stored spellings of `form` among `terms` — a `Ref` or an application of it.
fn spellings_of(kb: &KnowledgeBase, terms: Vec<Term>, form: &str) -> Vec<Term> {
    let form = kb
        .try_resolve_symbol(&format!("anthill.reflect.{form}"))
        .expect("the form resolves");
    terms
        .into_iter()
        .filter(|t| match t {
            Term::Ref(s) => *s == form,
            Term::Fn { functor, .. } => *functor == form,
            _ => false,
        })
        .collect()
}

/// Asserts `errs` holds a refusal of `Holder.s` naming `got`.
fn assert_refused(errs: &[String], got: &str) {
    assert!(
        errs.iter()
            .any(|e| e.contains("type mismatch in Holder.s") && e.contains(&format!("got {got}"))),
        "expected `Holder.s` refused as {got}: {errs:#?}"
    );
}

const RED: &str = "test.wi930.Colour.red";

// ── The subject ─────────────────────────────────────────────────────────────

/// A constructor's name in a `Symbol` slot is the name: the fact loads, and the term it
/// stores is the one the loader's own records name the constructor by — the join with
/// `MemberInfo` answers. Refused before (`expected Symbol, got Colour`).
#[test]
fn a_symbol_field_holds_a_constructor_name() {
    let mut kb = load_kb_with(&holder(
        "  fact Holder(s: red)\n  rule held_kind(?k) :- Holder(s: ?n), MemberInfo(name: ?n, kind: ?k, parent: ?)",
    ));
    assert_eq!(
        names(&mut kb, "test.wi930.held_kind"),
        ["anthill.reflect.MemberKind.Constructor"],
    );
}

/// Every place a clause writes a `Symbol` slot takes the name, and each answers it: a
/// rule head, a goal of the rule's own term, a field of a construction nested in a fact,
/// and a list's or an option's element, whose field is the `T` its position binds.
#[test]
fn a_symbol_slot_of_a_clause_holds_a_name_wherever_it_is_written() {
    let arms = [
        ("rule head", "  rule Holder(s: red) :- r(1)\n  rule got(?n) :- Holder(s: ?n)"),
        (
            "goal",
            "  rule got(?k) :- MemberInfo(name: red, kind: ?k, parent: ?)",
        ),
        (
            "nested construction",
            "  fact Outer(h: Holder(s: red))\n  rule got(?n) :- Outer(h: Holder(s: ?n))",
        ),
        ("List", "  fact L(xs: [red])\n  rule got(?n) :- L(xs: [?n])"),
        ("Option", "  fact O(x: red)\n  rule got(?n) :- O(x: some(?n))"),
    ];
    // Every arm's verdict, so a back-out names each arm it breaks.
    let mut failed: Vec<String> = Vec::new();
    for (arm, rest) in arms {
        let errs = load_errors_of(&holder(rest));
        if !errs.is_empty() {
            failed.push(format!("[{arm}] refused: {errs:?}"));
            continue;
        }
        let mut kb = load_kb_with(&holder(rest));
        let want = if arm == "goal" {
            "anthill.reflect.MemberKind.Constructor"
        } else {
            RED
        };
        let got = names(&mut kb, "test.wi930.got");
        if got != [want] {
            failed.push(format!("[{arm}] answers {got:?}"));
        }
    }
    assert!(failed.is_empty(), "{failed:#?}");
}

/// The loader's records are no longer skipped, so one written by hand is held to its
/// declared fields: a `String` where `EntityInfo.name: Symbol` is declared, and an
/// `Int64` where `Implementation.language: String` is. Both loaded under the skip.
#[test]
fn a_handwritten_declaration_record_is_held_to_its_fields() {
    let errs = load_errors_of(
        "
namespace test.wi930r
  import anthill.reflect.{EntityInfo}
  fact EntityInfo(name: \"Thing\", fields: [])
end
",
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("type mismatch in EntityInfo.name") && e.contains("got String")),
        "the record's name slot is checked: {errs:#?}"
    );

    let errs = load_errors_of(
        "
namespace test.wi930i
  import anthill.prelude.Option.{none}
  import anthill.realization.{Implementation}
  fact Implementation(target: \"t\", artifact: \"a\", language: 7, profile: none,
                      description: none, carrier: [], namespace_map: [], binding: none)
end
",
    );
    assert!(
        errs.iter().any(|e| e.contains("type mismatch in Implementation.language")
            && e.contains("got Int64")),
        "a realization record is checked too: {errs:#?}"
    );
}

/// A fact whose head carries a value — the shape of `OperationParamDefault`, whose
/// `default` is an occurrence — is checked at the fields it holds as terms; the whole
/// fact was skipped. Asserted by hand between the load and its typer: no source writes a
/// value head with a wrong term field, the loader's own being right.
#[test]
fn a_value_headed_fact_is_held_to_its_term_fields() {
    let (mut kb, result) =
        load_stdlib_kb_untyped(&holder("  entity Pair2(s: Symbol, n: Int64)"));
    let pair2 = kb.try_resolve_symbol("test.wi930.Pair2").expect("Pair2");
    let domain = kb.try_resolve_symbol("test.wi930").expect("namespace");
    let (s, n) = (kb.intern("s"), kb.intern("n"));
    let not_a_name = kb.alloc(Term::Const(Literal::String("x".into())));
    let head = Value::Entity {
        functor: pair2,
        pos: Vec::new().into(),
        // `n` on a value: what makes the head a value head.
        named: vec![(s, Value::term(not_a_name)), (n, Value::Int(3))].into(),
    };
    kb.assert_fact_value(head, ClauseKind::Fact, domain, None);
    let errs = type_check_sorts_typed(&mut kb, result.loaded());
    let refused: Vec<(String, String, String)> = errs
        .iter()
        .filter_map(|e| match e {
            TypeError::Other {
                context: TypeErrorContext::EntityField { entity, field },
                actual,
                ..
            } => Some((
                kb.local_name_of(*entity).to_owned(),
                kb.local_name_of(*field).to_owned(),
                actual.clone(),
            )),
            _ => None,
        })
        .collect();
    assert_eq!(
        refused,
        [("Pair2".to_owned(), "s".to_owned(), "String".to_owned())],
        "the term-carried field is checked: {errs:?}"
    );
}

/// `MemberInfo` and `EntityInfo` hold the three reflect collection forms' NAME, the `Ref`
/// `SortInfo.name` holds. Each held `TupleLiteral()` — the empty literal, the term `fact
/// H(s: ())` writes — which a `Symbol` slot refuses
/// (`control_a_symbol_field_refuses_the_empty_literal`).
///
/// Asked of the stored term, because that is what the check reads: a GOAL does not tell
/// the two apart. Measured, on both sides of the writers: `MemberInfo(name: (), kind: ?k,
/// parent: ?p)` and `MemberInfo(name: TupleLiteral, …)` each answer the one row.
#[test]
fn the_reflect_forms_records_name_them_by_their_name() {
    let kb = load_kb_with("namespace test.wi930f\nend\n");
    for form in ["TupleLiteral", "ListLiteral", "SetLiteral"] {
        let want = kb
            .try_resolve_symbol(&format!("anthill.reflect.{form}"))
            .expect("the form resolves");
        for record in ["anthill.reflect.MemberInfo", "anthill.reflect.EntityInfo"] {
            assert_eq!(
                spellings_of(&kb, slot_in(&kb, record, "name"), form),
                [Term::Ref(want)],
                "{form}: its {record} row names it by its name"
            );
        }
    }
}

/// `describe` writes its target by name too: a description of a reflect form loads, and
/// its `DescriptionInfo` names the form. It wrote the empty literal, which the check then
/// refused at reflect's `entity DescriptionInfo`.
#[test]
fn describing_a_reflect_form_names_it() {
    let kb = load_kb_with(
        "
namespace test.wi930d
  import anthill.reflect.{TupleLiteral}
  describe TupleLiteral {< the empty tuple's form >}
end
",
    );
    let want = kb
        .try_resolve_symbol("anthill.reflect.TupleLiteral")
        .expect("the form resolves");
    assert_eq!(
        spellings_of(
            &kb,
            slot_in(&kb, "anthill.reflect.DescriptionInfo", "target"),
            "TupleLiteral"
        ),
        [Term::Ref(want)],
    );
}

/// An operation's contract is recorded as its goals, each a quoted `Term` (proposal 048
/// §F), so a goal that is a construction loads and its record answers.
/// `OperationInfo.requires` / `ensures` were declared `List[NodeOccurrence]`, and once the
/// record was checked `requires Full(t)` was refused: `Full(t)` read as an instance of
/// `Tank`. The standard library writes no such contract, so its load did not show it.
#[test]
fn an_operation_contract_of_a_construction_is_recorded() {
    let mut kb = load_kb_with(
        "
namespace test.wi930c
  import anthill.prelude.Int64
  import anthill.prelude.List.{cons}
  import anthill.reflect.{OperationInfo}
  sort Tank
    entity tank(fuel: Int64)
    entity Full(t: Tank)
    operation fill(t: Tank) -> Tank requires Full(t) ensures Full(t) = t
  end
  rule contracted(?n)
    :- OperationInfo(name: ?n, requires: cons(head: ?, tail: ?), ensures: cons(head: ?, tail: ?))
end
",
    );
    let got = names(&mut kb, "test.wi930c.contracted");
    assert!(got.iter().any(|n| n == "test.wi930c.Tank.fill"), "{got:?}");
}

// ── Controls: what must NOT have changed ────────────────────────────────────

/// CONTROL — a literal is no name: refused in a `Symbol` slot with the rule and without
/// it, in a fact and in a rule body. `Symbol` is not a top type.
#[test]
fn control_a_symbol_field_refuses_a_literal() {
    assert_refused(&load_errors_of(&holder("  fact Holder(s: \"red\")")), "String");
    assert_refused(
        &load_errors_of(&holder("  rule q(?x) :- Holder(s: \"red\"), r(?x)")),
        "String",
    );
}

/// CONTROL — a construction is no name either: refused with the rule and without it.
#[test]
fn control_a_symbol_field_refuses_a_construction() {
    assert_refused(&load_errors_of(&holder("  fact Holder(s: rgb(r: 1))")), "Colour");
    assert_refused(
        &load_errors_of(&holder("  rule q(?x) :- Holder(s: rgb(r: 1)), r(?x)")),
        "Colour",
    );
}

/// CONTROL — the empty literal is no name: refused with the rule and without it. It is
/// the term the three reflect forms' records held.
#[test]
fn control_a_symbol_field_refuses_the_empty_literal() {
    assert_refused(&load_errors_of(&holder("  fact Holder(s: ())")), "TupleLiteral");
}

/// CONTROL — a const reads as its value (§4.4), in a fact and in a rule body, and its
/// value is no name.
#[test]
fn control_a_const_reads_as_its_value() {
    assert_refused(&load_errors_of(&holder("  fact Holder(s: k)")), "Int64");
    assert_refused(
        &load_errors_of(&holder("  rule q(?x) :- Holder(s: k), r(?x)")),
        "Int64",
    );
}

/// CONTROL — text written as an operation body evaluates `red` to the instance of
/// `Colour`, which is no `Symbol`: an operation's body and a `let` under a rule's goal are
/// refused, with the rule and without it.
#[test]
fn control_an_operation_body_evaluates_the_name() {
    assert_refused(
        &load_errors_of(&holder("  operation mk() -> Holder = Holder(s: red)")),
        "Colour",
    );
    assert_refused(
        &load_errors_of(&holder(
            "  rule fr(?r) :- ?r <=> (let h = Holder(s: red)  h)",
        )),
        "Colour",
    );
}

/// CONTROL — a well-typed record written by hand loads, with the skip and without it,
/// and answers as the loader's own do.
#[test]
fn control_a_welltyped_declaration_record_loads() {
    let mut kb = load_kb_with(
        "
namespace test.wi930w
  import anthill.reflect.{DescriptionInfo}
  entity Thing
  fact DescriptionInfo(target: Thing, content: \"by hand\", index: 7)
  rule described(?t) :- DescriptionInfo(target: ?t, content: \"by hand\", index: 7)
end
",
    );
    assert_eq!(names(&mut kb, "test.wi930w.described"), ["test.wi930w.Thing"]);
}
