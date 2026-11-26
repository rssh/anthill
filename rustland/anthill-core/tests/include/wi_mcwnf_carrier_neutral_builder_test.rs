//! WI-20261123-MCWNF — THE CARRIER-NEUTRAL BUILDER, from outside the crate.
//!
//! Reading an application is carrier-neutral (`TermView` over a `TermId` and over every
//! `Value`); building one was not: the public constructors take `TermId` children, and the
//! builder over `Value` children, `KnowledgeBase::fn_value` — the one place the
//! `Term`-vs-`Value::Entity` decision is made — was private. A client rebuilding a stored
//! contract clause with values put in (anthill-traces' contract evaluator) could only lower
//! the clause to a term first or write `Value::Entity { .. }` by hand. `fn_value` is now
//! public. It puts a RECORD's named arguments in declared field order, as `make_entity_term`
//! does, and takes every other functor's as given — unlike `make_entity_term`, which
//! re-sorts a functor with no field schema into interning order: that would move a type
//! application's arguments out of the order its sort declares (measured at
//! `KnowledgeBase::order_declared_named_args`).
//!
//! BACK-OUT, measured 2026-11-26 over this file (7 rows, green on the change):
//!  * [P] `fn_value` private again — the file does not compile (every row calls it);
//!  * [C] `fn_value` not ordering (the named arguments taken as given, as before) —
//!    2 fail: `a_records_named_arguments_are_put_in_declared_order` and
//!    `a_record_with_an_occurrence_child_is_put_in_declared_order`;
//!  * [I] `fn_value` ordering as `make_entity_term` does (`canonicalize_record_named_args`,
//!    interning order for a functor with no schema) — 1 fails:
//!    `a_type_applications_arguments_are_taken_as_given`.
//! CONTROL, passing either way by design: `an_ordered_product_keeps_its_order` (exempt
//! before and after), `a_stored_contract_goal_rebuilds_as_itself` (the loader's own goal,
//! already in order), and the two carrier rows, whose applications have no named arguments.

use crate::common::load_kb_with;
use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::{self, NodeOccurrence};
use anthill_core::kb::op_info::WrittenClause;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::term_view::{views_structurally_equal, TermView};
use anthill_core::kb::KnowledgeBase;
use smallvec::{smallvec, SmallVec};
use std::rc::Rc;

const SRC: &str = r#"
namespace test.mcwnf
  import anthill.prelude.{Int64}

  sort Money = Int64
  sort Show[T]
    operation show(x: T) -> Int64
  end
  sort IntShow
    entity intshow
    provides Show[T = Int64]
    operation show(x: Int64) -> Int64 = x + 1
  end

  sort Asks
    operation ask(x: Int64) -> Int64
      requires Show[T = Money], x > 0
  end

  sort Labelled
    entity labelled(zz_first: Int64, value: Int64)
  end

  sort Two[A, B]
  end

  fact triple(1, 2, 3)
end
"#;

fn sym(kb: &KnowledgeBase, name: &str) -> Symbol {
    kb.try_resolve_symbol(name)
        .unwrap_or_else(|| panic!("`{name}` names nothing"))
}

/// The goals of `ask`'s one written `requires` — `Show[T = Money]` and `x > 0` — as stored.
fn ask_goals(kb: &KnowledgeBase) -> Vec<Value> {
    let c = kb
        .operation_contract(sym(kb, "test.mcwnf.Asks.ask"))
        .expect("`ask` has a recorded contract");
    let [clause]: &[WrittenClause; 1] = c.requires[..].try_into().expect("one written clause");
    match &clause.stored {
        Value::Entity { functor, pos, .. } if kb.local_name_of(*functor) == "conjunction" => {
            pos.to_vec()
        }
        other => panic!("a clause over an alias is stored as a conjunction entity: {other:?}"),
    }
}

/// The occurrence `Money` is held on in `Show[T = Money]`: the loader keeps a binding written
/// through a type alias on its own node.
fn money_occurrence(kb: &KnowledgeBase) -> Rc<NodeOccurrence> {
    let goals = ask_goals(kb);
    let Value::Entity { named, .. } = &goals[0] else {
        panic!("the goal over an alias is stored as an application: {:?}", goals[0]);
    };
    let [(_, Value::Node(occ))] = &named[..] else {
        panic!("one binding, on its occurrence: {named:?}");
    };
    Rc::clone(occ)
}

fn int(kb: &mut KnowledgeBase, n: i64) -> TermId {
    kb.alloc(Term::Const(Literal::Int(n)))
}

/// An application whose children are an occurrence, a term and a native literal builds, and
/// reads through the view as its term twin does — the twin built by `make_entity_term` over
/// each child lowered to a term.
#[test]
fn an_application_over_three_carriers_reads_as_its_term_twin() {
    let mut kb = load_kb_with(SRC);
    let occ = money_occurrence(&kb);
    let triple = sym(&kb, "test.mcwnf.triple");
    let two = int(&mut kb, 2);

    let built = kb.fn_value(
        triple,
        vec![Value::Node(Rc::clone(&occ)), Value::term(two), Value::Int(3)],
        Vec::new(),
    );
    assert!(
        matches!(built, Value::Entity { .. }),
        "an occurrence child is no leaf, so the application is an entity: {built:?}"
    );

    let money = node_occurrence::value_to_term(&mut kb, &Value::Node(occ))
        .expect("the binding has a term");
    let three = int(&mut kb, 3);
    let twin = kb.make_entity_term(triple, smallvec![money, two, three], SmallVec::new());
    assert!(views_structurally_equal(&kb, &built, &Value::term(twin)));

    // CONTROL: the view tells a different application apart.
    let four = int(&mut kb, 4);
    let other = kb.make_entity_term(triple, smallvec![money, two, four], SmallVec::new());
    assert!(!views_structurally_equal(&kb, &built, &Value::term(other)));
}

/// Children that are all leaves — a term and native literals — build the hash-consed term
/// itself: the very `TermId` `make_entity_term` gives.
#[test]
fn an_application_over_leaves_is_the_hash_consed_term() {
    let mut kb = load_kb_with(SRC);
    let triple = sym(&kb, "test.mcwnf.triple");
    let one = int(&mut kb, 1);

    let built = kb.fn_value(triple, vec![Value::term(one), Value::Int(2), Value::Int(3)], Vec::new());
    let Value::Term { id, .. } = built else {
        panic!("leaf children build a term: {built:?}");
    };
    let (two, three) = (int(&mut kb, 2), int(&mut kb, 3));
    let twin = kb.make_entity_term(triple, smallvec![one, two, three], SmallVec::new());
    assert_eq!(id, twin);
}

/// The names `labelled`'s fields are written in, in the order `labelled` declares them.
fn labelled_keys(kb: &KnowledgeBase) -> (Symbol, Symbol, Symbol) {
    let labelled = sym(kb, "test.mcwnf.Labelled.labelled");
    let fields = kb.entity_field_names(labelled).expect("`labelled` has a field schema");
    let [first, value] = fields[..] else {
        panic!("two declared fields: {fields:?}");
    };
    assert_eq!(kb.local_name_of(first), "zz_first");
    // The row is a measurement only while the declared order is NOT the interning order —
    // `value` is the prelude's, interned before this file's `zz_first`: a canonicalizer that
    // fell back to interning order would leave the given order as it is.
    assert!(value.to_bits() < first.to_bits(), "`value` is interned first");
    (labelled, first, value)
}

/// A record's named arguments, given in another order than its fields are declared in, are
/// put in declared order — the term `make_entity_term` builds, and the one a loaded
/// `labelled(zz_first: 1, value: 2)` is.
#[test]
fn a_records_named_arguments_are_put_in_declared_order() {
    let mut kb = load_kb_with(SRC);
    let (labelled, first, value) = labelled_keys(&kb);

    let built = kb.fn_value(
        labelled,
        Vec::new(),
        vec![(value, Value::Int(2)), (first, Value::Int(1))],
    );
    assert_eq!(built.named_keys(&kb), [first, value], "in declared order");
    let (one, two) = (int(&mut kb, 1), int(&mut kb, 2));
    let twin = kb.make_entity_term(labelled, SmallVec::new(), smallvec![(value, two), (first, one)]);
    assert!(
        matches!(built, Value::Term { id, .. } if id == twin),
        "one term for one record: {built:?}"
    );
}

/// The same rule holds on the other carrier: with an occurrence among its children the record
/// is an entity, and its named arguments are in declared order as well.
#[test]
fn a_record_with_an_occurrence_child_is_put_in_declared_order() {
    let mut kb = load_kb_with(SRC);
    let (labelled, first, value) = labelled_keys(&kb);
    let occ = money_occurrence(&kb);

    let built = kb.fn_value(
        labelled,
        Vec::new(),
        vec![(value, Value::Node(occ)), (first, Value::Int(1))],
    );
    assert!(matches!(built, Value::Entity { .. }), "an occurrence child: {built:?}");
    assert_eq!(built.named_keys(&kb), [first, value], "in declared order");
}

/// An ORDERED PRODUCT — a named tuple — is exempt: its order is its identity, and is kept.
#[test]
fn an_ordered_product_keeps_its_order() {
    let mut kb = load_kb_with(SRC);
    let (_, first, value) = labelled_keys(&kb);
    let tuple = sym(&kb, "anthill.reflect.TupleLiteral");

    for given in [[value, first], [first, value]] {
        let built = kb.fn_value(
            tuple,
            Vec::new(),
            given.iter().map(|k| (*k, Value::Int(1))).collect(),
        );
        assert_eq!(built.named_keys(&kb), given, "as given");
    }
}

/// A functor that declares no fields — here a sort's type application — has its named
/// arguments taken as given, in both orders: one of the two is out of interning order, which
/// is where `make_entity_term`'s fallback would have moved it.
#[test]
fn a_type_applications_arguments_are_taken_as_given() {
    let mut kb = load_kb_with(SRC);
    let two = sym(&kb, "test.mcwnf.Two");
    assert!(kb.entity_field_names(two).is_none(), "a sort declares no fields");
    let (a, b) = (kb.intern("A"), kb.intern("B"));
    assert_ne!(a, b);
    let int64 = sym(&kb, "anthill.prelude.Int64");
    let int64 = kb.make_name_term_from_sym(int64);

    for given in [[a, b], [b, a]] {
        let built = kb.fn_value(
            two,
            Vec::new(),
            given.iter().map(|k| (*k, Value::term(int64))).collect(),
        );
        assert_eq!(built.named_keys(&kb), given, "as given");
    }
}

/// The loader stores `Show[T = Money]` through this builder; rebuilt from its own parts — the
/// functor and the children read through the view — it is the goal it was, on the carrier it
/// was.
#[test]
fn a_stored_contract_goal_rebuilds_as_itself() {
    let mut kb = load_kb_with(SRC);
    let goals = ask_goals(&kb);
    let Value::Entity { functor, pos, named } = &goals[0] else {
        panic!("the goal over an alias is stored as an application: {:?}", goals[0]);
    };
    let rebuilt = kb.fn_value(*functor, pos.to_vec(), named.to_vec());
    let Value::Entity { named: again, .. } = &rebuilt else {
        panic!("rebuilt on the carrier it was stored on: {rebuilt:?}");
    };
    let ([(k0, Value::Node(a))], [(k1, Value::Node(b))]) = (&named[..], &again[..]) else {
        panic!("one binding, on its occurrence: {named:?} / {again:?}");
    };
    assert_eq!(k0, k1);
    assert!(Rc::ptr_eq(a, b), "the binding's own occurrence, not a copy");
    assert!(views_structurally_equal(&kb, &goals[0], &rebuilt));
}
