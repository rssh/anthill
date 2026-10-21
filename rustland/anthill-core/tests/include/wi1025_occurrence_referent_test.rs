//! WI-1025 — an occurrence references a name the same way its term twin does.
//!
//! WI-1024 excluded `Value::Node` from `eval::value_functor` on the ground that an
//! occurrence's head can name a reflect ENCODING (`Arrow`, `Denoted`, a `Lambda`
//! constructor) rather than a referent. That line does not hold: the TERM carrier
//! has always answered `Some(Arrow)` for `Fn{Arrow, …}`, and no consumer treats it
//! as wrong — a reflect constructor IS a real constructor symbol. Excluding the
//! occurrence therefore made the two carriers of ONE thing disagree, which is the
//! defect this reader exists to prevent.
//!
//! THE RULE THAT DOES HOLD: **read the head when the carrier has a faithful TERM
//! FORM; refuse when the head is view-only.** `Term` / `Entity` / `SymbolRef` /
//! `Node` are the carriers `value_to_term` accepts whose head can name a functor;
//! `OpRef` / `Requirement` are `alloc_from_value`'s `UnsupportedVariant`, so the
//! head WI-1019 gave them has no stored term behind it.
//!
//! Admitting a carrier OBLIGES its paired readers (WI-1016's rule at
//! `eval/pattern.rs`): `constructor_sub_values` must destructure it, or
//! `MatchDispatch`'s pre-filter promises an arm that then declines. That is driven
//! here. The other paired reader, the standard `Modify` handler's cycle walk, was
//! retired with the handler (WI-200), and its two rows with it.
//!
//! The whole answer table for `value_functor` lives in
//! `wi1024_value_functor_test`; this file drives what WI-1025 CHANGED.

use std::rc::Rc;

use anthill_core::eval::{value_functor, Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence, TypeChild, TypeNode};
use anthill_core::kb::term::Term;
use anthill_core::span::{SourceId, SourceSpan};

const SRC: &str = r#"
namespace test.wi1025
  sort Item
    entity Box(id: String)
    entity Empty
  end
  fact Box(id: "B-001")
end
"#;

fn span() -> SourceSpan {
    SourceSpan::new(SourceId::from_raw(0), 0, 3)
}

fn box_sym(interp: &mut Interpreter) -> Symbol {
    interp
        .kb_mut()
        .resolve_qualified_name_sym("test.wi1025.Item.Box")
}

// ── the reachable case: a parameterized type that had to ride as an occurrence ──

/// THE GAP, DRIVEN END TO END: a parameterized type whose binding is `denoted`
/// cannot hash-cons, so it rides as `TypeNode::Parameterized` — whose head IS the
/// base sort, deliberately, so that "`TermView` reads the carrier and its term twin
/// identically" (WI-361). Before WI-1025 the term twin `Fn{Cell, bindings}`
/// answered `Some(Cell)` at `facts_of` and the occurrence answered "not a sort
/// reference".
///
/// This is why the exclusion was not merely inelegant: the carrier is not chosen by
/// the caller, it is forced by a denoted value inside the type.
///
/// CONTROL, MEASURED by restoring WI-1024's `Value::Node(_) => None`: the
/// occurrence row errors `TypeMismatch { expected: "Type (entity reference)", got:
/// "Node" }` while the term row still answers — one type, two carriers, two
/// answers.
#[test]
fn a_parameterized_type_occurrence_names_its_base_sort() {
    let mut interp = crate::common::interp_for(SRC);
    let sym = box_sym(&mut interp);
    let v_param = interp.kb_mut().intern("V");

    // The occurrence carrier: `Box[V = denoted(<a ref occurrence>)]`. The denoted
    // child is exactly what forces the Node carrier (WI-348).
    let denoted = NodeOccurrence::new_type(
        TypeNode::Denoted {
            value: NodeOccurrence::new_expr(Expr::Ref(sym), span(), None),
        },
        span(),
        None,
    );
    let base_tid = interp.kb_mut().alloc(Term::Ref(sym));
    let occ_type = Value::Node(NodeOccurrence::new_type(
        TypeNode::Parameterized {
            base: TypeChild::Interned(base_tid),
            bindings: vec![(v_param, TypeChild::Node(denoted))],
        },
        span(),
        None,
    ));

    // PREMISE, asserted: this really is the occurrence carrier and its head really
    // is the BASE SORT — not a `Parameterized` wrapper constructor. Without it a
    // `Some(Box)` below would not be evidence about `TypeNode::Parameterized`.
    {
        use anthill_core::kb::term_view::{TermView, ViewHead};
        assert!(
            matches!(occ_type.head(interp.kb()), ViewHead::Functor { functor: Some(f), .. } if f == sym),
            "premise: a parameterized type occurrence heads as its base sort (WI-361)",
        );
    }

    assert_eq!(
        value_functor(interp.kb(), &occ_type),
        Some(sym),
        "the occurrence names the sort its term twin names",
    );

    // And the consumer agrees with the term twin, fact for fact.
    let via_occ = facts_of(&mut interp, occ_type).expect("a type occurrence is a sort reference");
    let term_twin = Value::term(
        interp
            .kb_mut()
            .resolve_qualified_name_term("test.wi1025.Item.Box"),
    );
    let via_term = facts_of(&mut interp, term_twin).expect("its term twin already worked");
    // By CONTENT, not length: two DIFFERENT sorts with one fact each would agree on
    // a count. Each head is identified by the sort it names.
    let names = |interp: &Interpreter, list: &Value| -> Vec<Option<Symbol>> {
        crate::common::list_heads(list)
            .iter()
            .map(|h| value_functor(interp.kb(), h))
            .collect()
    };
    let occ_names = names(&interp, &via_occ);
    assert_eq!(
        occ_names.len(),
        1,
        "premise: the fixture asserts exactly one Box fact"
    );
    assert_eq!(
        occ_names,
        names(&interp, &via_term),
        "one type, one answer, whichever carrier it was forced onto",
    );
}

fn facts_of(interp: &mut Interpreter, sort: Value) -> Result<Value, String> {
    interp
        .call("anthill.reflect.KB.facts_of", &[Value::Unit, sort])
        .map_err(|e| format!("{e:?}"))
}

// ── the paired reader: the destructure must keep the pre-filter's promise ────

/// `case Empty()` matches a nullary constructor on ALL THREE carriers of its name.
///
/// `MatchDispatch` pre-filters branches by `value_functor`; once that accepts a
/// carrier, `constructor_sub_values` must be able to destructure it or the
/// pre-filter promises an arm that then declines (the rule WI-1016 wrote at
/// `eval/pattern.rs`, when it added the `SymbolRef` arm for exactly this reason).
///
/// THIS DRIVES THE DESTRUCTURE, NOT THE PAIR. `match_pattern` is called directly,
/// so the pre-filter at `eval/eval.rs`'s `AwaitState::MatchDispatch` is not on the
/// path. That the pre-filter cannot make things WORSE is established by reading it
/// rather than by this test: it skips a branch only when
/// `constructor_pattern_name` is `Some` — i.e. only a `Pattern::Constructor`, never
/// a var / wildcard / literal / tuple arm — and only on a functor mismatch, and
/// such a branch reaches `constructor_sub_values`' `None` anyway.
///
/// CONTROLS, each MEASURED:
///  - drop the `Value::Node` arm from `constructor_sub_values`: the `node` row
///    ALONE returns `None` — `value_functor` says the value names `Empty`, and the
///    destructure disagrees. (Measured: the wrapper row still passes, because
///    `carried()` has already unwrapped it to a `Value::SymbolRef`, which has its
///    own arm. The two controls are independent, and each names one row.)
///  - drop the `Value::carried()` cancellation from `constructor_sub_values`: the
///    wrapper row alone fails, which is the accept-then-decline pair reappearing
///    one level in.
#[test]
fn a_nullary_constructor_matches_on_every_carrier_of_its_name() {
    let mut interp = crate::common::interp_for(SRC);
    let empty = interp
        .kb_mut()
        .resolve_qualified_name_sym("test.wi1025.Item.Empty");
    let ref_tid = interp.kb_mut().alloc(Term::Ref(empty));
    let carriers: Vec<(&str, Value)> = vec![
        ("term", Value::term(ref_tid)),
        ("symbolref", Value::SymbolRef(empty)),
        (
            "node",
            Value::Node(NodeOccurrence::new_expr(Expr::Ref(empty), span(), None)),
        ),
        // The wrapper case, and the one that makes `Value::carried` load-bearing
        // HERE: `occ_head` reads through a top-level `Spliced`, so `value_functor`
        // accepts this and the pre-filter promises the arm — but every by-`Expr`
        // reader sees `Expr::Spliced` and would fall through, declining what was
        // just accepted.
        (
            "node-wrapping-a-symbolref",
            Value::Node(NodeOccurrence::new_expr(
                Expr::Spliced(Value::SymbolRef(empty)),
                span(),
                None,
            )),
        ),
    ];
    let pattern = constructor_pattern(&mut interp, empty);
    let missed: Vec<&str> = carriers
        .iter()
        .filter(|(_, v)| anthill_core::eval::pattern::match_pattern(&interp, &pattern, v).is_none())
        .map(|(name, _)| *name)
        .collect();
    assert!(
        missed.is_empty(),
        "`case Empty()` must match every carrier of the name; missed {missed:?}",
    );

    // …and it still REFUSES a different constructor on the new carrier, so the arm
    // above is a match and not a blanket accept.
    let other = box_sym(&mut interp);
    let wrong = Value::Node(NodeOccurrence::new_expr(Expr::Ref(other), span(), None));
    assert!(
        anthill_core::eval::pattern::match_pattern(&interp, &pattern, &wrong).is_none(),
        "a different constructor is still no match",
    );
}

/// A `case Empty()` pattern occurrence.
fn constructor_pattern(interp: &mut Interpreter, ctor: Symbol) -> Rc<NodeOccurrence> {
    let _ = interp;
    NodeOccurrence::new_pattern(
        anthill_core::kb::node_occurrence::Pattern::Constructor {
            name: ctor,
            pos_args: vec![],
            named_args: vec![],
        },
        span(),
        None,
    )
}
