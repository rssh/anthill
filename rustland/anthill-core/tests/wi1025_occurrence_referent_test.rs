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
//! `MatchDispatch`'s pre-filter promises an arm that then declines; and
//! `effects::detect_cycle` must walk it, or `Modify`'s guard reports no cycle for a
//! key `resource_key` accepted. Both are driven here.
//!
//! The whole answer table for `value_functor` lives in
//! `wi1024_value_functor_test`; this file drives what WI-1025 CHANGED.

use std::rc::Rc;

use anthill_core::eval::{value_functor, Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence, TypeChild, TypeNode};
use anthill_core::kb::term::Term;
use anthill_core::span::{SourceId, SourceSpan};

mod common;

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
    interp.kb_mut().resolve_qualified_name_sym("test.wi1025.Item.Box")
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
    let mut interp = common::interp_for(SRC);
    let sym = box_sym(&mut interp);
    let v_param = interp.kb_mut().intern("V");

    // The occurrence carrier: `Box[V = denoted(<a ref occurrence>)]`. The denoted
    // child is exactly what forces the Node carrier (WI-348).
    let denoted = NodeOccurrence::new_type(
        TypeNode::Denoted { value: NodeOccurrence::new_expr(Expr::Ref(sym), span(), None) },
        span(),
        None,
    );
    let base_tid = interp.kb_mut().alloc(Term::Ref(sym));
    let occ_type = Value::Node(NodeOccurrence::new_type(
        TypeNode::Parameterized {
            base: TypeChild::Ground(base_tid),
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
        interp.kb_mut().resolve_qualified_name_term("test.wi1025.Item.Box"),
    );
    let via_term = facts_of(&mut interp, term_twin).expect("its term twin already worked");
    // By CONTENT, not length: two DIFFERENT sorts with one fact each would agree on
    // a count. Each head is identified by the sort it names.
    let names = |interp: &Interpreter, list: &Value| -> Vec<Option<Symbol>> {
        common::list_heads(list).iter().map(|h| value_functor(interp.kb(), h)).collect()
    };
    let occ_names = names(&interp, &via_occ);
    assert_eq!(occ_names.len(), 1, "premise: the fixture asserts exactly one Box fact");
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

// ── paired reader 1: the destructure must keep the pre-filter's promise ─────

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
    let mut interp = common::interp_for(SRC);
    let empty = interp.kb_mut().resolve_qualified_name_sym("test.wi1025.Item.Empty");
    let ref_tid = interp.kb_mut().alloc(Term::Ref(empty));
    let carriers: Vec<(&str, Value)> = vec![
        ("term", Value::term(ref_tid)),
        ("symbolref", Value::SymbolRef(empty)),
        ("node", Value::Node(NodeOccurrence::new_expr(Expr::Ref(empty), span(), None))),
        // The wrapper case, and the one that makes `Value::carried` load-bearing
        // HERE: `occ_head` reads through a top-level `Spliced`, so `value_functor`
        // accepts this and the pre-filter promises the arm — but every by-`Expr`
        // reader sees `Expr::Spliced` and would fall through, declining what was
        // just accepted.
        ("node-wrapping-a-symbolref", Value::Node(NodeOccurrence::new_expr(
            Expr::Spliced(Value::SymbolRef(empty)),
            span(),
            None,
        ))),
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

// ── paired reader 2: the cycle guard must see through the same carrier ──────

/// `Modify[<sym>].set(<the same sym, as an occurrence>)` is a cycle.
///
/// `resource_key` reads its key through `value_functor`, so once that accepts an
/// occurrence, `detect_cycle`'s `_ => Ok(())` would report NO cycle for the one
/// shape the guard exists to catch — the same hole `Value::SymbolRef` had before
/// WI-1016 closed it.
///
/// CONTROL, MEASURED by dropping the `Value::Node` arm from `detect_cycle`: the
/// direct row returns `Ok(Unit)` — a silent accept of a self-reference — and the
/// nested row does too.
#[test]
fn the_cycle_guard_sees_a_self_reference_through_an_occurrence() {
    let mut interp = common::interp_for(SRC);
    common::register_modify_handler(&mut interp);
    let sym = box_sym(&mut interp);
    // The RESOURCE, on the carrier `resource_key` has always accepted.
    let resource = Value::SymbolRef(sym);
    let set = interp.kb_mut().intern("set");

    let set_to = |interp: &mut Interpreter, v: Value| {
        interp.invoke_effect_handler(
            "anthill.prelude.Modify",
            set,
            &[resource.clone(), v],
        )
    };

    // Direct: the new value IS the resource, spelled as an occurrence.
    let direct = Value::Node(NodeOccurrence::new_expr(Expr::Ref(sym), span(), None));
    // Nested: the reference is a CHILD, so the walk has to descend — the second
    // half of the `Entity` arm, on this carrier.
    let nested = Value::Node(NodeOccurrence::new_expr(
        Expr::Apply {
            functor: sym,
            pos_args: vec![NodeOccurrence::new_expr(Expr::Ref(sym), span(), None)],
            named_args: vec![],
            type_args: vec![],
        },
        span(),
        None,
    ));
    // Wrapped: an occurrence carrying the value — the carrier-algebra cancellation
    // `Value::carried` performs, driven through a reader that would otherwise see
    // `Expr::Spliced` and fall through.
    let wrapped = Value::Node(NodeOccurrence::new_expr(
        Expr::Spliced(Value::SymbolRef(sym)),
        span(),
        None,
    ));

    // Not merely `is_err()`: the verdict must be the CYCLE, or a row could pass on
    // an unrelated failure.
    let wrong: Vec<(&str, String)> = [
        ("direct", direct),
        ("nested", nested),
        ("wrapped", wrapped),
    ]
    .into_iter()
    .map(|(name, v)| (name, format!("{:?}", set_to(&mut interp, v))))
    .filter(|(_, got)| !got.contains("CyclicReference"))
    .collect();
    assert!(
        wrong.is_empty(),
        "a self-reference through an occurrence is a cycle; got {wrong:?}",
    );

    // COUNTER-CONTROL, and it earned its place: the first draft of this test
    // called a non-existent operation, so all the rows above "passed" on
    // `UnknownOperation`. An unrelated occurrence value must still be ACCEPTED, or
    // the rows measure a blanket refusal of the carrier rather than a cycle.
    let unrelated = Value::Node(NodeOccurrence::new_expr(
        Expr::Const(anthill_core::kb::term::Literal::Int(1)),
        span(),
        None,
    ));
    let got = set_to(&mut interp, unrelated);
    assert!(got.is_ok(), "an unrelated occurrence value is not a cycle: {got:?}");
}

/// The child walk must not be gated on the HEAD — the sibling `Entity` / `Tuple`
/// arms walk unconditionally and this one has to as well.
///
/// A `[…]` list-literal occurrence reads as its `ListLiteral(e…)` twin only when
/// the reflect constructors are loaded; without them `occ_head` answers `Opaque`
/// while `occ_pos_child` still hands back the elements. A first version of this arm
/// collected children as `match value.head(kb) { Functor{pos_arity} => (0..pos_arity)…,
/// _ => Vec::new() }` and so dropped every one of them — reinstating the silent
/// `_ => Ok(())` the arm was added to remove, one level in.
///
/// CONTROL, MEASURED by restoring that head-gated collection: `Ok(Unit)` — the
/// self-reference inside the literal is silently stored.
#[test]
fn the_cycle_walk_descends_a_head_that_presents_no_shape() {
    let mut interp = common::interp_for(SRC);
    common::register_modify_handler(&mut interp);
    let sym = box_sym(&mut interp);
    let v_param = interp.kb_mut().intern("V");
    let set = interp.kb_mut().intern("set");

    // A parameterized type whose BASE is itself an occurrence:
    // `parameterized_base_functor` answers `None` for a `TypeChild::Node` base, so
    // the head is `Opaque` — while the BINDINGS are still named children, and one
    // of them references the resource.
    let base = NodeOccurrence::new_type(
        TypeNode::Denoted { value: NodeOccurrence::new_expr(Expr::Ref(sym), span(), None) },
        span(),
        None,
    );
    let binding = NodeOccurrence::new_expr(Expr::Ref(sym), span(), None);
    let opaque_headed = Value::Node(NodeOccurrence::new_type(
        TypeNode::Parameterized {
            base: TypeChild::Node(base),
            bindings: vec![(v_param, TypeChild::Node(binding))],
        },
        span(),
        None,
    ));

    // PREMISE, asserted: the head really presents no shape, and the child really is
    // reachable. Without both, the row proves nothing about the gate.
    {
        use anthill_core::kb::term_view::{TermView, ViewHead};
        assert!(
            matches!(opaque_headed.head(interp.kb()), ViewHead::Opaque),
            "premise: a Node-based parameterized type heads Opaque",
        );
        let keys = opaque_headed.named_keys(interp.kb());
        assert_eq!(keys.len(), 1, "premise: and it still has a named child");
        assert!(opaque_headed.named_arg(interp.kb(), keys[0]).is_some());
    }

    let got = interp.invoke_effect_handler(
        "anthill.prelude.Modify",
        set,
        &[Value::SymbolRef(sym), opaque_headed],
    );
    assert!(
        format!("{got:?}").contains("CyclicReference"),
        "a self-reference under an opaque-headed occurrence is still a cycle, got {got:?}",
    );
}
