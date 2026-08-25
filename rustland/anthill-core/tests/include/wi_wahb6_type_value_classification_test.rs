//! WI-20260824-WAHB6 (proposal 055 §2, `docs/design/055-implementation.md` §1) — a
//! nominal type expression in a VALUE position is classified ONCE, by the LOADER, from
//! its resolved head, and that classification survives as an explicit occurrence form.
//!
//! WHAT THESE ROWS MEASURE, and what they deliberately do not. The capability
//! (`is_modifiable(Cell)`, `is_modifiable(Cell[V = Int64])`) already worked — WI-206 and
//! WI-707 shipped it — so a row that only evaluates one of those measures those tickets,
//! not this one. What is new is WHERE the decision is made: it used to be made by the
//! TYPER, from the expected sort (`expects_reflect_type` gating a hint), and it is now
//! made by the loader from the resolved head alone. Two consequences separate the two
//! worlds, and every row below drives one of them:
//!
//!   1. the occurrence SAYS what it is (`Expr::TypeValue`) instead of being an
//!      `Expr::Apply` / `Expr::VarRef` that four readers each re-recognised by asking
//!      `kb.kind_of(..) == Sort`;
//!   2. the reading no longer depends on the position, so a type expression denotes in
//!      places the hint could not reach — an unannotated `let` being the sharpest,
//!      because it has no expected type at all.
//!
//! BACK-OUT, MEASURED — both loader predicates mutated to `false`
//! (`bare_name_denotes_type` in `push_leaf_occ`, `is_type_value` in `build_load`), so
//! both forms lower to their old shapes. SEVEN rows fail, five of them here:
//! `a_bare_sort_reference_is_recorded_as_a_type_value`,
//! `a_sort_headed_bracket_application_is_recorded_as_a_type_value` and
//! `a_bare_type_value_evaluates_to_a_ref_not_an_empty_application` fail on the shape;
//! `a_type_argument_is_itself_classified` and `an_unannotated_let_denotes_and_evaluates`
//! fail as LOAD errors, because with no `Type` hint reaching them the inner sort names
//! go back to being unresolved names. The other two are the diagnostic flip, in the peer
//! files: `wi206_is_modifiable_test::a_sort_name_in_a_non_type_slot_is_still_an_error`
//! and `wi707_type_application_value_test::a_sort_application_in_a_non_type_slot_is_still_an_error`.
//!
//! PASSES EITHER WAY BY DESIGN — two rows, and that is what they are for:
//! `an_eponymous_constructor_keeps_its_construction_reading` and
//! `a_local_binding_shadowing_a_sort_name_is_not_a_type_value` pin the readings this
//! change must NOT move, so a back-out leaving them green is the correct outcome, not a
//! gap. The same holds for the whole of `wi206` / `wi707` / `wi708` / `wi709` / `wi710`
//! outside those two flipped rows: every one of them passes in both worlds, which is the
//! other half of the claim — the decision moved, the answers did not.

use anthill_core::eval::Value;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;

use crate::common::{interp_for, load_kb_with, try_load_kb_with};

const SRC: &str = r#"
namespace test.wahb6
  import anthill.prelude.{Cell, Int64, String, Type}

  operation bare() -> Type = Cell
  operation applied() -> Type = Cell[V = Int64]
  operation via_let() -> Type =
    let t = Cell[V = Int64]
    t
  operation bare_via_let() -> Type =
    let t = Cell
    t
end
"#;

fn body_of<'k>(kb: &'k KnowledgeBase, qn: &str) -> &'k NodeOccurrence {
    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("{qn} must resolve"));
    kb.op_body_node(sym)
        .unwrap_or_else(|| panic!("{qn} must have a stored body occurrence"))
}

/// The RECORD, bare form: the stored body of `operation bare() -> Type = Cell` is a
/// classified type value naming `Cell` — not the `Expr::VarRef` a bare identifier used
/// to lower to and that the typer then re-read through the expected sort.
#[test]
fn a_bare_sort_reference_is_recorded_as_a_type_value() {
    let kb = load_kb_with(SRC);
    match body_of(&kb, "test.wahb6.bare").as_expr() {
        Some(Expr::TypeValue {
            head,
            pos_args,
            named_args,
        }) => {
            assert_eq!(kb.local_name_of(*head), "Cell", "the classified head");
            assert!(
                pos_args.is_empty() && named_args.is_empty(),
                "a BARE reference carries no type arguments — the two faces stay \
                 structurally distinct (proposal 055 §7)",
            );
        }
        other => panic!(
            "a bare sort reference must be recorded as a type value, got {:?}",
            other.map(std::mem::discriminant)
        ),
    }
}

/// The RECORD, applied form: the arguments ride as this node's children, and the node
/// says it is a type value rather than an application that happens to be sort-headed.
#[test]
fn a_sort_headed_bracket_application_is_recorded_as_a_type_value() {
    let kb = load_kb_with(SRC);
    match body_of(&kb, "test.wahb6.applied").as_expr() {
        Some(Expr::TypeValue {
            head,
            pos_args,
            named_args,
        }) => {
            assert_eq!(kb.local_name_of(*head), "Cell");
            assert!(pos_args.is_empty(), "`Cell[V = Int64]` binds V by name");
            assert_eq!(named_args.len(), 1, "one type argument");
            assert_eq!(kb.local_name_of(named_args[0].0), "V");
        }
        other => panic!(
            "a bracketed sort application must be recorded as a type value, got {:?}",
            other.map(std::mem::discriminant)
        ),
    }
}

/// THE ARGUMENT IS CLASSIFIED TOO, and this is what replaced the hint rather than merely
/// surviving it. The old mechanism pushed a `Type` expectation from the application down
/// onto every argument, which is how the inner `Int64` read as a type; there is no such
/// push now — the inner name is classified by the same loader rule, on its own.
///
/// This row is why the classification lives in `push_leaf_occ` and not in the
/// `Term::Ident` arm of `visit_load`: a bracket argument reaches the loader as a
/// parse-side `Term::Ref`, so an `Ident`-only rule left it unclassified and five rows of
/// `wi707_type_application_value_test` went red.
#[test]
fn a_type_argument_is_itself_classified() {
    let kb = load_kb_with(SRC);
    let Some(Expr::TypeValue { named_args, .. }) = body_of(&kb, "test.wahb6.applied").as_expr()
    else {
        panic!("applied() must be a type value");
    };
    match named_args[0].1.as_expr() {
        Some(Expr::TypeValue {
            head,
            pos_args,
            named_args,
        }) => {
            assert_eq!(kb.local_name_of(*head), "Int64", "the argument's own head");
            assert!(pos_args.is_empty() && named_args.is_empty());
        }
        other => panic!(
            "the type ARGUMENT must carry its own classification, got {:?}",
            other.map(std::mem::discriminant)
        ),
    }
}

/// A POSITION WITH NO EXPECTED SORT AT ALL. An unannotated `let` value cannot be reached
/// by an expectation-directed classifier — there is no expectation to direct it — so
/// this program did not load before: the applied form got no `Type` hint, its argument
/// got none either, and `Int64` was reported as an unresolved name. It loads now because
/// the reading no longer depends on the position.
///
/// This row also DRIVES the value, so it says more than "it loads": the `let` binding is
/// returned and must be the canonical parameterized type term.
#[test]
fn an_unannotated_let_denotes_and_evaluates() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.wahb6.via_let", &[])
        .unwrap_or_else(|e| panic!("via_let: {e:?}"));
    let Value::Term { id, .. } = v else {
        panic!("expected a Term-carried type, got {v:?}")
    };
    match interp.kb().get_term(id).clone() {
        Term::Fn {
            functor,
            named_args,
            ..
        } => {
            assert_eq!(interp.kb().local_name_of(functor), "Cell");
            assert_eq!(named_args.len(), 1);
            assert_eq!(interp.kb().local_name_of(named_args[0].0), "V");
            match interp.kb().get_term(named_args[0].1).clone() {
                Term::Ref(s) | Term::Ident(s) => {
                    assert_eq!(interp.kb().local_name_of(s), "Int64")
                }
                other => panic!("V must bind Int64, got {other:?}"),
            }
        }
        other => panic!("expected the parameterized `Cell[V = …]` term, got {other:?}"),
    }
}

/// The bare face of the row above, and it pins the OTHER half of proposal 055 §7: a bare
/// reference backs onto `Ref(S)`, NOT the `Fn` head an empty parameterization would
/// build. The two are structurally different terms and do not unify, which is what makes
/// `fact Modifiable[T = Cell]` answer for `is_modifiable(Cell)`.
#[test]
fn a_bare_type_value_evaluates_to_a_ref_not_an_empty_application() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.wahb6.bare_via_let", &[])
        .unwrap_or_else(|e| panic!("bare_via_let: {e:?}"));
    let Value::Term { id, .. } = v else {
        panic!("expected a Term-carried type, got {v:?}")
    };
    match interp.kb().get_term(id).clone() {
        Term::Ref(s) => assert_eq!(interp.kb().local_name_of(s), "Cell"),
        other => panic!(
            "a bare sort must evaluate to `Ref(Cell)`, not an application; got {other:?}"
        ),
    }
}

/// THE ADJACENT NON-VALUE ROLE IS UNTOUCHED. A sort name written as a CONSTRUCTOR head
/// keeps its construction reading — the classification is keyed on the bracket surface
/// and the resolved head, not on "the head names a sort", so `Leaf(name: …)` is still a
/// value and only `Leaf[…]` is a type.
///
/// The eponymous sort is the case that makes this a real control rather than a
/// formality: `sort Leaf { entity Leaf(…) }` is ONE symbol carrying the `Sort` kind
/// (WI-926), so a rule that read the kind alone would have stolen both readings.
#[test]
fn an_eponymous_constructor_keeps_its_construction_reading() {
    let src = r#"
namespace test.wahb6c
  import anthill.prelude.{Int64, String, Type}

  sort Leaf
    entity Leaf(name: String)
  end

  operation build() -> Leaf = Leaf(name: "tip")
  operation as_type() -> Type = Leaf
end
"#;
    let mut interp = interp_for(src);
    // The APPLIED surface constructs.
    let built = interp
        .call("test.wahb6c.build", &[])
        .unwrap_or_else(|e| panic!("build: {e:?}"));
    assert!(
        !matches!(built, Value::Term { .. }),
        "`Leaf(name: …)` must construct a value, not denote a type; got {built:?}",
    );
    // The BARE surface of the same symbol still reaches its construction reading first
    // (it is a nullary-fieldless constructor test in `check_bare_ref`), which is exactly
    // what `bare_name_denotes_type` steps aside for. What it must NOT do is fail to load.
    let kb = interp.kb();
    let sym = kb
        .try_resolve_symbol("test.wahb6c.as_type")
        .expect("as_type resolves");
    assert!(
        kb.op_body_node(sym).is_some(),
        "as_type must have a stored body",
    );
}

/// A LOCAL SHADOWS A SORT, and the classification must not steal the local's reading.
/// The loader resolves the name before it classifies (`push_leaf_occ` reads the symbol
/// the leaf was built with), so a `let`-bound `Cell` is a value reference and stays one.
#[test]
fn a_local_binding_shadowing_a_sort_name_is_not_a_type_value() {
    let src = r#"
namespace test.wahb6s
  import anthill.prelude.{Int64}

  operation shadowed() -> Int64 =
    let Cell = 7
    Cell
end
"#;
    let kb = try_load_kb_with(src)
        .unwrap_or_else(|errs| panic!("a local may shadow a sort name: {errs:?}"));
    let sym = kb
        .try_resolve_symbol("test.wahb6s.shadowed")
        .expect("shadowed resolves");
    let body = kb.op_body_node(sym).expect("shadowed has a body");
    let Some(Expr::Let { body: inner, .. }) = body.as_expr() else {
        panic!("expected a let body");
    };
    assert!(
        !matches!(inner.as_expr(), Some(Expr::TypeValue { .. })),
        "a reference to the LOCAL `Cell` must stay a value reference",
    );
}

/// THE TWO CARRIERS MUST KEY ALIKE. A classified type value is read through
/// `TermView` on the discrimination / `goal_fingerprint` paths, and the occurrence and
/// its term twin have to answer the same head there — otherwise a goal the index has
/// pruned still matches, or two structurally different type values share one key.
///
/// This is not hypothetical for a NEW variant: `occ_head`'s catch-all is
/// `ViewHead::Opaque`, which is PAYLOAD-FREE, so an unwired variant does not merely
/// lose precision — it makes `Cell` and `Cell[V = Int64]` compare EQUAL.
///
/// BACK-OUT: remove the `Expr::TypeValue` entries in `term_view.rs`
/// (`expr_wrapped_shape`, `wrapped_expr_child`, the `occ_head` arm and the two child
/// accessors) and both halves fail — the agreement half because the occurrence goes
/// `Opaque` while its term twin does not, and the distinctness half because two Opaques
/// are equal.
#[test]
fn an_occurrence_and_its_term_twin_key_alike() {
    use anthill_core::kb::node_occurrence::try_occurrence_to_term;
    use anthill_core::kb::subst::Substitution;
    use anthill_core::kb::term_view::{goal_fingerprint, views_structurally_equal, TermIdView};

    let mut kb = load_kb_with(SRC);
    let s = Substitution::new();

    for qn in ["test.wahb6.bare", "test.wahb6.applied"] {
        let occ = {
            let sym = kb.try_resolve_symbol(qn).expect("op resolves");
            std::rc::Rc::clone(kb.op_body_node(sym).expect("body"))
        };
        let twin = TermIdView(
            try_occurrence_to_term(&mut kb, &occ).expect("a type value has a term twin"),
        );
        assert!(
            views_structurally_equal(&kb, &occ, &twin),
            "{qn}: the occurrence and its term twin must read as the same structure",
        );
        assert_eq!(
            goal_fingerprint(&kb, &occ, &s),
            goal_fingerprint(&kb, &twin, &s),
            "{qn}: the two carriers must produce the same key",
        );
    }

    // ...and the two FACES are not each other: `Ref(Cell)` and `Cell[V = Int64]` are
    // different terms and must key differently (proposal 055 §7 — the reason WI-206's
    // "a parameterized instance answers as its base does" lives in the operation layer
    // and not in term identity).
    let bare = {
        let sym = kb.try_resolve_symbol("test.wahb6.bare").expect("bare");
        std::rc::Rc::clone(kb.op_body_node(sym).expect("body"))
    };
    let applied = {
        let sym = kb.try_resolve_symbol("test.wahb6.applied").expect("applied");
        std::rc::Rc::clone(kb.op_body_node(sym).expect("body"))
    };
    assert!(
        !views_structurally_equal(&kb, &bare, &applied),
        "a bare and an applied type value are structurally different",
    );
    assert_ne!(
        goal_fingerprint(&kb, &bare, &s),
        goal_fingerprint(&kb, &applied, &s),
        "a bare and an applied type value must not share a key",
    );
}

/// THE TWIN'S SHAPE, not just its agreement with itself. A bare type value lowers to
/// `Ref(S)` — never to the `var_ref(name: Ref(S))` an unclassified bare identifier
/// lowers to.
///
/// This row exists because the peer above cannot see the difference: it compares the
/// occurrence against a twin computed FROM THAT SAME OCCURRENCE, so it stays green
/// whatever shape the twin takes. FOUND BY /code-review, which measured the applied
/// form lowering to `Cell(V: var_ref(name: Ref(Int64)))` where it used to lower to
/// `Cell(V: Ref(Int64))` — a decidable closed datum turned into something
/// `value_has_open_world_ref` reads as an open-world variable, which is what makes a
/// goal flounder instead of deciding.
///
/// BACK-OUT: change `try_occurrence_to_term`'s bare arm to `kb.make_var_ref_term(head)`
/// and this row fails on the argument's shape, while every other row in this file —
/// and the whole of wi206/707/709/710 — stays green.
#[test]
fn a_bare_type_value_lowers_to_a_ref_not_a_var_ref() {
    use anthill_core::kb::node_occurrence::try_occurrence_to_term;

    let mut kb = load_kb_with(SRC);

    // The bare face, on its own.
    let bare = {
        let sym = kb.try_resolve_symbol("test.wahb6.bare").expect("bare");
        std::rc::Rc::clone(kb.op_body_node(sym).expect("body"))
    };
    let bare_tid = try_occurrence_to_term(&mut kb, &bare).expect("twin");
    match kb.get_term(bare_tid).clone() {
        Term::Ref(s) => assert_eq!(kb.local_name_of(s), "Cell"),
        other => panic!("a bare type value must lower to `Ref(Cell)`, got {other:?}"),
    }

    // And as a type ARGUMENT, which is the route that regressed: a bracket argument
    // arrives as an `Expr::Ref`, whose twin has always been `Ref(S)`.
    let applied = {
        let sym = kb.try_resolve_symbol("test.wahb6.applied").expect("applied");
        std::rc::Rc::clone(kb.op_body_node(sym).expect("body"))
    };
    let applied_tid = try_occurrence_to_term(&mut kb, &applied).expect("twin");
    let arg = match kb.get_term(applied_tid).clone() {
        Term::Fn { named_args, .. } => {
            let hit = named_args
                .iter()
                .find(|(k, _)| kb.local_name_of(*k) == "V")
                .expect("the V binding");
            hit.1
        }
        other => panic!("expected `Cell(V: …)`, got {other:?}"),
    };
    match kb.get_term(arg).clone() {
        Term::Ref(s) => assert_eq!(kb.local_name_of(s), "Int64"),
        other => panic!(
            "the type argument must lower to `Ref(Int64)`, not a `var_ref` wrapper; \
             got {other:?}"
        ),
    }
}
