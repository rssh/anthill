//! WI-1014: `Expr::SetLit` and `Expr::TupleLit` occurrences read through
//! `TermView` as the term twins WI-559 already built for them, instead of
//! collapsing to `ViewHead::Opaque`.
//!
//! The seam this closes: WI-027 gave `ListLiteral` its term twin and occurrence
//! build and "deliberately left the siblings"; WI-559 closed that remainder on
//! the TERM side (`try_occurrence_to_term` has real `SetLit` / `TupleLit` arms);
//! WI-814 built the VIEW side for Lambda / If / Let / Match / Pattern and listed
//! its three known gaps EACH WITH A TICKET. SetLit / TupleLit were in neither
//! list — they got a JUSTIFICATION in the `_ => Opaque` comment instead of an
//! owner, which is what kept them off every list.
//!
//! Why it is a wrong answer and not a precision loss (WI-425): one source `{1}`
//! read `Fn{SetLiteral, [1]}` through the term carrier and `Opaque` through the
//! occurrence carrier — a view disagreeing with its own twin. And since
//! `views_structurally_equal` has no `(Opaque, Opaque)` arm, a set literal was
//! not equal to ITSELF through the occurrence carrier.
//!
//! Acceptance (ticket): a TERM-carrier-indexed set literal is found by an
//! OCCURRENCE-carrier query and a different one is not; two identical set
//! literals compare equal and two distinct ones do not; the TupleLit ordering
//! question is decided and tested; head arity and `named_keys` cannot disagree.

use std::rc::Rc;

use anthill_core::eval::value::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::term_view::{goal_fingerprint, views_structurally_equal, TermView, ViewHead};
use anthill_core::kb::ClauseKind;
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::span::{SourceId, SourceSpan};
use smallvec::SmallVec;

/// A KB with the full stdlib loaded — `anthill.reflect.SetLiteral` /
/// `TupleLiteral` resolved, as in any loader-built KB.
fn stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib loads");
    kb
}

fn span() -> SourceSpan {
    SourceSpan::new(SourceId::from_raw(0), 0, 0)
}

fn occ(expr: Expr) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(expr, span(), None)
}

fn int_occ(n: i64) -> Rc<NodeOccurrence> {
    occ(Expr::Const(Literal::Int(n)))
}

/// The TERM twin for `{n}`, built exactly as `try_occurrence_to_term`'s WI-559
/// arm does: `occ_build_fn(kb, SetLiteral, elems, &[])` → elements POSITIONAL.
fn set_term(kb: &mut KnowledgeBase, n: i64) -> TermId {
    let f = kb.try_resolve_symbol("anthill.reflect.SetLiteral").unwrap();
    let elem = kb.alloc(Term::Const(Literal::Int(n)));
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_elem(elem, 1),
        named_args: SmallVec::new(),
    })
}

/// The OCCURRENCE for the same `{n}`.
fn set_occ(n: i64) -> Rc<NodeOccurrence> {
    occ(Expr::SetLit(vec![int_occ(n)]))
}

/// `(a: x, b: y)` as an occurrence, in the given label order — the order IS the
/// tuple's identity (WI-788), so the two spellings are DIFFERENT tuples.
fn tuple_occ(labels: [(Symbol, i64); 2]) -> Rc<NodeOccurrence> {
    occ(Expr::TupleLit {
        positional: Vec::new(),
        named: labels.iter().map(|(s, n)| (*s, int_occ(*n))).collect(),
    })
}

/// PART A — the head and children mirror the WI-559 twin, so a set literal is
/// structural in BOTH carriers.
///
/// CONTROL: with the `Expr::SetLit` arm removed from `occ_head`, the occurrence
/// head is `ViewHead::Opaque` and every assert here fails — the arities compare
/// unequal and `functor_sym()` is `None`.
#[test]
fn set_literal_view_is_isomorphic_to_its_term_twin() {
    let mut kb = stdlib_kb();
    let term = set_term(&mut kb, 1);
    let node = set_occ(1);

    let (tf, tp, tn) = match TermView::head(&term, &kb) {
        ViewHead::Functor {
            functor,
            pos_arity,
            named_arity,
        } => (functor, pos_arity, named_arity),
        other => panic!("term twin must be a Functor head, got {other:?}"),
    };
    let (nf, np, nn) = match TermView::head(&node, &kb) {
        ViewHead::Functor {
            functor,
            pos_arity,
            named_arity,
        } => (functor, pos_arity, named_arity),
        other => panic!("the occurrence must read structurally, got {other:?}"),
    };
    assert_eq!(
        (tf, tp, tn),
        (nf, np, nn),
        "head must match the twin exactly"
    );
    assert_eq!(
        tp, 1,
        "one element, POSITIONAL — occ_build_fn does not re-label"
    );

    // The child is reachable and is the element, not a placeholder.
    let child = TermView::pos_arg(&node, &kb, 0).expect("element 0 is supplied");
    assert!(
        matches!(child.to_value().head(&kb), ViewHead::Const(Literal::Int(1))),
        "the promised child is the element itself",
    );
    assert!(
        TermView::pos_arg(&node, &kb, 1).is_none(),
        "and there is no child beyond the arity the head promised",
    );
}

/// PART A — a set literal is now equal to ITSELF, and to an equal sibling,
/// through the occurrence carrier; two distinct ones stay unequal.
///
/// CONTROL: `views_structurally_equal` has no `(Opaque, Opaque)` arm, so before
/// the view arm the FIRST assert failed — a set literal was not equal to itself.
#[test]
fn set_literals_compare_equal_through_the_occurrence_carrier() {
    let kb = stdlib_kb();
    let a = set_occ(1);
    let b = set_occ(1);
    let c = set_occ(2);

    assert!(
        views_structurally_equal(&kb, &a, &a),
        "a set literal equals itself"
    );
    assert!(
        views_structurally_equal(&kb, &a, &b),
        "and an identical sibling"
    );
    assert!(
        !views_structurally_equal(&kb, &a, &c),
        "a different element does not"
    );

    // …and the same distinction at the KEY, which is what WI-815 made a
    // soundness surface: distinct literals must not share a `GoalKey`.
    let sigma = Substitution::new();
    let ka = goal_fingerprint(&kb, &Value::Node(Rc::clone(&a)), &sigma);
    let kb_ = goal_fingerprint(&kb, &Value::Node(Rc::clone(&b)), &sigma);
    let kc = goal_fingerprint(&kb, &Value::Node(Rc::clone(&c)), &sigma);
    assert_eq!(ka, kb_, "identical literals key identically");
    assert_ne!(ka, kc, "distinct literals key distinctly");
    assert!(ka.is_opaque_free(), "and the key is usable, not degraded");
}

/// PART A — THE BLAST-RADIUS ASSERT the ticket asks for, in WI-814's shape: a
/// fact indexed under the TERM carrier is found by an OCCURRENCE-carrier query,
/// with a negative control that a DIFFERENT literal is not.
///
/// This is the assert that could not even be written before: an `Opaque` head
/// carries no discrimination key, so a set-literal-headed clause could not be
/// stored at all.
#[test]
fn set_literal_cross_carrier_discrim_match() {
    let mut kb = stdlib_kb();
    let domain = kb.intern("test");
    let term = set_term(&mut kb, 1);
    kb.assert_fact(term, ClauseKind::Fact, domain, None);

    let node = Value::Node(set_occ(1));
    assert_eq!(
        kb.browse_program_clauses_matching(&node).len(),
        1,
        "an occurrence-carrier query matches the term-indexed fact",
    );
    let other = Value::Node(set_occ(2));
    assert_eq!(
        kb.browse_program_clauses_matching(&other).len(),
        0,
        "a different literal does not — the candidate set is keyed, not widened",
    );
}

/// PART B — the tuple literal's head mirrors its twin, and ORDER IS IDENTITY.
///
/// The hazard this ticket named for Part B was never in the head: it was
/// `fingerprint_into` sorting named keys past the ORDERED-PRODUCT exemption
/// (WI-788), so `(a: 1, b: 2)` and `(b: 2, a: 1)` shared one key and fact dedup
/// DROPPED one of them. That was fixed under WI-815 and pinned there through the
/// `Value::Entity` carrier — which is how it was reachable, never through
/// `occ_head`. This pins the same property through the carrier WI-1014 opens,
/// so giving `TupleLit` a head does not re-open it.
///
/// CONTROL: revert `fingerprint_into` to sorting unconditionally and the
/// `assert_ne!` fails — the two order-variants collapse to one key.
#[test]
fn tuple_literal_reads_its_twin_and_order_stays_identity() {
    let mut kb = stdlib_kb();
    let f = kb
        .try_resolve_symbol("anthill.reflect.TupleLiteral")
        .unwrap();
    let (a, b) = (kb.intern("acomp"), kb.intern("bcomp"));

    let ab = tuple_occ([(a, 1), (b, 2)]);
    let ba = tuple_occ([(b, 2), (a, 1)]);

    match TermView::head(&ab, &kb) {
        ViewHead::Functor {
            functor,
            pos_arity,
            named_arity,
        } => {
            assert_eq!(functor, Some(f), "the twin's functor");
            assert_eq!((pos_arity, named_arity), (0, 2), "two NAMED components");
        }
        other => panic!("the occurrence must read structurally, got {other:?}"),
    }

    // Head arity and `named_keys` come off the same slice, so they cannot
    // disagree — the WI-814 shape-table discipline, and the WI-815 defect class
    // (a head promising N children and supplying fewer) it exists to prevent.
    let keys = TermView::named_keys(&ab, &kb);
    assert_eq!(
        keys.len(),
        2,
        "named_keys agrees with the head's named_arity"
    );
    assert_eq!(
        keys,
        vec![a, b],
        "in SOURCE order, which is the tuple's identity"
    );
    for k in &keys {
        assert!(
            TermView::named_arg(&ab, &kb, *k).is_some(),
            "every promised key has a child"
        );
    }

    let sigma = Substitution::new();
    assert_ne!(
        goal_fingerprint(&kb, &Value::Node(ab), &sigma),
        goal_fingerprint(&kb, &Value::Node(ba), &sigma),
        "two order-variant tuples are DIFFERENT tuples and must key distinctly",
    );
}

/// BLAST RADIUS, MEASURED rather than argued — the ticket asks for candidate-set
/// counts before and after, and this records what the population actually is.
///
/// The corpus answer is that the population is ZERO on the STORED side and it
/// could not have been anything else: an `Opaque` head carries no discrimination
/// key and `insert_walk` PANICS on one, so no set/tuple-literal-headed clause was
/// ever storable. Candidate sets for existing queries therefore cannot shrink;
/// they can only gain clauses that could not previously exist. What the change
/// really moves is the QUERY side (such a goal was unindexable and read
/// payload-free) and the KEY side (`is_cacheable`'s Opaque exclusion starts
/// admitting these goals).
///
/// This test pins the "cannot shrink" half concretely: a corpus load stores no
/// literal-headed clause, so nothing that used to be found stops being found.
#[test]
fn no_stored_clause_was_ever_literal_headed() {
    let kb = stdlib_kb();
    for name in ["anthill.reflect.SetLiteral", "anthill.reflect.TupleLiteral"] {
        let sym = kb.try_resolve_symbol(name).expect("declared by the stdlib");
        let probe = Value::Entity {
            functor: sym,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        assert_eq!(
            kb.browse_program_clauses_matching(&probe).len(),
            0,
            "{name}-headed clauses are 0 in the corpus — an Opaque head could not \
             be stored, so this change cannot shrink any candidate set",
        );
    }
}

/// THE REGRESSION THIS TICKET WAS ALSO CARRYING, closed and pinned.
///
/// WI-1015 made `project_field` read its receiver's head instead of reifying it.
/// That was right, but it turned this ticket's latent gap into a LIVE defect on
/// the dot path: `field_access` is the desugaring of every `?x.y`, and a
/// `Value::Node(Expr::TupleLit)` receiver used to reify to `Fn{TupleLiteral, …}`
/// and project. With `occ_head` answering `Opaque`, `functor_sym()` was `None`
/// and the projection simply failed. The two view arms above close it.
///
/// CONTROL: with the `Expr::TupleLit` arm removed from `occ_head`, this returns
/// 0 solutions. It passes both before and after WI-1015's `project_field` change
/// BY DESIGN — the point is that the two changes compose, and neither alone is
/// enough.
#[test]
fn a_tuple_literal_occurrence_receiver_projects_its_component() {
    use anthill_core::kb::resolve::ResolveConfig;
    use anthill_core::kb::term::Var;

    let mut kb = stdlib_kb();
    let tl = kb
        .try_resolve_symbol("anthill.reflect.TupleLiteral")
        .unwrap();
    assert!(
        kb.entity_field_names(tl).is_some(),
        "TupleLiteral is a declared entity, so project_field's Dispatch 1 applies",
    );
    // No `register_entity_fields` here on purpose: Dispatch 1 gates on
    // MEMBERSHIP and then matches the receiver's own named keys by local name,
    // so re-registering would only have masked whether the REAL declared
    // `TupleLiteral` reaches the projection.
    let comp = kb.intern("xcomp");

    let r_vid = {
        let n = kb.intern("?r");
        kb.fresh_var(n)
    };
    let recv = tuple_occ([(comp, 42), (kb.intern("ycomp"), 7)]);
    let fa = kb
        .try_resolve_symbol("anthill.reflect.field_access")
        .unwrap();
    let goal = Value::Node(occ(Expr::Apply {
        recv_type: None,
        functor: fa,
        pos_args: vec![
            recv,
            occ(Expr::Const(Literal::String("xcomp".into()))),
            occ(Expr::Var(Var::Global(r_vid))),
        ],
        named_args: Vec::new(),
        type_args: Vec::new(),
    }));

    let sols = kb.resolve_goals(vec![goal], &ResolveConfig::default());
    assert_eq!(
        sols.len(),
        1,
        "a tuple-literal occurrence receiver projects again"
    );
    assert!(
        matches!(sols[0].subst.resolve_as_value(r_vid), Some(Value::Node(_))),
        "and the component comes back in its own carrier",
    );
}

/// THE CASE THE FIRST VERSION OF THIS TICKET MISSED: a POSITIONAL tuple literal.
///
/// `(x, y)` has no labels in source, and the parser gives it some: it labels
/// every positional `_N` and emits `pos_args: []` — which `reflect.anthill`
/// states as THE representation, "(x, y) is represented as TupleLiteral(_1: x,
/// _2: y)". The first Part B arm mirrored `occ_build_fn` instead, which passed
/// positionals through, so a positional tuple literal viewed as
/// `Functor{TupleLiteral, 2, 0}` against a term twin of
/// `Functor{TupleLiteral, 0, 2}` — the WI-425 disagreement this ticket removes,
/// reintroduced inside its own fix. Both the reifier and the view now follow the
/// parser.
///
/// It went unnoticed because `tuple_occ` above builds `positional: Vec::new()` —
/// only NAMED components. A case a test cannot reach is a case it cannot pin,
/// which is why this drives the positional spelling explicitly.
///
/// CONTROL: with either side reverted to the positional shape, the arity assert
/// fails (`(2, 0)` vs `(0, 2)`) and the cross-carrier equality below fails with
/// it.
#[test]
fn a_positional_tuple_literal_agrees_with_the_parsers_term() {
    let mut kb = stdlib_kb();
    let f = kb
        .try_resolve_symbol("anthill.reflect.TupleLiteral")
        .unwrap();

    let node = occ(Expr::TupleLit {
        positional: vec![int_occ(1), int_occ(2)],
        named: Vec::new(),
    });

    match TermView::head(&node, &kb) {
        ViewHead::Functor {
            functor,
            pos_arity,
            named_arity,
        } => {
            assert_eq!(functor, Some(f));
            assert_eq!(
                (pos_arity, named_arity),
                (0, 2),
                "ALL-NAMED: the parser labels positionals `_N` and emits no pos_args",
            );
        }
        other => panic!("must read structurally, got {other:?}"),
    }

    // The keys are `_1` / `_2`, and each promised key has its component.
    let keys = TermView::named_keys(&node, &kb);
    let names: Vec<&str> = keys.iter().map(|k| kb.local_name_of(*k)).collect();
    assert_eq!(names, vec!["_1", "_2"], "one-based `_N` labels (WI-790)");
    for (i, k) in keys.iter().enumerate() {
        let child = TermView::named_arg(&node, &kb, *k).expect("every promised key has a child");
        assert!(
            matches!(child.to_value().head(&kb), ViewHead::Const(Literal::Int(n)) if n == i as i64 + 1),
            "`_{}` is the {}th component",
            i + 1,
            i + 1,
        );
    }

    // The whole point: the same source, through the two carriers, is ONE value.
    // Built as the PARSER builds it — all named, `_N` labels, no pos_args.
    let (k1, k2) = (kb.intern("_1"), kb.intern("_2"));
    let (e1, e2) = (
        kb.alloc(Term::Const(Literal::Int(1))),
        kb.alloc(Term::Const(Literal::Int(2))),
    );
    let term = kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(k1, e1), (k2, e2)]),
    });
    assert!(
        views_structurally_equal(&kb, &term, &node),
        "the occurrence and the parser's term for one source are equal",
    );
    let sigma = Substitution::new();
    assert_eq!(
        goal_fingerprint(&kb, &Value::term(term), &sigma),
        goal_fingerprint(&kb, &Value::Node(node), &sigma),
        "…and key identically, which is what makes a cross-carrier match sound",
    );
}
