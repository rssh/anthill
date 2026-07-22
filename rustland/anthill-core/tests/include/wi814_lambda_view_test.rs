//! WI-814: an `Expr::Lambda` occurrence — and the Pattern-kind occurrence it
//! binds — read through `TermView` as the term twin the loader emits for the
//! same source, instead of collapsing to `ViewHead::Opaque`.
//!
//! `LoadBuildFrame::Lambda` (load.rs) allocs `Fn{Expr.lambda_expr, param, body}`
//! ALONGSIDE the occurrence it builds from the same parse node, so the twin
//! already existed; only the occurrence carrier read `Opaque`. Same for the
//! param: `try_occurrence_to_term` has routed a Pattern to `pattern_to_term`
//! all along, so the `TermId` carrier of a pattern was structural while the
//! occurrence carrier was not.
//!
//! `Opaque` has no `(Opaque, Opaque)` arm, so as an IDENTITY test
//! `views_structurally_equal` returned false for two lambdas — including a
//! lambda and itself. That is what blocked WI-762's receiver-divergence guard
//! (`typing.rs`), which the `wi762_projection_provenance_test` companion pins.
//!
//! Acceptance (ticket): the isomorphism holds; two occurrences of ONE source
//! lambda compare equal and two distinct source lambdas do not; the effect on
//! discrim candidate sets and `GoalKey` dedup is measured.

use std::rc::Rc;

use anthill_core::eval::value::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence, Pattern};
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::term_view::{goal_fingerprint, views_structurally_equal, TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::span::{SourceId, SourceSpan};
use smallvec::SmallVec;

/// A KB with the full stdlib loaded — every reflect / prelude symbol the
/// lambda_expr and Pattern encodings use is resolved, as in any loader-built KB.
fn stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib loads");
    kb
}

fn span() -> SourceSpan {
    SourceSpan::new(SourceId::from_raw(0), 0, 0)
}

fn occ(expr: Expr) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(expr, span(), None)
}

fn pat(p: Pattern) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_pattern(p, span(), None)
}

fn fn_term(kb: &mut KnowledgeBase, functor: Symbol, named: &[(Symbol, TermId)]) -> TermId {
    kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(named),
    })
}

/// The TERM twin for `lambda b -> b`, built exactly as the loader does:
/// `LoadBuildFrame::Lambda` → `Fn{lambda_expr, param: <pattern_to_term>,
/// body: <var_ref>}`, the param through `pattern_to_term`'s `Var` arm
/// (`var_pattern(name: Ref(b), type_ann: none())`).
fn lambda_term(kb: &mut KnowledgeBase, binder: Symbol) -> TermId {
    let lambda = kb.try_resolve_symbol("anthill.reflect.Expr.lambda_expr").unwrap();
    let var_pattern = kb.try_resolve_symbol("anthill.reflect.Pattern.var_pattern").unwrap();
    let var_ref = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref").unwrap();
    let none = kb.try_resolve_symbol("anthill.prelude.Option.none").unwrap();
    let (k_param, k_body) = (kb.intern("param"), kb.intern("body"));
    let (k_name, k_type_ann) = (kb.intern("name"), kb.intern("type_ann"));

    let name_ref = kb.alloc(Term::Ref(binder));
    let none_t = fn_term(kb, none, &[]);
    let param = fn_term(kb, var_pattern, &[(k_name, name_ref), (k_type_ann, none_t)]);
    let body_name = kb.alloc(Term::Ref(binder));
    let body = fn_term(kb, var_ref, &[(k_name, body_name)]);
    fn_term(kb, lambda, &[(k_param, param), (k_body, body)])
}

/// The OCCURRENCE for the same `lambda b -> b`, as
/// `node_occurrence::BuildFrame::Lambda` builds it.
fn lambda_occ(binder: Symbol) -> Rc<NodeOccurrence> {
    occ(Expr::Lambda {
        param: pat(Pattern::Var { name: binder, type_ann: None }),
        body: occ(Expr::VarRef { name: binder }),
    })
}

#[test]
fn lambda_view_is_isomorphic_to_term_twin() {
    let mut kb = stdlib_kb();
    let b = kb.intern("b#1");
    let term = lambda_term(&mut kb, b);
    let node = Value::Node(lambda_occ(b));

    match (node.head(&kb), term.head(&kb)) {
        (
            ViewHead::Functor { functor: fa, pos_arity: pa, named_arity: na },
            ViewHead::Functor { functor: fb, pos_arity: pb, named_arity: nb },
        ) => {
            assert_eq!(fa, fb, "same lambda_expr functor");
            assert_eq!((pa, na), (0, 2), "occurrence head is arity-2 named");
            assert_eq!((pb, nb), (0, 2), "term head is arity-2 named");
        }
        (a, b) => panic!("non-functor head: occ={a:?} term={b:?}"),
    }

    // Identical named keys, in the same order — the discrim walk descends in
    // `named_keys` order, so order divergence alone would desync the walk.
    assert_eq!(node.named_keys(&kb), term.named_keys(&kb), "`param`, `body` in builder order");

    // The `param` child is the Pattern-kind occurrence, and it too must read as
    // its own twin — a `Functor` head over an `Opaque` child would make the
    // `named_keys` loop below compare nothing.
    let (occ_param, term_param) = (
        node.named_arg(&kb, kb.lookup_symbol("param").unwrap()).expect("occ param"),
        term.named_arg(&kb, kb.lookup_symbol("param").unwrap()).expect("term param"),
    );
    assert!(
        matches!(occ_param.head(&kb), ViewHead::Functor { named_arity: 2, .. }),
        "param reads as var_pattern(name, type_ann), not Opaque: {:?}",
        occ_param.head(&kb),
    );
    assert!(views_structurally_equal(&kb, &occ_param, &term_param), "param ≡ its twin");

    assert!(views_structurally_equal(&kb, &node, &term), "occurrence ≡ term through TermView");
    assert!(views_structurally_equal(&kb, &term, &node), "term ≡ occurrence through TermView");
}

/// Every `Pattern` variant reads as its `pattern_to_term` twin's head — the
/// arms are reachable only through a lambda's `param`, so a variant left
/// `Opaque` would silently make any lambda binding it compare unequal.
#[test]
fn every_pattern_variant_has_a_structural_head() {
    let mut kb = stdlib_kb();
    let (x, c) = (kb.intern("x#1"), kb.intern("C"));
    let sub = || pat(Pattern::Wildcard);

    let cases: Vec<(&str, Rc<NodeOccurrence>, usize)> = vec![
        ("var", pat(Pattern::Var { name: x, type_ann: None }), 2),
        ("literal", pat(Pattern::Literal { value: Literal::Int(1) }), 1),
        ("constructor", pat(Pattern::Constructor {
            name: c,
            pos_args: vec![sub()],
            named_args: Vec::new(),
        }), 2),
        // WI-445: the `named` key appears only when non-empty, exactly as
        // `pattern_to_term` omits it.
        ("constructor+named", pat(Pattern::Constructor {
            name: c,
            pos_args: Vec::new(),
            named_args: vec![(x, sub())],
        }), 3),
        ("tuple", pat(Pattern::Tuple { positional: vec![sub()], labels: Vec::new() }), 1),
    ];
    for (label, p, arity) in cases {
        match p.head(&kb) {
            ViewHead::Functor { named_arity, pos_arity, .. } => {
                assert_eq!((pos_arity, named_arity), (0, arity), "{label} arity");
            }
            other => panic!("{label} pattern head is not a Functor: {other:?}"),
        }
        assert_eq!(p.named_keys(&kb).len(), arity, "{label}: named_keys agrees with named_arity");
        for k in p.named_keys(&kb) {
            assert!(p.named_arg(&kb, k).is_some(), "{label}: key {k:?} has a child");
        }
    }

    // `wildcard` is nullary, so BOTH carriers canonicalize it to `Ref` through
    // `functor_view_head` (WI-436) rather than a 0-arity `Functor`.
    let wild = pat(Pattern::Wildcard);
    let wild_sym = kb.try_resolve_symbol("anthill.reflect.Pattern.wildcard").unwrap();
    let wild_term = fn_term(&mut kb, wild_sym, &[]);
    assert!(views_structurally_equal(&kb, &wild, &wild_term), "wildcard ≡ its nullary twin");
}

/// The WI-762 question, in the small: ONE source lambda duplicated (the N copies
/// `convert.rs`'s distribute-dot makes of one receiver share the parse node,
/// hence WI-550's per-parse-node binder gensym) compares EQUAL, and two
/// independently-written lambdas — distinct gensyms — compare UNEQUAL.
///
/// This pins that the view is SYNTACTIC, not alpha-aware: `lambda x -> x` and
/// `lambda y -> y` are alpha-equivalent and still compare unequal, because the
/// term twin they must agree with is compared by structure, not up to alpha.
#[test]
fn one_source_lambda_equal_two_distinct_sources_not() {
    let mut kb = stdlib_kb();
    // WI-550 mints a binder symbol per PARSE NODE, so two copies of one source
    // lambda carry the same gensym and two written lambdas carry different ones.
    let shared = kb.intern("c#7");
    let other = kb.intern("c#8");

    let copy_a = Value::Node(lambda_occ(shared));
    let copy_b = Value::Node(lambda_occ(shared));
    assert!(
        views_structurally_equal(&kb, &copy_a, &copy_b),
        "two occurrences of ONE source lambda are structurally equal",
    );
    // Self-comparison: `Opaque` used to answer false even here.
    assert!(views_structurally_equal(&kb, &copy_a, &copy_a), "a lambda equals itself");

    let distinct = Value::Node(lambda_occ(other));
    assert!(
        !views_structurally_equal(&kb, &copy_a, &distinct),
        "two distinct source lambdas (distinct binder gensyms) are NOT equal",
    );

    // Divergence in the BODY is caught too — the walk descends under the binder.
    let same_binder_other_body = Value::Node(occ(Expr::Lambda {
        param: pat(Pattern::Var { name: shared, type_ann: None }),
        body: occ(Expr::Const(Literal::Int(0))),
    }));
    assert!(
        !views_structurally_equal(&kb, &copy_a, &same_binder_other_body),
        "same binder, different body is NOT equal",
    );
}

/// Cross-carrier: a lambda-bearing fact indexed under the TERM carrier is found
/// by a query in the OCCURRENCE carrier, and vice versa. This is the property
/// `Opaque` could not have — an opaque head carries no discrimination key at
/// all, so the fact was unreachable through the occurrence carrier.
#[test]
fn lambda_cross_carrier_discrim_match() {
    let mut kb = stdlib_kb();
    let fact_sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("test");
    let b = kb.intern("b#1");
    let term = lambda_term(&mut kb, b);
    kb.assert_fact(term, fact_sort, domain, None);

    let node = Value::Node(lambda_occ(b));
    assert_eq!(kb.query_view(&node).len(), 1, "occurrence query matches the term-indexed fact");

    // Precision: a different binder must NOT match — the candidate set really is
    // keyed on the lambda's structure, not merely widened.
    let other_b = kb.intern("b#2");
    let other = Value::Node(lambda_occ(other_b));
    assert_eq!(kb.query_view(&other).len(), 0, "a different binder does not match");

    assert!(kb.match_view(term, &node).is_some(), "term pattern matches the occurrence target");
}

/// The other reflect-WRAPPED control-flow forms read as their loader twins too:
/// `if_expr(cond, then_branch, else_branch)`, `let_expr(pattern, value, body)`
/// and `match_expr(scrutinee, branches)`. None of these was protected — `If`
/// binds nothing at all, and is structurally simpler than `DotApply`, which has
/// had a head since WI-278.
///
/// `let_expr` is arity-3: WI-342 T8 deleted the term-side `type_name` slot, so a
/// faithful view must NOT expose `Expr::Let.type_annotation` (a `Value` living
/// only on the occurrence). Exposing it would give the occurrence a key its twin
/// lacks — a cross-carrier key divergence, which is a wrong answer (WI-425).
#[test]
fn control_flow_forms_read_as_their_loader_twins() {
    let mut kb = stdlib_kb();
    let x = kb.intern("x#1");
    let one = || occ(Expr::Const(Literal::Int(1)));

    let if_occ = occ(Expr::If {
        condition: occ(Expr::Const(Literal::Bool(true))),
        then_branch: one(),
        else_branch: one(),
    });
    let let_occ = occ(Expr::Let {
        pattern: pat(Pattern::Var { name: x, type_ann: None }),
        type_annotation: None,
        value: one(),
        body: occ(Expr::VarRef { name: x }),
    });
    let match_occ = occ(Expr::Match {
        scrutinee: one(),
        branches: vec![anthill_core::kb::node_occurrence::MatchBranch {
            pattern: pat(Pattern::Wildcard),
            guard: None,
            body: one(),
            span: span(),
        }],
    });

    for (label, o, qname, keys) in [
        ("if", &if_occ, "anthill.reflect.Expr.if_expr",
         &["cond", "then_branch", "else_branch"][..]),
        ("let", &let_occ, "anthill.reflect.Expr.let_expr", &["pattern", "value", "body"][..]),
        ("match", &match_occ, "anthill.reflect.Expr.match_expr", &["scrutinee", "branches"][..]),
    ] {
        let expected_functor = kb.try_resolve_symbol(qname).unwrap();
        match o.head(&kb) {
            ViewHead::Functor { functor: Some(f), pos_arity, named_arity } => {
                assert_eq!(f, expected_functor, "{label}: twin functor");
                assert_eq!((pos_arity, named_arity), (0, keys.len()), "{label}: arity");
            }
            other => panic!("{label} is not structural: {other:?}"),
        }
        // `named_keys` must agree with `named_arity` IN ORDER — a shorter list
        // would make `views_structurally_equal`'s key loop compare fewer
        // children than the head promises, silently over-matching.
        let got: Vec<String> =
            o.named_keys(&kb).iter().map(|s| kb.resolve_sym(*s).to_string()).collect();
        assert_eq!(got, keys, "{label}: keys in the loader's builder order");
        for k in o.named_keys(&kb) {
            assert!(o.named_arg(&kb, k).is_some(), "{label}: key {k:?} has a child");
        }
    }

    // Structural, not merely non-Opaque: a differing branch is detected.
    let other_if = occ(Expr::If {
        condition: occ(Expr::Const(Literal::Bool(true))),
        then_branch: one(),
        else_branch: occ(Expr::Const(Literal::Int(9))),
    });
    assert!(views_structurally_equal(&kb, &if_occ, &if_occ), "an if equals itself");
    assert!(!views_structurally_equal(&kb, &if_occ, &other_if), "a differing else-branch is unequal");
}

/// `proof_stmt` has CONDITIONAL keys — `strategy` / `conclude` present exactly
/// when the occurrence carries them, mirroring the twin, which pushes those
/// slots conditionally.
///
/// `let_expr` deliberately has NONE. WI-342 deleted the term-side `type_name`
/// slot as write-only and WI-814 finished the job — the reflect field and
/// `visit_fn`'s reader are gone — so no `let_expr` term can carry an
/// annotation and a conditional 4th key would describe a shape that no longer
/// exists. The consequence is pinned below: two `let`s differing only in
/// annotation compare EQUAL through the view, because the term carrier truly
/// does not distinguish them.
#[test]
fn conditional_keys_track_the_occurrence() {
    let mut kb = stdlib_kb();
    let (x, goal) = (kb.intern("x#1"), kb.intern("my_goal"));
    let int64 = kb.try_resolve_symbol("anthill.prelude.Int64").unwrap();
    let one = || occ(Expr::Const(Literal::Int(1)));
    let mk_let = |ann: Option<Value>| {
        occ(Expr::Let {
            pattern: pat(Pattern::Var { name: x, type_ann: None }),
            type_annotation: ann,
            value: one(),
            body: occ(Expr::VarRef { name: x }),
        })
    };

    let bare = mk_let(None);
    let annotated = mk_let(Some(Value::Node(occ(Expr::Ref(int64)))));
    for (label, l) in [("unannotated", &bare), ("annotated", &annotated)] {
        let got: Vec<String> =
            l.named_keys(&kb).iter().map(|s| kb.resolve_sym(*s).to_string()).collect();
        assert_eq!(got, ["pattern", "value", "body"], "{label} let is arity-3");
    }
    assert!(
        views_structurally_equal(&kb, &bare, &annotated),
        "the annotation is absent from the TERM carrier, so the view must not \
         distinguish them — distinguishing would be a cross-carrier miss",
    );
    assert!(
        kb.lookup_symbol("type_name").is_none_or(|k| annotated.named_arg(&kb, k).is_none()),
        "there is no `type_name` child to reach",
    );

    // `proof_stmt`: 2 conditional keys ⇒ 4 shapes, in the loader's order
    // `target, strategy?, body, conclude?`.
    let mk_proof = |strategy: Option<Symbol>, conclude: bool| {
        occ(Expr::Proof {
            target: goal,
            strategy,
            using: Vec::new(),
            conclude: conclude.then(one),
            body: one(),
        })
    };
    let induction = kb.intern("induction");
    for (strategy, conclude, expected) in [
        (None, false, vec!["target", "using", "body"]),
        (Some(induction), false, vec!["target", "strategy", "using", "body"]),
        (None, true, vec!["target", "using", "body", "conclude"]),
        (Some(induction), true, vec!["target", "strategy", "using", "body", "conclude"]),
    ] {
        let p = mk_proof(strategy, conclude);
        let got: Vec<String> =
            p.named_keys(&kb).iter().map(|s| kb.resolve_sym(*s).to_string()).collect();
        assert_eq!(got, expected, "proof_stmt keys track the occurrence's optional slots");
        for k in p.named_keys(&kb) {
            assert!(p.named_arg(&kb, k).is_some(), "proof key {k:?} has a child");
        }
        match p.head(&kb) {
            ViewHead::Functor { named_arity, .. } => {
                assert_eq!(named_arity, expected.len(), "head arity agrees with named_keys");
            }
            other => panic!("proof is not structural: {other:?}"),
        }
    }

    // WI-814: `using` is the PREMISE SET, so it is part of a proof's identity —
    // `proof Y using X` and `proof Y using Z` are different proofs. It had been
    // withheld from the term as "citation metadata, not a child", which made the
    // term an INCOMPLETE representation and silently conflated distinct proofs.
    // Pinned here because the loss was invisible: both shapes have the same
    // arity, so only comparing the cite lists catches it.
    let mk_using = |cites: Vec<Symbol>| {
        occ(Expr::Proof {
            target: goal,
            strategy: None,
            using: cites,
            conclude: None,
            body: one(),
        })
    };
    let (lemma_x, lemma_z) = (kb.intern("lemma_x"), kb.intern("lemma_z"));
    assert!(
        !views_structurally_equal(&kb, &mk_using(vec![lemma_x]), &mk_using(vec![lemma_z])),
        "proofs citing DIFFERENT premises are not equal",
    );
    assert!(
        !views_structurally_equal(&kb, &mk_using(vec![]), &mk_using(vec![lemma_x])),
        "an empty premise set differs from a non-empty one",
    );
    assert!(
        views_structurally_equal(&kb, &mk_using(vec![lemma_x]), &mk_using(vec![lemma_x])),
        "proofs citing the SAME premises are equal",
    );

    // `target` is an `Ident`, not a `Ref` — the twin spells it `Term::Ident`.
    let k_target = kb.lookup_symbol("target").unwrap();
    let plain_proof = mk_proof(None, false);
    let target_child = plain_proof.named_arg(&kb, k_target).expect("target");
    assert!(
        matches!(target_child.head(&kb), ViewHead::Ident(s) if s == goal),
        "proof target reads as Ident (matching `LoadBuildFrame::ProofStmt`), not Ref: {:?}",
        target_child.head(&kb),
    );
}

/// MEASURED, per the ticket's blast-radius clause: `goal_fingerprint` no longer
/// collapses two structurally-distinct lambda-bearing goals to one key, and the
/// key becomes cacheable.
///
/// The direction matters. `StructToken::Opaque` is payload-free, so BEFORE this
/// change two goals differing only inside a lambda produced the SAME `GoalKey`
/// — over-dedup in the resolver's `seen_goals` (the second answer was dropped)
/// — while `is_cacheable` rejected the key outright. Both move the safe way:
/// nothing that used to dedup stops dedupping (identical goals still key
/// identically, asserted below), and goals that used to be conflated separate.
#[test]
fn lambda_goal_keys_separate_and_become_cacheable() {
    let kb = stdlib_kb();
    let subst = Substitution::new();
    let mut kb = kb;
    let (b1, b2) = (kb.intern("b#1"), kb.intern("b#2"));

    let k1 = goal_fingerprint(&kb, &Value::Node(lambda_occ(b1)), &subst);
    let k1_again = goal_fingerprint(&kb, &Value::Node(lambda_occ(b1)), &subst);
    let k2 = goal_fingerprint(&kb, &Value::Node(lambda_occ(b2)), &subst);

    assert_eq!(k1, k1_again, "identical lambda goals still key identically — dedup preserved");
    assert_ne!(k1, k2, "distinct lambdas no longer collapse to one Opaque token");
    assert!(k1.is_cacheable(), "a ground lambda goal is now cacheable (no Opaque leaf)");

    // The term twin fingerprints identically — the carrier really is invisible.
    let term = lambda_term(&mut kb, b1);
    assert_eq!(
        goal_fingerprint(&kb, &anthill_core::kb::term_view::TermIdView(term), &subst),
        k1,
        "term and occurrence carriers produce the same GoalKey",
    );
}

/// The If / Let / Match / Proof arms are ISOMORPHIC to the terms the loader
/// emits — built here by hand, exactly as `LoadBuildFrame::{IfExpr, LetExpr,
/// MatchExpr, ProofStmt}` build them.
///
/// This is the test `control_flow_forms_read_as_their_loader_twins` could not
/// be: that one asserts `named_keys()` against the same literals
/// `expr_wrapped_shape` declares, so it validates the table against ITSELF and
/// would still pass if the table disagreed with the loader. A disagreement is a
/// cross-carrier miss — a fact stored under one carrier unreachable from the
/// other — which is a wrong answer, not a precision loss (WI-425). It matters
/// most for `proof_stmt`, whose loader WI-814 changed to carry `using`.
#[test]
fn control_flow_views_are_isomorphic_to_loader_twins() {
    let mut kb = stdlib_kb();
    // Every symbol resolved UP FRONT: `fn_term` takes `&mut kb`, so a lookup
    // nested in its argument list would be a borrow error.
    let r = |kb: &KnowledgeBase, n: &str| kb.try_resolve_symbol(n).unwrap();
    let (s_if, s_let, s_match, s_proof) = (
        r(&kb, "anthill.reflect.Expr.if_expr"),
        r(&kb, "anthill.reflect.Expr.let_expr"),
        r(&kb, "anthill.reflect.Expr.match_expr"),
        r(&kb, "anthill.reflect.Expr.proof_stmt"),
    );
    let (s_branch, s_varpat, s_wild, s_vref) = (
        r(&kb, "anthill.reflect.MatchBranch"),
        r(&kb, "anthill.reflect.Pattern.var_pattern"),
        r(&kb, "anthill.reflect.Pattern.wildcard"),
        r(&kb, "anthill.reflect.Expr.var_ref"),
    );
    let (cons, nil, none) = (
        r(&kb, "anthill.prelude.List.cons"),
        r(&kb, "anthill.prelude.List.nil"),
        r(&kb, "anthill.prelude.Option.none"),
    );
    let (x, goal, lemma) = (kb.intern("x#9"), kb.intern("my_goal"), kb.intern("lemma_a"));
    let (k_head, k_tail, k_value) = (kb.intern("head"), kb.intern("tail"), kb.intern("value"));
    let (k_cond, k_then, k_else) =
        (kb.intern("cond"), kb.intern("then_branch"), kb.intern("else_branch"));
    let (k_pattern, k_body, k_name, k_type_ann) =
        (kb.intern("pattern"), kb.intern("body"), kb.intern("name"), kb.intern("type_ann"));
    let (k_scrut, k_branches, k_guard) =
        (kb.intern("scrutinee"), kb.intern("branches"), kb.intern("guard"));
    let (k_target, k_using) = (kb.intern("target"), kb.intern("using"));

    let one_t = kb.alloc(Term::Const(Literal::Int(1)));
    let one = || occ(Expr::Const(Literal::Int(1)));
    let nil_t = fn_term(&mut kb, nil, &[]);
    let none_t = fn_term(&mut kb, none, &[]);

    // ── if_expr(cond, then_branch, else_branch) ──
    let tru_t = kb.alloc(Term::Const(Literal::Bool(true)));
    let if_t = fn_term(&mut kb, s_if, &[(k_cond, tru_t), (k_then, one_t), (k_else, one_t)]);
    let if_o = Value::Node(occ(Expr::If {
        condition: occ(Expr::Const(Literal::Bool(true))),
        then_branch: one(),
        else_branch: one(),
    }));

    // ── let_expr(pattern, value, body); pattern via pattern_to_term's Var arm ──
    let x_ref = kb.alloc(Term::Ref(x));
    let var_pat_t = fn_term(&mut kb, s_varpat, &[(k_name, x_ref), (k_type_ann, none_t)]);
    let x_ref2 = kb.alloc(Term::Ref(x));
    let vref_t = fn_term(&mut kb, s_vref, &[(k_name, x_ref2)]);
    let let_t =
        fn_term(&mut kb, s_let, &[(k_pattern, var_pat_t), (k_value, one_t), (k_body, vref_t)]);
    let let_o = Value::Node(occ(Expr::Let {
        pattern: pat(Pattern::Var { name: x, type_ann: None }),
        type_annotation: None,
        value: one(),
        body: occ(Expr::VarRef { name: x }),
    }));

    // ── match_expr(scrutinee, branches: List[MatchBranch(pattern, guard, body)]) ──
    let wild_t = fn_term(&mut kb, s_wild, &[]);
    let branch_t =
        fn_term(&mut kb, s_branch, &[(k_pattern, wild_t), (k_guard, none_t), (k_body, one_t)]);
    let branches_t = fn_term(&mut kb, cons, &[(k_head, branch_t), (k_tail, nil_t)]);
    let match_t = fn_term(&mut kb, s_match, &[(k_scrut, one_t), (k_branches, branches_t)]);
    let match_o = Value::Node(occ(Expr::Match {
        scrutinee: one(),
        branches: vec![anthill_core::kb::node_occurrence::MatchBranch {
            pattern: pat(Pattern::Wildcard),
            guard: None,
            body: one(),
            span: span(),
        }],
    }));

    // ── proof_stmt(target, using, body) — WI-814 put `using` on the term ──
    let target_t = kb.alloc(Term::Ident(goal));
    let lemma_t = kb.alloc(Term::Ident(lemma));
    let using_t = fn_term(&mut kb, cons, &[(k_head, lemma_t), (k_tail, nil_t)]);
    let proof_t =
        fn_term(&mut kb, s_proof, &[(k_target, target_t), (k_using, using_t), (k_body, one_t)]);
    let proof_o = Value::Node(occ(Expr::Proof {
        target: goal,
        strategy: None,
        using: vec![lemma],
        conclude: None,
        body: one(),
    }));

    let _ = k_value;
    for (label, node, term) in [
        ("if_expr", &if_o, if_t),
        ("let_expr", &let_o, let_t),
        ("match_expr", &match_o, match_t),
        ("proof_stmt", &proof_o, proof_t),
    ] {
        assert_eq!(
            node.named_keys(&kb),
            term.named_keys(&kb),
            "{label}: occurrence and loader twin expose the same keys IN THE SAME ORDER \
             (the discrim walk descends in this order)",
        );
        assert!(views_structurally_equal(&kb, node, &term), "{label}: occurrence \u{2261} term");
        assert!(views_structurally_equal(&kb, &term, node), "{label}: term \u{2261} occurrence");
    }
}
