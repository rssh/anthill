//! WI-819: ONE type-annotation channel, and it is on the PATTERN.
//!
//! `Expr::Let.type_annotation` is gone. A `let p: T = …` annotation now rides
//! the pattern occurrence's `type_ann`, the same slot the WI-517 binder channel
//! (`lambda (x: T) -> …`) already used — so `let`, `lambda` and match branches
//! annotate uniformly, and there is one reader (`extract_pattern_type_ann`)
//! instead of two.
//!
//! WHY IT WAS NOT MERELY UNTIDY. `type_ann` used to be declared on
//! `Pattern::Var` ALONE, so `let x: T` had somewhere to land and
//! `let (a, b): T` did not — the same syntax landing in different slots
//! depending on the pattern's SHAPE, which is not something the author chose.
//! The second slot then drifted: WI-342 T8 dropped the term-side `type_name`
//! and WI-814 finished the deletion, leaving the outer annotation on NEITHER
//! carrier. With `Expr::Let` reading as a structural `Functor{let_expr, 0, 3}`
//! and no `StructToken::Opaque` left to make the key uncacheable,
//! `let x: Int64 = 1` and `let x: String = 1` compared EQUAL, produced the SAME
//! `GoalKey`, and that key was CACHEABLE — the resolver's per-query cache and
//! `seen_goals` treated two different programs as one.
//!
//! THE RULE CHOSEN for patterns that bind nothing: EVERY pattern may be
//! annotated. The slot hangs on the pattern OCCURRENCE rather than on any
//! variant, so "which variants get it" is dissolved rather than answered —
//! there is no variant to exclude. `let _: T = e` asserts the value's type and
//! binds nothing (and the grammar already admits it); `let 5: Int64 = e` is odd
//! but harmless. `non_binding_patterns_annotate_and_are_enforced` drives both.

use std::rc::Rc;

use anthill_core::eval::value::Value;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{self, Expr, NodeOccurrence, Pattern};
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::term_view::{goal_fingerprint, views_structurally_equal};
use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::span::{SourceId, SourceSpan};

/// Load the stdlib plus `extras`, returning either the KB or the load errors.
/// `ParsedFile` is not publicly nameable, so the parse list is built inline —
/// the same shape every other loader-driven test in this suite uses.
fn load_with(extras: &[&str]) -> Result<KnowledgeBase, Vec<String>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    // FOOTGUN, paid for once already: `anthill run` MUTES load errors, so the
    // loader's verdict is taken from `load_all` directly.
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => Ok(kb),
        Err(errs) => Err(errs.iter().map(|e| e.to_string()).collect()),
    }
}

/// The KB for sources that are meant to load clean; panics WITH the errors.
fn load_ok(extras: &[&str]) -> KnowledgeBase {
    load_with(extras).unwrap_or_else(|errs| panic!("expected a clean load, got: {errs:?}"))
}

/// The load errors for sources that are meant to be rejected.
fn load_errors(extras: &[&str]) -> Vec<String> {
    load_with(extras).err().unwrap_or_default()
}

/// The `Expr::Let` occurrence at the root of operation `qn`'s body.
fn let_body(kb: &KnowledgeBase, qn: &str) -> Rc<NodeOccurrence> {
    let sym = kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("op {qn} not resolved"));
    let node = kb.op_body_node(sym).unwrap_or_else(|| panic!("op {qn} has no body node"));
    assert!(
        matches!(node.as_expr(), Some(Expr::Let { .. })),
        "{qn}'s body root must be a `let`, got {:?}",
        node.as_expr(),
    );
    Rc::clone(node)
}

/// The pattern occurrence of a `let` occurrence.
fn let_pattern(occ: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
    match occ.as_expr() {
        Some(Expr::Let { pattern, .. }) => Rc::clone(pattern),
        other => panic!("not a let: {other:?}"),
    }
}

// ── The headline defect, driven from source ─────────────────────

/// Two `let`s that differ in their ANNOTATION AND NOTHING ELSE — same binder,
/// same value, same body. That is the whole point: a pair differing in its value
/// or body would compare unequal for a reason that has nothing to do with the
/// annotation, and the test would pass with the annotation still invisible.
/// MEASURED — the first draft of this test used `= 1` / `= "s"` and stayed green
/// with the view deliberately blinded to `type_ann`.
///
/// `none()` is what makes identical values possible: it inhabits `Option[T]` at
/// every `T`, so both annotations are satisfiable by the same expression.
const TWO_LETS: &str = r#"
namespace wi819.keys
  import anthill.prelude.{Int64, String, Option}
  operation as_int() -> Int64
    = let x: Option[T = Int64] = none()
      1
  operation as_str() -> Int64
    = let x: Option[T = String] = none()
      1
end
"#;

/// ACCEPTANCE: two `let`s differing ONLY in their annotation are NOT
/// structurally equal and do NOT share a `GoalKey`.
///
/// This is the WI-814-measured conflation, and it disappears without restoring
/// anything: the annotation rides the pattern child, which BOTH carriers
/// already expose (`pattern_to_term` writes it, `pattern_shape` reads it), so
/// the view distinguishes the two lets without gaining a key its term twin
/// lacks — a cross-carrier divergence would itself be a wrong answer (WI-425).
///
/// HAND-BUILT, and the reason is worth recording because two drafts of this test
/// were VACUOUS before it was found. A loader-driven pair cannot isolate the
/// annotation: WI-550 mints every binder's Symbol per SOURCE SITE, so two `let`s
/// written in two operations differ in their binder name no matter what, and the
/// pair compares unequal whether or not the annotation is visible. (Draft 1 also
/// differed in its VALUE. Both drafts stayed GREEN with `pattern_shape`
/// deliberately blinded to `type_ann` — the control that caught them, and which
/// this version fails as it must.) What the loader actually does is pinned
/// separately, by `the_annotation_rides_the_pattern_term_not_the_let_term` and
/// `every_pattern_shape_annotates_through_one_channel`.
#[test]
fn let_annotation_separates_structural_equality_and_goal_keys() {
    let mut kb = load_ok(&[]);
    let span = SourceSpan::new(SourceId::from_raw(0), 0, 0);
    let x = kb.intern("x#1");
    let int64 = kb.try_resolve_symbol("anthill.prelude.Int64").unwrap();
    let string = kb.try_resolve_symbol("anthill.prelude.String").unwrap();

    // One binder, one value, one body — only the annotation varies.
    let mk = |ann: Option<Symbol>| {
        let pattern = NodeOccurrence::new_pattern_annotated(
            Pattern::Var { name: x },
            ann.map(|a| NodeOccurrence::new_expr(Expr::Ref(a), span, None)),
            span,
            None,
        );
        Value::Node(NodeOccurrence::new_expr(
            Expr::Let {
                pattern,
                value: NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None),
                body: NodeOccurrence::new_expr(Expr::VarRef { name: x }, span, None),
            },
            span,
            None,
        ))
    };
    let as_int = mk(Some(int64));
    let as_str = mk(Some(string));
    let bare = mk(None);

    // Positive control: the comparison DOES report equality when it should.
    // Without it, "not equal" is consistent with a comparison that always says
    // no — which is exactly what `Opaque` used to do.
    assert!(
        views_structurally_equal(&kb, &as_int, &mk(Some(int64))),
        "control: two lets with the SAME annotation must compare equal",
    );
    assert!(
        !views_structurally_equal(&kb, &as_int, &as_str),
        "`let x: Int64 = 1` and `let x: String = 1` must not compare equal",
    );
    assert!(
        !views_structurally_equal(&kb, &as_int, &bare),
        "an annotated and an unannotated let must not compare equal either",
    );

    let subst = Substitution::new();
    let k_int = goal_fingerprint(&kb, &as_int, &subst);
    let k_str = goal_fingerprint(&kb, &as_str, &subst);
    let k_bare = goal_fingerprint(&kb, &bare, &subst);
    assert_eq!(
        k_int,
        goal_fingerprint(&kb, &mk(Some(int64)), &subst),
        "control: identical goals still key identically — dedup is preserved, not broken",
    );
    assert_ne!(
        k_int, k_str,
        "the annotation must reach `goal_fingerprint`; equal keys let the query cache \
         and `seen_goals` treat two different programs as one",
    );
    assert_ne!(k_int, k_bare, "an absent annotation is not the same goal as a present one");

    // CROSS-CARRIER, checked at the PATTERN — which is where the annotation
    // lives, and the only level at which both carriers can be compared here
    // (`occurrence_to_term` has no arm for a control-flow `let`; a `let_expr`
    // term is built by the loader, and wi814 pins that isomorphism).
    let pat_of = |v: &Value| match v {
        Value::Node(o) => match o.as_expr() {
            Some(Expr::Let { pattern, .. }) => Rc::clone(pattern),
            _ => unreachable!(),
        },
        _ => unreachable!(),
    };
    let (p_int, p_str) = (pat_of(&as_int), pat_of(&as_str));
    let (t_int, t_str) = (
        node_occurrence::pattern_to_term(&mut kb, &p_int),
        node_occurrence::pattern_to_term(&mut kb, &p_str),
    );
    assert_ne!(t_int, t_str, "the pattern TERMS must differ — the annotation reaches that carrier");
    assert_eq!(
        goal_fingerprint(&kb, &anthill_core::kb::term_view::TermIdView(t_int), &subst),
        goal_fingerprint(&kb, &Value::Node(p_int), &subst),
        "term and occurrence carriers must produce the same GoalKey for the pattern",
    );
}

/// The LOADER really does attach the annotation, and it distinguishes two lets
/// written with different types — the half `let_annotation_separates_…` cannot
/// show, since binder gensym confounds a source-driven identity comparison.
/// Compared at the pattern's TERM twin, which is where the annotation had to
/// reach for the `GoalKey` above to differ.
#[test]
fn the_loader_attaches_distinct_annotations_to_distinct_lets() {
    let mut kb = load_ok(&[TWO_LETS]);
    let ann_of = |kb: &mut KnowledgeBase, op: &str| -> anthill_core::kb::term::TermId {
        let pattern = let_pattern(&let_body(kb, op));
        let twin = node_occurrence::pattern_to_term(kb, &pattern);
        let Term::Fn { named_args, .. } = kb.get_term(twin).clone() else {
            panic!("{op}: pattern twin should be a Fn")
        };
        named_args
            .iter()
            .find(|(k, _)| kb.resolve_sym(*k) == "type_ann")
            .unwrap_or_else(|| panic!("{op}: pattern twin carries no `type_ann`"))
            .1
    };
    let a = ann_of(&mut kb, "wi819.keys.as_int");
    let b = ann_of(&mut kb, "wi819.keys.as_str");
    assert_ne!(
        a, b,
        "`Option[T = Int64]` and `Option[T = String]` must lower to different \
         annotations on the pattern term — equal ones would mean the loader wrote \
         something that does not depend on what was written",
    );
}

/// The annotation reaches the TERM carrier too — which is what makes the key
/// above differ, and what WI-342 T8 / WI-814 had left with no carrier at all.
///
/// Checked at the pattern's twin rather than at `let_expr`: `let_expr` is
/// arity-3 on both carriers and stays that way (no annotation slot regrows on
/// it), so a term-side annotation can only be visible through the pattern child.
#[test]
fn the_annotation_rides_the_pattern_term_not_the_let_term() {
    let mut kb = load_ok(&[TWO_LETS]);
    let pattern = let_pattern(&let_body(&kb, "wi819.keys.as_int"));

    // `let_expr` keeps exactly three keys.
    let let_occ = let_body(&kb, "wi819.keys.as_int");
    let keys: Vec<String> = {
        use anthill_core::kb::term_view::TermView;
        Value::Node(let_occ).named_keys(&kb).iter().map(|s| kb.resolve_sym(*s).to_string()).collect()
    };
    assert_eq!(keys, ["pattern", "value", "body"], "`let_expr` gains no annotation slot");

    // The pattern's term twin carries `type_ann`.
    let twin = node_occurrence::pattern_to_term(&mut kb, &pattern);
    let Term::Fn { named_args, .. } = kb.get_term(twin).clone() else {
        panic!("pattern twin should be a Fn, got {:?}", kb.get_term(twin));
    };
    assert!(
        named_args.iter().any(|(k, _)| kb.resolve_sym(*k) == "type_ann"),
        "the pattern TERM must carry `type_ann`; keys were {:?}",
        named_args.iter().map(|(k, _)| kb.resolve_sym(*k).to_string()).collect::<Vec<_>>(),
    );
}

// ── The shape-dependence is gone ────────────────────────────────

/// ACCEPTANCE: `let (a, b): (Int64, String) = p` annotates through the SAME
/// channel as `let x: Int64 = 1`.
///
/// Before WI-819 the first landed on `Expr::Let.type_annotation` (because a
/// `Pattern::Tuple` had no slot) and the second on `Pattern::Var.type_ann` —
/// one syntax, two homes, chosen by the pattern's shape. Both now answer
/// `pattern_type_ann()`, and an UNANNOTATED let answers `None`, so the check
/// discriminates rather than being satisfied by everything.
#[test]
fn every_pattern_shape_annotates_through_one_channel() {
    let kb = load_ok(&[r#"
namespace wi819.shapes
  import anthill.prelude.{Int64, String}
  operation scalar() -> Int64
    = let x: Int64 = 1
      x
  operation destructure(p: (a: Int64, b: String)) -> Int64
    = let (a, b): (a: Int64, b: String) = p
      a
  operation unannotated() -> Int64
    = let y = 1
      y
end
"#]);
    for op in ["wi819.shapes.scalar", "wi819.shapes.destructure"] {
        let pattern = let_pattern(&let_body(&kb, op));
        assert!(
            pattern.pattern_type_ann().is_some(),
            "{op}: the annotation must be on the PATTERN, whatever its shape",
        );
    }
    let bare = let_pattern(&let_body(&kb, "wi819.shapes.unannotated"));
    assert!(
        bare.pattern_type_ann().is_none(),
        "control: an unannotated let leaves the slot empty — the check above is not vacuous",
    );
}

/// The annotation on a NON-Var pattern is not merely stored, it is ENFORCED:
/// the value is checked against it. This is the behaviour `let (a, b): T` could
/// not have before, since its annotation had no reader on the pattern side.
#[test]
fn a_tuple_pattern_annotation_is_enforced() {
    let errs = load_errors(&[r#"
namespace wi819.tuple_enforced
  import anthill.prelude.{Int64, String}
  operation bad(p: (a: Int64, b: String)) -> Int64
    = let (a, b): (a: String, b: String) = p
      1
end
"#]);
    assert!(
        errs.iter().any(|e| e.contains("Int64") && e.contains("String")),
        "a tuple-pattern annotation contradicting the value must be rejected; got: {errs:?}",
    );
}

// ── The stated rule for patterns that bind nothing ──────────────

/// THE RULE, exercised: a pattern that binds NOTHING may still be annotated,
/// and the annotation still constrains the value. `let _: T = e` asserts the
/// value's type; that is the whole content of the statement.
#[test]
fn non_binding_patterns_annotate_and_are_enforced() {
    let kb = load_ok(&[r#"
namespace wi819.wildcard
  import anthill.prelude.Int64
  operation f() -> Int64
    = let _: Int64 = 1
      2
end
"#]);
    let pattern = let_pattern(&let_body(&kb, "wi819.wildcard.f"));
    assert!(
        matches!(pattern.as_pattern(), Some(Pattern::Wildcard)),
        "the pattern is a wildcard, which binds nothing",
    );
    assert!(
        pattern.pattern_type_ann().is_some(),
        "a wildcard may be annotated — the slot is on the occurrence, so no variant is excluded",
    );

    let errs = load_errors(&[r#"
namespace wi819.wildcard_bad
  import anthill.prelude.{Int64, String}
  operation f() -> Int64
    = let _: String = 1
      2
end
"#]);
    assert!(
        errs.iter().any(|e| e.contains("String") && e.contains("Int64")),
        "`let _: String = 1` asserts a false type and must be rejected FOR THAT REASON, \
         not merely stored; got: {errs:?}",
    );
}

/// An UNANNOTATED `wildcard` keeps its nullary term form, even though the
/// reflect entity now DECLARES a `type_ann` field.
///
/// This is the one thing the reflect-surface change could have broken silently.
/// `KnowledgeBase::alloc`'s WI-511 flip stores a nullary constructor application
/// as the bare `Ref(c)` so `Fn{c}` and `Ref(c)` share one TermId, and WI-436's
/// `functor_view_head` relies on that to head a wildcard the same way on both
/// carriers. The flip keys on the ACTUAL args being empty, not on the
/// declaration — which is exactly why declaring the field is safe, and why
/// omitting the key when there is no annotation (rather than carrying `none()`)
/// was the encoding chosen.
#[test]
fn an_unannotated_wildcard_stays_nullary() {
    let mut kb = load_ok(&[]);
    let span = SourceSpan::new(SourceId::from_raw(0), 0, 0);

    let bare = NodeOccurrence::new_pattern(Pattern::Wildcard, span, None);
    let twin = node_occurrence::pattern_to_term(&mut kb, &bare);
    assert!(
        matches!(kb.get_term(twin), Term::Ref(_)),
        "an unannotated wildcard must stay the bare `Ref` form, got {:?}",
        kb.get_term(twin),
    );

    // ...and an ANNOTATED one becomes an applied `Fn`, which is the honest
    // representation of a wildcard that carries something.
    let int64 = kb.try_resolve_symbol("anthill.prelude.Int64").unwrap();
    let annotated = NodeOccurrence::new_pattern_annotated(
        Pattern::Wildcard,
        Some(NodeOccurrence::new_expr(Expr::Ref(int64), span, None)),
        span,
        None,
    );
    let ann_twin = node_occurrence::pattern_to_term(&mut kb, &annotated);
    assert!(
        matches!(kb.get_term(ann_twin), Term::Fn { .. }),
        "an annotated wildcard carries a `type_ann` arg, got {:?}",
        kb.get_term(ann_twin),
    );
    assert_ne!(twin, ann_twin, "the two must not hash-cons to one term");
}

/// Both spellings of the annotation name the SAME slot when the parenthesized
/// typed binder IS the whole pattern, so writing both is a contradiction with
/// nowhere to put the loser. Loud, because before WI-819 the outer one silently
/// won and the inner was dropped without a word.
#[test]
fn annotating_one_pattern_twice_is_a_loud_error() {
    let errs = load_errors(&[r#"
namespace wi819.twice
  import anthill.prelude.{Int64, String}
  operation f() -> Int64
    = let (x: Int64): String = 1
      x
end
"#]);
    assert!(
        errs.iter().any(|e| e.contains("annotated twice")),
        "`let (x: T1): T2` writes two types into one slot and must say so; got: {errs:?}",
    );
    // LOCATED, not just loud. A `LoadError::Other` carries no span and renders
    // with no `line:col` at all; WI-745 made file identity part of every load
    // error's contract, and this one is user-reachable.
    assert!(
        errs.iter().any(|e| e.contains("annotated twice") && e.contains(':')
            && e.split(':').next().is_some_and(|h| h.chars().all(|c| c.is_ascii_digit()))),
        "the diagnostic must carry a line:col location; got: {errs:?}",
    );
}

// ── WI-803's remaining gap, closed on the same arms ─────────────

/// WI-803 recorded `Pattern::Tuple.labels` as "KNOWN LOSSY AND UNCOVERED":
/// `pattern_to_term` dropped them because the reflect surface had nowhere to
/// put them, so a pattern lowered after typing and rebuilt came back label-less
/// and silently reverted to reading its components BY SLOT — the WI-788 wrong
/// answer on a permuted value. `tuple_pattern` now declares `labels`, emitted
/// only when non-empty, and the round trip preserves them.
#[test]
fn tuple_pattern_labels_survive_the_term_round_trip() {
    let mut kb = load_ok(&[]);
    let span = SourceSpan::new(SourceId::from_raw(0), 0, 0);
    let (a, b) = (kb.intern("a"), kb.intern("b"));
    let sub = |n| NodeOccurrence::new_pattern(Pattern::Var { name: n }, span, None);

    let labelled = NodeOccurrence::new_pattern(
        Pattern::Tuple { positional: vec![sub(a), sub(b)], labels: vec![b, a] },
        span,
        None,
    );
    let twin = node_occurrence::pattern_to_term(&mut kb, &labelled);
    let back = node_occurrence::term_to_param_occurrence(&kb, twin, span);
    match back.as_pattern() {
        Some(Pattern::Tuple { labels, .. }) => assert_eq!(
            labels,
            &vec![b, a],
            "labels must survive; dropping them reverts the matcher to reading BY SLOT",
        ),
        other => panic!("expected a tuple pattern back, got {other:?}"),
    }

    // An UNLABELLED tuple pattern's term is unchanged — `labels` is omitted when
    // empty, exactly as `constructor_pattern.named` is, so nothing that used to
    // key one way starts keying another.
    let bare = NodeOccurrence::new_pattern(
        Pattern::Tuple { positional: vec![sub(a), sub(b)], labels: Vec::new() },
        span,
        None,
    );
    let bare_twin = node_occurrence::pattern_to_term(&mut kb, &bare);
    let Term::Fn { named_args, .. } = kb.get_term(bare_twin).clone() else {
        panic!("tuple twin should be a Fn");
    };
    assert_eq!(
        named_args.iter().map(|(k, _)| kb.resolve_sym(*k).to_string()).collect::<Vec<_>>(),
        ["elements"],
        "an unlabelled, unannotated tuple pattern keeps its one-key term shape",
    );
}

#[test]
fn wi819_spec_claim_subbinder_annotation_coexists() {
    // SPEC CLAIM under test: "A per-element binder annotation inside a
    // destructuring is a different slot on a different (sub-)pattern, so
    // `let (a: A, b): T = …` is fine."
    let errs = load_errors(&[r#"
namespace wi819.spec_subbinder
  import anthill.prelude.{Int64, String}
  operation f(p: (a: Int64, b: String)) -> Int64
    = let (a: Int64, b): (a: Int64, b: String) = p
      a
end
"#]);
    assert!(errs.is_empty(), "sub-binder + whole-pattern annotation must coexist; got: {errs:?}");
}
