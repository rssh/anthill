//! WI-1013: an `Expr::Apply`'s CALL-SITE TYPE ARGUMENTS (`f[T = Int64](x)`) reach
//! `TermView`, so a `GoalKey` over a call is injective again.
//!
//! `occ_head`'s `Expr::Apply` arm destructured `{ functor, pos_args, named_args, .. }`
//! and the `..` was `type_args`, so `f[T = Int64](x)` and `f[T = String](x)` presented
//! IDENTICAL views. Three consumers inherited it, each with a different failure mode:
//! `goal_fingerprint` (the resolver's `seen_goals` answer-dedup drops the second of two
//! answers differing only in a bracket, and `query_cache` — keyed on the same `GoalKey`
//! — can serve one goal's candidate list for another), `GoalKey::is_opaque_free` (fact
//! dedup then answers TRUE on a key that is not injective, and over-dedup DROPS A FACT
//! rather than merely losing precision), and `views_structurally_equal` (two
//! bracket-distinct occurrences report EQUAL, which is what WI-762's
//! receiver-divergence guard reads).
//!
//! WHAT BACKING WI-1013 OUT DOES, test by test — MEASURED by running this file against
//! the parent commit, not predicted. FAIL: `bracket_distinct_calls_key_apart`,
//! `bracket_distinct_calls_are_unequal` and `bracket_distinct_fact_heads_do_not_over_dedup`
//! (each measures precisely the distinction the `..` erased);
//! `a_bracket_survives_the_term_round_trip` (the twin loses the bracket, so the
//! round-tripped key differs from the occurrence's); `a_written_bracket_reaches_the_view`
//! (the loader path — the occurrence carries the bracket at HEAD too, but the view does
//! not report it); and `a_type_args_argument_beside_a_bracket_still_loads` (at HEAD the
//! head has ONE named child, since the bracket is not one).
//!
//! PASS EITHER WAY, by design — the zero-blast-radius controls, which is what makes the
//! deltas above attributable: `carriers_agree_on_a_bracket_free_call`,
//! `a_bracket_free_call_keys_and_matches_as_before`,
//! `a_type_args_argument_without_a_bracket_has_one_child`, and
//! `the_slot_key_is_not_spellable_as_a_label`.
//!
//! MEASURED BLAST RADIUS over the stdlib corpus (`docs/` note in the ticket): stored
//! clause heads 169 → 169 candidates with 0 self-misses and 1214 → 1214 GoalKey tokens;
//! rule-body atoms 8 → 8 with 46 → 46 tokens; operation-body applies 205 → 205 with 198
//! → 198 distinct keys. The ONLY delta is 1695 → 2353 tokens across the 23
//! `field_access[Name = …]` calls the typer mints — they carry their bracket now.
//! Nothing in the corpus separates as a result, because `field_access` supplies the
//! projected name TWICE (WI-759) and the positional copy already distinguished them.

use std::rc::Rc;

use anthill_core::eval::value::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{self, Expr, NodeOccurrence};
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::term_view::{goal_fingerprint, views_structurally_equal, TermView, ViewHead};
use anthill_core::kb::{ClauseKind, KnowledgeBase};
use anthill_core::parse;
use anthill_core::span::{SourceId, SourceSpan};

/// A KB with the full stdlib loaded — every prelude / reflect symbol the
/// `List[type_arg]` encoding resolves is defined, as in any loader-built KB.
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
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib loads");
    kb
}

fn span() -> SourceSpan {
    SourceSpan::new(SourceId::from_raw(0), 0, 0)
}

/// `f(arg)` with the given call-site type-argument bindings — the occurrence a
/// `f[T = <bound>](arg)` call builds (`node_occurrence::BuildFrame::Apply`).
fn call(
    functor: Symbol,
    arg: Rc<NodeOccurrence>,
    type_args: Vec<(Option<Symbol>, Value)>,
) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(
        Expr::Apply { functor, pos_args: vec![arg], named_args: Vec::new(), type_args },
        span(),
        None,
    )
}

fn ref_occ(s: Symbol) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(Expr::Ref(s), span(), None)
}

/// `(f, x, [T = Int64], [T = String])` on a stdlib KB — one call functor, one
/// argument, and two type-argument lists differing ONLY in the bound type.
fn fixture(kb: &mut KnowledgeBase) -> (Symbol, Rc<NodeOccurrence>, Vec<(Option<Symbol>, Value)>, Vec<(Option<Symbol>, Value)>) {
    let f = kb.intern("wi1013_f");
    let t = kb.intern("T");
    let x = kb.intern("wi1013_x");
    let int64 = Value::term(kb.alloc(Term::Ref(kb.resolve_symbol("anthill.prelude.Int64"))));
    let string = Value::term(kb.alloc(Term::Ref(kb.resolve_symbol("anthill.prelude.String"))));
    (f, ref_occ(x), vec![(Some(t), int64)], vec![(Some(t), string)])
}

/// FAILS when WI-1013 is backed out: with `type_args` dropped from the view, the two
/// calls fingerprint to one key — which is what silently discards the second answer in
/// `seen_goals` and lets `query_cache` serve one goal's candidates for the other.
#[test]
fn bracket_distinct_calls_key_apart() {
    let mut kb = stdlib_kb();
    let (f, x, ta_int, ta_str) = fixture(&mut kb);
    let sigma = Substitution::new();

    let a = Value::Node(call(f, Rc::clone(&x), ta_int));
    let b = Value::Node(call(f, Rc::clone(&x), ta_str));
    let bare = Value::Node(call(f, Rc::clone(&x), Vec::new()));

    let (ka, kb_, kbare) = (
        goal_fingerprint(&kb, &a, &sigma),
        goal_fingerprint(&kb, &b, &sigma),
        goal_fingerprint(&kb, &bare, &sigma),
    );
    assert_ne!(ka, kb_, "two calls differing only in `[T = …]` must key apart");
    assert_ne!(ka, kbare, "a bracketed call must not key as its bracket-less twin");

    // The keys are USABLE as dedup keys — `is_opaque_free` is what fact dedup asks,
    // and a bracket must not degrade a call to an unkeyable head.
    for (k, what) in [(&ka, "[T = Int64]"), (&kb_, "[T = String]")] {
        assert!(k.is_opaque_free(), "the {what} key carries no Opaque token");
    }

    // The head PROMISES the extra child, and `named_keys` supplies it — a head that
    // announced N+1 and listed N is the WI-815 shape defect `fingerprint_into` guards.
    match a.head(&kb) {
        ViewHead::Functor { pos_arity, named_arity, .. } => {
            assert_eq!((pos_arity, named_arity), (1, 1), "one arg + the type_args child");
        }
        other => panic!("expected a Functor head, got {other:?}"),
    }
    assert_eq!(a.named_keys(&kb).len(), 1, "`named_keys` supplies what the head promised");
}

/// FAILS when WI-1013 is backed out: `views_structurally_equal` answers `true`, which
/// is a wrong answer for the identity test WI-762's receiver-divergence guard reads.
#[test]
fn bracket_distinct_calls_are_unequal() {
    let mut kb = stdlib_kb();
    let (f, x, ta_int, ta_str) = fixture(&mut kb);

    let a = Value::Node(call(f, Rc::clone(&x), ta_int.clone()));
    let b = Value::Node(call(f, Rc::clone(&x), ta_str));
    let a2 = Value::Node(call(f, Rc::clone(&x), ta_int));

    assert!(!views_structurally_equal(&kb, &a, &b), "`[T = Int64]` ≠ `[T = String]`");
    assert!(
        views_structurally_equal(&kb, &a, &a2),
        "and the distinction is not a blanket refusal — two calls with the SAME bracket \
         are still equal, so the extra child is compared rather than merely counted"
    );
}

/// FAILS when WI-1013 is backed out: `value_fact_dedup_key` answers one key for both
/// heads, `is_opaque_free` says it may be used, and asserting the second returns the
/// FIRST RuleId — over-dedup DROPS A FACT.
#[test]
fn bracket_distinct_fact_heads_do_not_over_dedup() {
    let mut kb = stdlib_kb();
    let (f, x, ta_int, ta_str) = fixture(&mut kb);
    let domain = kb.intern("wi1013");

    let a = Value::Node(call(f, Rc::clone(&x), ta_int.clone()));
    let b = Value::Node(call(f, Rc::clone(&x), ta_str));
    let a_again = Value::Node(call(f, Rc::clone(&x), ta_int));

    let ra = kb.assert_fact_value(a, ClauseKind::Fact, domain, None);
    let rb = kb.assert_fact_value(b, ClauseKind::Fact, domain, None);
    assert_ne!(ra, rb, "two bracket-distinct fact heads are two facts, not one");

    // The CONTROL for the same mechanism: dedup still works. Re-asserting a
    // structurally identical head collapses, so the assertion above measures
    // injectivity and not a dedup that stopped working.
    let ra2 = kb.assert_fact_value(a_again, ClauseKind::Fact, domain, None);
    assert_eq!(ra, ra2, "an identical head still dedups to one RuleId");
}

/// FAILS when WI-1013 is backed out: `try_occurrence_to_term` drops the bracket, so the
/// term twin of `f[T = Int64](x)` is `Fn{f, [x]}` — the same term as the bracket-less
/// call, and a key that disagrees with the occurrence's. A view that disagrees with its
/// twin is a wrong answer, not a precision loss (WI-425).
#[test]
fn a_bracket_survives_the_term_round_trip() {
    let mut kb = stdlib_kb();
    let (f, x, ta_int, ta_str) = fixture(&mut kb);
    let sigma = Substitution::new();

    let occ_a = call(f, Rc::clone(&x), ta_int);
    let occ_b = call(f, Rc::clone(&x), ta_str);
    let occ_bare = call(f, Rc::clone(&x), Vec::new());

    let term_a = node_occurrence::try_occurrence_to_term(&mut kb, &occ_a)
        .expect("a bracketed call has a term twin");
    let term_b = node_occurrence::try_occurrence_to_term(&mut kb, &occ_b)
        .expect("a bracketed call has a term twin");
    let term_bare = node_occurrence::try_occurrence_to_term(&mut kb, &occ_bare)
        .expect("a bracket-less call has a term twin");

    assert_ne!(term_a, term_b, "the twins of two bracket-distinct calls are distinct terms");
    assert_ne!(term_a, term_bare, "and neither is the bracket-less twin");

    // THE ISOMORPHISM: one call, read through either carrier, keys identically.
    for (occ, term, what) in
        [(&occ_a, term_a, "[T = Int64]"), (&occ_b, term_b, "[T = String]")]
    {
        assert_eq!(
            goal_fingerprint(&kb, &Value::Node(Rc::clone(occ)), &sigma),
            goal_fingerprint(&kb, &term, &sigma),
            "the {what} call must key the same through the occurrence and term carriers",
        );
        assert!(
            views_structurally_equal(&kb, &Value::Node(Rc::clone(occ)), &term),
            "and compare equal across the two carriers",
        );
    }

    // Cross-carrier DISCRIM agreement, the property `discrim-query-is-the-unifier`
    // makes a correctness question: index the term, query with the occurrence.
    let domain = kb.intern("wi1013_iso");
    kb.assert_fact(term_a, ClauseKind::Fact, domain, None);
    assert_eq!(
        kb.browse_program_clauses_matching(&Value::Node(Rc::clone(&occ_a))).len(),
        1,
        "the occurrence query finds the term-indexed fact",
    );
    assert_eq!(
        kb.browse_program_clauses_matching(&Value::Node(Rc::clone(&occ_b))).len(),
        0,
        "and a different bracket does not — the candidate set narrowed, not widened",
    );
}

/// CONTROL — GREEN BEFORE AND AFTER by design. A call with no bracket must key, match
/// and lower exactly as it did: the extra child is declared only when the channel is
/// non-empty, which is what keeps the corpus-wide candidate counts unchanged (stored
/// heads 169 → 169, rule-body atoms 8 → 8, see the module note).
#[test]
fn a_bracket_free_call_keys_and_matches_as_before() {
    let mut kb = stdlib_kb();
    let (f, x, _, _) = fixture(&mut kb);
    let occ = call(f, Rc::clone(&x), Vec::new());

    match Value::Node(Rc::clone(&occ)).head(&kb) {
        ViewHead::Functor { functor, pos_arity, named_arity } => {
            assert_eq!(functor, Some(f));
            assert_eq!((pos_arity, named_arity), (1, 0), "no synthesized child appears");
        }
        other => panic!("expected a Functor head, got {other:?}"),
    }
    assert!(Value::Node(Rc::clone(&occ)).named_keys(&kb).is_empty());

    // The twin is the plain `Fn{f, [x]}` — byte-identical to what a hand-built term
    // gives, so an existing fact keeps its existing TermId.
    let twin = node_occurrence::try_occurrence_to_term(&mut kb, &occ).expect("twin");
    let x_sym = kb.intern("wi1013_x");
    let arg = kb.alloc(Term::Ref(x_sym));
    let expected: TermId = kb.alloc(Term::Fn {
        functor: f,
        pos_args: smallvec::SmallVec::from_slice(&[arg]),
        named_args: smallvec::SmallVec::new(),
    });
    assert_eq!(twin, expected, "a bracket-less call lowers to the unchanged term");
}

/// CONTROL — GREEN BEFORE AND AFTER. The two carriers already agreed for a bracket-less
/// call; asserting it here is what makes the `a_bracket_survives_the_term_round_trip`
/// assertions attributable to the bracket rather than to carrier drift in general.
#[test]
fn carriers_agree_on_a_bracket_free_call() {
    let mut kb = stdlib_kb();
    let (f, x, _, _) = fixture(&mut kb);
    let sigma = Substitution::new();
    let occ = call(f, x, Vec::new());
    let twin = node_occurrence::try_occurrence_to_term(&mut kb, &occ).expect("twin");
    assert_eq!(
        goal_fingerprint(&kb, &Value::Node(Rc::clone(&occ)), &sigma),
        goal_fingerprint(&kb, &twin, &sigma),
    );
}

/// The LOADER path, driven end to end: a real `f[T = Int64](…)` in an operation body
/// carries its bracket into the occurrence the typer and resolver read, and the view
/// reports it. Without this the tests above would only prove that a HAND-BUILT
/// occurrence keys correctly.
#[test]
fn a_written_bracket_reaches_the_view() {
    let src = r#"
namespace wi1013.written
  operation pick[A](v: A) -> A
    = v

  operation caller(n: Int64) -> Int64
    = pick[A = Int64](n)
end
"#;
    let mut kb = crate::common::load_stdlib_kb();
    let parsed = parse::parse(src).expect("parses");
    load::load_all(&mut kb, &[&parsed], &NullResolver).expect("loads");

    let caller = kb.resolve_symbol("wi1013.written.caller");
    let body = Rc::clone(kb.op_body_node(caller).expect("caller has a body"));
    let brackets = match body.as_expr() {
        Some(Expr::Apply { type_args, .. }) => type_args.len(),
        other => panic!("expected the body to be an Apply, got {other:?}"),
    };
    assert_eq!(brackets, 1, "the written `[A = Int64]` reached the occurrence");

    match Value::Node(Rc::clone(&body)).head(&kb) {
        ViewHead::Functor { pos_arity, named_arity, .. } => {
            assert_eq!(
                (pos_arity, named_arity),
                (1, 1),
                "the view reports the argument AND the bracket",
            );
        }
        other => panic!("expected a Functor head, got {other:?}"),
    }
}

/// THE PREMISE THE KEY CHOICE RESTS ON, pinned rather than assumed: a RESOLVED
/// qualified symbol and the bare intern of its local name are DIFFERENT symbols.
/// `SymbolTable::define` writes `by_qualified_name` (and the scope's locals);
/// `SymbolTable::intern` writes `intern_map`. An argument LABEL is always the latter,
/// so `anthill.reflect.type_arg` is not a name any call site can spell — which is what
/// lets the type-args slot exist without a reserved-name rule.
///
/// If this ever stopped holding, `a_type_args_argument_beside_a_bracket_still_loads`
/// below would start reporting two same-keyed children instead of failing here, and
/// the two would be much harder to tell apart.
#[test]
fn the_slot_key_is_not_spellable_as_a_label() {
    let mut kb = stdlib_kb();
    let slot_key = kb.resolve_symbol("anthill.reflect.type_arg");
    for label in ["type_arg", "type_args"] {
        assert_ne!(
            kb.intern(label),
            slot_key,
            "an argument labelled `{label}` must not be the type-args slot key",
        );
    }
}

/// WI-839's pin, kept: a callee parameter literally named `type_args` must not disable
/// the bracket — `f[T = Int64](type_args: n)` LOADS. WI-839 chose to discriminate the
/// channel by the ParseAux VALUE rather than by reserving the name, and WI-1013 must not
/// reverse that decision as a side effect of giving the slot a KB-level key.
///
/// So this drives the case the collision would have broken: the call's head carries TWO
/// named children — the user's `type_args` argument and the bracket's slot — and they
/// are addressable SEPARATELY. A shared key would make `named_arg` return the argument
/// for both (every reader takes the first match, WI-805/808/809).
#[test]
fn a_type_args_argument_beside_a_bracket_still_loads() {
    let src = r#"
namespace wi1013.collide
  operation pick[A](type_args: A) -> A
    = type_args

  operation caller(n: Int64) -> Int64
    = pick[A = Int64](type_args: n)
end
"#;
    let mut kb = crate::common::load_stdlib_kb();
    let parsed = parse::parse(src).expect("parses");
    load::load_all(&mut kb, &[&parsed], &NullResolver).expect("loads");

    let caller = kb.resolve_symbol("wi1013.collide.caller");
    let body = Rc::clone(kb.op_body_node(caller).expect("caller has a body"));
    let view = Value::Node(Rc::clone(&body));

    let keys = view.named_keys(&kb);
    assert_eq!(keys.len(), 2, "the user argument AND the bracket slot: {keys:?}");
    assert_eq!(
        keys.iter().collect::<std::collections::HashSet<_>>().len(),
        2,
        "and under DISTINCT keys — a repeat would leave one child unreachable",
    );

    let arg_key = kb.intern("type_args");
    let slot_key = kb.resolve_symbol("anthill.reflect.type_arg");
    assert!(view.named_arg(&kb, arg_key).is_some(), "the user argument is addressable");
    assert!(view.named_arg(&kb, slot_key).is_some(), "and so is the bracket, separately");
}

/// CONTROL — GREEN BEFORE AND AFTER. The same argument name on a call with NO bracket:
/// one child, and it is the user's. Without this the test above would not show that the
/// second child comes from the bracket rather than from the name.
#[test]
fn a_type_args_argument_without_a_bracket_has_one_child() {
    let src = r#"
namespace wi1013.nocollide
  operation pick(type_args: Int64) -> Int64
    = type_args

  operation caller(n: Int64) -> Int64
    = pick(type_args: n)
end
"#;
    let mut kb = crate::common::load_stdlib_kb();
    let parsed = parse::parse(src).expect("parses");
    load::load_all(&mut kb, &[&parsed], &NullResolver).expect("loads");

    let caller = kb.resolve_symbol("wi1013.nocollide.caller");
    let body = Rc::clone(kb.op_body_node(caller).expect("caller has a body"));
    let keys = Value::Node(body).named_keys(&kb);
    assert_eq!(keys, vec![kb.intern("type_args")], "just the user's argument");
}
