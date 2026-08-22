//! WI-939 item 4 — ONE OPERATION, ONE DEFINITION: a body OR hand-written clauses,
//! never both.
//!
//! THE HAZARD, and it is a LOSS rather than an ambiguity. A rule's operation name is
//! its label else its head functor (proposal 052 §"Naming the relation"), so a clause
//! landing on a bodied operation's functor is a second DEFINITION of it. Design §3.3
//! gives the clauses precedence ("rules win"), which SUPPRESSES the body's derived
//! relational view (WI-938) — so the pair does not offer two readings, it removes the
//! one that worked. [`body_alone_answers_a_definite_value`] and
//! [`a_clause_beside_a_body_answers_a_residual_instead`] are that pair, measured
//! against each other; every other row here would pass on a check that merely refused
//! things.
//!
//! CLAUSE 1 CANNOT SEE IT (WI-1049). That check is keyed on two written `operation`
//! DECLARATIONS reaching one symbol; a rule declares nothing — its head runs the
//! ordinary ladder and contributes a clause to the operation it finds (§8.6, WI-896).
//! [`the_pair_leaves_one_symbol_with_one_declaration`] pins that, because it is the
//! reason this needed a check of its own rather than a widening of that one.
//!
//! THE BODY IS THE DISCRIMINATOR, AND THE PRELUDE IS WHY. A BODY-LESS operation
//! carrying clauses is ONE definition written relationally — `Set.contains` (2 clauses,
//! no body), `Set.subset`, `Set.eq`, all shipped — so a check keyed on "has clauses"
//! would refuse the standard library. [`a_body_less_operation_with_clauses_is_legal`]
//! drives that shape to a value, and [`the_shipped_prelude_still_loads`] is the
//! corpus itself.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! MEASURED by making each edit and re-running, not predicted.
//!
//! Delete the `check_operation_body_and_clauses(kb)` call in `load_phase_inner` —
//! **2 fail, 8 pass**: [`a_clause_beside_a_body_answers_a_residual_instead`] and
//! [`a_same_arity_clause_on_a_bodied_bool_op_is_refused`], each fixture then loading
//! clean, which is the defect. The rest PASS EITHER WAY, BY DESIGN — they are the
//! controls, and without them a check that refused every operation carrying clauses
//! (the standard library included) would look correct here.
//!
//! Drop the `bool_view` disjunct, leaving `params + 1` — **exactly 1 fails**,
//! [`a_same_arity_clause_on_a_bodied_bool_op_is_refused`]. That is the first cut,
//! and it is what /code-review refuted.
//!
//! Drop the BUILTIN gate in `would_derive_bool_relation` — **exactly 2 fail**, both
//! lemma rows: [`a_clause_at_the_operations_own_arity_is_a_lemma`] and
//! [`a_same_arity_lemma_on_a_builtin_backed_bool_op_is_legal`]. That is the trap on
//! the other side: widening to the Bool arity WITHOUT the builtin gate refuses the
//! 26 `PartialOrd.gte` / `.lte` SMT lemmas the spec says are intended.

use anthill_core::eval::Value;
use anthill_core::intern::SymbolKind;
use anthill_core::kb::term::{Literal, Term, Var};

/// The body alone. Its arity+1 relational view is DERIVED (WI-938).
const BODY_ONLY: &str = r#"
namespace wi939d.body
  sort Box
    entity box(n: Int64)
    operation twice(b: Box) -> Int64 = 2
  end
end
"#;

/// The same program plus ONE clause under the same functor.
const BODY_PLUS_CLAUSE: &str = r#"
namespace wi939d.both
  sort Box
    entity box(n: Int64)
    operation twice(b: Box) -> Int64 = 2
    rule twice(?b, ?r) :- ?r = 7
  end
end
"#;

/// The prelude's own spelling: a BODY-LESS operation whose clauses ARE its
/// definition. `Set.contains` in miniature.
const CLAUSES_ONLY: &str = r#"
namespace wi939d.rel
  sort Coll
    entity nothing
    entity put(c: Coll, x: Int64)
    operation has(x: Int64, c: Coll) -> Bool
    rule has(?x, put(?, ?x)) :- true
    rule has(?x, put(?c, ?)) :- has(?x, ?c)
  end
end
"#;

fn refusal(src: &str) -> String {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => panic!("expected a one-definition refusal; the fixture loaded CLEAN"),
        Err(errs) => errs.join("\n"),
    }
}

/// Drive the arity+1 goal `twice(box(0), ?r)`: how many answers, definite, and what
/// did `?r` bind to? Returns `(rendered answers, first binding if it is an Int)`.
fn arity_plus_one(src: &str, qn: &str) -> (usize, bool, Option<i64>) {
    use anthill_core::kb::resolve::ResolveConfig;
    use smallvec::SmallVec;
    let mut kb = crate::common::load_kb_with(src);
    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("`{qn}` does not resolve"));
    let ctor = kb
        .try_resolve_symbol(&format!("{}.box", qn.rsplit_once('.').unwrap().0))
        .expect("box constructor");
    let zero = kb.alloc(Term::Const(Literal::Int(0)));
    let n = kb.intern("n");
    let arg = kb.alloc(Term::Fn {
        functor: ctor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(n, zero)]),
    });
    let r_sym = kb.intern("r");
    let vid = kb.fresh_var(r_sym);
    let rvar = kb.alloc(Term::Var(Var::Global(vid)));
    let goal = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(&[arg, rvar]),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let definite = sols.iter().all(|s| s.is_definite()) && !sols.is_empty();
    let bound = sols.first().and_then(|s| match kb.reify(rvar, &s.subst) {
        Value::Term { id, .. } => match kb.get_term(id) {
            Term::Const(Literal::Int(i)) => Some(*i),
            _ => None,
        },
        Value::Int(i) => Some(i),
        _ => None,
    });
    (sols.len(), definite, bound)
}

// ── the pair: what the second definition actually costs ─────────────────────

#[test]
fn body_alone_answers_a_definite_value() {
    // PASSES EITHER WAY, BY DESIGN — the "before" the refusal protects. Without it
    // the next test's refusal would not be attributable to the lost capability.
    assert_eq!(
        arity_plus_one(BODY_ONLY, "wi939d.body.Box.twice"),
        (1, true, Some(2)),
        "the body's derived arity+1 view (WI-938) must answer 2, definite"
    );
}

#[test]
fn a_clause_beside_a_body_answers_a_residual_instead() {
    // THE HEADLINE. Backed out, this fixture LOADS CLEAN and the same goal answers
    // one INDEFINITE solution whose `?r` is a residual term rather than 7 or 2 — the
    // clause suppressed the derived view (design §3.3) and computed nothing in its
    // place. This test FAILS when the check is deleted.
    let errs = refusal(BODY_PLUS_CLAUSE);
    for want in ["wi939d.both.Box.twice", "ONE definition", "`rule` at"] {
        assert!(
            errs.contains(want),
            "refusal must name {want:?}; got:\n{errs}"
        );
    }
}

#[test]
fn the_pair_leaves_one_symbol_with_one_declaration() {
    // WHY CLAUSE 1 (WI-1049) CANNOT SEE IT, driven rather than asserted in prose: the
    // rule contributes a clause to the operation's own symbol and declares nothing,
    // so there is no second declaration and no `Goal` kind for that check to find.
    // PASSES EITHER WAY, BY DESIGN — it measures the loader, not the refusal, and is
    // why this needed its own check instead of widening clause 1.
    let kb = crate::common::load_kb_with(BODY_ONLY);
    let sym = kb.try_resolve_symbol("wi939d.body.Box.twice").unwrap();
    assert!(kb.has_kind(sym, SymbolKind::Operation));
    assert!(
        !kb.has_kind(sym, SymbolKind::Goal) && !kb.has_kind(sym, SymbolKind::Rule),
        "a bodied operation's own symbol carries no rule kind"
    );
}

// ── the controls: what must stay legal ──────────────────────────────────────

#[test]
fn a_body_less_operation_with_clauses_is_legal() {
    // THE PRELUDE'S SPELLING, and the reason the discriminator is the BODY rather
    // than "has clauses": `Set.contains` is exactly this shape. DRIVEN — the goal
    // answers — because a control that only loaded would keep passing if the clauses
    // stopped meaning anything.
    //
    // PASSES EITHER WAY, BY DESIGN. It fails only if the check is keyed wrongly.
    use anthill_core::kb::resolve::ResolveConfig;
    use smallvec::SmallVec;
    let mut kb = crate::common::load_kb_with(CLAUSES_ONLY);
    let has = kb.try_resolve_symbol("wi939d.rel.Coll.has").unwrap();
    let put = kb.try_resolve_symbol("wi939d.rel.Coll.put").unwrap();
    let nothing = kb.try_resolve_symbol("wi939d.rel.Coll.nothing").unwrap();
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    let empty = kb.alloc(Term::Fn {
        functor: nothing,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let (c_sym, x_sym) = (kb.intern("c"), kb.intern("x"));
    let one = kb.alloc(Term::Fn {
        functor: put,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(c_sym, empty), (x_sym, seven)]),
    });
    let goal = kb.alloc(Term::Fn {
        functor: has,
        pos_args: SmallVec::from_slice(&[seven, one]),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        sols.len(),
        1,
        "`has(7, put(nothing, 7))` must be provable from the clauses"
    );
}

#[test]
fn an_equation_beside_a_body_is_a_law_not_a_clause() {
    // THE EXEMPTION, and it has a real population: `List.nth` / `insert` / `empty` /
    // `split`, `Relation.where` and three `Stream` ops all carry `<=>` equations
    // beside a body. An equation loads under the connective's functor, never the
    // operation's, so it does not reach this check at all.
    //
    // PASSES EITHER WAY, BY DESIGN — but it is what would have caught a check keyed
    // on "any rule mentioning the operation".
    crate::common::load_kb_with(
        r#"
namespace wi939d.law
  sort Box
    entity box(n: Int64)
    operation twice(b: Box) -> Int64 = 2
    rule twice(box(n: 0)) <=> 0 [simp]
  end
end
"#,
    );
}

#[test]
fn a_clause_at_the_operations_own_arity_is_a_lemma() {
    // THE EXEMPTION THAT COST THE FIRST CUT, and it is the spec's own example. The
    // check first keyed on "a bodied operation with ANY clauses" and refused 26 sites
    // across the workspace, every one of them `PartialOrd.gte` / `.lte` — which have
    // BODIES (ordered.anthill:58/62) and carry SMT lemmas written exactly like this.
    // §"A rule head functor is resolved, not declared" (WI-896) states that shape is
    // legal and intended: "`rule bound: gte(?x, 3.0) :- gte(?x, 5.0)` is a lemma
    // about `PartialOrd.gte` because `gte` RESOLVES".
    //
    // So the arity is the discriminator, not the presence of clauses: at the
    // operation's OWN arity a clause states something ABOUT it, and only at
    // params+1 does it occupy the graph slot WI-938's derived view would answer.
    //
    // PASSES EITHER WAY, BY DESIGN once the check is narrowed — and FAILED on the
    // unnarrowed cut, which is the whole reason it exists.
    crate::common::load_kb_with(
        r#"
namespace wi939d.lemma
  import anthill.prelude.{PartialOrd}
  rule bound939: gte(?x, 3.0) :- gte(?x, 5.0)
end
"#,
    );
}

#[test]
fn the_shipped_prelude_still_loads() {
    // THE CORPUS IS THE CONTROL. `Set.contains` / `Set.subset` / `Set.eq` are body-less
    // operations carrying clauses; a check keyed on "has clauses" refuses the whole
    // standard library, and every other row above would still pass.
    //
    // PASSES EITHER WAY, BY DESIGN.
    let kb = crate::common::load_kb_with("namespace wi939d.corpus\nend\n");
    let member = kb
        .try_resolve_symbol("anthill.prelude.Set.contains")
        .expect("Set.contains must resolve");
    assert!(
        !kb.program_clauses_by_functor(member).is_empty() && kb.op_body_node(member).is_none(),
        "the shape this control exists for: clauses, no body"
    );
}

// ── the BOOL arity, which the first cut missed (found by /code-review) ──────

/// A Bool-returning bodied operation's derived relational view sits at its OWN
/// arity — `eq(op(args), true)`, `bare_bodied_bool_relation` — not at arity+1. The
/// first cut filtered on `params + 1` alone and called every own-arity clause a
/// lemma, which let WI-580's OWN unsound shape back in.
///
/// MEASURED by the reviewer on the built binary, and reproduced here: with the
/// clause the goal answered NO SOLUTIONS while the body says `true` — the clause
/// suppressed the derived view AND contradicted it.
///
/// BACKED OUT (drop the `bool_view` disjunct, leaving `params + 1`): this test
/// FAILS — the fixture loads clean.
#[test]
fn a_same_arity_clause_on_a_bodied_bool_op_is_refused() {
    let errs = refusal(
        r#"
namespace wi939d.boolarity
  sort Box
    entity box(n: Int64)
    operation isbig(b: Box) -> Bool = true
    rule isbig(box(n: 0)) :- true
  end
end
"#,
    );
    for want in ["wi939d.boolarity.Box.isbig", "ONE definition"] {
        assert!(errs.contains(want), "refusal must name {want:?}; got:\n{errs}");
    }
}

/// THE CONTROL THAT KEEPS THE LEMMAS LEGAL, and the one the widening could break.
/// `PartialOrd.gte` is Bool-returning AND bodied AND carries same-arity SMT lemmas —
/// 26 such sites across the workspace. They stay legal because `gte` is
/// BUILTIN-BACKED: a builtin decides its goal before any clause is consulted, so the
/// clause suppresses nothing. `would_derive_bool_relation` reads that gate.
///
/// PASSES EITHER WAY, BY DESIGN once the builtin gate is present — and FAILS if the
/// widening is written without it, which is the trap.
#[test]
fn a_same_arity_lemma_on_a_builtin_backed_bool_op_is_legal() {
    crate::common::load_kb_with(
        r#"
namespace wi939d.lemma2
  import anthill.prelude.{PartialOrd}
  rule bound939b: gte(?x, 3.0) :- gte(?x, 5.0)
end
"#,
    );
}

/// And an EFFECTFUL Bool op keeps its own-arity clauses too: an effectful body is
/// not a logical relation, so it is granted no derived view and a clause beside it
/// takes nothing away. Same gate `bare_bodied_bool_relation` applies.
#[test]
fn a_same_arity_clause_on_an_effectful_bool_op_is_legal() {
    crate::common::load_kb_with(
        r#"
namespace wi939d.eff
  import anthill.prelude.{Error}
  sort Box
    entity box(n: Int64)
    operation risky(b: Box) -> Bool effects Error = true
    rule risky(box(n: 0)) :- true
  end
end
"#,
    );
}
