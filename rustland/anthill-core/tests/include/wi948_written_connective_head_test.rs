//! WI-948 — A HEAD IS AN EQUATION BECAUSE THE DESUGAR WROTE IT, NOT BECAUSE OF ITS
//! NAME. `load::parse_equation_lhs` decided "is this head an equation?" from the head
//! functor's SPELLING (`pratt::EQUATION_FUNCTORS`, read via `is_equation_functor`)
//! with nothing asking whether the node came from the infix desugar — the exact
//! re-derivation `SimpleTermStore::minted` (WI-618) exists to replace. The guard is
//! `is_minted(head)`, and `rule_introduced_functor_name` already asks that same
//! question about the SUBJECT two steps later.
//!
//! Found porting pass 3 to scaland, whose `Loader.parseEquationLhs` carries the guard
//! and the sibling test (`WI-618: a written eq(?a, ?b) head is a predicate, not an
//! equation`). This file is the rustland half, and it drives the shape through BOTH of
//! `parse_equation_lhs`'s readers, because the misreading reached both:
//!
//!   * `Loader::collect_rule_tvar_names` — WHERE A HEAD'S `[t]` INTRODUCER RIDES. On an
//!     equation it rides on the LHS operand; on a predicate head, on the head itself.
//!     A written `eq[t](?x, ?y)` was read as an equation, so the `[t]` was looked for on
//!     the ARGUMENT `?x`, found nowhere, and dropped. This is WI-619's defect reached
//!     through the name instead of through arity — WI-619 fixed the arity gate and left
//!     the name gate standing.
//!   * `rule_introduced_functor_name` — WHICH NAME THE RULE INTRODUCES. A written
//!     `unify(f948(?x), ?x)` made the ARGUMENT `f948` the subject and minted it
//!     `SymbolKind::EquationFunctor`: WI-898's distinction inverted for a rule that
//!     contains no equation at all.
//!
//! # WHAT THIS FIX DOES NOT CHANGE, MEASURED HERE RATHER THAN LEFT IMPLIED
//!
//! A written connective-named head still does not RUN, and this file must not read as
//! a promise that it does. Every connective spelling is reserved vocabulary
//! (`kernel_vocab_qualified` / `PRELUDE_QUALIFIED`), so such a head RESOLVES rather
//! than declares (WI-896) — to `anthill.prelude.PartialEq.eq` or
//! `anthill.kernel.unify` — and its clause joins that builtin-backed name, where
//! WI-139 unindexes it (`is_equational_head`) or the builtin decides the goal before
//! any clause is consulted. Loaded, unreachable, silent. That is **WI-899**, still
//! open, which names connective heads explicitly and whose acceptance is
//! "a clause the resolver can never reach is refused or diagnosed rather than silently
//! loaded". The inertness is PRE-EXISTING, not created by this guard, and one row of
//! each of the first two tests MEASURES it on a shape that loads with the guard AND
//! without it. Each such row is placed AHEAD of the row the fix is about, so the control
//! run reaches it instead of short-circuiting on the failure. What the guard changes is
//! the LOADER's reading of the head — which name pass 3 introduces, and where the head's
//! `[t]` rides.
//!
//! One verdict does flip: `rule eq[t](?x, ?y) :- Eq[t]` is refused today and loads
//! after. It exchanges a refusal that named the wrong thing (`unresolved name 't'`,
//! because the guard never folded) for WI-899's known silence. It does not become a
//! working predicate, and the test says so at its site.
//!
//! WHY THE DIRECTION-2 FIXTURES SAY `unify` AND NOT `struct_eq`. They said `struct_eq`
//! when this landed, and WI-1090 then removed that spelling from
//! `pratt::EQUATION_FUNCTORS` — after which `parse_equation_lhs` declined those fixtures
//! on the NAME test and the `is_minted` guard stopped being what decided them. The tests
//! kept passing and measured nothing; the back-out run is what showed it. Any fixture
//! here must be spelled with a live connective, and a future narrowing of that list has
//! to move these with it.
//!
//! THE CONTROL, measured by backing the `is_minted` guard out of `parse_equation_lhs`:
//! all three tests fail, each on the assertion its doc names. The rows marked
//! "either way" pass in both runs, on purpose. `wi619_two_ary_head_introducer_test` and
//! `wi898_equation_functor_kind_test` also pass either way, by design — a head the
//! desugar DID write is untouched here, and those files are what pin it. The first test
//! below is deliberately the NAME-gate twin of wi619's two arity-gate rows and shares
//! their fixture shape: same scan, two different gates, and neither file's rows fail for
//! the other's cause.

use anthill_core::intern::SymbolKind;
use anthill_core::kb::KnowledgeBase;

fn load_errors(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

/// Clauses indexed under a qualified functor — "did this rule's head land anywhere a
/// goal can reach?", asked of the same index SLD consults.
fn clauses_under(kb: &mut KnowledgeBase, qn: &str) -> usize {
    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("`{qn}` must be a defined symbol"));
    kb.rules_by_functor(sym).len()
}

/// DIRECTION 1 — the `[t]` introducer on a written 2-ary connective-named head. The
/// last two rows fail without the guard, and they fail differently, which is the point:
/// the introducer is not merely mis-scoped, it is never collected at all, so the head's
/// `[t]` bracket is left UNCONSUMED and WI-839's sweep reports the whole bracket
/// unsupported.
///
/// * INERT (first, either way) — the row that keeps the other two honest. Its fixture
///   carries no bracket, so it loads with the guard and without it, and in both the
///   clause is absent from the index SLD consults. A written connective head resolves to
///   the connective's own symbol (WI-896) and WI-139 unindexes it; WI-899 owns making
///   that loud.
/// * BOUNDED — refused today: `unresolved name 't' in scope '…'`, the scope named
///   QUALIFIED since WI-977 and left elided here because this row describes the
///   guard-less variant, which the assertion below does not run (the `:- Eq[t]`
///   guard never folded into a bound, so `t` reached scope resolution as an ordinary
///   term) plus the `call-site type arguments 'eq[…](…)' are not supported here` sweep.
///   With the guard it loads. It does NOT thereby run — see the row above.
/// * UNBOUNDED — the WI-582 diagnostic, which can only fire if the introducer WAS
///   collected. That is what makes the clean load above evidence of collection rather
///   than evidence of a check that stopped running: the same guard produces a REFUSAL
///   here and an ACCEPTANCE there, out of the same scan.
#[test]
fn a_written_connective_head_keeps_its_type_var_introducer() {
    // EITHER WAY, and FIRST so the control run reaches it (no bracket, so
    // `collect_rule_tvar_names` has nothing to read and the program loads with the
    // guard and without it). The comparison is against the same program minus the
    // rule, so the number is a DELTA and not a stdlib census.
    const WITH_RULE: &str = r#"
namespace wi948.inert
  rule eq(?x, ?y)
end
"#;
    const WITHOUT_RULE: &str = r#"
namespace wi948.inert
  rule unrelated948(?x)
end
"#;
    let mut with_rule = crate::common::load_kb_with(WITH_RULE);
    let mut without_rule = crate::common::load_kb_with(WITHOUT_RULE);
    let qn = "anthill.prelude.PartialEq.eq";
    assert_eq!(
        clauses_under(&mut with_rule, qn),
        clauses_under(&mut without_rule, qn),
        "a written `eq` head RESOLVES to the canonical connective (WI-896) and WI-139 \
         unindexes it, so the rule contributes nothing a goal can reach. This fix does \
         not change that and must not be read as claiming it does — WI-899 owns it",
    );

    let bounded = load_errors(
        r#"
namespace wi948.bounded
  import anthill.prelude.{Int64, Eq}
  rule eq[t](?x, ?y) :- Eq[t]
end
"#,
    );
    assert!(
        bounded.is_empty(),
        "a written `eq[t](?x, ?y)` is a PREDICATE head, so its `[t]` rides on the head \
         and the `:- Eq[t]` guard folds into the bound — exactly as WI-619's \
         `same_ty[t]` does. Got: {bounded:?}",
    );

    let unbounded = load_errors(
        r#"
namespace wi948.unbounded
  import anthill.prelude.{Int64, Eq}
  rule eq[t](?x, ?y)
end
"#,
    );
    assert!(
        unbounded
            .iter()
            .any(|e| e.contains("no bounding guard") && e.contains("`t`")),
        "the introducer must be COLLECTED and then found unbounded, and the message \
         must name `t` — read off the argument `?x` instead it is found nowhere and the \
         WI-582 scan never runs. Got: {unbounded:?}",
    );
}

/// DIRECTION 2 — which node the rule is about. `f948` is deliberately UNDECLARED: a
/// name that already denotes sends `scan_rule_goal`'s B2 guard home before the mint, so
/// the wrong stamp would never be written and the defect would be invisible.
///
/// THE NEIGHBOUR ROWS (`mine948` / `boxed948` / the drive) come FIRST, and deliberately:
/// the claim about `f948` is an ABSENCE, and an absence read off a pass that never ran is
/// worth nothing. They establish, on THIS load, that pass 3 minted a head functor as a
/// `Goal` and that a goal reaches the clause indexed under it. They pass with the guard
/// and without it — MEASURED, in this order — because `mine948` is not a connective
/// spelling, so `parse_equation_lhs` declines it on the name test alone either way.
///
/// The row just before the absence is the WI-899 counterpart of the first test's first,
/// on this fixture's own connective: the `unify` head resolves to the kernel symbol and
/// is then unindexed as a law, so it reaches no goal. Stated rather than left implied,
/// because a fixture whose rule does nothing is exactly the kind of thing a reader
/// should see said out loud. Either way, guard or no guard.
#[test]
fn an_argument_of_a_written_connective_head_is_not_the_subject() {
    const SRC: &str = r#"
namespace wi948.subject
  sort S
    import anthill.prelude.{Int64}
    entity boxed948(v: Int64)
    rule unify(f948(?x), ?x)
    rule mine948(boxed948(v: ?x), ?x)
    rule drive948(?v) :- mine948(boxed948(v: 7), ?v)
  end
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);

    let mine = kb.try_resolve_symbol("wi948.subject.S.mine948").expect(
        "neighbour: a head functor IS introduced, so the absence below is not a pass \
         that failed to run",
    );
    assert_eq!(
        kb.kind_of(mine),
        Some(SymbolKind::Goal),
        "neighbour: a predicate head owns its clauses — the kind an equation subject \
         would NOT get",
    );
    assert!(
        kb.try_resolve_symbol("wi948.subject.S.boxed948").is_some(),
        "neighbour: the entity is declared, so `boxed948` is the shape `f948` would \
         have had if an argument were ever a subject",
    );

    // Carrier-agnostic, per `wi616_semantic_eq_test::reifies_to_int`: the binding can
    // come back as `Value::Int` or as a hash-consed `Value::Term(Const)`.
    use anthill_core::kb::term::Literal;
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let answers = crate::common::query_unary(&mut kb, "wi948.subject.S.drive948");
    let values: Vec<ViewHead> = answers.iter().map(|(v, _)| v.head(&kb)).collect();
    assert!(
        matches!(values.as_slice(), [ViewHead::Const(Literal::Int(7))]),
        "neighbour: the clause is indexed under the minted head symbol, so a goal \
         reaches it and the head's shared `?x` carries 7 out; got {values:?}",
    );

    // EITHER WAY, and before the absence below so the control run reaches it. `unify` is
    // reserved kernel vocab, so this head RESOLVES to `anthill.kernel.unify` (WI-896) —
    // and an untagged bodyless head on a connective is a WI-139 cite-required law, so
    // `unindex_functor` drops it. The rule reaches no goal, with the guard or without.
    // A DELTA against the same program minus the rule, because the stdlib's own `[simp]`
    // equations live in that bucket and an absolute count would be a census of them.
    const WITHOUT_THE_CONNECTIVE_HEAD: &str = r#"
namespace wi948.subject
  sort S
    import anthill.prelude.{Int64}
    entity boxed948(v: Int64)
    rule mine948(boxed948(v: ?x), ?x)
  end
end
"#;
    let mut without = crate::common::load_kb_with(WITHOUT_THE_CONNECTIVE_HEAD);
    let qn = "anthill.kernel.unify";
    assert_eq!(
        clauses_under(&mut kb, qn),
        clauses_under(&mut without, qn),
        "the head resolves to the kernel connective and is then unindexed as a law, so \
         it contributes nothing a goal can reach — stated here rather than hidden. \
         This fix does not change it; WI-899 owns making it loud",
    );

    assert!(
        kb.try_resolve_symbol("wi948.subject.S.f948").is_none(),
        "`f948` is an ARGUMENT of the head. Reading the head as an equation made it the \
         subject and minted it — as an `EquationFunctor`, for a rule with no equation \
         in it (WI-898's kinds inverted)",
    );
}

/// …AND WHAT THE WRONG STAMP TELLS THE AUTHOR. `f948` is declared nowhere, so a
/// citation of it must say so. Stamped `EquationFunctor` it instead drew WI-898's
/// equation refusal — MEASURED, today, verbatim: "`wi948.cite.S.f948` is defined by
/// equations, not declared as an operation … no defining equation for it can be found".
/// The file contains no equation, so that message sends the author looking for a
/// missing `[simp]` rule that was never meant to exist.
#[test]
fn an_argument_is_not_reported_as_defined_by_equations() {
    const SRC: &str = r#"
namespace wi948.cite
  sort S
    import anthill.prelude.{Int64}
    rule unify(f948(?x), ?x)
    operation drive(n: Int64) -> Int64 = f948(n)
  end
end
"#;
    let errs = load_errors(SRC);
    assert!(
        !errs.is_empty(),
        "`f948` is declared nowhere — the citation must be refused",
    );
    let joined = errs.join("\n");
    assert!(
        !joined.contains("defined by equations"),
        "nothing in this program is an equation; the refusal must not invent one. \
         Got: {joined}",
    );
    assert!(
        joined.contains("unknown functor"),
        "the honest answer is that `f948` names nothing. Got: {joined}",
    );
}
