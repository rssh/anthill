//! WI-896 — A RULE HEAD FUNCTOR IS RESOLVED, NOT DECLARED. The one rule, stated in
//! `docs/kernel-language.md` §"A rule head functor is resolved, not declared": the head
//! functor runs the ordinary name ladder, and the rule contributes a clause to whatever
//! it lands on. Only when the ladder finds NOTHING — scope, imports, and the implicit
//! prelude / kernel vocab all miss — does the rule INTRODUCE the name, scoped where it
//! is written (WI-894). A label names the CLAUSE and takes no part in this.
//!
//! WI-894 scoped the equation half and froze the predicate half behind a label
//! carve-out; this file is the predicate half, so it drives the two cases the carve-out
//! decided oppositely from their unlabeled twins.
//!
//! STDLIB LOADS: FIVE, one per `#[test]` — `load_kb_with` parses and loads ~76 stdlib
//! and binding files each (~0.5s). The per-claim naming is what forces most of them; see
//! `wi884_sibling_backing_test`'s header. Two are forced by more than convention: both
//! `or` fixtures resolve to the SAME `anthill.kernel.or`, so merging them would add one
//! test's clause to the other's predicate and change its solution count.

/// THE TICKET'S OWN ASYMMETRY, all four cells on one load. A new name resolves nowhere,
/// so both twins introduce it; `gte` resolves through the implicit prelude, so neither
/// does.
///
/// EACH CELL GETS ITS OWN SORT, and that is not tidiness. The labeled and unlabeled
/// `gte` twins named the same symbol when written in one scope, so the unlabeled one's
/// mint answered for both and the labeled cell was never measured at all — caught by
/// running this table as a control against the pre-WI-896 loader, where three rows must
/// flip and only two distinct symbols existed to carry them.
const FOUR_CASES: &str = r#"
namespace wi896.fourcases
  sort BareNew
    import anthill.prelude.{Int64}
    rule bareNew896(?x) :- Int64.gt(?x, 0)
  end

  sort LabeledNew
    import anthill.prelude.{Int64}
    rule lbl896: labeledNew896(?x) :- Int64.gt(?x, 0)
  end

  sort BarePrelude
    import anthill.prelude.{Float}
    rule gte(?x, 3.0) :- gte(?x, 5.0)
  end

  sort LabeledPrelude
    import anthill.prelude.{Float}
    rule bound896: gte(?x, 3.0) :- gte(?x, 5.0)
  end
end
"#;

/// The four cases of the acceptance, as a table: each row names the rule that decides
/// it, and the rule is the same sentence for all four.
///
/// Pre-WI-896 the second and third rows read the other way — `LabeledNew.labeledNew896`
/// did not introduce (the label suppressed it) and `BarePrelude.gte` did (nothing in
/// scope resolved it, and the predicate path did not consult the implicit prelude). Those
/// two flips ARE this ticket; the other two cells were already right, which is what made
/// the label look like a rule.
#[test]
fn the_four_cases_are_decided_by_resolution_not_by_the_label() {
    let kb = crate::common::load_kb_with(FOUR_CASES);
    // Every row is checked before reporting: the two rows this ticket FLIPS are
    // adjacent, and an assert-on-first-mismatch loop would have shown only one of them
    // when run as a control against the pre-WI-896 loader.
    let mut wrong = Vec::new();
    for (q, want, why) in [
        (
            "BareNew.bareNew896",
            true,
            "unlabeled x new name: the ladder finds nothing, so the rule introduces it \
             in the sort it is written in",
        ),
        (
            "LabeledNew.labeledNew896",
            true,
            "labeled x new name: same ladder, same answer — a label names the CLAUSE, \
             so it cannot decide whether the head names a new predicate",
        ),
        (
            "BarePrelude.gte",
            false,
            "unlabeled x prelude name: `gte` resolves to `anthill.prelude.PartialOrd.gte` \
             through the implicit prelude, so the rule is a clause ABOUT it — capturing \
             it would silently change what the rule is about",
        ),
        (
            "LabeledPrelude.gte",
            false,
            "labeled x prelude name: unchanged, and now for the ladder's reason rather \
             than the label's (this is the smt-gen `bound` lemma's shape)",
        ),
    ] {
        let qn = format!("wi896.fourcases.{q}");
        let got = kb.has_qualified_name(&qn);
        if got != want {
            wrong.push(format!("`{qn}` introduced={got}, want {want}: {why}"));
        }
    }
    assert!(
        wrong.is_empty(),
        "the label decided a case it may not decide:\n{}",
        wrong.join("\n")
    );
}

/// THE OBSTACLE THE TICKET NAMES, DRIVEN INSTEAD OF ARGUED. WI-523's handoff refused a
/// broad implicit-prelude skip on the predicate path because "a user's own `or` / `not`
/// predicate head must keep its own Goal symbol rather than rerouting to the kernel
/// primitive." Keeping it is what this test measures, and the protection is worse than
/// the thing it protects against: minting `<ns>.or` re-points EVERY bare `or` in the
/// scope, so the disjunction two lines down silently stops being disjunction.
///
/// MEASURED both ways on this exact fixture. Pre-WI-896 `reach896` yields ZERO solutions
/// — the `or` in its body resolves to the freshly-minted 1-ary `<ns>.or` Goal and no
/// clause matches, with no diagnostic anywhere. Post-WI-896 it yields TWO, because `or`
/// keeps meaning `anthill.kernel.or` in head position exactly as it already did in body
/// position. That consistency is the argument: one spelling, one meaning, whichever side
/// of the `:-` it is written on.
///
/// What becomes of the user's own `or` clause is [`a_clause_on_a_builtin_backed_name_is_inert_at_sld`].
#[test]
fn a_kernel_primitive_head_does_not_capture_the_scope() {
    const SRC: &str = r#"
namespace wi896.orcapture
  import anthill.prelude.{Int64}
  fact p896(1)
  fact q896(2)
  -- a user predicate head naming the kernel disjunction primitive
  rule or(?x) :- p896(?x)
  -- …and a genuine disjunction in the SAME scope, two lines down
  rule reach896(?x) :- or(p896(?x), q896(?x))
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    let got =
        crate::wi282_rule_body_dot_test::resolve_query(&mut kb, "wi896.orcapture.reach896", 1);
    assert_eq!(
        got, 2,
        "`or` must still be the kernel disjunction in a scope that also writes it in \
         head position — a rule head does not re-point a name for the whole scope; \
         got {got} solution(s)",
    );
    assert!(
        !kb.has_qualified_name("wi896.orcapture.or"),
        "…and the reason is that no `<ns>.or` was minted: the head RESOLVED",
    );
}

/// THE OTHER HALF OF THE SAME COIN — what a user does when they want their own. The
/// ladder is what decides, so putting the name in scope is what changes the answer: a
/// DECLARED `gte` operation is found before the implicit prelude, and the rule binds to
/// the declaration (proposal 044 / B2) rather than to `PartialOrd.gte`. Without this
/// route the rule above would be a dead end rather than a stated one.
#[test]
fn a_declaration_is_how_a_prelude_name_becomes_your_own() {
    const SRC: &str = r#"
namespace wi896.declared
  sort S
    import anthill.prelude.{Int64, Bool}
    operation gte(a: Int64, b: Int64) -> Bool
    rule gte(?x, 3) :- Int64.gt(?x, 5)
  end
end
"#;
    let kb = crate::common::load_kb_with(SRC);
    assert!(
        kb.has_qualified_name("wi896.declared.S.gte"),
        "the DECLARED operation is the scoped `gte` here — the rule binds to it, and the \
         implicit prelude is never reached",
    );
}

/// THE CONNECTIVE IS NOT THE SUBJECT, and this ticket must not lose that. WI-530 forbids
/// minting `<ns>.eq` / `<ns>.unify` for an equation-SHAPED head, and WI-894 made a
/// BODIED such rule take the predicate path (§8.3: an equation is bodyless), where its
/// head functor really is `eq`. Under the unified ladder that skip is no longer a
/// special case — `eq` and `unify` are implicit-prelude names like any other — so this
/// pins that the outcome survived the unification, on both spellings and both labels.
///
/// `field.anthill` is the in-tree writer of this shape (`rule mul(div(?a, ?b), ?b) = ?a
/// :- neq(?b, 0)`), which is why it is driven rather than assumed.
#[test]
fn a_bodied_equation_shaped_head_still_mints_no_connective() {
    const SRC: &str = r#"
namespace wi896.connective
  sort S
    import anthill.prelude.{Int64, Bool}
    rule bodiedEq896(?x) = ?y :- Int64.gt(?x, 0), ?y = 1
    rule lbl896: bodiedUni896(?x) <=> ?y :- Int64.gt(?x, 0), ?y = 1
  end
end
"#;
    let kb = crate::common::load_kb_with(SRC);
    for (q, why) in [
        (
            "S.eq",
            "a bodied `=` head is a predicate rule whose functor is the CONNECTIVE; \
                  a local shadow hides every equation from `apply_eq_rules`",
        ),
        ("S.unify", "same for `<=>`"),
        (
            "S.bodiedEq896",
            "and the LHS is not the subject either — a bodied rule is not \
                           an equation, so its head is not about its LHS",
        ),
        (
            "S.bodiedUni896",
            "same, labeled — the label still decides nothing",
        ),
    ] {
        let qn = format!("wi896.connective.{q}");
        assert!(
            !kb.has_qualified_name(&qn),
            "`{qn}` must not be minted: {why}"
        );
    }
}

/// …AND THE RESIDUE, PINNED RATHER THAN HIDDEN. Once the head RESOLVES, the clause joins
/// whatever it resolved to — and if that symbol is backed by a resolver builtin, the
/// builtin decides the goal and the clause is never reached. No diagnostic says so.
///
/// This is NOT introduced here, and the ticket must not be read as introducing it: the
/// smt-gen `bound` lemma has always been a clause on the builtin-backed
/// `anthill.prelude.PartialOrd.gte`, inert at SLD and cited only by the SMT backend. What
/// WI-896 changes is which names reach that state, not the state itself.
///
/// MEASURED, and the arity is the surprising half — which is why both are driven rather
/// than one being assumed from the other. At the builtin's OWN arity the builtin wins:
/// `or(?a, ?b)` enumerates disjunction choice points and leaves the user's clause
/// unreached. At any OTHER arity there is no builtin behaviour to shadow it, and the
/// clause resolves normally. So "a reserved-name head is dead" is false as stated, and
/// the honest claim is narrower.
///
/// Filed as WI-899. When a refusal lands, this test fails and names what to update.
#[test]
fn a_clause_on_a_builtin_backed_name_is_inert_at_sld() {
    const SRC: &str = r#"
namespace wi896.inert
  import anthill.prelude.{Int64}
  fact p896(1)
  rule or(?a) :- p896(?a)
  rule or(?a, ?b) :- p896(?a), p896(?b)
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    let solve = |kb: &mut _, arity| {
        crate::wi282_rule_body_dot_test::resolve_query(kb, "anthill.kernel.or", arity)
    };
    assert_eq!(
        solve(&mut kb, 1),
        1,
        "PINNED (not an endorsement): off the builtin's arity the user's clause is \
         reachable — `p896` has exactly one fact",
    );
    assert!(
        solve(&mut kb, 2) > 1,
        "PINNED (not an endorsement): at the builtin's own arity `or` is disjunction and \
         the user's 2-ary clause is never reached, with no diagnostic. If this now FAILS, \
         WI-899's refusal has landed — delete this test and assert the load error instead.",
    );
}
