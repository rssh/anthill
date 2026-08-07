//! WI-894 — a rule-introduced functor is SCOPED to where it is written, not one bare
//! global name. The rule and its rationale live in `docs/kernel-language.md` §"A
//! rule-introduced functor is scoped where it is written"; the mechanism lives on
//! `load::scan_rule_goal`. This file drives what a LOAD and an EVAL see.
//!
//! Read [`an_unimported_functor_is_refused_in_an_operation_body`] first if this file
//! goes red: scoping is only safe because an un-imported use is refused rather than
//! silently inert. WI-1034 extended that refusal to a rule body's GOAL position, and
//! [`a_rule_body_does_not_yet_refuse_an_unimported_functor`] pins the one position
//! where it still does not exist: a goal's ARGUMENT, i.e. a `[simp]` redex that can
//! never fire (WI-895's remaining half).
//!
//! STDLIB LOADS: FIVE, one per `#[test]` — `crate::common::interp_for` /
//! `load_kb_with` parse and load ~76 stdlib and binding files each time (~0.5s). The
//! per-claim naming is what forces them; see `wi884_sibling_backing_test`'s header.

use anthill_core::eval::Value;

/// THE TICKET'S OWN MEASUREMENT, deliberately INVERTED so a merge is visible rather
/// than inferred: sort `B`'s laws answer the OPPOSITE branch from sort `A`'s, and both
/// sorts call `pick894(true, 10, 20)` from their own body.
///
/// Pre-fix BOTH answered 10 — `A`'s definition won for both, and `B` could not use its
/// own rules. Asserting only `A` would have passed against the defect, which is exactly
/// how WI-887 was misled by a half-eaten rule pair.
const INVERTED_PAIR: &str = r#"
namespace wi894.inverted
  sort A
    import anthill.prelude.{Int64, Bool}
    rule {
      pickTrue:  pick894(true, ?t, ?_) = ?t [simp]
      pickFalse: pick894(false, ?_, ?e) = ?e [simp]
    }
    operation driveA(n: Int64) -> Int64 = pick894(true, 10, 20)
  end

  sort B
    import anthill.prelude.{Int64, Bool}
    rule {
      pickTrue:  pick894(true, ?_, ?e) = ?e [simp]
      pickFalse: pick894(false, ?t, ?_) = ?t [simp]
    }
    operation driveB(n: Int64) -> Int64 = pick894(true, 10, 20)
  end
end
"#;

/// Both levels of the one claim on ONE load: what each sort COMPUTES, and the symbol
/// identity that explains it — so a regression names itself at the symbol level instead
/// of surfacing only as an arithmetic surprise.
#[test]
fn each_sort_uses_its_own_rules() {
    let mut interp = crate::common::interp_for(INVERTED_PAIR);
    for (op, expected, why) in [
        ("A.driveA", 10, "A's `pickTrue` selects the THEN argument"),
        ("B.driveB", 20, "B's `pickTrue` selects the ELSE argument — its own law, not A's"),
    ] {
        let path = format!("wi894.inverted.{op}");
        match interp.call(&path, &[Value::Int(0)]) {
            Ok(Value::Int(n)) if n == expected => {}
            other => panic!("{path} must answer {expected}: {why}; got {other:?}"),
        }
    }
    for q in ["wi894.inverted.A.pick894", "wi894.inverted.B.pick894"] {
        assert!(
            interp.kb().has_qualified_name(q),
            "`{q}` must be a scoped symbol of its own sort — there is no bare global \
             `pick894` for the two to collapse onto",
        );
    }
}

/// A LABEL NAMES THE RULE; AN EQUATION'S LHS NAMES THE FUNCTION. Both spellings of the
/// same definition must scope alike, since `bool.anthill` writes its two `ite` clauses
/// LABELED (`ite_true:` / `ite_false:`) and the ticket's own example writes them bare.
/// If only one were scoped, `ite` — this ticket's worked example — would still travel.
///
/// The PREDICATE column scopes alike since WI-896, which removed the label carve-out this
/// file originally recorded. The four label x name cells live in
/// `wi896_labeled_predicate_head_test`; the rows here keep the SHAPES honest.
const HEAD_SHAPES: &str = r#"
namespace wi894.labels
  sort S
    import anthill.prelude.{Int64, Bool}
    rule {
      lblEq894: labeledEq894(?x) = ?x [simp]
      bareEq894(?x) = ?x [simp]
      lblUni894: labeledUnify894(?x) <=> ?x [simp]
      lblPred894: labeledPred894(?x) :- Int64.gt(?x, 0)
      barePred894(?x) :- Int64.gt(?x, 0)
      -- a BODIED `=` head is not an equation (§8.3: an equation is bodyless), so it
      -- takes the predicate path, where its head names the CONNECTIVE
      lblBodied894: bodied894(?x) = ?y :- Int64.gt(?x, 0), ?y = 1
      -- the same shape UNLABELED: the predicate path must still refuse to mint the
      -- CONNECTIVE (`eq`/`unify`), which is what WI-530 forbids
      bareBodied894(?x) <=> ?y :- Int64.gt(?x, 0), ?y = 1
    }
  end

  -- The converter's own functors sit at the subject position for the accessor forms;
  -- they are the desugar's, not the rule's. Deliberately UNTAGGED: a `[simp]` here
  -- would be indexed under the GLOBAL kernel `field_access` / `dot_apply` functor and
  -- so would rewrite `?x.f` for ANY receiver in the whole loaded stdlib during this
  -- test's typing pass. The claim under test is which SYMBOL is minted, which the tag
  -- has no bearing on — so the tag is a live hazard buying nothing.
  sort M
    import anthill.prelude.{Int64, Bool}
    entity M(f: Int64)
    rule { dotted: ?x.foo894(?y) = ?y }
    rule { fieldy: ?x.f = 7 }
    -- the PREDICATE spellings of the same shapes. They reach the OTHER path, where the
    -- guard was missing: MEASURED, `rule ?x.m894(?y) :- p894(?x)` minted
    -- `<ns>.dot_apply`, shadowing reserved kernel vocab for the whole scope.
    rule p894(?x) :- Int64.gt(1, 0)
    rule ?x.m894(?y) :- p894(?x)
    rule ?a + ?b :- Int64.gt(?a, 0)
  end

  -- Names that already mean something globally must not be captured.
  sort C
    import anthill.prelude.{Int64, List, Bool}
    rule { consLaw: cons(?h, ?t) <=> ?h }
    rule { someLaw: some(?x) <=> ?x }
    rule { eqLaw: eq(?a, ?a) <=> true }
    -- a QUALIFIED subject REFERENCES; it never introduces. `resolve_in_scope` matches
    -- SHORT names only, so it says NotFound for `String.isEmpty894` and the caller's
    -- check cannot see the reference — MEASURED minting a symbol whose SHORT name was
    -- literally `String.isEmpty894`, which the WI-752 ladder then ranks first.
    rule { qualified: String.isEmpty894(?s) <=> true }
  end
end
"#;

/// WHICH NAME A RULE HEAD INTRODUCES — every shape in one table, on one load, because
/// they are one question asked six ways and a table reads better than six near-identical
/// tests. Each row names its own reason, so a regression still fails by claim.
///
/// TWO ROWS ARE REGRESSION GUARDS FOR DEFECTS THIS FIX ITSELF INTRODUCED, both caught in
/// review and both MEASURED. (1) Descending into an equation's LHS re-opened WI-530's
/// hole one level down, since `resolve_in_scope` answers `NotFound` for every
/// implicit-prelude name: `rule cons(?h, ?t) <=> ?h [simp]` loaded CLEAN, minted a
/// sort-local `cons`, and silently re-pointed every bare `cons` in the sort so that
/// `cons(1, nil())` answered `1` — a law written about `List.cons` quietly became a law
/// about a different function, this ticket's own defect class. (2) Without the
/// bodyless guard, `bodied894` was introduced AND the label guard bypassed, on a rule
/// that is not an equation at all. What a non-captured law MEANS is unchanged from
/// pre-WI-894: it applies to the real `List.cons`.
#[test]
fn which_name_a_rule_head_introduces() {
    let kb = crate::common::load_kb_with(HEAD_SHAPES);
    for (q, want, why) in [
        ("S.labeledEq894", true, "a labeled equation still defines its LHS function"),
        ("S.bareEq894", true, "an unlabeled equation defines its LHS function"),
        ("S.labeledUnify894", true, "`<=>` is the same definition as `=` here"),
        ("S.barePred894", true, "an unlabeled predicate head IS the rule's identity"),
        ("S.labeledPred894", true, "WI-896: a label names the CLAUSE, so it does not decide \
                                    whether the head introduces — this row read `false` \
                                    while the carve-out stood"),
        ("S.bodied894", false, "a bodied `=` head is a predicate rule ABOUT `eq`, not about \
                                its LHS — the label is not what stops it"),
        ("S.eq", false, "WI-530: a bodied equation-SHAPED head must never mint the connective"),
        ("S.unify", false, "same for `<=>` — a local shadow silently reclassifies the rule"),
        ("S.bareBodied894", false, "nor its subject: a bodied rule is not an equation, so \
                                    its LHS is not what the head is about (unchanged pre-WI-894)"),
        ("M.dot_apply", false, "`?x.m(?y)` carries the converter's functor, not the rule's \
                                — on the EQUATION and the PREDICATE path alike"),
        ("M.field_access", false, "`?x.f` likewise — and a local copy shadows kernel vocab"),
        ("M.add", false, "a minted INFIX head (`?a + ?b`) is the desugar's functor too"),
        ("M.p894", true, "…while an ordinary unlabeled predicate head still introduces"),
        ("C.cons", false, "`cons` already resolves through the implicit prelude"),
        ("C.some", false, "same — capturing it changes what the law is about"),
        ("C.eq", false, "same, and WI-530 is the precedent for the connective itself"),
        ("C.String.isEmpty894", false, "a dotted subject is a REFERENCE — minting it would \
                                        define a symbol whose short name contains a dot"),
        ("C.isEmpty894", false, "…and it must not be re-homed under the short name either"),
    ] {
        let qn = format!("wi894.labels.{q}");
        assert_eq!(kb.has_qualified_name(&qn), want, "`{qn}`: {why}");
    }
}

/// THE HALF THAT MAKES SCOPING SAFE, IN AN OPERATION BODY. An un-imported use is
/// REFUSED there, so WI-894 does not trade a silent merge for a silent death:
/// `wi884_sibling_backing_test` drives the positive twin (the import, and the qualified
/// member spelling, both reducing) and this is its negative control.
#[test]
fn an_unimported_functor_is_refused_in_an_operation_body() {
    const SRC: &str = r#"
namespace wi894.unimported2
  sort S
    import anthill.prelude.{Int64, Bool}
    operation viaBare(n: Int64) -> Int64 = ite(true, 1, 2)
  end
end
"#;
    let Err(errs) = crate::common::try_load_kb_with(SRC) else {
        panic!("a bare `ite` with no import must be refused, not reach `Bool`'s rules");
    };
    assert!(
        errs.iter().any(|e| e.contains("ite")),
        "the refusal must NAME the functor it is about, got {errs:?}",
    );
}

/// THE IMPORTED SPELLING IS ALSO REFUSED where there is no `[simp]` redex — a computed
/// condition has nothing to inline (WI-884), and `ite` is not an operation to dispatch
/// to (WI-887), so `ite(gte(a, b), a, b)` in an operation body cannot load either way.
/// Driven so the pair is a matched set: the naming path WI-894 adds does NOT make this
/// shape work, and nothing here should be read as claiming it does.
///
/// Asserts REFUSAL and the named functor, deliberately NOT the message text: the
/// imported spelling's message is currently misleading ("expected resolved name, got
/// unresolved", because a `Goal` functor routes into WI-714's relation machinery and
/// finds no clauses), which is WI-898. Pinning the string would make fixing that a
/// test edit rather than an improvement.
#[test]
fn an_imported_functor_with_no_redex_is_also_refused() {
    const SRC: &str = r#"
namespace wi894.noredex
  sort S
    import anthill.prelude.{Int64, Bool}
    import anthill.prelude.Bool.{ite}
    operation pickMax(a: Int64, b: Int64) -> Int64 = ite(Int64.gte(a, b), a, b)
  end
end
"#;
    let Err(errs) = crate::common::try_load_kb_with(SRC) else {
        panic!("no redex and no operation to dispatch to — this must not load");
    };
    assert!(
        errs.iter().any(|e| e.contains("ite")),
        "the refusal must NAME the functor it is about, got {errs:?}",
    );
}

/// …AND THE GAP, PINNED RATHER THAN HIDDEN — now HALF closed, and this pins the half
/// that is not. An un-imported functor interns bare, so the goal loads clean and simply
/// never matches the scoped `[simp]` rules. That is silent inertness — the failure mode
/// the test above rules out for operation bodies — and it is how this very change first
/// showed up (`wi884`'s `ite_reduces` went from 1 solution to 0 with no diagnostic until
/// its `import` was added).
///
/// **WI-1034 closed the GOAL-position half**: a rule-body goal whose functor names
/// nothing is refused at load, named and located. This fixture survives it because
/// `ite` here is in an ARGUMENT — a DATA slot, which is not a goal and is not walked —
/// and `holds894` is a declared fact. So the shape still loads, still never fires, and
/// still says nothing, which is WI-895's remaining half.
///
/// The distance between the halves is a factor of fifteen and that is why they are
/// separate: WI-1034's probe counted 20 dangling names over the corpus in goal position
/// and ~313 with argument positions included — every constructor written in an argument
/// is one — so the argument half needs its own predicate (a `[simp]` redex that cannot
/// fire is not the same claim as a goal that cannot match), not a wider walk.
///
/// This test asserts TODAY'S behaviour deliberately, so the gap is a recorded fact with
/// a home rather than an assumption: when WI-895's remaining half lands, this test FAILS
/// and names what to update.
#[test]
fn a_rule_body_does_not_yet_refuse_an_unimported_functor() {
    const SRC: &str = r#"
namespace wi894.rulebodygap
  import anthill.prelude.{Int64, Bool}
  rule uses894(?x) :- holds894(ite(true, 10, 20)), ?x = 1
  fact holds894(10)
end
"#;
    assert!(
        crate::common::try_load_kb_with(SRC).is_ok(),
        "PINNED GAP (not an endorsement): a rule body's un-imported functor in an \
         ARGUMENT position still loads clean — the GOAL position is refused as of \
         WI-1034 (`wi1034_undefined_rule_body_goal_test`). If this now FAILS, WI-895's \
         remaining half has landed — delete this test and fold the case into \
         `an_unimported_functor_is_refused_in_an_operation_body`.",
    );
}
