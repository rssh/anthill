//! WI-859 (proposal 058 phase 8a) — the coherence grouping's MISSING CANDIDATE
//! KIND: a SELF-PROVIDER.
//!
//! WI-838 made the grouping general over provider kinds — one group per
//! `(spec, dispatch carrier)`, so a kind can no longer have a grouping of its own
//! to hide in. It admitted a candidate two ways, and a carrier's OWN provision is
//! neither: `sort Leaf { fact Desc[T = Leaf]; operation describe(…) = … }` binds no
//! op (so `provision_binds_any_op` rejects it as an instance FACT) and its provider
//! IS its carrier (so `witness_dispatch_carrier` answers `None` and rejects it as a
//! WITNESS). MEASURED at WI-855's delivery: a self-provider could therefore never be
//! one half of anything, so `Leaf` beside a rival provider of `Desc[T = Leaf]`
//! formed a group of ONE and the pair was invisible to load-time coherence
//! altogether.
//!
//! This ticket adds the third kind. It is a change of VISIBILITY, not of verdicts —
//! measured cell by cell over the stdlib and the whole test corpus before any arm was
//! written. The measurement (per-cell occurrence counts) is the record in
//! `docs/design/058-implementation.md` §11; what the tests below are organised around
//! is which cell each one drives:
//!
//! | composition (facts, witnesses, selves) | verdict | driven by |
//! |---|---|---|
//! | (0, ≥1, *) | ADMIT — every candidate nameable (058 tier 3) | `a_self_provider_is_a_candidate_of_its_own_group` |
//! | (1, 0, 1)  | ADMIT — may be ONE dictionary; see below | `a_fact_completing_a_type_only_self_provision_still_answers` (+ its rival twin) |
//! | (≥2, *, *) | `AmbiguousInstanceFact`, unchanged | `wi838_mixed_provider_coherence_test` |
//! | (1, ≥1, *) | `MixedProviderKinds`, unchanged (a self-provider in such a group goes unnamed by the message) | `the_mixed_fact_and_witness_pair_is_still_refused` |
//!
//! The `(1, 0, 1)` cell is the one that had to be DECIDED rather than inherited, and
//! the measurement decided it: the corpus holds exactly two, and they are the two
//! opposite shapes. `test.wi837.hidden.Pebble` is a type-only self-provision COMPLETED
//! by a retroactive `fact PartialEq[T = Pebble, eq = pebbleEq]` — one dictionary
//! written in two places, the WI-431 shape, which loads clean and whose `eq` answers.
//! `test.wi837.ownplusfact.Pebble` is the carrier's OWN `eq` member RIVALLED by a
//! fact binding a different one — already refused, by `AmbiguousEqDispatch`. A group
//! cannot tell them apart, because the question is per-OP and a group is per-SPEC.
//! So the cell is admitted here and the rival half stays with the readers that can
//! count per op (058 §3.7) — each driven below, so "someone else refuses it" is
//! measured rather than assumed.
//!
//! WHAT FAILS IF THIS IS BACKED OUT — measured, by disabling the self leg and
//! re-running: exactly the three tests that read the grouping.
//! `a_self_provider_is_a_candidate_of_its_own_group`,
//! `two_self_provisions_of_one_carrier_are_one_candidate`, and the group half of
//! `a_fact_completing_a_type_only_self_provision_still_answers` — before WI-859 each
//! of those groups holds one candidate or none. The rest pass EITHER WAY by design:
//! they are the matrix's unchanged cells, and their job is to fail if a future change
//! to the grouping moves one. (Deleting only the SECOND admission arm is caught
//! elsewhere: `check_provider_operations`' `debug_assert` fires on the wi837
//! fixtures, which is what keeps that arm from being decorative.)
//!
//! REFERENCE: proposal 058 §3.6; `docs/design/058-implementation.md` §3, §8, §11.

use anthill_core::kb::typing::provider_coherence_candidates;

/// The load diagnostics of `src`, empty when it loads clean.
fn load_errors(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

/// `Desc` plus a self-providing `Leaf`, with `rival` interpolated after them — so the
/// control program IS the pinned program minus the rival, rather than a retyped twin
/// of it (the trap `common::DESC_INSTANCES` was lifted to close). `wi855`'s shape,
/// which this file's cell (0, ≥1, 1) is measured on.
fn self_provider_program(ns: &str, rival: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
{rival}end
"#
    )
}

/// An ABSTRACT witness of `Desc[T = Leaf]` — the second candidate. Abstract on
/// purpose: a CONCRETE rival is exempted from the witness rule as a manifest backend,
/// so it would form no group at all (`wi855`'s other arm pins that).
const RIVAL: &str = r#"
  sort Rival
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
"#;

/// THE ACCEPTANCE PROBE, and cell (0, ≥1, 1). A carrier's own provision is a candidate
/// of its own group; beside a rival the group counts TWO, and it is ADMITTED because
/// both are nameable (058 tier 3 lets them coexist and refuses only an unselected
/// dispatch — `load_kb_with` panics on any load error, so the clean load is asserted
/// here rather than in a test of its own).
///
/// Before WI-859 this group held ONE candidate (the witness) in the pair program and
/// NONE in the control — which is the whole defect, since a group of one is skipped
/// before any rule looks at it. The VERDICT is the same either way, which is exactly
/// why the acceptance had to be a probe: nothing about the load could show it.
///
/// Note `Leaf` is CONCRETE (`entity leaf`). That is deliberate: the concrete-provider
/// exemption applies to the WITNESS kind only, and applying it to the self kind would
/// exempt nearly every real carrier and leave the kind empty.
///
/// `wi855_ambiguous_requirement_test::load_coherence_admits_the_tie_either_way` holds
/// the other half — that this pair still reaches its RUNTIME tie.
#[test]
fn a_self_provider_is_a_candidate_of_its_own_group() {
    let kb = crate::common::load_kb_with(&self_provider_program("test.wi859.selfwitness", RIVAL));
    let mut cands = provider_coherence_candidates(
        &kb,
        "test.wi859.selfwitness.Desc",
        "test.wi859.selfwitness.Leaf",
    );
    cands.sort();
    assert_eq!(
        cands,
        vec![
            "self:test.wi859.selfwitness.Leaf".to_string(),
            "witness:test.wi859.selfwitness.Rival".to_string(),
        ],
        "the (Desc, Leaf) group must hold the self-provider AND the witness"
    );

    // THE CONTROL that makes the count mean something: with the rival deleted the
    // self-provider is STILL a candidate — so the two above are two kinds, not one
    // kind counted twice, and the assertion is about the SELF-PROVIDER rather than
    // about there happening to be two of anything.
    let alone = crate::common::load_kb_with(&self_provider_program("test.wi859.selfalone", ""));
    assert_eq!(
        provider_coherence_candidates(
            &alone,
            "test.wi859.selfalone.Desc",
            "test.wi859.selfalone.Leaf"
        ),
        vec!["self:test.wi859.selfalone.Leaf".to_string()],
        "a sole self-provider is a group of ONE — recorded, and skipped by the size gate"
    );
}

/// CELL (1, 0, 1), the COMPLETION half — a type-only self-provision plus a
/// retroactive instance fact binding the op is ONE dictionary, and it must keep
/// LOADING AND ANSWERING.
///
/// This is the shape the measurement found (`test.wi837.hidden.Pebble`), reproduced
/// here to tie the matrix row to a driven answer: `pebbleEq` is true for ANY pair, so
/// ONE solution means the fact's binding is the live entry and NONE means equality
/// fell back to structural — the same discriminator
/// `a_type_only_provision_does_not_hide_a_later_eq_binding` uses, asserted here
/// beside the GROUP it forms, which is the half that ticket had no reason to look at.
///
/// `PartialEq` rather than an invented spec, and that is forced rather than chosen: a
/// CONCRETE carrier's provision must back every spec op
/// (`UnbackedProviderOperation`), so a type-only self-provision only loads where the
/// op is backed some other way — `eq` is a resolver builtin. The one other way to back
/// it is a spec-op DEFAULT BODY, and that route cannot express this cell at all,
/// because the default SHADOWS the fact: MEASURED three ways, a `Desc` whose
/// `describe` defaults to `1` beside `fact Desc[T = Leaf, describe = leafDescribe]`
/// answers **1** — with a self-provision AND without one (so the shadowing is not this
/// grouping's business), while the same default beside the carrier's OWN `describe`
/// member correctly answers `7`. That is WI-444's "defaults fill gaps, they do not
/// shadow" wired to route 1 and never to WI-431's fact binding — a dispatch-precedence
/// defect, filed as WI-1010.
#[test]
fn a_fact_completing_a_type_only_self_provision_still_answers() {
    let src = r#"namespace test.wi859.completion
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Pebble
    entity pebble(n: Int64)
    provides PartialEq[T = Pebble]
  end

  operation pebbleEq(a: Pebble, b: Pebble) -> Bool = true

  fact PartialEq[T = Pebble, eq = pebbleEq]

  rule peq(?x, ?y) :- eq(?x, ?y)
end
"#;
    crate::wi837_witness_eq_dispatch_test::assert_loads_clean(
        src,
        "a fact completing a type-only self-provision is ONE dictionary",
    );
    // The group IS the cell claimed above — asserted rather than assumed, since a
    // program that loads for some unrelated reason would satisfy everything else.
    let mut kb = crate::common::load_kb_with(src);
    let mut cands = provider_coherence_candidates(
        &kb,
        "anthill.prelude.PartialEq",
        "test.wi859.completion.Pebble",
    );
    cands.sort();
    assert_eq!(
        cands,
        vec![
            "fact".to_string(),
            "self:test.wi859.completion.Pebble".to_string()
        ],
        "expected the (1 fact, 0 witnesses, 1 self) cell — the composition whose \
         admission this ticket had to decide"
    );
    let ctor = "test.wi859.completion.Pebble.pebble";
    let (x, y) = (
        crate::wi837_witness_eq_dispatch_test::entity_term(&mut kb, ctor, &[("n", 1)]),
        crate::wi837_witness_eq_dispatch_test::entity_term(&mut kb, ctor, &[("n", 2)]),
    );
    assert_eq!(
        crate::wi837_witness_eq_dispatch_test::solutions(
            &mut kb,
            "test.wi859.completion.peq",
            x,
            y
        ),
        1,
        "the retroactive fact's `eq` must still ANSWER — 0 solutions is the structural \
         fallback, i.e. the completing fact was dropped"
    );
}

/// CELL (1, 0, 1), the RIVAL half — the carrier's OWN member beside a fact binding a
/// DIFFERENT op is two dictionary entries, and the refusal is the per-OP reader's,
/// not the group's.
///
/// This is what makes admitting the cell honest rather than a hole: the composition
/// the grouping waves through is refused by a check that can see the thing the
/// grouping cannot — that two candidates supply the SAME op.
///
/// WHICH check that is CHANGED at WI-1032, and this test was the one that could not tell:
/// its assertions used to be `"ambiguous dispatch of …"` plus the carrier's name, and both
/// substrings appear in BOTH `unselected_instance_message` and
/// `ambiguous_spec_op_dispatch_message` — so it passed while its mechanism flipped
/// underneath it. It was `DispatchAmbiguous`, printing `(Leaf, Leaf)` — one carrier twice,
/// with a repair that cannot apply. It is now WI-1027's supplier tie, and the assertion
/// names the ROUTES so a future flip fails here instead of passing silently.
#[test]
fn a_fact_rivalling_the_carriers_own_member_is_still_refused() {
    let src = r#"namespace test.wi859.rival
  import anthill.prelude.Int64
  import test.wi859.rival.Desc.{describe}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end

  operation rivalDescribe(x: Leaf) -> Int64 = 7

  fact Desc[T = Leaf, describe = rivalDescribe]

  sort Driver
    operation drive(n: Int64) -> Int64 = describe(leaf())
  end
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| {
            e.contains("ambiguous dispatch of `test.wi859.rival.Desc.describe`")
                && e.contains("the carrier's own member 'test.wi859.rival.Leaf.describe'")
                && e.contains(
                    "an instance fact binding `describe = test.wi859.rival.rivalDescribe`",
                )
        }),
        "the rival pair must be refused, naming the op whose two suppliers tie AND each \
         supplier by its SUPPLY ROUTE — the refusal is WI-1027's `AmbiguousSpecOpDispatch` \
         at the CALL, a different mechanism from the grouping, firing with or without \
         WI-859: {errs:?}"
    );
}

/// DEDUP, and the BARE provision — two claims in one program, because one shape
/// drives both.
///
/// `provides Desc[T = Leaf]` and a bare `provides Desc` are two distinct provisions
/// (two spec views, two `SortProvidesInfo` facts) and ONE candidate: the dictionary
/// is the carrier's member set, and a carrier has one of those however many ways it
/// says it provides. That the candidate's identity is the CARRIER — not the provision
/// — is what makes the collapse right rather than lossy.
///
/// The bare provision is the second claim: it names no carrier at all, so
/// `witness_dispatch_carrier` answers `None` for it exactly as it does for the
/// explicit self-provision, and the self kind must take it. Grouping it anywhere else
/// would disagree with `provision_supplier`, which keys a carrier-less provision at
/// its provider — the load check and the dispatch reader answering different carriers
/// is the WI-838 shape.
#[test]
fn two_self_provisions_of_one_carrier_are_one_candidate() {
    let src = r#"namespace test.wi859.dedup
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    provides Desc
    operation describe(x: Leaf) -> Int64 = 1
  end
end
"#;
    crate::wi837_witness_eq_dispatch_test::assert_loads_clean(
        src,
        "one carrier saying twice that it provides one spec is not a conflict",
    );
    let kb = crate::common::load_kb_with(src);
    assert_eq!(
        provider_coherence_candidates(&kb, "test.wi859.dedup.Desc", "test.wi859.dedup.Leaf"),
        vec!["self:test.wi859.dedup.Leaf".to_string()],
        "one carrier, one member set, ONE self-provider candidate — and the BARE \
         provision lands in the same group as the explicit one"
    );
}

/// EXEMPTION, SHARED WITH THE WITNESS KIND — a spec that declares NO OPS has no
/// dictionary to be ambiguous about, so a self-provision of one is not a candidate at
/// all. Without this the kind would record a candidate for every binding-extraction
/// provision in the tree.
#[test]
fn a_self_provision_of_an_op_less_spec_is_not_a_candidate() {
    let src = r#"namespace test.wi859.noops
  import anthill.prelude.Int64

  sort BareCarrier
    sort C = ?
  end

  sort Leaf
    entity leaf
    provides BareCarrier[C = Leaf]
  end
end
"#;
    let kb = crate::common::load_kb_with(src);
    assert!(
        provider_coherence_candidates(&kb, "test.wi859.noops.BareCarrier", "test.wi859.noops.Leaf")
            .is_empty(),
        "an op-less spec has no dictionary, so its self-provision records no candidate"
    );
}

/// UNCHANGED CELL (1, ≥1, 0) — a fact beside a witness is still `MixedProviderKinds`.
/// Passes either way by design: its job is to fail if the new kind ever swallows the
/// mixed pair (it would, if the self leg claimed a provision the witness leg owns).
#[test]
fn the_mixed_fact_and_witness_pair_is_still_refused() {
    let src = r#"namespace test.wi859.mixed
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end

  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 99)
  fact Combiner[T = Tag, combine = tagCombine]

  sort WitCombiner
    fact Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 5)
  end
end
"#;
    assert!(
        load_errors(src)
            .iter()
            .any(|e| e.contains("ambiguous provider kinds")),
        "WI-838's verdict is unchanged by the third kind: {:?}",
        load_errors(src)
    );
}
