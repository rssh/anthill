//! WI-838 — the MIXED provider pair is a load-time ambiguity.
//!
//! Two dictionaries for one `(spec, carrier)` are ambiguous whatever KIND
//! supplies them, but the two checks that refuse them were each grouped BY
//! PROVIDER KIND, so neither saw a cross-kind pair:
//!
//!   * `AmbiguousInstanceFact` keyed a provision on its own `sort_ref`, which for
//!     a namespace-level `fact Combiner[T = Tag, combine = …]` IS the carrier;
//!   * `AmbiguousWitness` skipped every provision whose provider IS the carrier,
//!     and the witness's own provision (`sort WitCombiner provides
//!     Combiner[T = Tag]`) binds no op, so the fact grouping never saw it either.
//!
//! MEASURED at HEAD before the fix, the pair loaded clean and the two dispatch
//! routes did not even agree on the winner:
//!
//!   * value-directed dispatch ran the INSTANCE FACT's op (`99`, not the
//!     witness's `5`) — eval's `own .or_else(instance_fact_op_binding)
//!     .or_else(witness_op_for_carrier)` chain — regardless of which was
//!     declared first;
//!   * the THREADED-DICT route (a nullary spec op, where no value can classify
//!     the carrier) died `EvalError::Internal("unhandled Expr variant in eval")`,
//!     though each provider ALONE works on that route (`42` / `7`).
//!
//! The fix is ONE coherence grouping over all provider kinds
//! (`check_provider_operations`), from which every diagnostic is read — so a kind
//! can no longer have a grouping of its own to hide in. The grouping is also where
//! "what is a witness" now lives once (`witness_dispatch_carrier`), shared with
//! the eval/typer dispatch reader that previously kept its own copy.
//!
//! WHAT WI-843 THEN CHANGED, since it is visible in the controls below. Tier 3
//! (058 §4.1) let two NAMEABLE providers coexist and deleted `AmbiguousWitness`
//! outright, so control 1 flipped from "keeps the witness diagnostic" to "loads
//! clean". The MIXED pair did not flip, and that is this file's point restated
//! rather than weakened: the gate is NAMEABILITY (§4.3), an instance fact has no
//! name, and the grouping built here is what lets a per-GROUP rule see the
//! unnameable candidate at all.
//!
//! REFERENCE: `docs/proposals/058-modular-instances.md` §4.3.

/// The load diagnostics of `src`, empty when it loads clean — `common`'s shared
/// loader, the same one `interp_for` runs on, so a program asserted to load here
/// is the program the eval assertions below actually run.
fn load_errors(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

/// THE FIX: the mixed pair is refused, by a diagnostic that names BOTH providers
/// AND their kinds. The diagnostic IDENTITY is asserted, not merely that the load
/// fails — this program loaded CLEAN before WI-838, so a failure-only assertion
/// would have been satisfied by any unrelated error appearing later.
#[test]
fn mixed_instance_fact_and_witness_is_a_loud_ambiguity() {
    let snippet = r#"namespace test.wi838.mixed
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
    let errs = load_errors(snippet);
    let mixed: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains("ambiguous provider kinds"))
        .collect();
    assert_eq!(
        mixed.len(),
        1,
        "the mixed instance-fact + witness pair for (Combiner, Tag) must be ONE loud \
         cross-kind ambiguity; all errors: {errs:?}"
    );
    let text = mixed[0];
    // BOTH providers, and BOTH kinds, must be legible from the message: the
    // witness is nameable, the instance fact is not, so it is identified by kind
    // and count.
    assert!(
        text.contains("test.wi838.mixed.Combiner")
            && text.contains("test.wi838.mixed.Tag")
            && text.contains("test.wi838.mixed.WitCombiner")
            && text.contains("instance fact")
            && text.contains("witness sort"),
        "the diagnostic must name the spec, the carrier, the WITNESS provider, and \
         both provider KINDS: {text}"
    );
    // The cross-kind pair is neither same-kind conflict — a mixed pair reported
    // under a same-kind diagnostic would name a nonexistent second fact/witness.
    // WI-843 deleted the witness diagnostic, so only the instance-fact one is a
    // live mis-labelling risk; asserting the absence of a string no code can emit
    // would be a control that cannot fail.
    assert!(
        !errs.iter().any(|e| e.contains("ambiguous instance:")),
        "one fact + one witness is not the same-kind FACT ambiguity: {errs:?}"
    );
}

/// CONTROL 1 (same kind, witnesses) — replacing the instance fact with a SECOND
/// witness sort must NOT be a load error at all.
///
/// It was one when WI-838 landed (`AmbiguousWitness`, asserted here verbatim);
/// WI-843 deleted that refusal, because a witness sort has a NAME and so a use
/// site can select one (058 §4.1 tier 3). Keeping the row as a CLEAN-LOAD control
/// is what makes the mixed-pair test above mean something: the two programs differ
/// only in whether one candidate is an unnameable instance fact, so this is the
/// evidence that `MixedProviderKinds` fires on NAMEABILITY and not merely on
/// "two providers".
#[test]
fn two_witnesses_coexist_and_are_no_load_error() {
    let snippet = r#"namespace test.wi838.twowit
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end

  sort WitA
    fact Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 5)
  end

  sort WitB
    fact Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 6)
  end
end
"#;
    let errs = load_errors(snippet);
    assert!(
        errs.is_empty(),
        "two NAMEABLE providers coexist under 058 tier 3 — no load diagnostic of \
         any kind, including the cross-kind one: {errs:?}"
    );
}

/// CONTROL 2 (same kind, instance facts) — two differing instance facts must keep
/// the pre-existing `AmbiguousInstanceFact` diagnostic verbatim.
#[test]
fn two_instance_facts_keep_the_instance_diagnostic() {
    let snippet = r#"namespace test.wi838.twofact
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end

  operation combineA(x: Tag, y: Tag) -> Tag = tag(n: 1)
  operation combineB(x: Tag, y: Tag) -> Tag = tag(n: 2)

  fact Combiner[T = Tag, combine = combineA]
  fact Combiner[T = Tag, combine = combineB]
end
"#;
    let errs = load_errors(snippet);
    assert!(
        errs.iter().any(|e| e.contains(
            "ambiguous instance: 2 distinct instance facts provide \
             'test.wi838.twofact.Combiner' for carrier 'test.wi838.twofact.Tag'"
        )),
        "two instance facts must keep the INSTANCE diagnostic: {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("ambiguous provider kinds")),
        "two facts are a SAME-kind conflict, not a mixed one: {errs:?}"
    );
}

/// NON-REGRESSION — a single instance fact and a witness for DIFFERENT carriers
/// are independent instances, not a pair. Guards the unified grouping against
/// collapsing candidates that never meet at one dispatch site.
#[test]
fn fact_and_witness_for_distinct_carriers_do_not_collide() {
    let snippet = r#"namespace test.wi838.distinct
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  sort Ring
    entity ring(n: Int64)
  end

  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 99)
  fact Combiner[T = Tag, combine = tagCombine]

  sort RingCombiner
    fact Combiner[T = Ring]
    operation combine(x: Ring, y: Ring) -> Ring = ring(n: 5)
  end
end
"#;
    let errs = load_errors(snippet);
    assert!(
        !errs.iter().any(|e| e.contains("ambigu")),
        "a fact for Tag and a witness for Ring are distinct instances: {errs:?}"
    );
}

/// EXEMPTION 1, PRESERVED — a spec that declares NO OPS has no dictionary to be
/// ambiguous about (binding-extraction plumbing, not dispatch), so two providers
/// of it still load. The gate is the witness kind's own (`own_ops` non-empty);
/// its `Provider::Fact` peer is `provision_binds_any_op`, and since a Fact
/// candidate requires an op-valued binding, a no-ops spec can never raise the
/// cross-kind error either.
#[test]
fn spec_with_no_ops_exemption_still_loads() {
    let snippet = r#"namespace test.wi838.noops
  import anthill.prelude.Int64

  sort BareCarrier
    sort C = ?
  end

  sort Tag
    entity tag(n: Int64)
  end

  sort HolderA
    fact BareCarrier[C = Tag]
  end

  sort HolderB
    fact BareCarrier[C = Tag]
  end
end
"#;
    let errs = load_errors(snippet);
    assert!(
        !errs.iter().any(|e| e.contains("ambigu")),
        "a spec declaring no operations has no dictionary to be ambiguous about: {errs:?}"
    );
}

/// EXEMPTION 2, PRESERVED — two CONCRETE providers (sorts WITH constructors) of
/// one spec application are the existential / manifest-provider pattern
/// (`MemStore` / `DiskStore` provide `KVStore[K = String]`), selected by the
/// value, not an ambiguity.
#[test]
fn concrete_provider_exemption_still_loads() {
    let snippet = r#"namespace test.wi838.concrete
  import anthill.prelude.{Int64, String}

  sort KVStore
    sort K = ?
    operation get(k: K) -> Int64
  end

  sort MemStore
    entity mem(n: Int64)
    fact KVStore[K = String]
    operation get(k: String) -> Int64 = 1
  end

  sort DiskStore
    entity disk(n: Int64)
    fact KVStore[K = String]
    operation get(k: String) -> Int64 = 2
  end
end
"#;
    let errs = load_errors(snippet);
    assert!(
        !errs.iter().any(|e| e.contains("ambigu")),
        "two concrete backends providing one spec are selected by the value: {errs:?}"
    );
}

/// EXEMPTION 2, REACH — pinned deliberately, because WI-838 does NOT widen it. A
/// mixed pair whose WITNESS provider is CONCRETE is still exempt, so it still
/// loads: the gate asks whether the PROVIDER carries values, and this one does.
/// That is the same reach the exemption already had for two concrete witnesses,
/// carried across unchanged — WI-838's scope is the cross-kind BLIND SPOT (a
/// grouping that could not see the pair), not the exemption's criterion. Pinned
/// so that changing the criterion is a deliberate act with a failing test, rather
/// than an unnoticed side effect.
#[test]
fn concrete_witness_beside_a_fact_stays_exempt() {
    let snippet = r#"namespace test.wi838.concretemixed
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
    entity wit(n: Int64)
    fact Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 5)
  end
end
"#;
    let errs = load_errors(snippet);
    assert!(
        !errs.iter().any(|e| e.contains("ambigu")),
        "the concrete-provider exemption is carried across kinds unchanged by WI-838: {errs:?}"
    );
}

/// NON-REGRESSION — each provider ALONE still loads and still dispatches. Without
/// this, every assertion above could be satisfied by a check that refused both
/// single-provider programs too.
#[test]
fn each_provider_alone_still_loads_and_dispatches() {
    let fact_only = r#"namespace test.wi838.factonly
  import anthill.prelude.Int64
  import test.wi838.factonly.Combiner.{combine}

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 99)
  fact Combiner[T = Tag, combine = tagCombine]

  operation runCombine() -> Int64 =
    match combine(tag(n: 1), tag(n: 2))
      case tag(v) -> v
end
"#;
    let witness_only = r#"namespace test.wi838.witonly
  import anthill.prelude.Int64
  import test.wi838.witonly.Combiner.{combine}

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end

  sort WitCombiner
    fact Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 5)
  end

  operation runCombine() -> Int64 =
    match combine(tag(n: 1), tag(n: 2))
      case tag(v) -> v
end
"#;
    for (src, ns, want) in [
        (fact_only, "test.wi838.factonly.runCombine", 99),
        (witness_only, "test.wi838.witonly.runCombine", 5),
    ] {
        assert!(
            !load_errors(src).iter().any(|e| e.contains("ambigu")),
            "a SOLE provider is never ambiguous ({ns})"
        );
        // A fresh interpreter per program — a trapped call poisons later calls.
        let mut interp = crate::common::interp_for(src);
        match interp.call(ns, &[]) {
            Ok(anthill_core::eval::Value::Int(n)) => {
                assert_eq!(n, want, "{ns} must dispatch to its sole provider")
            }
            other => panic!("{ns} should dispatch to its sole provider; got {other:?}"),
        }
    }
}
