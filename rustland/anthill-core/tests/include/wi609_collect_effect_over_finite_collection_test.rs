//! WI-609 — typer: thread the RESULT effect of a carrier-param spec op called on
//! a receiver whose carrier is the op's OWN spec (the REFLEXIVE case).
//!
//! The thin finite combinators (WI-599) provide `FiniteCollection` by
//! materializing their wrapped source: `collect(m) = … collect(src) …`, where the
//! `source` field is typed `FiniteCollection[C = SrcC, Element = Src, E = ES]`.
//! The inner `collect(src)` dispatches `FiniteCollection.collect` — so spec_sort ==
//! carrier_sym == `FiniteCollection`. A spec does not *provide* itself, so
//! `carrier_param_receiver`'s `transitive_provision_view` (and WI-608's
//! `requires`-view, which matches `requires` entries only) found nothing, and
//! `collect`'s declared `effects E` never grounded to the receiver's written
//! `E = ES` — `collect.effects: expected [ES,…], got undeclared ?_`.
//!
//! The REFLEXIVE branch in `bind_spec_params_from_carrier_param` binds the spec's
//! params DIRECTLY off the receiver's own type-args (they share canonical VarIds
//! when carrier == spec), so `FiniteCollection.E ↦ ES` threads the result effect;
//! `carrier_param_receiver` hands it an empty view + `transitive=true` so the
//! `carrier_is_abstract_spec` gate defers dispatch to eval. The sibling of WI-608's
//! `requires`-view for the reflexive relationship.

/// FREE-OP shape: `collect(src)` on `src: FiniteCollection[E = ES]` — the op's own
/// (skolemized) type params are ground in the body, isolating the result-effect
/// threading. The op-level `requires FiniteCollection[…]` discharges the abstract
/// collect dispatch (WI-599 gap-2).
#[test]
fn wi609_collect_effect_over_finite_collection_param() {
    let src = r#"
namespace test.wi609b
  import anthill.prelude.{FiniteCollection, List, Modify, EffectsRuntime}
  import anthill.prelude.FiniteCollection.{collect}

  operation probe[SrcC, Src, ES](src: FiniteCollection[C = SrcC, Element = Src, E = ES])
    -> List[T = Src] effects ES
    requires FiniteCollection[C = SrcC, Element = Src, E = ES] =
    collect(src)
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.is_empty(),
        "collect(src) over a FiniteCollection-typed param should thread its result \
         effect E from the receiver's own E:\n{}",
        errs.join("\n")
    );
}

/// SORT-MEMBER shape (the thin-combinator use): a combinator whose `collect2` body
/// materializes its `FiniteCollection` source. Threads the receiver's element/effect
/// through the match destructure via explicit op type params bound from the receiver
/// (the `FilteredStream.splitFirst` pattern), then relies on the WI-609 reflexive
/// grounding for `collect(src)`'s result effect. The sort-level `requires
/// FiniteCollection[…]` discharges the abstract-collect dispatch (WI-599 gap-2).
#[test]
fn wi609_collect_effect_over_abstract_finite_collection_field() {
    let src = r#"
namespace test.wi609
  import anthill.prelude.{FiniteCollection, List, Modify, EffectsRuntime}
  import anthill.prelude.FiniteCollection.{collect}

  sort FCMapped
    import anthill.prelude.{FiniteCollection, List, Modify, EffectsRuntime}
    import anthill.prelude.FiniteCollection.{collect}
    sort SrcC = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    requires FiniteCollection[C = SrcC, Element = Src, E = ES]
    entity fcm(source: FiniteCollection[C = SrcC, Element = Src, E = ES], fn: (Src) -> T @ {EF})

    operation collect2[SrcCc, Srcc, Tt, ESs, EFf](
        m: FCMapped[SrcC = SrcCc, Src = Srcc, T = Tt, ES = ESs, EF = EFf])
      -> List[T = Srcc] effects ESs =
      match m
        case fcm(src, fn) -> collect(src)
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.is_empty(),
        "a combinator's collect body over a FiniteCollection source should thread \
         the source access effect and load clean:\n{}",
        errs.join("\n")
    );
}
