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
//!
//! WI-20261005-KSSA4 — THE SOURCE IS A VALUE OF A SORT THE SPEC IS REQUIRED OF, and there
//! is no reflexive case. `src: FiniteCollection[C = SrcC, …]` was a value typed at the
//! spec, read as a value of its carrier; it is not one, and the reflexive branch is
//! deleted. Both shapes are written with `src: SrcC` under the `requires
//! FiniteCollection[C = SrcC, Element = Src, E = ES]` they already declared, which is
//! what says `collect(src)`'s effect is `ES`.

/// FREE-OP shape: `collect(src)` on `src: SrcC` — the op's own (skolemized) type params are
/// ground in the body, isolating the result-effect threading. The op-level `requires
/// FiniteCollection[C = SrcC, …]` licenses the call and says its effect.
#[test]
fn wi609_collect_effect_over_finite_collection_param() {
    let src = r#"
namespace test.wi609b
  import anthill.prelude.{FiniteCollection, List, Modify, EffectsRuntime}
  import anthill.prelude.FiniteCollection.{collect}

  operation probe[SrcC, Src, ES](src: SrcC)
    -> List[T = Src] effects ES
    requires FiniteCollection[C = SrcC, Element = Src, E = ES] =
    collect(src)
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.is_empty(),
        "collect(src) over a FiniteCollection-typed param should thread its result \
         effect E from the receiver's own E:\n{}",
        errs.join("\n")
    );
}

/// SORT-MEMBER shape (the thin-combinator use): a combinator whose `collect2` body
/// materializes its source, a value of the sort's own `SrcC`. The sort-level `requires
/// FiniteCollection[C = SrcC, …]` licenses `collect(src)` and says its effect.
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
    entity fcm(source: SrcC, fn: (Src) -> T @ {EF})

    operation collect2(m: Self) -> List[T = Src] effects ES =
      match m
        case fcm(src, fn) -> collect(src)
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.is_empty(),
        "a combinator's collect body over a FiniteCollection source should thread \
         the source access effect and load clean:\n{}",
        errs.join("\n")
    );
}
