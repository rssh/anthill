//! WI-608 — typer: ground the element/effect of a carrier-param spec op called on
//! a receiver whose carrier is ITSELF an abstract spec that `requires` the op's
//! spec.
//!
//! The thin finite combinators (WI-599) provide `Iterable` by delegating their
//! `iterator` to the wrapped source: `iterator(m) = mapped(iterator(src), fn)`,
//! where the `source` field is typed `FiniteCollection[C = SrcC, Element = Src,
//! E = ES]`. The inner `iterator(src)` dispatches `Iterable.iterator` (spec_sort =
//! `Iterable`), but the receiver's carrier is `FiniteCollection`, which *requires*
//! `Iterable` rather than *providing* it — so `carrier_param_receiver`'s
//! `provides`-only `transitive_provision_view` found nothing and the produced
//! `Stream[Element, E]` leaked `??_` for both params, cascading into
//! `mapped(…) : MappedStream[T = ??_, Src = ??_, ES = ??_]`.
//!
//! `abstract_spec_required_view` builds the provision view from the `requires`
//! clause instead (the same view shape a `provides` fact yields), so the spec's
//! `Element`/`E` thread off the receiver's own written type-args, and the
//! `carrier_is_abstract_spec` dispatch gate defers the call to eval's
//! value-directed dispatch — the carrier-param twin of the WI-598/601
//! self-receiver abstract-spec deferral.

/// FREE-OP shape: `src`'s `FiniteCollection` type-args are the op's own
/// (skolemized) type params, ground in the body. Isolates the iterator-grounding
/// from the receiver-binding a sort member threads through its match destructure.
#[test]
fn wi608_iterator_over_finite_collection_param() {
    let src = r#"
namespace test.wi608b
  import anthill.prelude.{FiniteCollection, Iterable, Stream, Int64, Modify, EffectsRuntime}
  import anthill.prelude.MappedStream.{mapped}
  import anthill.prelude.Iterable.{iterator}

  operation probe[SrcC, Src, ES, EF](
      src: FiniteCollection[C = SrcC, Element = Src, E = ES],
      fn: (Src) -> Int64 @ {EF})
    -> Stream[T = Int64, E = {ES, EF}] =
    mapped(iterator(src), fn)
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.is_empty(),
        "iterator(src) over a FiniteCollection-typed param should ground its \
         Element/E from the receiver's own type-args:\n{}",
        errs.join("\n")
    );
}

/// SORT-MEMBER shape (the thin-combinator use): a combinator that provides
/// `Iterable` by delegating `iterator` to its wrapped `FiniteCollection` source.
/// Threads the receiver's element/effect through the match destructure via
/// explicit op type params bound from the receiver (the proven `FilteredStream.
/// splitFirst` pattern), then relies on the WI-608 grounding for `iterator(src)`.
#[test]
fn wi608_iterator_over_abstract_finite_collection_field() {
    let src = r#"
namespace test.wi608
  import anthill.prelude.{FiniteCollection, Iterable, Stream, Modify, EffectsRuntime}
  import anthill.prelude.MappedStream.{mapped}

  sort FCMapped
    import anthill.prelude.{FiniteCollection, Stream, Iterable, Modify, EffectsRuntime}
    import anthill.prelude.MappedStream.{mapped}
    sort SrcC = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    entity fcm(source: FiniteCollection[C = SrcC, Element = Src, E = ES], fn: (Src) -> T @ {EF})
    provides Iterable[C = FCMapped, Element = T, E = {ES, EF}]

    operation iterator[SrcCc, Srcc, Tt, ESs, EFf](
        m: FCMapped[SrcC = SrcCc, Src = Srcc, T = Tt, ES = ESs, EF = EFf])
      -> Stream[T = Tt, E = {ESs, EFf}] =
      match m
        case fcm(src, fn) -> mapped(iterator(src), fn)
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.is_empty(),
        "a thin Iterable combinator delegating iterator to a FiniteCollection \
         source should load clean (iterator(src) grounds):\n{}",
        errs.join("\n")
    );
}
