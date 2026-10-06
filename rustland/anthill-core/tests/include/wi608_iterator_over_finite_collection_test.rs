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
//! `mapped(…) : MappedStream[T = ??_, SourceElement = ??_, SourceEffects = ??_]`.
//!
//! `abstract_spec_required_view` builds the provision view from the `requires`
//! clause instead (the same view shape a `provides` fact yields), so the spec's
//! `Element`/`E` thread off the receiver's own written type-args, and the
//! `carrier_is_abstract_spec` dispatch gate defers the call to eval's
//! value-directed dispatch — the carrier-param twin of the WI-598/601
//! self-receiver abstract-spec deferral.
//!
//! WI-20261005-KSSA4 — THE SOURCE IS A VALUE OF A SORT THE SPEC IS REQUIRED OF. A source
//! typed `FiniteCollection[C = SrcC, …]` was a value typed at the spec, read as a value of
//! `SrcC`; it is not one, `iterator(src)` refuses it, and `abstract_spec_required_view` is
//! deleted ([`a_source_typed_at_the_spec_is_not_iterable`]). The same two shapes are
//! written with `src: SrcC` under `requires FiniteCollection[C = SrcC, Element = Src, E =
//! ES]`: the clause licenses `Iterable.iterator` on `src` — `FiniteCollection` requires
//! `Iterable` of its carrier — and says its element and effect.

/// FREE-OP shape: `src` is a value of the op's own type parameter `SrcC`, and the op's
/// `requires FiniteCollection[C = SrcC, Element = Src, E = ES]` names its element and
/// effect by the op's own (skolemized) type params, ground in the body.
#[test]
fn wi608_iterator_over_finite_collection_param() {
    let src = r#"
namespace test.wi608b
  import anthill.prelude.{FiniteCollection, Iterable, Stream, Int64, Modify, EffectsRuntime}
  import anthill.prelude.MappedStream.{mapped}
  import anthill.prelude.Iterable.{iterator}

  operation probe[SrcC, Src, ES, EF](
      src: SrcC,
      fn: (Src) -> Int64 @ {EF})
    -> Stream[T = Int64, E = {ES, EF}]
    requires FiniteCollection[C = SrcC, Element = Src, E = ES] =
    mapped(iterator(src), fn)

  operation firstTwo() -> Int64 =
    Stream.takeN(probe([1, 2, 3], lambda (x: Int64) -> x + 1), 2).size()
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.is_empty(),
        "iterator(src) over a parameter `FiniteCollection` is required of should ground \
         its Element/E from the clause:\n{}",
        errs.join("\n")
    );
    // …and the stream it builds is walked: the dictionary of `Iterable` the body's
    // `iterator(src)` runs through is the one `FiniteCollection`'s holds for a list.
    assert_eq!(crate::common::run_int64(src, "test.wi608b.firstTwo"), Ok(2));
}

/// THE SPELLING THE ROW ABOVE HAD: the source typed at the spec. A value typed at a spec
/// over a parameter is not a value of a sort that provides it, so `iterator(src)` refuses
/// it where the carrier is expected.
#[test]
fn a_source_typed_at_the_spec_is_not_iterable() {
    let src = r#"
namespace test.wi608c
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
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("expected anthill.prelude.Iterable.C, got FiniteCollection[")
            && e.contains("a value typed at it is not a value of a sort that provides it")),
        "a source typed at `FiniteCollection[…]` is not a value `iterator` receives:\n{}",
        errs.join("\n")
    );
}

/// SORT-MEMBER shape (the thin-combinator use): a combinator that provides
/// `Iterable` by delegating `iterator` to its wrapped source, a value of the sort's own
/// `SrcC`, of which the sort requires `FiniteCollection`. `iterator(src)` is licensed and
/// grounded by that clause.
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
    requires FiniteCollection[C = SrcC, Element = Src, E = ES]
    entity fcm(source: SrcC, fn: (Src) -> T @ {EF})
    provides Iterable[C = Self, Element = T, E = {ES, EF}]

    operation iterator(m: Self) -> Stream[T = T, E = {ES, EF}] =
      match m
        case fcm(src, fn) -> mapped(iterator(src), fn)
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.is_empty(),
        "a thin Iterable combinator delegating iterator to a FiniteCollection \
         source should load clean (iterator(src) grounds):\n{}",
        errs.join("\n")
    );
}
