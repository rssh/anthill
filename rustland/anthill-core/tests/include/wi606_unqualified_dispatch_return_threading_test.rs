//! WI-606 — an UNQUALIFIED self-named spec-op call value-dispatches (WI-411) on
//! a receiver whose CARRIER SORT is statically known but whose TYPE-ARGS are
//! ABSTRACT (op params). The spec-op dispatch must thread the return type from
//! the RESOLVED IMPL's signature (the concrete carrier tail), not leave it at the
//! spec's interface return (an abstract `Stream` tail that a downstream dispatch
//! cannot ground).
//!
//! Repro shape (the WI-590 witness-collect drain, minimal-real-stdlib form): a
//! single lazy carrier `Mapped` parameterized over its SOURCE sort, providing
//! `Stream` by an overriding `splitFirst`, plus a witness `MappedFinite` whose
//! `collect` DRAINS the carrier by the UNQUALIFIED `splitFirst(m)`:
//!
//! ```text
//!   match splitFirst(m)                 -- m : Mapped[Source=S, Src=Src, T=T, …]  (abstract op params)
//!     case none() -> nil
//!     case some(pair(h, rest)) -> cons(h, FiniteCollection.collect(rest))
//! ```
//!
//! Before the fix the destructured `rest` came back a bare `Var` (the spec op
//! `Stream.splitFirst`'s return tail is the abstract `Stream`, not the concrete
//! `Mapped`), so the downstream `FiniteCollection.collect(rest)` left its
//! `Element` at `?_`: "expected List[T=?T], got List[T=?_]". QUALIFYING the call
//! (`Mapped.splitFirst(m)`) always threaded clean (static dispatch computes the
//! return from the impl's signature); this test pins the UNQUALIFIED form to the
//! same behaviour.

const SRC: &str = r#"
namespace wi606.witness
  import anthill.prelude.{FiniteCollection, Stream, Option, Pair, List, Int64, EffectsRuntime}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.List.{nil, cons}
  import anthill.prelude.Stream.{splitFirst}

  -- one lazy carrier, parameterized over its SOURCE sort.
  sort Mapped
    sort Source = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    entity mk(source: Source, fn: (Src) -> T @ {EF})
    provides Stream[T = T, E = {ES, EF}]
    operation splitFirst(m: Mapped)
      -> Option[Pair[A = T, B = Mapped[Source = Source, Src = Src, T = T, ES = ES, EF = EF]]] effects {ES, EF} =
      match m
        case mk(src, fn) ->
          match Stream.splitFirst(src)
            case none() -> none
            case some(pair(h, rest)) -> some(pair(fn(h), mk(rest, fn)))
  end

  -- WITNESS: Mapped[Source = S] provides FiniteCollection WHEN S does. Its
  -- `collect` DRAINS the carrier via the UNQUALIFIED spec op `splitFirst(m)` and
  -- recurses on the destructured tail — the WI-606 threading gap.
  sort MappedFinite
    import anthill.prelude.{FiniteCollection, Stream, List, Option, Pair, EffectsRuntime}
    import anthill.prelude.List.{nil, cons}
    import anthill.prelude.Option.{some, none}
    import anthill.prelude.Pair.{pair}
    import anthill.prelude.Stream.{splitFirst}
    sort S = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    requires FiniteCollection[C = S, Element = Src, E = ES]
    fact FiniteCollection[C = Mapped[Source = S, Src = Src, T = T, ES = ES, EF = EF], Element = T, E = {ES, EF}]
    operation collect(m: Mapped[Source = S, Src = Src, T = T, ES = ES, EF = EF]) -> List[T = T] effects {ES, EF} =
      match splitFirst(m)
        case none() -> nil
        case some(pair(h, rest)) -> cons(h, FiniteCollection.collect(rest))
  end
end
"#;

#[test]
fn unqualified_spec_op_dispatch_threads_return_from_impl() {
    match crate::common::try_load_kb_with(SRC) {
        Ok(_) => {}
        Err(errs) => panic!(
            "unqualified `splitFirst(m)` on a statically-known carrier with \
             abstract type-args must thread the impl's concrete-carrier return \
             so the downstream `collect(rest)` grounds its Element; got {} load \
             error(s):\n{}",
            errs.len(),
            errs.join("\n"),
        ),
    }
}
