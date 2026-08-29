//! WI-590 — a WITNESS provider keyed on a PARAMETERIZED carrier (the
//! conditional-finiteness pattern: "a mapped stream is finite WHEN its source
//! is"). Pins two typer fixes that the finite-combinator consolidation surfaced;
//! both made a witness over a parameterized, effect-row-bearing carrier fail to
//! LOAD or DISPATCH before the fix:
//!
//!  1. **Provider-requires base-sort unwrap.** A witness
//!     `fact FiniteCollection[C = Mapped[Source = S, …]]` keys the carrier as a
//!     parameterized type, stored as a `SortView` wrapper. `check_provider_requires`
//!     read the wrapper functor (`SortView`) instead of the base sort `Mapped`, so
//!     it never saw that `Mapped` provides `FiniteCollection`'s required `Iterable`
//!     (transitively, via its `provides Stream`). It rejected the sound provision
//!     with `UnsatisfiedProviderRequires`. Fixed by unwrapping to the base sort.
//!
//!  2. **`EffectsRuntime` skip in the dispatch sub-goals.** The witness's
//!     effect-row params (`effects ES`, `effects EF`) each synthesize a
//!     `requires EffectsRuntime[…]`. `candidate_provider_sub_goals` (then named
//!     `candidate_sub_goals_owned`; WI-857 split the dictionary's two halves) emitted those as
//!     dispatch sub-goals, which `resolve_inner` can never satisfy
//!     (`EffectsRuntime` is the runtime marker, not a resolvable provider) — so
//!     dispatching ANY op through the witness failed with `DispatchNoMatch`. The
//!     provider-requires *check* already skipped `EffectsRuntime`; this adds the
//!     same skip to the dispatch path.
//!
//! The source below is the minimal real-stdlib shape: a single lazy carrier
//! parameterized over its SOURCE sort, plus a witness making it provide
//! `FiniteCollection` exactly when its source does. It must load clean and a
//! `FiniteCollection.collect` dispatch on the carrier must resolve.

const SRC: &str = r#"
namespace wi590.witness
  import anthill.prelude.{FiniteCollection, Stream, Option, Pair, List, Int64, EffectsRuntime}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.List.{nil, cons}

  -- one lazy carrier, parameterized over its SOURCE sort (so the type preserves
  -- which carrier the source is — the key to keying finiteness on it).
  sort Mapped
    sort Source = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    entity mk(source: Source, fn: (Src) -> T @ {EF})
    provides Stream[T = T, E = {ES, EF}]
    -- WI-20260829-1SSXM — THE SIGNATURE IS THE SUBJECT; THE BODY IS THE EMPTY STREAM.
    -- The peel this used to spell (`match Stream.splitFirst(src) … mk(rest, fn)`) never
    -- type-checked, and could not: it sat in a match SCRUTINEE, whose error the typer
    -- dropped until this WI. It is wrong TWICE over, and the second break is the one
    -- that decides the shape:
    --   1. `src : Source`, a bare sort param under NO `requires`, so it is not a Stream.
    --      The real stdlib `MappedStream` (combinators.anthill) fixes exactly this by
    --      typing the field on the `Iterable[C = Source, …]` SPEC VIEW and peeling
    --      `Stream.splitFirst(Iterable.iterator(src))`.
    --   2. Even repaired that way, `mk(rest, fn)` wants `rest : Source` and the peel
    --      yields a bare `Stream` — the tail wraps the SOURCE's tail, so its `Source` is
    --      that tail's sort, NOT this carrier's. That is precisely why `MappedStream`
    --      returns a BARE `Stream` tail, with a comment saying so.
    -- Adopting the stdlib's bare-`Stream` tail here would DELETE what these two fixtures
    -- measure: WI-606's whole subject is that this declared return IS the CONCRETE
    -- carrier tail, which the unqualified `splitFirst(m)` in `MappedFinite.collect` must
    -- thread. So the RETURN stands and the body stops pretending to peel: the empty
    -- stream, which is a total and truthful `splitFirst` — neither test evaluates it,
    -- both read this signature. It stays body-HAVING (rather than becoming a body-less
    -- primitive like `LogicalStream.splitFirst`) so the fixture keeps exercising the
    -- same dispatch route it did before.
    operation splitFirst(m: Mapped)
      -> Option[Pair[A = T, B = Mapped[Source = Source, Src = Src, T = T, ES = ES, EF = EF]]] effects {ES, EF} =
      match m
        case mk(_, _) -> none
  end

  -- WITNESS: Mapped[Source = S] provides FiniteCollection WHEN S does. Keys on the
  -- parameterized carrier (fix 1) and carries effect-row params (fix 2).
  sort MappedFinite
    import anthill.prelude.{FiniteCollection, List, EffectsRuntime}
    import anthill.prelude.List.{nil}
    sort S = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    requires FiniteCollection[C = S, Element = Src, E = ES]
    fact FiniteCollection[C = Mapped[Source = S, Src = Src, T = T, ES = ES, EF = EF], Element = T, E = {ES, EF}]
    operation collect(m: Mapped[Source = S, Src = Src, T = T, ES = ES, EF = EF]) -> List[T = T] effects {ES, EF} = nil
  end

  -- dispatch site: collecting a Mapped over a real-List source must RESOLVE
  -- through the witness (fix 2). The List source satisfies the witness's
  -- `requires FiniteCollection[C = S]`, and List provides Iterable transitively
  -- (fix 1, exercised at load).
  operation drive(m: Mapped[Source = List[T = Int64], Src = Int64, T = Int64, ES = {}, EF = {}]) -> List[T = Int64] effects {} =
    FiniteCollection.collect(m)
end
"#;

#[test]
fn witness_over_parameterized_effect_row_carrier_loads_and_dispatches() {
    // Loads clean iff BOTH fixes hold: the witness provision passes
    // provider-requires (fix 1) AND the `FiniteCollection.collect` dispatch in
    // `drive` resolves through it (fix 2). Either regression re-introduces a
    // load error here.
    match crate::common::try_load_kb_with(SRC) {
        Ok(_) => {}
        Err(errs) => panic!(
            "witness over a parameterized + effect-row carrier must load and \
             dispatch clean; got {} load error(s):\n{}",
            errs.len(),
            errs.join("\n"),
        ),
    }
}
