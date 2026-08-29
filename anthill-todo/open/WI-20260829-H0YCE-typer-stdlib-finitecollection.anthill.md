## Attributes

- id: WI-20260829-H0YCE-typer-stdlib-finitecollection
- created: 2026-08-29T19:01:35Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T19:01:35Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPER/STDLIB: `FiniteCollection.size` BYPASSES the finiteness gate that `collect` ENFORCES — an infinite-sourced lazy carrier type-checks under `size` and would diverge at runtime.

MEASURED on the tree BEFORE WI-20260829-X13YV (so this is not that ticket's doing), one
fixture, two rows differing in ONE token — the CONSUMER:

  operation viaCollect(m: MappedStream[Source = Nats, Src = Int64, T = Int64, ES = {}, EF = {}])
    -> List[T = Int64] = FiniteCollection.collect(m)      REFUSED
      ...FiniteCollection.collect.dispatch: no impl matches — unresolved:
      FiniteCollection[C = Nats, Element = Int64, E = ...] (no impl provides FiniteCollection)

  operation viaSize(m: MappedStream[Source = Nats, ...]) -> Int64
    = FiniteCollection.size(m)                            LOADS

`Nats` provides `Stream` and never `FiniteCollection` — counting it does not terminate. It
is the same carrier `wi590_conditional_finiteness_test` uses for its negative row, and that
suite is GREEN, so the gate itself works: it is this consumer that does not ask it. Over
`Source = List[T = Int64]` BOTH rows load, so the axis under test is finiteness and the only
thing that differs is which member consumes.

WHY, as far as reading goes (NOT TRACED — verify before fixing): `collect` is
FiniteCollection's BODY-LESS primitive, and providing it IS the finiteness guarantee, so a
call re-asks the witness and the conditional `MappedStreamFinite` provision fails to
discharge for `Nats`. `size` is the DEFAULTED member (`= List.length(collect(c))`,
finite_collection.anthill:38) and evidently resolves against the declaration without
re-asking.

WHAT IT COSTS: `.size()` is the spelling the docs and tests reach for.
`typer_capability_matrix_test::an_author_declared_consumer_takes_a_finite_carrier` uses
`size` in most of its cells, and `x13yv_map_map_chain_test` had to put its GATE rows on
`collect` because a `size` row cannot witness the gate at all. Anything the gate is meant to
refuse is accepted through `size`.

CENSUS THE DEFAULTED MEMBERS, not just the one that was found: `foldLeft` and `foldRight` are
defaulted on FiniteCollection the same way (`= List.foldLeft(collect(c), ...)`), and `Map.size`
is a counted OVERRIDE (WI-444) which may answer differently again. Enumerate
FiniteCollection's defaulted members and ask each the same question.

ACCEPTANCE: `FiniteCollection.size` over a `MappedStream[Source = Nats]` is a LOAD ERROR
naming `FiniteCollection[C = Nats]`, as `collect` already is; the `List`-sourced row still
loads AND evaluates; every defaulted member of FiniteCollection has a row saying which way it
goes; `wi590_conditional_finiteness_test` gains the `size` rows beside its `collect` ones;
say at the site which rows fail when the fix is backed out.

