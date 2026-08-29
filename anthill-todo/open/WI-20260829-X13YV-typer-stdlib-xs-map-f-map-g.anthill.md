## Attributes

- id: WI-20260829-X13YV-typer-stdlib-xs-map-f-map-g
- created: 2026-08-29T16:37:34Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T16:37:34Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPER/STDLIB: `xs.map(f).map(g)` and `xs.filter(p).filter(q)` DO NOT LOAD — a lazy carrier's own STATIC CONSTRUCTOR shadows the spec combinator in dot dispatch, and its `EffS` does not ground from the receiver's provision. Found while delivering WI-20260829-N01PY (a different root: that one was the subtype reader's blindness to witness provisions).

MEASURED, one fixture, `xs: List[T = Row]`:

  xs.map(lambda r -> r.a).map(lambda n -> n)          REFUSED -- type mismatch in
      anthill.prelude.MappedStream.map.type_arg: expected a type for 'EffS', got
      unconstrained — use `map[EffS = …](…)`
  xs.filter(lambda r -> r.flag).filter(lambda r -> true)  REFUSED -- same, on
      anthill.prelude.FilteredStream.filter
  xs.map(lambda r -> r.a).filter(lambda n -> true)    LOADS
  xs.filter(lambda r -> r.flag).map(lambda r -> r.a)  LOADS
  xs.map(lambda r -> r.a).collect().map(lambda n -> n).size()  LOADS  (the workaround)

THE MIXED CHAINS ARE THE CONTROL and they are what localizes it: `MappedStream` has no
`filter` member, so `.filter` on a mapped stream falls through to `FiniteCollection.filter`
via the `MappedStreamFinite` witness and works. `MappedStream` DOES have a `map` member —
`operation map[S, Dst, EffS, EffP](s: Stream[S, EffS], f) -> Stream[Dst, {EffS, EffP}]`
in `combinators.anthill`, a STATIC CONSTRUCTOR, not a receiver method — so dot dispatch
stops there and never reaches the spec combinator. `FilteredStream.filter` is its twin.

TWO THINGS ARE WRONG AT ONCE, and they should be separated when this is picked up:
  (1) the static constructor shadows the spec's combinator in dot dispatch, which is why
      the SAME chain works when spelled through the other combinator; and
  (2) even reached deliberately, `EffS` does not ground from the receiver's provision
      (`MappedStream provides Stream[T = T, E = {ES, EF}]` names both), where the
      sort-param effect on `Iterable.map` DOES ground. WI-594 recorded exactly this
      asymmetry as its gap (2) and it was not closed for this shape.

Also: `xs.map(f).map[EffS = {}](g)` DOES NOT PARSE — a dot call takes no explicit type-arg
bracket (WI-439's delivery note records the qualified-call half of the same parse gap), so
the message's own repair ("use `map[EffS = …](…)`") is not available in the spelling that
produces it.

WORTH ASKING WHETHER THE TWO STATIC CONSTRUCTORS SHOULD EXIST AT ALL. Nothing in the
stdlib calls `MappedStream.map` / `FilteredStream.filter` — `Iterable.map` builds
`mapped(...)` directly — and they duplicate `Iterable.map`/`filter` at the Stream level.
`wi439_iterable_filter_test` asserts parity between `Iterable.filter` and
`FilteredStream.filter`, and `wi1049_duplicate_operation_declaration_test` resolves
`anthill.prelude.MappedStream.map` by name, so removing them is not free.

ACCEPTANCE: `xs.map(f).map(g).size()` and `xs.filter(p).filter(q).size()` load AND
evaluate to the right value; the mixed chains and `Iterable.map`'s erased-Stream boundary
are unchanged; a cell for each in
`typer_capability_matrix_test::an_author_declared_consumer_takes_a_finite_carrier`'s
neighbourhood.

