## Attributes

- id: WI-20260829-H0YCE-typer-stdlib-finitecollection
- created: 2026-08-29T19:01:35Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-26T18:47:40Z

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

## Changes

### 2026-09-26T18:47:29Z — feedback — user

DELIVERED. Cause as the ticket guessed, now traced: a DEFAULTED spec op (size/foldLeft/foldRight) at a concrete carrier goes through apply.rs's defaulted-op arm, whose instance gate (carrier_is_an_instance) is binding-blind — MappedStream/FilteredStream HAVE a FiniteCollection row (the conditional MappedStreamFinite/FilteredStreamFinite witness), so the gate passed at Source = Nats and the witness's condition was never asked; body-less collect goes through dispatch, which asks it. Fix: in that arm, a resolution that ends NoMatch on a GROUND goal (every spec param bound, none open) is refused as DispatchNoMatch naming the unmet condition — the same refusal collect gets. Open goals keep loading: an unbound param is DROPPED from the goal, hence the param-count check (size(MutableStack.new()), isEmpty(nil) — wi508/wi818 caught the first cut without it). CENSUS, measured: over MappedStream AND FilteredStream (the ticket named only Mapped; Filtered had the same hole), size, m.size(), foldLeft, foldRight over Nats are now refused naming FiniteCollection[C = Nats]; over List / Fin all load; size, dot-size and both folds over a List-sourced map EVALUATE (3, 3, 9, 9); Map.size (the WI-444 counted override) = 2 and the defaulted foldLeft over Map's direct provision = 30. Rows in wi590_conditional_finiteness_test (defaulted_members_*). BACK-OUT measured: disabling the new arm reddens only defaulted_members_over_an_infinite_source_are_refused; the finite and eval rows pass either way by design. NOT CHANGED, observed: FiniteCollection.size over a BARE Nats (not a combinator) is refused only by an effect error (undeclared effect ?_), not by finiteness — the carrier is never classified, so this arm is not reached. scaland has no typer; the change touches no stdlib file, so it has nothing to mirror — sbt not installed in this container, not run.

