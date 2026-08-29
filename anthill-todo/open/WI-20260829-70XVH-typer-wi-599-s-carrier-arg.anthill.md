## Attributes

- id: WI-20260829-70XVH-typer-wi-599-s-carrier-arg
- created: 2026-08-29T19:02:25Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T19:02:25Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPER: WI-599's `carrier_arg_provision_projection` covers the SPEC-METHOD shape ONLY, and the FREE-OP shape it excluded has NO TICKET.

WI-599 IS DELIVERED — this is not unfinished work inside it, it is a scope boundary its own
delivery note draws and that nothing tracks:

  'Binding source = carrier_provision_short_bindings: the SPEC-METHOD case only
   (op(c:C,..) ON the spec) ... FREE-OP requires case (the WI repro tmap) NOT supported:
   op.rigidify not on env, requires-entry Refs don't resolve to body rigids -> would break
   the sibling field; documented, returns None -> original leak error.'

`grep -rl carrier_arg_provision_projection anthill-todo/{open,claimed,pre_opened}` is EMPTY.
WI-599 recommended splitting its OTHER gaps into their own WIs; this exclusion never got one,
so it exists only as prose inside a delivered item — which is how it was reachable again.

MEASURED while delivering WI-20260829-X13YV, which wanted exactly this shape. A free
operation on a DATA sort, generic over the source carrier, with an op-level `requires`:

  operation map[Sc, S, Dst, EffS, EffP](s: Sc, f: (x: S) -> Dst @ {EffP, -Modify[x]})
    -> MappedStream[Source = Sc, Src = S, T = Dst, ES = EffS, EF = EffP]
    requires Iterable[C = Sc, Element = S, E = EffS] =
    mapped(s, f)

  REFUSED -- type mismatch in anthill.prelude.MappedStream.map.type_arg:
      expected a type for 'S', got unconstrained — use `map[S = …](…)`

The element `S` does not ground from the argument's own provision though the `requires`
binds it. THE SORT-PARAM VARIANT IS NOT AN ESCAPE either — typing the input as the sort's own
`Source` param, covered by the sort-level `requires Iterable[C = Source, ...]`, fails
DIFFERENTLY: `Dst` goes unconstrained (the callback's return cannot be read off an argument
whose element type comes from a sort param rather than from the argument) and the effect row
leaks 'undeclared effect: ?_'. Both were measured; neither route is available.

WHAT THE ABSENCE COST X13YV: `MappedStream.map` / `FilteredStream.filter` had to be re-typed
onto their OWN carrier as receiver methods rather than staying general over any Iterable
source. That works and is driven — see `x13yv_map_map_chain_test` — but it NARROWED the two
operations: they no longer accept a bare `List`, which is why `wi439_iterable_filter_test`'s
parity op moved to `Iterable.filter`. Closing this gap would let them be general again, which
is the only reason to want it — so weigh that against the typer cost before claiming.

ACCEPTANCE: the free-op form above loads and grounds `S` and `Dst` from the argument's own
provision; `wi599_carrier_arg_provision_test` gains the free-op row beside its spec-method
one; state at the site which rows fail when it is backed out, and which pass either way.

