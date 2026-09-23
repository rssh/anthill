## Attributes

- id: WI-20260923-ZBWMC-scan-sort-carrier-bindings
- created: 2026-09-23T20:45:20Z

- status: Open
- status_agent: user
- status_at: 2026-09-23T20:45:20Z

- acceptance: cargo-test

- tags: typing

## Description

`scan_sort_carrier_bindings`' `provides` ARM IS DEAD: the WI-201 bare-spec sugar never narrows a carrier from a `provides` clause.

FOUND by WI-20260923-N3W68 (its #9 audit of the positional-binding fill) and REASONED FROM THE CODE, not yet driven by a program — so this ticket's first job is to reproduce it.

WHAT THE CODE SAYS. `Loader::scan_sort_carrier_bindings` (load.rs) pre-scans a sort's items for `fact Spec[…]` and `provides Spec[…]` and records `(spec, member) → carrier` for the WI-201 bare-spec sugar. Its `provides` arm lowers the clause with `sort_inst_to_value`, which returns a `SortView(base, …)`-headed term (WI-366). The arm's next gate — "only a SPEC lends carrier members": `matches!(kind_of(functor), Some(SymbolKind::Sort)) && !sort_has_constructors(functor)` — then reads the head `anthill.reflect.SortView`, which is an ENTITY, so every parameterized `provides` clause is skipped. A bare `provides Spec` carries no binding to record. So only the `fact` arm can ever record anything — and WI-20260917-S8JYF retired the `fact` spelling of a provision, which makes it worth asking whether the scan as a whole still has a producer.

WHAT TO DO. Reproduce first: a sort whose `provides Spec[Member = X]` should let the bare-spec sugar narrow a parameter to `X`, observed through a load verdict or a dispatch answer, against the same program in a spelling that does record. Then either
  * the narrowing is wanted: unwrap the view in the arm (`unwrap_spec_view` — base from `pos[0]`, the bindings named, positionals through `KnowledgeBase::positional_param_slots`) before the spec gate; or
  * it is not: delete the arm, and say at the scan why a `provides` clause does not lend carrier members.

ACCEPTANCE: a test that DRIVES the chosen behaviour (the narrowing observed, or its absence pinned where a program would notice), its back-out stated at the test; full workspace green via rustland/scripts/test.sh.

