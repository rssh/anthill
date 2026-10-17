## Attributes

- id: WI-20261017-D36RN-relation-provides
- created: 2026-10-17T09:39:50Z

- status: Open
- status_agent: user
- status_at: 2026-10-17T09:39:50Z

- acceptance: cargo-test, scaland-sbt-test

## Description

RELATION PROVIDES LOGICALSTREAM AND BACKS ONE OF ITS SIX OPERATIONS -- `Relation provides LogicalStream[T = T, E = E]` (stdlib relation.anthill) supplies only splitFirst (host-mapped); empty, pure, mplus, guard and interleave have no default on LogicalStream and no member on Relation, so a dispatch of any of them at a Relation dies 'operation has no body'. WI-20260909-M8QWJ's provision check holds a host-realized carrier to every operation of a spec it provides EXCEPT on a row forwarding the carrier's own parameters, and that exemption exists only so this row loads (provider_owes_operations, kb/typing/coherence.rs; kernel-language §5.4 names the gap). TO DO: give Relation the five members -- mplus is close to its host union; empty / pure / guard / interleave need anthill bodies over the relational algebra or host functions -- then drop the forwarding exemption for host carriers and measure what else it refuses. ACCEPTANCE: each of the five driven at a Relation value (answering, not loading); the exemption gone; stdlib loads. RELATION: WI-20261017-CK7PP's case (2) refuses such a call at the call site meanwhile.

