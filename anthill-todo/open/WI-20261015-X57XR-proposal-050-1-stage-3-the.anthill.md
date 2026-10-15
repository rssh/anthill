## Attributes

- id: WI-20261015-X57XR-proposal-050-1-stage-3-the
- created: 2026-10-15T13:47:15Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T13:47:15Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261014-6T5C6-an-entity-field-s-arrow-type

- tags: proposal-050.1, typing

## Description

Proposal 050.1, stage 3: the memory clauses are checked, not only read — an anthill body against its own `ensures memory_maybe_connected` / `memory_alias`, a member against its spec's, a function value against the type it meets — and the stdlib writes its clauses.

PROGRAMS (measured on 5da88f1f; docs/proposals/050.1-memory-alias-and-maybe-connected.md):
- viaCall: first(l: List[T = Cell[V = Int64]]) -> Option[T = Cell[V = Int64]] (match l, returning some(h)) declares no clause, and match first(l) case some(c) -> put(c, 9) writes the caller's cell with nothing declared (viaCall([d]) writes 9).
- At g(s, c, f) with f: (a: MutableStack[T = Cell[V = Int64]], b: Cell[V = Int64]) -> Unit @ {Modify[a]}, lambda (a, b) -> MutableStack.push(a, b) loads: nothing compares the sharing it makes with f's type (a lambda writing b there is refused — the row is compared).
- requires shares(f.a, f.zz) loads over a declared rule shares(?a, ?b): a misspelled callback parameter in a clause is not caught.

EXPECTED (§4, §8 B, §8 E):
- An anthill body is checked at its boundary over every pair of places a caller can name — its parameters, the ambient resources it names, result: each pair it leaves sharing a region, where nothing at entry said so, is named by an ensures memory_maybe_connected(…); each ensures memory_alias(result, a) holds on every return path. A host operation's clauses are trusted. A member and an override declare no more sharing than the spec and keep its alias promises — a refinement leg beside the effects one (check_override_refinement).
- The stdlib writes its clauses: a census of the operations whose result can hold a resource taken from an argument, or that store one argument into another — generic accessors (List.head, Map.get), stores (MutableStack.push), persistent structures built from their arguments (Map.put) — each with its clause; host operations audited by hand. A result no clause speaks of is connected with nothing.
- Function values: a lambda's sharing is inferred from its body, as its row is, and rides on its arrow type beside the row; it is checked where a function value meets a declared type — an argument, an annotated let, an entity field, an operation's result. An operation states what its callback may share in its own clauses, naming the callback's parameters as places (requires memory_maybe_connected(f.a, f.b)) — no syntax added; where no clause is, a written arrow type admits no sharing, and an unannotated let keeps the lambda's inferred sharing. A clause naming a callback parameter that does not exist (f.zz) is refused.

ROWS: first refused at its boundary without its clause, and viaCall then charged Modify[l]; a body wrapping MutableStack.push(s, v) and returning Unit refused without ensures memory_maybe_connected(s, v); the push lambda refused at f's slot and admitted under requires memory_maybe_connected(f.a, f.b), g then owing ensures memory_maybe_connected(s, c); a member that returns a fresh cell refused where its spec promises memory_alias(result, b); f.zz refused.

