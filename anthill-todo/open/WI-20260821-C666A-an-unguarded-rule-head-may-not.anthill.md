## Attributes

- id: WI-20260821-C666A-an-unguarded-rule-head-may-not
- created: 2026-08-21T13:15:32Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T13:15:32Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN UNGUARDED RULE HEAD MAY NOT JOIN A PREDICATE INTRODUCED THROUGH A NON-ENCLOSING EDGE.
Joining across `requires` (or a wildcard import) merges independent authors' clauses into
one predicate with nothing selecting between them, and today the guard that would make it
correct cannot be written.

MEASURED (rustland, WI-980's tree):
  namespace rlib
    sort Spec { rule p(0) }
    sort A { requires rlib.Spec  entity a(n: Int64)  rule p(1) }
    sort B { requires rlib.Spec  entity b(n: Int64)  rule p(2) }
  -> LOADS CLEAN. `rlib.Spec.p` = 3 clauses; `rlib.A.p` and `rlib.B.p` DO NOT EXIST.
  CONTROL, rename only the spec's head to `rule other(0)`
  -> `rlib.A.p` = 1, `rlib.B.p` = 1, `rlib.Spec.other` = 1. Each implementor keeps its own.
So two unrelated sorts, each merely declaring that it satisfies a library's spec, end up
contributing clauses to ONE predicate that every other implementor of that spec resolves.
Neither author named the other; neither can see the other's file. This is the ticket's own
"extension is non-monotone" hazard, crossing a library boundary nobody opted into.

THE MERGE IS THE RIGHT STRUCTURE *WITH* A GUARD, and that is why this is a refusal and not
a redesign. A spec predicate whose clauses come from its implementors, each guarded by its
own carrier, is a typeclass method with per-instance definitions -- proposal 060's table
row: `?x: T` on a relational head generates `domain(?x, T)`, "the clause fires only where
the argument is in T's domain". Written `rule p(?x: rlib.A)`, A's clause fires for A and
nothing else, and the three-clause `Spec.p` is exactly what it should be.

THE GUARD CANNOT BE WRITTEN TODAY. MEASURED: `rule p(?x: rlib.A)` on a plain relational
head is REFUSED -- "WI-582: a typed rule pattern (`?x: T`) is enforced only where the
resolver fires a directional rewrite -- a `[simp]` ...". 060's own status line says
WI-742's plain-relational typed heads "remain explicitly unimplemented". So the safe form
is unavailable and the unsafe one loads silently, which is the wrong way round.

WHAT TO DO NOW: refuse a head that would join a predicate introduced through a
NON-ENCLOSING edge (`requires`, wildcard import) when the clause carries no guard
selecting its own carrier. The ENCLOSING chain is untouched -- `namespace demo { rule
p(1); sort Rec { rule p(2) } }` is WI-980's own case and stays a join, because writing
inside a namespace is opting into its names (kernel-language.md §"Joining is not confined
to one file").

COST: ZERO. Instrumented every cross-scope join over stdlib + anthill-stl + the
github-todo example: NO head anywhere joins another scope's rule-introduced name, by any
edge. The only non-enclosing joins in the tree are 7 sites inside
`wi980_rule_head_order_test`'s own `requires` rows, which exist to pin the behaviour this
ticket refuses -- they invert with the change and their comments say so.

DEPENDS ON NOTHING; UNBLOCKS THE RELAXATION. The refusal can land now. What needs WI-742
is lifting it: once `?x: T` on a relational head generates its `domain` goal, a GUARDED
head may join across the edge and the spec-predicate shape becomes writable. Record the
link both ways so the refusal is not later read as a policy against the shape itself.

ACCEPTANCE: the two-implementor program above is a located load error naming the spec's
head and the joining one. The rename control still loads with a predicate per implementor.
The enclosing-chain join still loads (control -- this rule does not reach it). Say at the
site which rows fail when the refusal is backed out. cargo-test green via
rustland/scripts/test.sh.

