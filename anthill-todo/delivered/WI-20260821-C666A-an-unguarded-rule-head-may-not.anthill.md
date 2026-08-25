## Attributes

- id: WI-20260821-C666A-an-unguarded-rule-head-may-not
- created: 2026-08-21T13:15:32Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-25T05:34:14Z

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

## Changes

### 2026-08-24T19:26:37Z — feedback — user

PROPOSAL 061 PREMISE CORRECTION (2026-08-24). The original no-declaration program is no longer the live defect: WI-20260822-845G7 makes each undeclared head auto-declare where written and the existing NameIntroducedAtTwoVisibleScopes check refuses the visible pair. The live C666A shape explicitly declares p in Spec with a body-less rule, after which clauses in A and B DENOTE Spec.p through requires and still load clean into one predicate. Rebased acceptance: that declared-predicate requires shape and its wildcard-import twin are located errors naming the joining scope and the qualified target predicate; renaming the Spec declaration keeps independent A.p and B.p predicates; an enclosing scope may contribute to its declared predicate; a selective import naming p is an explicit opt-in and may contribute. The implementation must distinguish resolution available through locals, named imports, or the enclosing chain from resolution available only through whole-scope non-enclosing parents. WI-742 later admits the generated carrier-selecting domain guard at this check without removing the unguarded refusal.

### 2026-08-25T05:34:07Z — feedback — claude

IMPLEMENTED (2026-08-25), rebased onto Proposal 061 ownership. Rust now compares ordinary rule-head resolution with the same ladder restricted to locals, named imports, and lexical enclosing parents. A declared Goal reached only through requires, conversion-style provides, wildcard import, or another non-enclosing whole-scope edge raises a located UnguardedNonEnclosingPredicateJoin error naming the writing scope and qualified target. Named imports, enclosing contributions, and independently renamed predicates remain legal. WI-742 is documented as the future narrow bypass for its generated carrier-selecting domain guard; the unguarded refusal remains. Driven coverage includes requires with two implementors, wildcard import, parameterized provides, rename, enclosing, and selective-import controls, plus updated Proposal 061 ownership/order fixtures. Verification: focused C666A 6 passed; anthill-core wi_tests 3423 passed and 3 existing ignored; full rustland scripts/test.sh passed all workspace, CLI, generator, solver, and doc suites with zero failures; scaland sbt test passed module totals 1, 23, and 514 with zero failures; git diff --check passed. Manual diff review found no issue.

