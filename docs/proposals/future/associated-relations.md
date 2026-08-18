# Future: Associated (dispatched) relations as spec members

> **Sketch** (2026-07-14; moved from proposal 052 on 2026-08-15) — unnumbered
> (see [README](README.md)). Related to
> [proposal 052](../052-rules-as-stream-valued-operations.md), but not part of its committed design.

Proposal 052 makes a relation a first-class **value**. A separate axis, surfaced while pinning down how `requires`
reaches a spec's rules: a relation as a **per-instance-dispatched spec member** — the relational dual of a
spec operation.

**Baseline — what already holds (no operations-vs-rules asymmetry).** `requires Spec` is **sort
composition**: it splices Spec's scope in as a parent, and Spec's contents are reachable bare in the
requiring sort. This is **uniform across operations and rules** — a spec's rules are bare-callable through
`requires` exactly as its operations are (verified) — *subject to the same variant-exposure filter*: a
required sort carrying `entity` variants leaks only those constructors, hiding its operations **and** its
rules alike; an entity-less sort (a spec) leaks everything (WI-291 / [proposal 044](../044-unified-name-resolution.md)).
So a spec's **static** rules already compose in; there is no visibility gap to close.

**The genuine gap — per-instance dispatch.** A spec *operation* is abstract: each provider supplies its
own impl, selected at the call by the discharged requirement (the dictionary). A spec *rule* today is
concrete: **one fixed clause set, shared by every requirer**. What is missing is the relational analogue
of operation dispatch — a spec rule whose **clauses are supplied per provider** and selected at
resolution. That, not visibility, is what this feature adds.

**The construct.** A spec declares a rule **head with no clauses** (a relational signature); each
instance **provides** clauses; generic code `requires`-ing the spec cites the rule bare and it resolves
to *the discharged instance's* clauses:

```anthill
sort Graph
  sort Node = ?
  rule edge(?a: Node, ?b: Node)            -- associated relation: a signature, no clauses

sort SocialNet
  provides Graph[Node = Person]
  rule edge(?a, ?b) :- follows(?a, ?b)      -- this instance's clauses

sort Reach
  requires Graph
  rule reachable(?a, ?b) :- edge(?a, ?b)                    -- bare `edge` DISPATCHES per instance
  rule reachable(?a, ?b) :- edge(?a, ?c), reachable(?c, ?b)
```

`reachable` over a `SocialNet` walks *follows*-edges; over a `RoadMap`, *road*-edges — one generic rule,
a per-instance relation. This is to a relation what `Ord.compare` (declared abstract, provided per
type) is to a function. Static rules force the alternative: thread the graph explicitly
(`reachable(g, ?a, ?b) :- edge_of(g, ?a, ?b)`) — the boilerplate dispatch removes for operations.

**What it needs (NOT visibility — that already works via `requires` composition).** Two pieces:
1. **Provider-scoped clauses** — a provider's `rule edge …` associated with *its provision*, not with the
   global `rules_by_functor` / `rules_by_label` index every rule lands in today. (The spec's own `edge` is
   a clause-less signature, like an abstract operation.)
2. **Requirement-directed clause selection** (the load-bearing engine capability) — bare `edge` in a
   `requires Graph` clause fires the *discharged* `Graph` instance's clauses, read from the resolver's Γ
   (the SLD analog of a frame's `requirements`, already threaded for rule-body requirements by **WI-300 /
   `find_dictionary`**, §Requirements in a clause body). This is the clause-level parallel of **WI-222
   defer-to-requirement** for operations.

The surface and the coherence rule are comparatively easy; piece 2 is the crux. Because name resolution is
untouched (the name already composes in), the work is entirely in *storage* + *resolver dispatch*.

**Coherence (resolution policy; owned by [proposal 044](../044-unified-name-resolution.md)).**
- An **associated** rule is one whose spec-level head is **clause-less** (a signature) — firing it selects
  the *discharged provider's* clauses. A spec's ordinary (clause-bearing) rule stays **static** — one
  shared relation, composed in unchanged. The two are distinguished by the spec-head having clauses or not,
  not by a new visibility rule.
- **Ambiguity is a LOAD error** (decided). Two required specs declaring the same associated-rule name ⟹
  bare use is ambiguous ⟹ reject at load, qualify to disambiguate. Decidable statically at the `requires`
  site — unlike a plain unqualified rule miss, which is a *silent* 0-solutions — so it is loud by
  construction, matching the repo's "loud error over silent skip".
- A sort's **own** rule of that name **overrides** the associated one (mirror the operation override
  policy, WI-444 / WI-411).

**Relationship.** Complements 052's relations-as-*values* with relations-as-dispatched-*members*; both
rest on the same 026.1 engine — the value face composes a *fixed* query, the member face selects a *query
per instance*. Out of scope for the 052 build; recorded as the natural next axis.

## Promotion

Assign a main-sequence proposal number and move out of `future/` when the provider-scoped clause model,
requirement-directed resolver dispatch, syntax, and coherence rules are concrete and scheduled.
