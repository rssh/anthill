# Future: Associated (dispatched) relations as spec members

> **Sketch** (2026-07-14; moved from proposal 052 on 2026-08-15; **refreshed 2026-09-18** against
> proposals 060 / 061, the requirement-channel design and the current build) — unnumbered
> (see [README](README.md)). Related to
> [proposal 052](../052-rules-as-stream-valued-operations.md), but not part of its committed design.
> Ticket: WI-721 (`PreOpened`).

Proposal 052 makes a relation a first-class **value**. A separate axis, surfaced while pinning down how `requires`
reaches a spec's rules: a relation as a **per-instance-dispatched spec member** — the relational dual of a
spec operation.

**What the refresh changed.** When this was written a spec rule was "one fixed clause set, shared by
every requirer", and everything per-instance was the gap. That is no longer where the line runs.
[061](../061-rule-declarations.md) gave the clause-less head a meaning (it DECLARES),
[060](../060-clause-level-requirements-and-typed-heads.md) §2 with C666A delivered a per-CARRIER
join onto such a declaration, and the requirement channel replaced the Γ *requirement slot* this
sketch leaned on (piece 2 below says which Γ that was — not 050's Γ itself, which stands). So half
of what it asked for exists, spelled differently, and what remains is
narrower. It is restated below as it stands today. Every **measured** below is 2026-09-18, on the
`anthill` CLI, over `follows(alice, bob)`, `follows(bob, carol)`, `road(kyiv, lviv)`.

## What already holds

**Name visibility — unchanged, and never the gap.** `requires Spec` is **sort composition**: it
splices Spec's scope in as a parent, and Spec's contents are reachable bare in the requiring sort.
This is **uniform across operations and rules** — a spec's rules are bare-callable through
`requires` exactly as its operations are — *subject to the same variant-exposure filter*: a
required sort carrying `entity` variants leaks only those constructors, hiding its operations
**and** its rules alike; an entity-less sort (a spec) leaks everything (WI-291 /
[proposal 044](../044-unified-name-resolution.md)).

**A spec can declare a relation and supply no clauses** (061, delivered). `rule edge(?a, ?b)` in
`sort Graph` DECLARES `Graph.edge` and stores nothing. This is the "relational signature" the
sketch asked for, already in the language — with one difference everything below turns on: a 061
declaration is a name that clauses JOIN, not a name that dispatches.

**Carriers can supply its clauses, each kept to its own values** (060 §2 / WI-742 with C666A, both
delivered). A typed head compiles to a generated `domain(?x, T)` guard, and that guard is what
C666A admits across a `requires` edge when the annotation names the contributing sort:

```anthill
sort Graph
  sort Node = ?
  rule edge(?a, ?b)                                       -- 061: declares, stores no clause
end

sort Person
  entity alice  entity bob  entity carol
  requires Graph
  rule edge(?a: Person, ?b: Person) :- follows(?a, ?b)    -- joins Graph.edge, kept to Person
end

sort City
  entity kyiv  entity lviv
  requires Graph
  rule edge(?a: City, ?b: City) :- road(?a, ?b)           -- joins Graph.edge, kept to City
end

sort Reach
  requires Graph
  rule reachable(?a, ?b) :- edge(?a, ?b)
  rule reachable(?a, ?b) :- edge(?a, ?c), reachable(?c, ?b)
end
```

Measured: this loads, `Graph.edge(?a, ?b)` answers 3 rows and `reachable(?a, ?b)` 4 — the union —
while `reachable(alice, ?b)` answers `bob`, `carol` and `reachable(kyiv, ?b)` answers `lviv`. One
generic rule, a per-carrier relation: this is `reachable` over a social graph walking
*follows*-edges and over a road map walking *road*-edges, which is what the sketch set out to buy.
**The selector is the argument's carried type**, read by the guard; nothing is dispatched. The
admission and its three refusals are pinned in `wi742_typed_relational_head_test.rs`
(`a_typed_head_may_join_the_predicate_its_carrier_exposes` and the rows after it).

## The genuine gap — an instance the carried type does not determine

A guard reads a value. So the join above separates instances exactly as far as their carriers
differ, and stops there. Three shapes fall outside it, and they are what this sketch is now about.

**1. The provider is not the carrier.** The sketch's own example — a sort that *provides* the spec
for someone else's node type:

```anthill
sort Graph
  sort Node = ?
  rule edge(?a, ?b)                          -- associated relation: a signature, no clauses
end

sort SocialNet
  provides Graph[Node = Person]
  rule edge(?a, ?b) :- follows(?a, ?b)       -- this instance's clauses
end

sort RoadMap
  provides Graph[Node = City]
  rule edge(?a, ?b) :- road(?a, ?b)
end

sort Reach
  requires Graph
  rule reachable(?a, ?b) :- edge(?a, ?b)                    -- bare `edge` should DISPATCH per instance
  rule reachable(?a, ?b) :- edge(?a, ?c), reachable(?c, ?b)
end
```

Measured: it loads clean, `SocialNet.edge` answers 2 rows and `RoadMap.edge` 1, `Graph.edge`
answers 0 — and `reachable(?a, ?b)` answers **0, silently**. An instance `provides` opens no scope
to a rule head, so each provider's `edge` is its OWN predicate, and nothing records that it
implements the spec's. The guarded join cannot repair it: C666A admits an annotation naming the
*contributing* sort, and `?a: Person` selects nothing about `SocialNet`.

**2. Two instances over one carrier** — a follows-graph and a friends-graph, both
`Graph[Node = Person]`. However their clauses are joined — both written in `sort Person` under
the one `domain(?a, Person)` guard, or contributed by two provider sorts through a named import —
`edge` is their union and no argument can tell them apart. Which one is meant is
[058](../058-modular-instances.md)'s question — coexistence gated on nameability (§3.1), selection
by a bracket at an *operation* call site (§3.3, and a bracket in a rule body is refused) — and the
selected dictionary then has to REACH the goal.

**3. Generating mode at an abstract type** — no argument is bound, so there is no carried type to
read. 060 §2.2 records this for `domain` ("abstract `T` does NOT enumerate"), and
[`060-typedomains-implementation.md`](../../design/060-typedomains-implementation.md)
(*typedomains* below) explores the
way out: `SortDomain.member`, declared clause-less in a spec, defined once per provider, reached
through a dictionary. **That is an associated relation** — the first worked instance of this
sketch — and its measurements are reused below rather than repeated.

This is to a relation what `Ord.compare` (declared abstract, provided per type) is to a function.
Static rules force the alternative: thread the graph explicitly
(`reachable(g, ?a, ?b) :- edge_of(g, ?a, ?b)`) — the boilerplate dispatch removes for operations.

**The spec's head is written UNTYPED.** The original spelling, `rule edge(?a: Node, ?b: Node)`, is
a load error today: a typed column needs an enforcer, and a declaration stores no clause for the
`domain` guard to run in (the loader names the declaration reading as undelivered). `:- true` is
not the way out — that is a clause, and asserts every pair of nodes.

## What it needs (NOT visibility — that already works via `requires` composition)

The original named two pieces: provider-scoped clauses, and requirement-directed clause selection
read from the resolver's Γ. The first has mostly arrived and the second has moved.

**Which Γ that was, since the letter names two things.** Γ proper is
[050](../050-local-interpretation.md)'s logical environment — the FACTS known at a program point,
computed by the typing pass, carried by WI-580's specializer
([`abstract-interpreter-and-rules.md`](../../design/abstract-interpreter-and-rules.md) §6) and
handed to the resolver as `ResolveConfig.gamma`, so that a search runs over KB ∪ Γ (WI-537). None
of that moved. What this sketch leaned on was a second USE of that carrier:
`requirement-dictionaries.md` §3.3 kept a rule's requirement DICTIONARY in "a requirement
environment carried in the resolver's Γ" — WI-721 says "local-interpretation env" — and that use was
withdrawn on 2026-08-07, for a reason that bears directly on dispatch: the overlay is global to one
resolve call, neither per-activation nor backtrackable, while an instance is per-activation
(typedomains §5 has two nodes of one dictionary live at once).

1. **The LINK, not the storage.** A rule written in a provider's sort body already lands in the
   provider's scope — `SocialNet.edge`, measured above, and typedomains §4.3 measures the same for
   `Colour.member`, "the same place a spec op's implementation lands". What does not exist is the
   record that `SocialNet.edge` IMPLEMENTS `Graph.edge` for that provision — the rule twin of §8.7's
   operation auto-binding. Without it shape 1 is two unrelated predicates that share a spelling,
   which is why it fails silently rather than loudly.
2. **Dictionary-directed application** (the load-bearing engine capability). In the model that
   replaced the Γ slot, a dictionary is a term, `find_dictionary` an ordinary relation, the binding
   is σ
   ([`requirement-channel.md`](../../design/requirement-channel.md) §2), and a predicate's
   requirements are implicit PARAMETERS its goals carry implicit ARGUMENTS for — replace, never
   inherit, and no `ResolverFrame` field
   ([`op-to-rule-requirement-channel.md`](../../design/op-to-rule-requirement-channel.md),
   *op-to-rule* below). In that
   model a clause reads its dictionary with `?d = require[Graph[…]]` (WI-1040, delivered), and an
   associated goal compiles — in the typing sweep that already rewrites clause bodies — to an
   application THROUGH `?d`. typedomains §3–§4.3 works the mechanism out for one relation,
   `apply_domain(?d, ?x)`: resolve `<?d.impl_sort()>.member`, BUILD that goal and let the ordinary
   discrimination-tree lookup find the candidates (no variable-headed goal, no second clause
   opener), with the dictionary riding as a written argument wherever the provider's own clause
   has sub-requirements — *the symbol finds, the tree runs*. Generalizing that from one hard-wired
   member to any associated relation at any arity is this sketch's engine work. None of it is
   built. It stays inside 058 §3.9: the dictionary was selected where the typer or loader resolved
   the witness, and applying a relation through it is a read over a decided entry — an instance is
   never CHOSEN at run time.
3. **The entry — where the dictionary comes from — decides how much dispatch can distinguish.**
   *Derived* from a bound argument's carried type (`find_dictionary`'s witness scan, or 060 §3's
   typed-head anchor; delivered for `require[X]`), it selects by carrier: enough for shape 1 where
   a carrier has one provider, and by construction no finer than the guarded join. *Supplied* by a
   caller, it is what shapes 2 and 3 need. As a written argument a dictionary already crosses
   rule→rule (WI-1040's crossing row); the implicit-argument form is designed and unbuilt
   (op-to-rule §7 steps 1–2); the ground op→rule test needs no channel at all (WI-20260909-NAR1X's
   measurement); and the GENERATIVE op→rule edge — a relation cited in an operation body, which is
   how a bracket-selected instance would arrive — is designed as a capture in the
   `Value::Relation` (op-to-rule §5.1, §7 step 4) and owned by nobody.

Because name resolution is untouched (the name already composes in), the work is entirely in the
*link* + *resolver application* + *the entry*.

## Coherence (resolution policy; owned by [proposal 044](../044-unified-name-resolution.md))

- **Which declarations dispatch — REOPENED by 061.** The original rule was "an associated rule is
  one whose spec-level head is clause-less; a clause-bearing spec rule stays static". Under 061
  *every* declared predicate has a clause-less declaration, and its clauses arrive separately — by
  the guarded join above, or unguarded through a named import (`import Graph.{edge}`; measured:
  one shared `Graph.edge`, 3 rows, and the provider has no `edge` of its own). So the same
  declaration can already be JOINED, and this sketch wants it PROVIDED; one text must not mean
  both. What marks a declaration as dispatched has to be said in the source and is undecided. One
  constraint is delivered: 061 refuses a declaration carrying a label, a tag, an introducer or a
  typed column, so a marker on the declaration itself means lifting one of those refusals
  deliberately.
- **Ambiguity is a LOAD error — holds today.** Measured: two required specs both declaring `edge`
  and a bare use is refused, `ambiguous symbol 'edge'`, both candidates named; `Graph.edge(?a, ?b)`
  loads. It is the ordinary name-resolution ambiguity — the name composes in through `requires` —
  so nothing associated-specific has to be built, and it is loud by construction, unlike a plain
  unqualified rule miss.
- **A sort's own rule of that name overrides — holds today, in 061's spelling.** Measured: an
  unguarded `rule edge(…) :- …` written in the requiring sort is refused (C666A), and the message
  carries the repair; declaring `rule edge(?a, ?b)` there gives the sort its own predicate
  (`Reach.edge` 2 rows, `Graph.edge` 0) and bare `edge` means the local one. This mirrors the
  operation override policy (WI-444 / WI-411), with the declaration as the explicit opt-in.

## Open questions the refresh raised

1. **The marker** — the first Coherence bullet. Until it is answered shape 1's program keeps its
   current meaning: two unrelated predicates and a silent 0.
2. **Nothing checks a provider's columns.** The spec's declaration is untyped, so a provider whose
   `edge` ranges over the wrong sort loads clean — typedomains §6 measures exactly this for
   `member`. The typed DECLARATION (061 OQ1's "name plus typed columns", undelivered) is the
   natural owner, and is the same refusal the sketch's original spelling now hits.
3. **Where the two axes meet.** Citing an associated relation as a 052 `Relation[T]` value inside
   generic code is the generative entry of piece 3 — typedomains §6 calls it "the largest unknown".
   Goal-position dispatch inside a rule body does not need it; the value face does.

## Relationship

Complements 052's relations-as-*values* with relations-as-dispatched-*members*; both rest on the
same 026.1 engine — the value face composes a *fixed* query, the member face selects a *query per
instance*. Out of scope for the 052 build. 060 / 061 deliver the carrier-directed half by JOINING;
this sketch is the dictionary-directed remainder, and `060-typedomains-implementation.md` is its
first instance, scoped to one relation.

## Promotion

Assign a main-sequence proposal number and move out of `future/` when the provider-to-declaration
link, the dictionary-directed application and its entry, the marker that says which declarations
dispatch, and the coherence rules are concrete and scheduled.
