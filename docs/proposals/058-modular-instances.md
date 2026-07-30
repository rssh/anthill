# Proposal 058 — Modular instances: selecting a non-canonical provider at a use site

**Status:** Active. The core (§3.1–§3.5) is delivered; defaults (§3.6) and the library architecture (§3.8) are proposed. This document states the language **rules and surface** only. Implementation mapping, phase status, measurements, and build order: [`../design/058-implementation.md`](../design/058-implementation.md). Exploration record: `docs/brainstorms/prelude-multiple-orderings.md` and git history.

## 1. Problem

`5` is an element of `(Int64, +, 0)` and of `(Int64, ×, 1)`, but Anthill refused two providers of one spec for one carrier at load — and even without that refusal, a call `Monoid.combine(a, b)` had no way to say which instance it means. Bundling (`algebra.Ring`) serves only fixed pairs known in advance. The spec's per-`import` selection promise cannot express the need at all: `fold[Monoid = AddM](xs)` beside `fold[Monoid = MulM](ys)` requires both providers in one body, and a sorted set chooses its order per construction site, not per scope.

## 2. Model

Supply and demand are two ends of one relation, and the language already has it. Every `provides Spec[…]` or `fact Spec[…]` declaration is recorded by the loader as a `SortProvidesInfo` fact, and the reflect layer exposes those facts as a queryable relation: `provides(?A, ?S_inst)` — "sort `?A` provides the spec instance `?S_inst`" (`stdlib/anthill/reflect/typing.anthill`, whose own comment calls `requires X` and `fact X[Y]` "the two ends of one relation").

A `requires Spec[…]` clause is the demand end. It adds nothing to the `provides` relation; it asks it a question: *which sort `?W` provides `Spec[…]`?* In SLD terms that question is the **goal** `provides(?W, Spec[…])` — "goal" being the ordinary name for a query the resolver tries to prove, binding its variables as it succeeds. Instance resolution is therefore not a new subsystem: it is the language's own relational search, aimed at its own `provides` relation. Each answer binds `?W` to a provider, and the requirement dictionary the runtime threads is that answer made concrete — the chosen provider plus, recursively, the answers to that provider's own requirements.

Every rule in §3 is a policy about this one query's answers:

- **Coherence** (§3.7) demands the query have at most one answer for a given carrier.
- **Ambiguity** (§3.2 tier 3) is a call site that faces two answers and picks neither — a two-answer query is itself ordinary.
- **Explicit selection** `f[Spec = W]` (§3.3) substitutes `W` for `?W` *before* asking, so the query only checks that `W` provides the spec.
- **A named slot** `requires O: Spec[T]` (§3.4) gives the answer a source-level name — which is what lets the chosen provider appear in a type.
- **A default** (§3.6) is the answer silence prefers when several exist.

(The checker implements this account inside the typer rather than by literally querying the reflect KB at each check, and `requires provides(O, Spec[T])` is not an available spelling — the model is the semantics, not the code path.)

## 3. Rules

### 3.1 Coexistence, gated on nameability

Two or more providers of one spec for one carrier **may coexist** — if and only if every ambiguous call they could cause has a repair the author can write. There are two repair currencies. Concrete providers pay in **values**: their values carry their own sort, dispatch answers by the value, and they coexist as before with no names involved. Abstract providers pay in **names**: an unselected call's repair is `[Spec = W]`, so every candidate needs a spelling. A witness sort has one — its declared sort name. An instance fact does not — its identity *is* the bindings it asserts — so a group containing one keeps the load-time refusal: coexistence one cannot select out of is a trap, not a feature.

The missing names are **not generated**, deliberately. A bracket value is a *declared identity* — stable under edits, resolved through the ordinary name system. A generated name would be either derived from the fact's content (a fingerprint: editing the fact breaks every site that wrote it, or silently re-binds them if another fact matches the old fingerprint) or ordinal (reordering two declarations silently swaps what every written selection means — last-wins in a new costume). Wanting a name is served by declaring one: wrap the fact in a witness sort, or — the deferred increment — an *authored* name slot on the fact form (`fact AddM: Monoid[…]`).

### 3.2 Dispatch — the ladder

An unselected spec-op dispatch resolves, in order:

1. **Explicit selection** written at the use site (§3.3).
2. **The unique provider** for `(spec, carrier)` — the pre-existing rule, unchanged.
   - *2a (proposed):* **the default provider** (§3.6), when exactly one of the tied most-specific candidates is it. Specificity ranks first — a strictly-more-specific candidate wins silently; a default is a fallback, not a competitor.
3. Otherwise: a **loud error at that use site**, naming every candidate and the repair (the bracket to write, or the reason none applies — a value-directed tie has no bracket; a sub-goal's tie is reported at its own level, never re-attributed to the outer spec).

### 3.3 Selection surface

The call-site bracket, keyed by the **requirement slot**; the value names a witness sort:

```anthill
fold[Monoid = AddM](xs)                    -- key = the slot's spec
Desc.describe[Desc = LoudDesc](w)          -- a direct spec-op call: key = the spec itself
biFold[plus = AddM, times = MulM](xs)      -- two slots of one spec: keys = the slot NAMES (§3.4)
```

A key resolves as: (1) a declared **type parameter** of the operation or its enclosing sort — a named slot *is* one; (2) a requirement's **spec short name**, when unambiguous among the callee's anonymous slots. A **qualified** key is refused, not resolved — selection must not depend on the caller's imports, and any selection a short name cannot express is written with a named slot instead. Name collisions across the two scopes, with a requirement's short name, or with the spec's own name are refused **at the declaration**: one name, one channel. A bracket in a **rule body** is refused loudly (selection there is deferred, not ignored); route through an operation.

Pinning does not reach into the resolution tree: a witness's own sub-goals always resolve by search. Steering one is written as a named slot **on the witness**, bound in the key's value position — `fold[Monoid = ListM[O = MyEq]]`, an ordinary type application.

### 3.4 A named requirement slot is a parameter; an anonymous one is a constraint

```anthill
requires Eq[T]              -- anonymous: a CONSTRAINT — solved, not recorded
requires O: Ordered[T]      -- named: a PARAMETER — part of the type's identity
```

An anonymous slot fixes nothing about the type: `List[T = Int64]` is one type no matter which `Eq` satisfied it. A named slot is an ordinary type parameter, addressable in brackets and in type position — `SortedSet[T = String, O = ByLength]` and `…O = Alphabetical]` are **different types**, so merging them is a type error before it is a wrong answer. The author chooses by naming. Omitting a named slot in type position means "any" — it is how order-agnostic signatures are written, so the merge guarantee is per-signature, holding exactly where the slot is written. Omitting it at a call leaves it to inference (the ladder, §3.2).

### 3.5 Validation at the selection site

`f[Spec = W](…)` requires: `W` provides `Spec` at the call's bindings (else loud, naming both); the slot exists on the callee; and the dispatch is not value-directed on a concrete carrier — there the value decides, and an explicit witness is **refused**, not preferred.

### 3.6 Defaults — one relation, one inference rule *(proposed)*

Whether silence may pick is **not a property of the spec** — `Monoid[Int64]` has no canonical instance while `Monoid[List]` has concatenation — so it is a per-`(spec, carrier)` partial function, expressed as reflect-layer facts (the variance pattern, proposal 035; **zero new grammar**):

```anthill
entity DefaultProvider(spec: Symbol, provider: Symbol)

rule default_provider(?S, ?C, ?W) :- DefaultProvider(spec: ?S, provider: ?W), …
rule default_provider(?S, ?C, ?C) :- self_provides(?C, ?S)      -- the inference rule

constraint one_default: eq(?W1, ?W2) :-
  default_provider(?S, ?C, ?W1), default_provider(?S, ?C, ?W2)  -- refused at load
```

- **The carrier's own provision is its default**, inferred — the existing standard library needs no edits.
- A `DefaultProvider` fact marks an *existing* provider (typically a witness for a foreign carrier) as the fallback — the **application's** act when linking libraries that don't know each other; the carrier is derived from the provider's provision.
- **Conditionality composes for free.** The rule above joins the mark with `provides`, and a conditional provision (§3.8) provides only where its chain discharges — so marking `ListOrd` default for `Ordered` yields a default for `List[T = E]` at exactly those `E` whose `Ordered[E]` resolves. Two default rows whose carriers *unify* (a ground row beside a parametric one) are refused by `one_default`; layering defaults by specificity would be a widening needing its own measurement.
- **Sugar *(proposed)*: a provision may mark itself** — `default provides X[…]`, one leading modifier (the `internal` pattern), desugaring to the same `DefaultProvider` row. (A trailing `[default]` annotation was considered and dropped: a bracket list right after a bracketed type invites a parse tie, and the `[simp]` precedent follows a rule body, not a type.) The reference-form fact keeps its own job — marking a provider you *cannot edit*. Discipline: mark inline when you own the carrier or ship its canonical companion; mark by reference as the assembler otherwise; `one_default` arbitrates all rows regardless of origin.
- **No-displacement is derived, not stated**: for a self-providing carrier the inferred row already exists, so an explicit fact naming a rival violates `one_default`. *Fill silence, never overwrite speech* — no one line can flip what every linked library's bracket-less dispatch means.
- No row means: say which (§3.2 tier 3). Deferred, same idiom: a `within:` field for sort-scoped defaults; a per-carrier `NoDefault` guard.

The learnable core: **a silent dispatch takes the carrier's own provision, or the one a `DefaultProvider` fact names; two such rows for one carrier refuse to load; no row means say which.**

### 3.7 Coherent specs

One property *is* per-spec: when a spec's dispatch fires from **unification**, no call site exists anywhere to select, so two suppliers per carrier are refused **at load**. The `Eq` family is such a spec, permanently — semantic equality cannot be selected, and no bracket alters which spec a carrier provides. In general: a read that asks *existence* of a provider stays boolean; a read that *selects* one goes loud on the second candidate — never first-match.

### 3.8 Conditional provisions; an alternative to an ordered carrier is a BUNDLE

**A provision may be conditional** — `Ordered[List[T = E]]` exists only where `Ordered[E]` does. In the §2 model this is a Horn clause over the `provides` relation, and it is written today as the provider's own `requires` chain:

```anthill
sort ListOrd
  sort E = ?
  requires OE: Ordered[T = E]            -- the condition, AND the evidence the body uses.
                                         -- NAMED (§3.4): the element ordering is not
                                         -- incidental — selectable (`ListOrd[OE = …]`,
                                         -- §3.3) and part of ListOrd's identity
  provides PartialOrd[T = List[T = E]]   -- the bundle (below): List has no order of its own
  provides Ordered[T = List[T = E]]
  operation compare(…) = … Ordered.compare(headA, headB) …
end
```

The chain does double duty: it *conditions* the provision and it *supplies the evidence* the provider's bodies dispatch through. A direct per-clause spelling — `provides Ordered[T = List[T = E]] :- Ordered[T = E]` — is the same clause with conditions scoped to one provision instead of the whole sort; a candidate surface refinement, recorded, not required, and the conditional leg of §4's provides-consolidation. Two boundaries: **a condition admits, it never ranks** — it shrinks where a provision applies, and provisions still applicable after their conditions resolve by the ladder (§3.2), which is the line between this and the predicate-directed selection §7 rejects; and a provider's chain does **not** discharge the *spec's* own requirements (`Eq[List[E]]` must come from `List`'s provision, not from the witness's chain) — lifting that is a separate, deferred increment.

*(proposed from here)* `Ordered`'s laws derive the inherited comparison surface from `compare`, so a lone alternative `Ordered` witness contradicts the `PartialOrd` it inherits from the carrier — for *any* order but the carrier's own. A lawful alternative therefore **bundles** its own `PartialOrd` + `Ordered`, mutually consistent, anchored to the one shared `Eq` (which stays outside the bundle — §3.7). This generalizes: in a spec tower, an alternative is a consistent bundle of floors, never one floor over shared lower floors. Companion rule: **a provider's dictionary resolves a sub-goal the provider itself provides to its own provision**; global search serves the rest — locality by *selected provider*, independent of caller scope.

### 3.9 Dictionaries are PASSED at run time — instances are never CHOSEN at run time

When a body dispatches through an abstract slot — `report[T, O](s: SortedSet[T = T, O = O])` — the provider arrives as a **dictionary in the frame**, passed like an argument: two calls may carry two different orders through one body. That is ordinary dictionary passing, the delivered threading.

What does not exist is an operation that *constructs or selects* a dictionary from runtime data. Every dictionary in flight was built at a site where the typer resolved the witness (by the §3.2 ladder); run time only copies it along. "Choosing at run time" therefore always means *which statically-resolved branch executed*:

```anthill
if cfg then report(SortedSet.empty[T = String, O = ByLength]())
       else report(SortedSet.empty[T = String, O = Alphabetical]())
```

Each branch's dictionary is static; only the branch taken is runtime. Two consequences: a witness is not a value (`let o = if cfg then ByLength else …` is unwritable — sorts are not terms), and a first-class dictionary *value*, if ever added, may fill an anonymous slot — a constraint records nothing in the type — but never a named one: a named slot is a type parameter, and a value cannot determine a type.

## 4. Syntax

New grammar — **one production**: the named requirement binder, at sort level and operation level:

```anthill
requires O: Ordered[T]                          -- sort-level: a named slot, a type parameter

operation biFold[T](xs: List[T]) -> T
  requires plus: Monoid[T], times: Monoid[T]    -- op-level: two slots of one spec, one name each
```

A named slot becomes an ordinary type parameter of its declarer — which is exactly what the bracket then binds (`biFold[plus = AddM, times = MulM](xs)`).

Two notes on the surface this rides on. Inside a sort, `provides X[…]` and `fact X[…]` are today **one construct** — both record the same provision (measured end to end). *(Proposed)* **the `fact` spelling of provisions retires**: `provides` becomes the one spelling, and `fact` returns to meaning only a plain data assertion (`WorkItem`, `Covariant`, `DefaultProvider`) — removing the language's one construct whose meaning depended on its container. The retirement converges with §3.8's per-clause surface (`provides X[…] :- goals` is the conditional leg of the same consolidation) and halves the sugar: `default provides X[…]` — one leading modifier, the `internal` pattern, marking the enclosing sort as that instance's default (sugar for the §3.6 row) — needs no `default fact` twin. Namespace-level op-binding instance facts (§3.1) sit outside sorts and are untouched. Migration is mechanical, warned at the loader's own lowering site.

The modifier family generalizes by one principle: **a modifier attaches where its relation's key lives.** `default` is keyed per `(spec, carrier)` derived from a provision, so it rides `provides`; `Coherent` is keyed per **spec**, so its sugar rides the spec's own declaration — `coherent sort PartialEq … end`, desugaring to the `Coherent(spec)` row (the `enum sort` precedent; arrives with §3.6's deferred re-homing). On a *provision*, `coherent` is **refused**: a provision must not foreclose coexistence for a spec and carrier it does not own — the mirror image of the no-displacement rule.

Everything else rides existing surface: selection uses the 042 bracket channel (already parsed and lowered — new *meaning*, no new grammar); defaults are ordinary facts of a reflect entity (§3.6, no grammar).

## 5. Examples

```anthill
-- two monoids on one carrier, both in one body
fold[Monoid = AddM]([2, 3, 4])    --  9
fold[Monoid = MulM]([2, 3, 4])    -- 24

-- the opposite pole (§3.7): equality dispatches from UNIFICATION — `eq(?a, ?b)` in a
-- rule body has no call site where a bracket could ever be written — so a second
-- supplier is refused at LOAD, naming both. The check is delivered (keyed to the Eq
-- family); declaring the family as data rows is the deferred §3.6 re-homing:
fact Coherent(spec: PartialEq)
sort Coin       provides PartialEq[T = Coin]  operation eq(a: Coin, b: Coin) -> Bool = …  end
sort CoinEqAlt  provides PartialEq[T = Coin]  operation eq(a: Coin, b: Coin) -> Bool = …  end
-- load error: two `eq` suppliers for `Coin` — coexistence would leave rule matching
-- with two answers and no way to say which, so it is refused where it is declared

-- an ordered container: choose at construction, thread by type
let a = SortedSet.empty[T = String, O = ByLength]()
SortedSet.insert(a, "zz")          -- no bracket: a's TYPE says which
SortedSet.union(a, b)              -- b Alphabetical ⇒ TYPE ERROR naming both orderings

-- a conditional provision (§3.8): lists are ordered wherever their elements are
sort ListOrd
  sort E = ?
  requires OE: Ordered[T = E]              -- named: the element ordering is selectable
  provides PartialOrd[T = List[T = E]]
  default provides Ordered[T = List[T = E]]   -- sugar (§3.6/§4): = a DefaultProvider row.
                                           -- CONDITIONAL for free — holds where Ordered[E]
                                           -- does; matters once a rival (say ShortLex)
                                           -- coexists: silence takes ListOrd, rival opt-in
  operation compare(a: List[T = E], b: List[T = E]) -> Int64 = …   -- lexicographic over OE
end
let s  = SortedSet.empty[T = List[T = Int64], O = ListOrd]()              -- OE inferred (§3.2)
let s2 = SortedSet.empty[T = List[T = P],    O = ListOrd[OE = LexFst]]()  -- OE selected (§3.3)
-- status: loads and types by delivered legs; RUNS only after the dictionary-chain
-- settlement (implementation notes §7), which gates all of §3.8

-- linking libraries you do NOT own (proposed, §3.6) — in lib_b, shipped UNMARKED:
sort MoneyByAmount                             -- glue: a witness beside a foreign carrier
  provides PartialOrd[T = lib_a.Money]         -- the §3.8 bundle
  provides Ordered[T = lib_a.Money]
  operation compare(a: lib_a.Money, b: lib_a.Money) -> Int64 = …
end
-- …and in the APPLICATION, the default declared by REFERENCE — the spelling for a
-- provider you cannot edit (the inline `default` sugar is lib_b's to write, not yours):
fact DefaultProvider(spec: Ordered, provider: lib_b.MoneyByAmount)
```

## 6. What does not change

The `Eq`/`Ordered` hierarchy and its laws (§3.7 makes "untouched" enforced); `TotalFloat` for `Map[K = Float]` — a container's key requirement is anonymous, hence a constraint, hence outside the type's identity: the newtype changes the *type*, selection changes the *witness*.

## 7. Rejected alternatives

- **Per-`import` / scoped-implicit selection** — cannot express two providers in one body; an import silently changes results.
- **Numeric priorities** — a global scale nobody owns; every surveyed language ranks by a partial order and errors on incomparable pairs.
- **Scope-distance ranking** of provisions — couples supply to caller imports. Its sound residues are in the design: self-provision inference and provider-locality (§3.6, §3.8).
- **Predicate-directed selection AMONG applicable candidates** — ranking by arbitrary computation makes coherence undecidable at load, and two libraries' predicates claiming one carrier re-create the unowned total order. Not to be confused with the **conditional provision** (§3.8), which is embraced: a condition *admits* a provision into the candidate set; nothing ranks within it.
- **Keyword surfaces / spec-level dispatch modes** — selectable-vs-default is per-carrier state, not a spec property (§3.6); relations carry it with zero grammar.
- **Last-wins** — silent and order-dependent. **Newtype-per-instance** as the general answer — kept for `TotalFloat`; does not scale to algebra (re-exporting arithmetic per wrapper). **A new keyword** (`using`/`given`) — the bracket channel already exists.

## 8. Spec amendment (`kernel-language.md` §Instance coherence)

Replace the per-`import` promise with:

> **Instance coherence.** A spec has at most one *default* provider for a given carrier — the carrier's own provision when one exists, or the provider a `DefaultProvider` fact names; a second default for one carrier is a load error naming both declarations. A second provider is permitted — but only when **every** candidate can be named, and every dispatch against that carrier must then say **which**, by binding the requirement slot at the call: `fold[Monoid = AddM](xs)`. An unselected dispatch with two or more candidates takes the default when exactly one of the tied most-specific candidates is it, and is an error naming every candidate otherwise. A sort's *embedded* requirements are handled by whether the slot is **named**: a **named** slot is a type parameter, so the chosen provider is part of the sort's type identity and every value of that type carries it (`SortedSet[T = String, O = ByLength]`); an **anonymous** slot is a constraint — it is solved, not recorded, so it fixes nothing about the type and is re-answered at each dispatch, which is why two `Map[K = Int64]`s cannot differ by which `Eq` satisfied them. Selection is therefore **explicit and per-call**, not per-scope: two routes to `A[X]` agree unless a call site deliberately says otherwise. (Implicit scope-directed selection — a nearer provider silently winning — is deliberately **not** the rule.)

The sentence *"resolved in that sort's scope and captured when its instance is constructed…"* is dropped, not reworded — an anonymous slot records nothing. *"A consumer chooses which instantiation to use via `import`"* is replaced: an import governs **visibility**; among visible providers the call selects.
