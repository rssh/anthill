# Proposal 058 — Modular instances: selecting a non-canonical provider at a use site

**Canonical reference:** named requirement slots and call-site selection are in
[`kernel-language.md` §§5.2–5.4](../kernel-language.md#52-sort); conditional
provisions are in [§5.10](../kernel-language.md#510-proof-declarations-in-body-proofs-and-provides-blocks).

**Status:** Active. The core (§3.1–§3.5) is delivered, including §3.3's composition (WI-870); §3.8's bundle rule and per-provision conditions (WI-869) are driven end to end over `Pair` (`wi858_pair_orderings_test`); §3.6's relations, their load checks (WI-860) and **their consumer — §3.2's rung 2a (WI-861) — are delivered for the DISPATCH**, and withheld at a named slot for the reason §3.4 now states; §3.10's congruent positive lawfulness, the use-site discharge WI-869 left unread, is proposed. This document states the language **rules and surface** only. Implementation mapping, phase status, measurements, and build order: [`../design/058-implementation.md`](../design/058-implementation.md). Exploration record: `docs/brainstorms/prelude-multiple-orderings.md` and git history.

## 1. Problem

`5` is an element of `(Int64, +, 0)` and of `(Int64, ×, 1)`, but Anthill refused two providers of one spec for one carrier at load — and even without that refusal, a call `Monoid.combine(a, b)` had no way to say which instance it means. Bundling (`algebra.Ring`) serves only fixed pairs known in advance. The spec's per-`import` selection promise cannot express the need at all: `fold[Monoid = AddM](xs)` beside `fold[Monoid = MulM](ys)` requires both providers in one body, and a sorted set chooses its order per construction site, not per scope.

## 2. Model

Supply and demand are two ends of one relation, and the language already has it. Every `provides Spec[…]` or `fact Spec[…]` declaration is recorded by the loader as a `SortProvidesInfo` fact, and the reflect layer exposes those facts as a queryable relation: `provides(?A, ?S_inst)` — "sort `?A` provides the spec instance `?S_inst`" (`stdlib/anthill/reflect/typing.anthill`, whose own comment calls `requires X` and `fact X[Y]` "the two ends of one relation").

Each such declaration is a **provision** — one claim, one row. A provision may carry a **condition** (§3.8): the goals under which the claim applies. The pair is an ordinary clause — the provision is the **head**, the condition its **body** — so an unconditional provision is a fact and a conditional one is a rule. That naming is used throughout §3.

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
   - *2a:* **the default provider** (§3.6), when exactly one of the tied most-specific candidates is it. Specificity ranks first — a strictly-more-specific candidate wins silently; a default is a fallback, not a competitor. Exactly one, never the first: two tied candidates naming ONE provider (a carrier's own member beside its own instance fact's binding; one provider reached through two non-identical provisions) leave the tie standing, because a default names a provider and does not arbitrate between two of that provider's own texts. **The rung answers a DISPATCH, not a named slot** — see §3.4.
3. Otherwise: a **loud error at that use site**, naming every candidate and the repair (the bracket to write, or the reason none applies — a value-directed site carries no bracket, though a witness among its rivals is still nameable at a site that does; a sub-goal's tie is reported at its own level, never re-attributed to the outer spec). "At that use site" fixes the **blame**, not the phase: when the use site's carrier is known statically the error is raised while loading, still naming the call.

### 3.3 Selection surface

The call-site bracket, keyed by the **requirement slot**; the value names a witness sort:

```anthill
fold[Monoid = AddM](xs)                    -- key = the slot's spec
Desc.describe[Desc = LoudDesc](w)          -- a direct spec-op call: key = the spec itself
biFold[plus = AddM, times = MulM](xs)      -- two slots of one spec: keys = the slot NAMES (§3.4)
```

A key identifies one of the callee's slots, as: (1) a declared **type parameter** of the operation or its enclosing sort — a named slot *is* one; (2) a requirement's **spec short name**, when unambiguous among the callee's anonymous slots. A **qualified** key is refused, not resolved — the key is *matched* against the callee's declaration, never looked up in the caller's scope, so selecting a slot never requires importing its spec. Qualification is only meaningful for a resolved name, and admitting it would make the short form import-dependent in turn. It would also buy nothing: the ambiguity that actually arises is two anonymous slots of one spec, which share a qualified name — and a named slot's key is a parameter name, which has no qualified form at all. Any selection a short name cannot express is written with a named slot instead. Name collisions across the two scopes, with a requirement's short name, or with the spec's own name are refused **at the declaration**: one name, one channel. A bracket in a **rule body** is refused loudly (selection there is deferred, not ignored); route through an operation.

Pinning does not reach into the resolution tree: a witness's own sub-goals always resolve by search. Steering one is written as a named slot **on the witness**, bound in the key's value position — `fold[Monoid = ListM[O = MyEq]]`, an ordinary type application. *(delivered — WI-870)* A key still reaches exactly one level, so the two channels are exclusive by construction: a spec key answers the goal the call made, a value's slot binding answers a sub-goal of the provider it names, and the composition nests.

### 3.4 A named requirement slot is a parameter; an anonymous one is a constraint

```anthill
requires Eq[T]              -- anonymous: a CONSTRAINT — solved, not recorded
requires O: Ord[T]          -- named: a PARAMETER — part of the type's identity
```

An anonymous slot fixes nothing about the type: `List[T = Int64]` is one type no matter which `Eq` satisfied it. A named slot is an ordinary type parameter, addressable in brackets and in type position — `SortedSet[T = String, O = ByLength]` and `…O = Alphabetical]` are **different types**, so merging them is a type error before it is a wrong answer. The author chooses by naming. Omitting a named slot in type position means "any" — it is how order-agnostic signatures are written, so the merge guarantee is per-signature, holding exactly where the slot is written. Omitting it at a call leaves it to inference (the ladder, §3.2).

**A default may not stand in for an omitted NAMED slot** (WI-861). §3.2's rung 2a fills *silence*: nowhere did anyone say which provider, so the language may. An omitted named slot is not silence — the value flowing into an order-agnostic signature already chose, and its choice is part of its type. Answering there with a default overrides a decision made elsewhere: **measured**, a `SortedSet[T = Int64, O = Descending]` inserted into through a signature that omits `O` reads back in *ascending* order. So the rung is withheld at a named slot and such a dispatch stays a §3.2 tier-3 error. Inference for an omitted named slot is a different mechanism — it must **bind the slot in the call's result type**, so the choice travels with the value instead of being re-derived per call — and is *delivered separately* (WI-1094); a dictionary-only default cannot express it and does not compose across the next call.

**What the binder resolves to at a call is what tells the two apart** (WI-1094). A still-FLEX binder is silence — nobody wrote it anywhere — so the ladder answers and the answer is written INTO the binder, and every later bracket-less call reads it back as an ordinary tier-1 selection. A binder the enclosing signature QUANTIFIED (`size(s: SortedSet[T = String])`) is not silence, and §3.9 leaves only two answers for it. Forwarding is the value's own only where the parameter's **type names the slot as one of that signature's own declared parameters** — §7.1's `report[T, O]` form. Anything else the frame happens to hold is evidence for the signature and not for the value: an *anonymous* `requires Ord[T]` covers the goal and forwards, and **measured**, that reads a `Descending` set back in ascending order exactly as a construction would. So the erased slot is refused, at that call, **whatever the provider count** — the pre-WI-1094 refusal of this shape came from a tier-3 tie and disappeared as soon as one provider was left standing.

### 3.5 Validation at the selection site

`f[Spec = W](…)` requires: `W` provides `Spec` at the call's bindings (else loud, naming both); the slot exists on the callee; and the dispatch is not value-directed on a concrete carrier — there the value decides, and an explicit witness is **refused**, not preferred.

### 3.6 Defaults — one relation, one inference rule *(delivered, with §3.2's rung 2a as their consumer)*

Whether silence may pick is **not a property of the spec** — `Monoid[Int64]` has no canonical instance while `Monoid[List]` has concatenation — so it is a per-`(spec, carrier)` partial function, expressed as reflect-layer facts (the variance pattern, proposal 035; **zero new grammar**):

```anthill
entity DefaultProvider(spec: Symbol, provider: Symbol)

rule default_provider(?S, ?C, ?W) :- DefaultProvider(spec: ?S, provider: ?W), …
rule default_provider(?S, ?C, ?C) :- self_provides(?C, ?S)      -- the inference rule
```

`one_default` — *any two answers for one carrier name one provider* — is a **load check**, not a constraint written here: it compares rows at carriers that OVERLAP rather than at carriers that are equal, which is a question about the row set and about term overlap that an equality goal over two answers cannot ask.

- **The carrier's own provision is its default**, inferred — the existing standard library needs no edits.
- **Which provision is "the carrier's own" depends on the spec's SHAPE** (WI-1076). The carrier parameter is read off the operations, nothing in the surface declaring it: as implemented, the first declared type parameter some operation **takes** (`Iterable.iterator(c: C)` ⇒ `C`), and the carrier is that parameter's binding. A spec **none** of whose operations takes any of its type parameters has no carrier parameter, so every provision of it is the provider's own — a witness for one is unsayable, dispatch being directed by the receiver value's sort. Taking the first type parameter regardless made seven library provisions (`List`/`FiniteStream`/`MappedStream`/`FilteredStream`/`LogicalStream` `provides Stream`, `List provides FiniteStream`, `Relation provides LogicalStream`) infer no default row at all — exactly the "no edits needed" claim above failing quietly. All seven are closed, six by this predicate and the seventh by repairing the declaration that misled it (next bullet).
- **"Accepts", not "receives on", is the rule** (WI-1077, decided): a spec that takes its own element somewhere — `Set.insert(s: Set, x: T)`, `Map.put(m: Map, …)` — records that parameter, and its provision is filed at the element. Anything built on this substrate should assume the inferred leg covers specs whose operations touch no type parameter, and not `Set`/`Map`. That is settled rather than pending: narrowing it needs the surface to *say* which parameter is the carrier (a marker, or a `spec` keyword), and inferring it from a wider shape instead was measured to **refuse a program that loads** — a spec may declare both a carrier parameter and a self-receiving operation, and gating on self-representation discards its explicit binding. Where the reuse is *accidental* the repair is the declaration: `LogicalStream.pure` reused the sort's `T` for a value it only lifts (it predates operation type parameters) and now takes its own, so `Relation provides LogicalStream` infers its default like the rest.
- **A carrier's own member and its provision's op binding are both suppliers** for the same operation, on either shape, and two of them are refused rather than settled by route order. Filing a self-representing provision at its provider is what made the second one visible there (WI-1076); before, route order picked the member silently.
- A `DefaultProvider` fact marks an *existing* provider (typically a witness for a foreign carrier) as the fallback — the **application's** act when linking libraries that don't know each other; the carrier is derived from the provider's provision.
- **A default row carries the carrier its provision WROTE**, which is all conditionality needs: marking `ListOrd` default for `Ord` yields a row at `List[T = E]`, and a default only ever chooses among candidates that already resolved — a provision whose chain (§3.8) fails offers no candidate to prefer. The row itself is unconditional; the condition is the provision's, and holds where the provision is used.
- Two default rows whose carriers **overlap** are refused by `one_default` — a ground row beside a parametric one for one family; two DISJOINT ground rows coexist. Layering defaults by specificity would be a widening needing its own measurement.
- A `DefaultProvider` is a **fact**. Written as a rule it is refused: a derived mark would answer through `default_provider` while escaping `one_default`.
- **Sugar *(delivered — WI-862)*: a provision may mark itself** — `default provides X[…]`, one leading modifier (the `internal` pattern), desugaring to the same `DefaultProvider` row. (A trailing `[default]` annotation was considered and dropped: a bracket list right after a bracketed type invites a parse tie, and the `[simp]` precedent follows a rule body, not a type.) The modifier does not reserve the word — `default` remains an ordinary identifier everywhere else, which the corpus needed (an operation parameter is called `default`). The reference-form fact keeps its own job — marking a provider you *cannot edit*. Discipline: mark inline when you own the carrier or ship its canonical companion; mark by reference as the assembler otherwise; `one_default` arbitrates all rows regardless of origin.
- **No-displacement is derived, not stated**: for a self-providing carrier the inferred row already exists, so an explicit fact naming a rival violates `one_default`. *Fill silence, never overwrite speech* — no one line can flip what every linked library's bracket-less dispatch means.
- No row means: say which (§3.2 tier 3). Deferred, same idiom: a `within:` field for sort-scoped defaults; a per-carrier `NoDefault` guard.

The learnable core: **a silent dispatch takes the carrier's own provision, or the one a `DefaultProvider` fact names; two such rows for one carrier refuse to load; no row means say which.**

### 3.7 Coherent specs

One property *is* per-spec: when a spec's dispatch fires from **unification**, no call site exists anywhere to select, so two suppliers per carrier are refused **at load**. The `Eq` family is such a spec, permanently — semantic equality cannot be selected, and no bracket alters which spec a carrier provides. In general: a read that asks *existence* of a provider stays boolean; a read that *selects* one goes loud on the second candidate — never first-match.

### 3.8 Conditional provisions; an alternative to an ordered carrier is a BUNDLE

**A provision may be conditional** — `Ord[List[T = E]]` exists only where `Ord[E]` does. In the §2 model this is a Horn clause over the `provides` relation, and it is written today as the provider's own `requires` chain:

```anthill
sort ListOrd
  sort E = ?
  requires OE: Ord[T = E]            -- the condition, AND the evidence the body uses.
                                         -- NAMED (§3.4): the element ordering is not
                                         -- incidental — selectable (`ListOrd[OE = …]`,
                                         -- §3.3) and part of ListOrd's identity
  provides Ord[T = List[T = E]]      -- the PartialOrd floor is DERIVED, not written
                                         -- (below): List has no order of its own
  operation compare(…) = … Ord.compare(headA, headB) …
end
```

The chain does double duty: it *conditions* the provision and it *supplies the evidence* the provider's bodies dispatch through.

**A condition is written on the provision it constrains, not on the sort** *(delivered — WI-869)*. A sort's `requires` chain is shared by every provision it makes — and it also supplies the evidence the bodies dispatch through — so a provider of two floors of one tower cannot condition them at two strengths. In clause terms (§2) it is one **body copied onto every head** the sort declares, which is why it can express only one strength. That is not hypothetical; it is what the shipped `Pair` needs:

```anthill
provides PartialEq[Pair[A, B]] :- PartialEq[A], PartialEq[B]
provides Eq[Pair[A, B]]        :- Eq[A], Eq[B]        -- STRICTLY stronger condition
```

With one chain the weaker condition must win — `Pair` takes `requires PartialEq[…]`, since an `Eq` chain would make `Pair[A = Float, B = Int64]` a load error and stop `Pair` being a general product — and the stronger provision then **over-claims**: `Eq[Pair]` asserts lawful equality wherever the components merely have the partial one. The rule is that a `:- goals` tail scopes its conditions to the one provision — each head carrying its own body. A sort-level `requires` keeps both its present jobs (conditioning every provision, *and* supplying the bodies' evidence); a `:- goals` tail does only the first, for one provision. They compose because they are not the same mechanism. Not new machinery: a per-provision chain is a second contributor to the dictionary's **provider half**, not a new half. As delivered the provider half is ONE slot set per sort — the `requires` chain then the provisions' conditions, deduplicated, because a body is owned by the sort and not by a provision — and it is STRICTNESS that is per-provision: a slot is demanded at a dispatch when it is sort-level or a condition of the provision dispatched, otherwise left unfilled, and reading an unfilled slot is refused at the read.

*(design — WI-1040 / proposal 060)* Under the rule-clause requirement channel a conditional provision also makes a **partially composed** dictionary reachable: resolving `Eq[Pair[Int64, ?B]]` pins the outer provider while `?B` is unbound, so one sub-dictionary is not yet known. That splits "unfilled" into two representably distinct states ([`../design/requirement-channel.md`](../design/requirement-channel.md) §9–9.1): **not yet known** — an unbound variable, reading it *delays* and a later binding fills it; **never promised** — a structural hole, reading it *refuses*, exactly the refusal above. The two-leaf representation is owned by WI-1040.

Two boundaries: **a condition admits, it never ranks** — it shrinks where a provision applies, and provisions still applicable after their conditions resolve by the ladder (§3.2), which is the line between this and the predicate-directed selection §7 rejects; and a provider's chain does **not** discharge the *spec's* own requirements (`Eq[List[E]]` must come from `List`'s provision, not from the witness's chain) — lifting that is a separate, deferred increment.

*(proposed from here)* A lone alternative `Ord` witness contradicts the `PartialOrd` it inherits from the carrier — `Ord`'s laws derive `gt`/`lt`/`gte`/`lte` from `compare`, so for *any* order but the carrier's own the two disagree. The lawful shape is a consistent **bundle** of floors, never one floor over shared lower floors, anchored to the one shared `Eq` (which stays outside the bundle — §3.7). But the bundle is **derived, not written**: WI-876 already gives that derivation real default bodies, so "a carrier that supplies `compare` alone inherits the whole surface" (`stdlib/anthill/prelude/ordered.anthill:20`) — the only missing piece is the provision row a `requires PartialOrd[X]` goal finds, which is one clause in the §2 model:

```anthill
provides(?W, PartialOrd[T = ?X]) :- provides(?W, Ord[T = ?X])
```

Deriving beats writing both floors: two hand-written provisions permit a bundle whose halves disagree, whereas one `compare` cannot. The rule does **not** generalize to "a spec provides what it requires" — `Ord requires Eq` as well, and §3.7 refuses a second `Eq` provider permanently, since unification-fired dispatch has no call site to select at. It is narrower: **derive the provision for a required floor iff the upper floor's laws determine that floor's surface *and* the floor is selectable.** `PartialOrd` qualifies; `Eq` does not. Two mechanics it must respect, both recorded at the declaration: the derivation adds a provision **row**, never a second op declaration (`ordered.anthill:24` — declaring `gt`/`lt` on both specs gives a carrier providing both two `sort_ops` entries for one short name, "and which one wins is HashMap-iteration order — a coin flip, not a rule"); and the inherited default bodies read `Ord.compare`, which `PartialOrd` does not `requires`, so the per-provision condition above is also what states that they are backed only where `Ord[T]` holds (`ordered.anthill:35`, which names this very clause as the fix). Companion rule: **a provider's dictionary resolves a sub-goal the provider itself provides to its own provision**; global search serves the rest — locality by *selected provider*, independent of caller scope.

### 3.9 Dictionaries are PASSED at run time — instances are never CHOSEN at run time

When a body dispatches through an abstract slot — `report[T, O](s: SortedSet[T = T, O = O])` — the provider arrives as a **dictionary in the frame**, passed like an argument: two calls may carry two different orders through one body. That is ordinary dictionary passing, the delivered threading.

What does not exist is an operation that *selects* a dictionary from runtime data. Every dictionary in flight was **selected** where the typer or loader resolved the witness (the §3.2 ladder at a pinned site; the load-built `provides`/sort-ops tables for a rule clause); run time copies it along — or, in a rule clause, **composes** it at fire time from the already-selected table entries, keyed by the witness value's carried type. Fetch-and-compose is reads over decided entries, not choice — run time performs no typing operations ([`../design/requirement-channel.md`](../design/requirement-channel.md) §2.1, §4; WI-300 delivered the checking half, WI-1040 is the binding half). A locally derivable dictionary and a caller-supplied one must **agree** (WI-860); a supplied one decides only where local derivation cannot (`Unresolvable`/`Ambiguous`, WI-855). "Choosing at run time" therefore always means *which statically-resolved branch executed*:

```anthill
if cfg then report(SortedSet.empty[T = String, O = ByLength]())
       else report(SortedSet.empty[T = String, O = Alphabetical]())
```

Each branch's dictionary is static; only the branch taken is runtime. Two consequences: a witness is not a value (`let o = if cfg then ByLength else …` is unwritable — sorts are not terms), and a first-class dictionary *value* — delivered as the runtime sorts `Dictionary[S]` / `OpRef[A]` (WI-577), bindable to a clause variable by `?d = require[X]` (proposal 060) — may fill an anonymous slot — a constraint records nothing in the type — but never a named one: a named slot is a type parameter, and a value cannot determine a type.

### 3.10 Lawfulness derives positively — the missing use-site discharge *(delivered: the derivation by WI-1098, the use-site discharge by WI-1102)*

WI-869 conditioned the provisions; nothing yet **reads** the resulting failure. `stdlib/anthill/prelude/pair.anthill:55` records the measurement: `Set[T = Pair[Float, Int64]]` still **loads** although `Eq[Pair[Float, Int64]]` does not hold — "not an over-claim any more — the provision is conditioned and the goal genuinely fails — but no POSITIVE use-site check for `requires Eq` exists," and, measured, **a key providing nothing at all is accepted too**. Conditioning a provision changes what is *derivable*. It does not change what any use site *checks*.

**The rule: positive from positive.** A composite is lawful exactly when its parts are, which is §3.8's clause shape applied **congruently** rather than per hand-written provision:

```anthill
provides Eq[Pair[A, B]]  :- Eq[A], Eq[B]
provides Eq[List[T = E]] :- Eq[E]
provides Eq[Point]       :- Eq[<each field's type>]
```

Conjunctive over the parts, because lawfulness is a universal claim. No new machinery: a head with its own body (§2), over the relation §3.8 already conditions.

**The use-site check then reads positively.** `Set[T = X]` asks the goal `Eq[X]`, discharged either by a provision row or — inside a generic context — by the enclosing `requires Eq[T]` as an ordinary **assumption** (`Candidate::Assumption`, `rustland/anthill-core/src/kb/resolve.rs`). That is what Rust and Haskell do for `Map<K: Eq>`, and it settles three cases at once:

| written | today | with positive derivation |
| --- | --- | --- |
| `Set[T = Pair[Float, Int64]]` | loads (measured, `pair.anthill:55`) | refused — `Eq[Pair[…]]` needs `Eq[Float]` |
| `Set[T = Point(x: Int64, y: Int64)]` | loads, by *absence* of a `NonEq` | loads, by a derived `Eq[Point]` |
| `Set[T = T]` under `requires Eq[T]` | loads, by absence | loads, by assumption |

The middle row is what made the check negative in the first place — `stdlib/anthill/prelude/map.anthill:11`, "no `Eq` fact is derived for a lawful all-`Eq` composite." That is a **gap in the positive channel, not a reason to stop reading it**, and `rustland/anthill-core/src/kb/eq_derive.rs` already computes the classification: it asserts only the partial side. Assert the lawful side too and the reason lapses.

**The parametric reach is why this is a rule and not more Rust.** WI-664 already derives composite lawfulness as a monotone fixpoint over the field-reference graph — sound under recursion, stopping at a dispatched-`eq` boundary, which is what keeps `TotalFloat` lawful and shields its wrappers. What it structurally cannot reach is the parametric case: `sort_functor_of_view` resolves a field's type to its **base sort**, whose element parameter is abstract, so `Pair[Float, Int64]` / `List[Float]` / `Option[Float]` are never seen. A fixpoint over concrete field types has nowhere to put a condition on a type parameter. A clause does — and after WI-869 the clause form exists.

**What `NonEq` is left doing — the declaration, not the use site.** `eq_refl` is never discharged per instance (`stdlib/anthill/prelude/eq.anthill`: "documentation-only … NOT discharged per instance"), so nothing inspects reflexivity and nothing stops a carrier claiming lawfulness it lacks. `Float` is blocked today *only* because `NonEq[Float]` exists and the exclusion fires — `eq.anthill` says so outright. That job survives intact, and it is the only one needing a witness: `eq(w, w) = false` is a computation, checkable in a way the universal law is not.

So the remit narrows to one sentence: **`NonEq` is the checkable shadow of an unchecked law, used to refuse a false claim at the declaration.** It is not a use-site mechanism, and "provides nothing at all" stops being an accepting state — a carrier deriving no `Eq` is refused *for that reason*, rather than admitted for want of a refutation. That leaves `pair.anthill:55`'s two named halves as one: the composite `NonEq` derivation stays a declaration-side follow-up, and the positive use-site discharge is this section.

**Boundaries.** `Eq` stays coherent (§3.7) — one provider per carrier, never selectable — so a derived provision must be *the* provision, not a second candidate. The derivation is conditional in §3.8's sense, so it admits and never ranks. And it adds a provision **row**, never a second op declaration.

**What landed.** WI-1098 asserts the lawful side (`Eq` + `PartialEq` for every Total composite, `eq_derive::derive_total_eq`), so the "gap in the positive channel" is closed for a concrete-field composite; the parametric case still wants the clause form and is not derived. WI-1102 reads the discharge positively at the **call**, which is where both the carrier and the spec are in hand: a requirement whose type parameters the call site pins concretely, and whose goal no provision answers, is a load error naming the carrier and the missing provision (`kernel-language.md` §5.2, "A requirement whose carrier the call names…"). The refusal is withheld for an abstract element, a rule-body goal, a callee that never reads the slot, and a spec op that resolves structurally — each stated at `typing::OpSlotParkSite` with the program it was measured against. The `Set[T = X]` / entity-field reading of the same rule is WI-644's `check_use_site_requires_eq`, which is the *declaration*-side reader and unchanged here.

**To measure before drafting further.** (1) Whether `Map[K = (a: Float)]` is refused *today*: `docs/kernel-language.md` lists it as a gap, but a named tuple with concrete fields is inside WI-664's delivered scope, and `wi664_composite_eq_test.rs` drives the derivation and the `provides Eq[Point]` conflict but **no use-site refusal**. (2) What `map.anthill:11`'s other reason — "WI-616's universal structural default would make the positive reading vacuous" — actually denotes; it is not reconstructible from the sources, since `Float` provides `PartialEq` + `NonEq` and not `Eq`, so a check reading provision *rows* is not obviously vacuous. (2) decides whether the check may be flipped at all.

## 4. Syntax

New grammar — **one production**, delivered: the named requirement binder, at sort level and operation level:

```anthill
requires O: Ord[T]                          -- sort-level: a named slot, a type parameter

operation biFold[T](xs: List[T]) -> T
  requires plus: Monoid[T], times: Monoid[T]    -- op-level: two slots of one spec, one name each
```

*(delivered — WI-869)* **One more**: a `:- goals` tail on a provision, scoping its conditions to that provision (§3.8) — the same arrow a rule body already uses, in the one place a provision could not say "only where". The tail is a list of SPEC INSTANTIATIONS, not `rule_body` goals: a condition must be something a dictionary slot can hold, and admitting `_goal` would accept `neq(b, 0)` here with nowhere to put it.

```anthill
provides Eq[Pair[A, B]] :- Eq[A], Eq[B]
```

A named slot becomes an ordinary type parameter of its declarer — which is exactly what the bracket then binds (`biFold[plus = AddM, times = MulM](xs)`).

Two notes on the surface this rides on. Inside a sort, `provides X[…]` and `fact X[…]` are today **one construct** — both record the same provision (measured end to end). *(Delivered — WI-862)* **the `fact` spelling of provisions retires**: `provides` becomes the one spelling, and `fact` returns to meaning only a plain data assertion (`WorkItem`, `Covariant`, `DefaultProvider`) — removing the language's one construct whose meaning depended on its container. The retirement converges with §3.8's per-clause surface (`provides X[…] :- goals` is the conditional leg of the same consolidation) and halves the sugar: `default provides X[…]` — one leading modifier, the `internal` pattern, marking the enclosing sort as that instance's default (sugar for the §3.6 row) — needs no `default fact` twin. Namespace-level op-binding instance facts (§3.1) sit outside sorts and are untouched. Migration is warned at the loader's own lowering site — and it is **not** mechanical, which is the one claim here that measurement corrected. A `fact` is a rule with an empty body, so it also enters the **rule index**, and four readers keyed on that alone: region analysis, in its two functions (`is_modifiable(Cell)` answered *false*), the Rust supertrait bound, and a `requires` clause mixing a value precondition with a spec requirement, which was proved from Γ wholesale and only ever passed because the raw `Ord[T = Int64]` row made its spec conjunct resolvable as a goal. Each was found by migrating the tree and running it. The rule that survives: where some rule resolves `Spec[…]` as a **goal**, keep the fact and write the `provides` clause beside it — the deprecation is of the *spelling of a provision*, not of the fact. A `provides` clause is admitted inside a proposal-038 `provides <Carrier> language <L> … end` block too, since the block opens the carrier's scope; without that the retirement would have deprecated the only text that worked there.

The modifier family generalizes by one principle: **a modifier attaches where its relation's key lives.** `default` is keyed per `(spec, carrier)` derived from a provision, so it rides `provides`; `Coherent` is keyed per **spec**, so its sugar rides the spec's own declaration — `coherent sort PartialEq … end`, desugaring to the `Coherent(spec)` row (the `enum sort` precedent; arrives with §3.6's deferred re-homing). On a *provision*, `coherent` is **refused**: a provision must not foreclose coexistence for a spec and carrier it does not own — the mirror image of the no-displacement rule. As delivered the modifier set on a provision is `default` alone, so `coherent` there is unwritable rather than written-and-rejected; the grammar records the reason at the production.

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

-- …and the SHIPPED driver (prelude/pair.anthill + wi858_pair_orderings_test). The
-- prelude gives `Pair` componentwise `PartialEq`/`Eq` and NO ordering, so the two
-- orderings are the PROGRAM's — which is where an alternative belongs anyway, and what
-- makes every repair writable (a carrier that already had a provider, like `String`,
-- ties three ways and a bracket-less compare there can never succeed):
sort ByFst  requires OA: Ord[A]  requires OB: Ord[B]
  provides PartialOrd[Pair[A, B]]  provides Ord[Pair[A, B]]  … end
sort BySnd  … end                                              -- the mirror
let s = SortedSet.empty[T = Pair[Int64, Int64], O = ByFst]()   -- (1,9) before (2,1)
let t = SortedSet.empty[T = Pair[Int64, Int64], O = BySnd]()   -- (2,1) before (1,9)
Ord.compare(p, q)            -- no bracket ⇒ tier 3, naming ByFst and BySnd

-- a conditional provision (§3.8): lists are ordered wherever their elements are
sort ListOrd
  sort E = ?
  requires OE: Ord[T = E]              -- named: the element ordering is selectable
  provides PartialOrd[T = List[T = E]]
  default provides Ord[T = List[T = E]]   -- sugar (§3.6/§4): = a DefaultProvider row.
                                           -- CONDITIONAL for free — holds where Ord[E]
                                           -- does; matters once a rival (say ShortLex)
                                           -- coexists: silence takes ListOrd, rival opt-in
  operation compare(a: List[T = E], b: List[T = E]) -> Int64 = …   -- lexicographic over OE
end
let s  = SortedSet.empty[T = List[T = Int64], O = ListOrd]()              -- OE inferred (§3.2)
let s2 = SortedSet.empty[T = List[T = P],    O = ListOrd[OE = LexFst]]()  -- OE selected (§3.3)
-- both forms are delivered and RUN (WI-870). The selected form composes to any depth
-- and survives into a bracket-less later call, `OE` being an ordinary type parameter
-- (§3.4) and so part of `s2`'s type; a binding whose value provides nothing at the
-- slot's bindings is refused naming the SLOT

-- linking libraries you do NOT own (proposed, §3.6) — in lib_b, shipped UNMARKED:
sort MoneyByAmount                             -- glue: a witness beside a foreign carrier
  provides PartialOrd[T = lib_a.Money]         -- the §3.8 bundle
  provides Ord[T = lib_a.Money]
  operation compare(a: lib_a.Money, b: lib_a.Money) -> Int64 = …
end
-- …and in the APPLICATION, the default declared by REFERENCE — the spelling for a
-- provider you cannot edit (the inline `default` sugar is lib_b's to write, not yours):
fact DefaultProvider(spec: Ord, provider: lib_b.MoneyByAmount)
```

## 6. What does not change

The `Eq`/`Ord` hierarchy and its laws (§3.7 makes "untouched" enforced); `TotalFloat` for `Map[K = Float]` — a container's key requirement is anonymous, hence a constraint, hence outside the type's identity: the newtype changes the *type*, selection changes the *witness*.

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
