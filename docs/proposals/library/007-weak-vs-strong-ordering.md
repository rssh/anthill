# Library proposal 007: Weak vs. strong ordering — `PartialOrd` / `WeakOrd` / `Ord`

**Status:** Implemented (WI-1109). The three-floor tower ships in `stdlib/anthill/prelude/ordered.anthill`; `SortedSet`'s comparator slot is `WeakOrd`; the forwarding derivation is `derive_forwarded_provisions` (`kb/typing.rs`). Three things are recorded in §Open questions rather than done: the laws are dormant (nothing discharges them per instance); the `Eq`/`PartialEq` tower is **not** given the same forwarding, because `requires` is what makes `Eq.eq` a *name*; and a forwarding row is still offered as a provider candidate, which makes a reachable diagnostic wart on **both** towers.

Continues [`004`](004-partial-vs-total-equality-and-ordering.md) exactly as 004 continues [`051`](../051-structural-vs-semantic-equality.md): 051 separated *structural* from *semantic* equality; 004 separated *partial* from *total (lawful)* equality and ordering; this separates *weak* from *strong* ordering — because `Ord` conflates two independent questions, and a witness that satisfies one but not the other already ships in this repo.

**Driver:** WI-1109. Arose from WI-456 (`SortedSet` in the prelude), whose second clause — *"maybe local `Eq` should be derived from `Ord`?"* — is answered in §"Why `Eq` is required, never provided".

---

## Motivation

### `Ord` answers two questions at once

`Ord` as 004 left it demands `compare -> Int64`, `requires Eq, PartialOrd`, and states the law

```anthill
compare_eq: eq(?a, ?b) <=> eq(compare(?a, ?b), 0)
```

That biconditional bundles two independent properties:

1. **Totality** — every pair is comparable. (What `PartialOrd` lacks: a `NaN` operand answers `false`.)
2. **Antisymmetry w.r.t. `Eq`** — `compare(a, b) = 0` implies `eq(a, b)`, i.e. the *kernel* of `compare` is exactly `Eq`.

They are orthogonal, and the standard names separate them: a reflexive, transitive, **total** relation whose kernel may be coarser than equality is a *total preorder*, or **weak order**; one that is additionally antisymmetric is a *total order*, or **linear order**.

### The conflation is not hypothetical — it ships

`ByLength` (`wi844_sorted_set_driver_test`) orders `String` by length and provides `Ord[T = String]`. Measured:

```
ByLength.compare("zz", "aa") = 0        String.eq("zz", "aa") = false
```

so `compare_eq` is **false** for a witness this repo ships and drives. It loads only because the law is dormant (`eq.anthill`: obligations are "not discharged or refuted per instance").

### And the consequence is observable

`SortedSet.insertSorted` treats `compare = 0` as identity, so a set under a coarse comparator stores **equivalence classes**. Measured:

| | |
|---|---|
| `{"zz","aa","b"}` under `ByLength` | **2** elements |
| the same three under the host `Ord[String]` | **3** elements |
| `union({"zz"}, {"aa"})` | `["zz"]` |
| `union({"aa"}, {"zz"})` | `["aa"]` |

`union` keeps the **left** operand's representative, so under a coarse kernel it is **not commutative** — same members, different terms. This is not a `SortedSet` bug; it is the only thing the operation can mean once the comparator is chosen. Nothing in the library said so, and `sortedset.anthill` positively claimed the opposite ("the sorted item list is canonical, so two sets with the same members are the same term").

---

## Design

### The tower

```
PartialEq[T]                                 -- eq, neq ; NO reflexivity law
Eq[T]          requires PartialEq[T]         -- + eq_refl

PartialOrd[T]  requires PartialEq[T]         -- gt/lt/gte/lte ; INCOMPARABLE pairs possible
WeakOrd[T]     requires Eq[T], PartialOrd[T] -- compare ; TOTAL ; CONGRUENT:
                                             --   eq(x, y) -> compare(x, y) = 0
Ord[T]         requires WeakOrd[T]           -- + the converse:
               provides WeakOrd[T = T]       --   compare(x, y) = 0 -> eq(x, y)
```

`Ord` declares **no operation**. Its entire content is the extra law — deliberately the shape 004 gave `Eq` over `PartialEq` ("a marker + obligation, no new operation").

### The congruence law is the one `WeakOrd` owns

`eq(x, y) → compare(x, y) = 0` says **`compare` is well-defined on `Eq`-classes**: the kernel of `compare` is a union of `Eq`-classes, never a splitting of one. That is exactly what keeps a sorted structure well-formed — no `Eq`-class can land in two positions — and it is the weakest law that does. Every comparator satisfies it, `ByLength` included.

It is written as a **`constraint`**, not an equation, and the reason is soundness rather than style: an `<=>` is what the equational / `[simp]` / proof layers *rewrite* with, and rewriting `eq(a, b)` to `eq(compare(a, b), 0)` is exactly the unsound step at a coarse kernel. `Ord` — whose whole content is that the two coincide — carries the biconditional `compare_eq`, where the rewrite **is** valid.

### Why `Eq` is required, never provided

WI-456 asked whether a local `Eq` should be *derived from* `Ord`. It should not, and the reason is mechanical: **the reader of an `eq` instance is the unifier.** `sem_eq_core` (`kb/resolve.rs`) is a resolver builtin probed per structurally-unequal goal, so the call an instance answers was made by the engine, at no syntactic position an author could write a choice in. `build_eq_dispatch_index` states it at the enforcement site — it is "the one `eq` reader with no later site to complain from" — so a derived `Eq` would be a second supplier and `AmbiguousEqDispatch` (WI-837) refuses one.

What the question was reaching for is nevertheless available, and the distinction is the useful part: **a proof is not a supplier.** A law adds no `sort_ops` entry, no provision row, no dispatch candidate — so relating an order to `Eq` never mints a rival. `Eq` therefore sits on `WeakOrd` as the **relatum the congruence law is stated against**, not as something the order supplies.

### Naming

Not `TotalOrd`. Totality is what `WeakOrd` already adds over `PartialOrd`; the top floor adds **antisymmetry**, so naming it "Total" would attach the name to the wrong property. Not `PreOrd` either: a preorder need not be total and this one is. *Weak order* is the standard term for a total preorder.

The three floors are one-to-one with **C++20 `<compare>`** — `partial_ordering` (NaN), `weak_ordering` (equivalence *without* substitutability, canonically case-insensitive compare), `strong_ordering` (equivalent implies substitutable) — which is not merely cosmetic: a carrier's floor is what decides the comparison category its generated `operator<=>` returns, so this taxonomy feeds **WI-1107** (004 step 4's unshipped total half) rather than having to be invented there.

**Prior art.** Haskell's `Ord` documents a total order *including* antisymmetry and `compare x y == EQ` iff `x == y`, unchecked — and `Data.Map.union` is documented **left-biased**, the same non-commutativity measured above, acknowledged in container docs rather than ruled out by the class. Scala's `Ordering[A]` is total in *comparability* only; `Ordering.by(_.length)` is legal and `TreeSet` collapses under it. Lean 4's `Ord` is bare `compare` with no superclass and no laws, with lawfulness factored into separate classes (`OrientedOrd`, `TransOrd`, and `LawfulEqOrd`, whose statement `compare a b = .eq ↔ a = b` is precisely this proposal's `Ord` law). Of the three, only Lean gives the two questions two names; 004 already chose Lean's model for the equality side, so factoring the ordering side the same way is consistency rather than novelty.

### One provision per carrier: the forwarding

`Ord provides WeakOrd[T = T]` is a **spec forwarding to a spec** — the `Stream provides Iterable` shape — and 058 §3.8 states its consequence as one clause over the relation:

```anthill
provides(?W, WeakOrd[T = ?X]) :- provides(?W, Ord[T = ?X])
```

A load pass materializes that **row** (`derive_forwarded_provisions`), so `Int64`, `String` and `BigInt` write `provides Ord` alone and the floor below is derived. Deriving beats writing both floors: two hand-written provisions permit a bundle whose halves disagree, whereas one `compare` cannot.

Deriving the **row** rather than teaching each reader is the load-bearing choice. The `provides` relation has many readers — the provider-requirements check, witness selection, the resolver's pin filter, `build_sort_ops_table`, dispatch, codegen — and a forwarding invisible to any *one* of them is a silent wrong answer there, because "no provision" is a legitimate answer everywhere. A materialized row is read by all of them unchanged.

Two constraints on that pass, both learned by measurement:

- **Placement.** A derived row is worthless before its first consumer. Asserted below `req_insertion` the rows were correct and read by nobody; they must land beside `derive_total_eq`, whose own comment already says so.
- **Conditional provisions derive nothing.** A `:- goals` tail rides in separate `ProvidesConditionInfo` facts, so a conditional provision's row is a plain fact and copying only its head would claim the lower floor *unconditionally* — the `ProvisionConditionsTooWeak` over-claim, manufactured by the deriver. A conditional provider writes both floors by hand, each with its own tail; `Pair` does, and its two tails genuinely differ (weak iff both components weak, strong iff both strong).

`Ord` **also** `requires WeakOrd[T]`, and the two clauses are not redundant: `provides` says every `Ord` *carrier* is a `WeakOrd` carrier (what the derivation reads); `requires` says every `Ord` *dictionary* contains a `WeakOrd` one (what a **use site** reads). Without the second, a body written `requires Ord[T] … WeakOrd.compare(a, b)` — every ordering-generic in every downstream program — fails to resolve its own call.

### What `SortedSet` now says

`requires O: WeakOrd[T]`, because a sorted structure needs congruence and nothing more. The quotient behaviour is therefore **declared contract**, not a surprise: under a coarse `O` the set stores classes, `insert` keeps the incumbent, and `union` keeps the left operand's representative. A consumer wanting a set of *elements* writes `requires O: Ord[T]` and gets it checked.

---

## Migration

Additive for the standard library. Every stdlib and binding provider is genuinely strong and keeps `provides Ord`; the derivation supplies its `WeakOrd` row. `Pair` gains a second conditional provision (`provides WeakOrd[Pair] :- WeakOrd[A], WeakOrd[B]`) beside its `Ord` one, since a lexicographic pair is weakly ordered iff both components are — a strictly weaker condition. `Float` is untouched (it provides `PartialOrd` and nothing above). `TotalFloat` is untouched (lawful `Eq`, still no order).

What moves is **coarse comparators**, which is the point: a witness ordering by a key declares `WeakOrd`. `ByLength` did, and so did the ordering slots and call-site brackets naming it. Comparators that are lexicographic over *all* components (`ByFst`, `BySnd`) have kernel = `Eq` and stay `Ord`.

---

## Interaction with other proposals

- **[004](004-partial-vs-total-equality-and-ordering.md)** — this refines 004's ordering half. 004's `Ord` becomes this proposal's `WeakOrd` in everything but the extra law; 004's text stands as written.
- **[058 (kernel)](../058-modular-instances.md)** — §3.8's forwarding clause is what the derivation implements, and §3.8's *exclusion* of `Eq` is vindicated here for a second reason it does not state (below).
- **WI-1107** — the comparison-category mapping for generated `operator<=>`.

---

## Open questions

1. **The laws are dormant.** Nothing discharges `eq_refl`, `compare_congruent` or `compare_eq` per instance, so `Ord`-vs-`WeakOrd` is enforced by which spec a carrier *declares*, not by a proof. A law-discharge capability is what would catch a `ByLength` declared under the wrong spec; it is a separate arc.

2. **`Eq` does not get the same forwarding, and the reason is NAMING, not circularity.** Both variants were driven:

   | | |
   |---|---|
   | `requires` **and** `provides` | **1867 of 2849** fail — `construction is cyclic: PartialEq[X] -> PartialEq[X]` |
   | `provides` alone | **32** fail — every one `unresolved import 'anthill.prelude.Eq.eq'` |

   The second number is the real reason. **`requires` is what makes `Eq.eq` a name**: 004 deliberately kept `Eq.eq` resolving to the inherited `PartialEq.eq` through the requires-chain (WI-614) so call sites stay source-compatible, and `provides` is a statement about *carriers* that puts nothing in the spec's own scope. The two clauses are mutually exclusive here, and the one that keeps written names working wins.

   **A FIRST DRAFT OF THIS SECTION CLAIMED THE CYCLE WAS PECULIAR TO THE EQUALITY TOWER. It is not, and the correction matters more than the claim did.** `Ord` carries both clauses and cycles identically — it is merely *masked*, because `WeakOrd requires PartialOrd` fails first for most carriers. Driven: a carrier providing `Eq` and `PartialOrd` but no `compare` gets `construction is cyclic: WeakOrd[T = Half] -> WeakOrd[T = Half]`. The first probe used a carrier with *no* provisions at all, failed at `PartialOrd`, and was read as absence of the cycle rather than as an earlier failure hiding it.

3. **The forwarding row is offered as a provider candidate, and it should not be.** That is what both cycles are: `Ord` is not a carrier — nothing has type `Ord` — yet `impl_sorts_providing_spec(WeakOrd)` returns it, so the resolver tries it and loops. A forwarding row is a *rule about the relation*, not a provider of anything. Excluding such rows from candidate collection is the clean statement, and it would remove the cycle from both towers; it is not done here because `Stream provides Iterable` is the same shape and dispatch on streams may depend on it, so the change needs its own measurement. Today the cycle only degrades a diagnostic — a refusal either way, never a wrong answer — which is why it is recorded rather than rushed.

4. **`max`/`min` return an observable representative.** At a tie the first operand wins both, which is invisible when the kernel is `Eq` and observable when it is coarser. Stated as contract at the declaration; whether a `WeakOrd` consumer should be able to *ask* for a canonical representative is unexplored.
