# Library proposal 004: Partial vs. total equality and ordering — `PartialEq` / `Eq` / `PartialOrd` / `Ord`

**Status:** Draft. A **library proposal** — it restructures the stdlib equality/ordering typeclasses (`stdlib/anthill/prelude/{eq,ordered,float,set,map}.anthill`) and adds no language feature (the spec hierarchy, laws, and conformance checking it uses all already exist — §"Everything already exists"). The one kernel-touching piece — the resolver reflexivity-shortcut soundness fix (§"The soundness fix") — is an *implementation consequence* of the restructuring (not a new feature), tracked in the driver WI, exactly as [`library/003`](003-finite-collection.md)'s typer work was; per the library-proposal convention it is called out but not spun into a kernel proposal.

Continues [051](../051-structural-vs-semantic-equality.md) (the `===` / semantic-`=` split): 051 separated *structural* from *semantic* equality; this proposal separates *partial* from *total (lawful)* equality — because the single `Eq` spec conflates two obligations, and IEEE `Float` is the first carrier that satisfies one but not the other.

**Depends on:** [051-structural-vs-semantic-equality](../051-structural-vs-semantic-equality.md), [049-equality-and-unification](../049-equality-and-unification.md)
**Driver / implementation:** WI-644 (this proposal is that ticket's resolution — it evolved from "drop the universal `Eq` default" to this split).
**Related:** WI-616 (semantic-`eq` dispatch, delivered), WI-645 (interpreter Float `eq`/`ordered` violate IEEE — the concrete soundness bug this closes, its direction B), WI-648 (deferred modular/scoped instances — the `SortedSet`-custom-`Ord` sibling), WI-300 (rule-body requirement goals), [043-simp-rewrite](../043-simp-rewrite.md)
**Affects:** `stdlib/anthill/prelude/{eq,ordered,set,map,float,…}.anthill`, `rustland/anthill-core/src/kb/{resolve,load}.rs`, `rustland/anthill-cpp-gen/src/lib.rs`, `docs/kernel-language.md`, `scaland/.../{parse,resolve}`

## Motivation

Anthill's `Eq` (`stdlib/anthill/prelude/eq.anthill`) is a single spec carrying `eq`/`neq` and one rule (`neq(?a,?b) <=> not(eq(?a,?b))`). It is used two incompatible ways at once:

1. **As a partial comparison** — "is `a` equal to `b`", a plain `Bool`-valued test. This is all a body goal `eq(?x, ?y)` needs.
2. **As a lawful equivalence** — the thing `Set`/`Map` keys, deduplication, sorting, and the resolver's own reflexivity shortcut rely on: `eq` must be **reflexive** (`a = a`), symmetric, transitive. `Map requires Eq[T = K]` / `Set requires Eq[T]` mean "keys have a *lawful* equality."

**IEEE `Float` satisfies (1) but not (2), and fails it *two* independent ways.** IEEE `==` is **not reflexive** (`NaN == NaN` is *false*) *and* **not a congruence** (`-0.0 == +0.0` is *true*, yet the two are not substitutable: `1.0 / 0.0 = +∞ ≠ 1.0 / -0.0 = -∞`). Either failure alone disqualifies it as a lawful equivalence — so `-0.0` is not a footnote but a *second, independent* reason Float's `==` is not lawful. Every host draws this line, and Lean draws it most precisely (see §"Prior art"): **Rust** gives `f64: PartialEq` but deliberately `f64: !Eq`; **Lean** separates propositional `=` (reflexive) from computable `==` (`BEq`, no axioms) and withholds the `LawfulBEq Float` instance for exactly these two reasons; **Haskell**'s `Eq` is lawful by convention with floats the standing caveat. Anthill, by conflating the two, forces a false choice — and the conflation has already produced a *soundness bug* (WI-645): the interpreter answers `eq(nan, nan) = true` (structural, via `OrderedFloat`) while the C++ codegen answers `false` (IEEE `==`), so the same program means different things by backend. The stdlib itself documents the intended contract it cannot currently keep — `float.anthill:19-20`: *"Float.eq returns false for NaN (NaN != NaN in IEEE)."*

Two further pressures:

- **`requires Eq[T]` is operationally vacuous today.** Because the resolver treats structural equality as a universal default instance (WI-616), *every* `T` trivially "has" `Eq`, so the requirement never fails — exactly the "operationally vacuous / actively dishonest" gap 051 flagged. It becomes meaningful only once `Eq` denotes the *lawful* obligation and some carriers genuinely lack it.
- **`Ordered` is already a *total* order.** `ordered.anthill` declares `compare_refl: compare(?a,?a) <=> 0` and `compare_antisym` and `requires Eq[T]`. Float's IEEE order is *partial* (`NaN` is unordered), so `Float` is not lawfully `Ordered` either — and today `gt(nan, 1.0) = true` in the interpreter (NaN sorts as `OrderedFloat`'s max) versus `false` compiled. The same split is owed on the ordering side.

## Everything already exists

this proposal needs no new kernel feature — it composes three delivered mechanisms:

- **Spec hierarchy** — a spec `requires` another: `Ordered requires Eq[T]`, `Field requires Numeric[T]`, `Collection requires Iterable[…]`. This is how `Eq requires PartialEq` and `Ord requires Eq, PartialOrd` are expressed.
- **Laws as labelled `<=>` rules** — `Ordered.compare_refl`, `compare_antisym`, `compare_eq`. `eq_refl: eq(?a,?a) <=> true` is written the same way.
- **Instance-law conformance checking** — `kb/load.rs` (§"requires-law ProofRecords Discharged" / Specialization witnesses, ~3866-3972, 12425): a `provides Spec[T = X]` must **discharge every one of the spec's required laws** as a proof. So a law is not aspirational — an instance that cannot prove it fails to load.

The last point is what makes this proposal *principled rather than a patch*: adding `eq_refl` to `Eq` makes `provides Eq[T = Float]` **fail to load** on its own — `Float` cannot discharge `eq(?a,?a) <=> true` for `NaN`. No blocklist, no special case; the conformance checker does the rejection.

## Design

### The hierarchy (mirrors Rust)

```
PartialEq[T]                          -- eq, neq ; NO reflexivity law
Eq[T]         requires PartialEq[T]   -- + law  eq_refl:  eq(?a, ?a) <=> true
PartialOrd[T] requires PartialEq[T]   -- partialCompare(a,b) -> Option[Int64] ; gt/lt/… derived ; NO totality law
Ord[T]        requires Eq[T], PartialOrd[T]
                                      -- compare(a,b) -> Int64 ; + compare_refl / compare_antisym / compare_eq (total)
```

- **`PartialEq`** is the base — it holds the `eq`/`neq` *operations*. Any two-valued comparison lives here; `neq(?a,?b) <=> not(eq(?a,?b))` moves here unchanged.
- **`Eq`** adds *only* the reflexivity law (a marker + obligation, no new operation). `Eq.eq` is the inherited `PartialEq.eq`; requiring `Eq[T]` means "and it is lawful."
- **`PartialOrd`** is `compare` returning `Option[Int64]` (`none` = *unordered*, the IEEE case for a `NaN` operand); `gt`/`lt`/`gte`/`lte` derive from it and answer `false` on `none`.
- **`Ord`** is the total order (`compare -> Int64`, the current `Ordered` renamed) with reflexivity/antisymmetry.

Symmetry / transitivity may be added as further `Eq`/`Ord` laws later; reflexivity is the one that decides the `Float` question and is the minimum this proposal commits to.

### Prior art — Rust (2-level) and Lean (3-level)

The split is the standard host-language answer, and Anthill's *three* equality notions map onto Lean's three more precisely than onto Rust's two:

| Anthill | Rust | Lean | reflexive? | `Float` has it |
|---|---|---|---|---|
| `===` / `struct_eq` | *(no direct analogue)* | propositional `=` (decidable) | yes | yes (`nan === nan`) |
| `PartialEq.eq` | `PartialEq` | `BEq` / `==` (no axioms) | no | yes (IEEE) |
| `Eq` + `eq_refl` (**checked**) | `Eq` (nominal marker) | `LawfulBEq` (**checked**) | yes | **no** |

Two consequences worth stating:

- **The checked-law decision is Lean's model, not Rust's.** Rust's `Eq` is a *nominal* marker (you simply don't `impl Eq for f64`); Lean's `LawfulBEq` is a *proof obligation* an instance must discharge, which `Float` cannot — the stronger, more principled form. this proposal's conformance-checker discharging `eq_refl` is exactly that. Lean withholds `LawfulBEq Float` for **both** reflexivity *and* congruence failures (the `-0.0` case above).
- **But Anthill's `Eq` is Rust-shaped, not the full Lean `LawfulBEq`.** Lean's `LawfulBEq` ties `==` to the type's *logical* `=` (for `Finset`, set equality — so `LawfulBEq Finset` holds). Anthill's `===` is *structural* (`{1,2} !== {2,1}`), **not** per-type logical equality, so `Eq` must be defined by **equivalence laws** (reflexive / symmetric / transitive) — *not* "`eq` coincides with `===`". Otherwise `Set`/`Map`, whose semantic `eq` legitimately differs from structural `===`, would wrongly fail to be lawful. Reflexivity (this proposal's law) is the equivalence reading; that is the correct one here.

### What `Float` provides — and what it does not

```anthill
-- Float provides the PARTIAL specs, backed by IEEE, and declares NOTHING lawful.
provides PartialEq[T = Float]     -- eq = IEEE ==   (nan eq nan = false, -0.0 eq +0.0 = true)
provides PartialOrd[T = Float]    -- partialCompare = IEEE ; a NaN operand -> none (unordered)
-- NO  provides Eq[T = Float]     -- would fail to discharge eq_refl (nan) -> a load error, automatically
-- NO  provides Ord[T = Float]
```

Consumers pick the strength they actually need:

- `Map requires Eq[T = K]`, `Set requires Eq[T]`, dedup, sort keys, and the resolver's structural-`eq` shortcut keep requiring **`Eq`/`Ord`** → a raw `Float` key is a **load error** with a precise message, not a silent wrong answer.
- A clause / op that merely compares requires **`PartialEq`/`PartialOrd`** → `Float` works.

### Using `Float` where a lawful key is needed — `TotalFloat`

For the genuine "I want floats as `Map` keys / sorted / deduped" case, a wrapper carrier provides the *total* instances (the `ordered_float::OrderedFloat` pattern the interpreter already uses internally):

```anthill
sort anthill.prelude.TotalFloat            -- newtype over Float
  entity TotalFloat(raw: Float)
  provides Eq[T = TotalFloat]              -- total: all NaN equal, -0.0 == +0.0 (or distinct — a decided convention)
  provides Ord[T = TotalFloat]             -- NaN is the maximum (a total order)
  -- eq_refl / compare_refl DISCHARGE here: total equality IS reflexive.
end
```

So `Map[K = TotalFloat, V]` is legal; `Map[K = Float, V]` is a load error. The user names their intent.

### The soundness fix — gate the resolver's reflexivity shortcut

`sem_eq_core` (resolve.rs) shortcuts `if values_equal(a, b) { return true }` — i.e. *"structurally equal ⟹ semantically equal."* That is sound **iff** the carrier's `eq` refines structural equality — true for a reflexive `Eq` carrier, **false** for a `PartialEq`-only carrier (`Float`: two `NaN`s are structurally equal via `OrderedFloat` but IEEE-unequal). The fix:

> take the structural shortcut only when the operand's carrier provides **reflexive `Eq`** (or has a purely structural `eq`); for a `PartialEq`-only carrier, dispatch to the carrier's own `eq` (the IEEE builtin for `Float`).

The eval path (`builtin_eq`) is the same story: for a `Float` operand it must use IEEE `==`, not `views_structurally_equal`. `builtin_cmp` already extracts `value_num`; `eq`/`neq` need the analogous Float-numeric IEEE path, **falling back to structural for non-numeric carriers** so `Set`/`Map`/entity `eq` (WI-616 override dispatch) is unchanged.

Crucially, the **structural layer is untouched**: `===`/`struct_eq`, `views_structurally_equal`, and `Literal`'s `Hash`/`Eq` stay on `OrderedFloat` — hash-consing/dedup need a total `Hash`+`Eq` on `Literal`, and `nan === nan = true` is *correct* (structural identity, wanted for reflection/dedup). Only the *semantic* `PartialEq`/`PartialOrd` builtins change.

### Codegen alignment (C++)

`anthill-cpp-gen` maps `Eq.eq -> ==`, `Ordered.gt -> >` (lib.rs:2889-2906). Under this proposal:

- **`PartialEq.eq` / `PartialOrd.*` → C++ `==` / `<` (IEEE)** — the *current* mapping, now *correct*, because these are the partial specs.
- **`Eq` / `Ord` / `TotalFloat` → a total comparator** — a defaulted `operator==` / `operator<=>` on the generated struct (C++20 `= default`), or, for `TotalFloat`, a bit/`OrderedFloat`-style total compare. (This also closes the *separate* pre-existing gap that entity structs are emitted fields-only with no `operator==` — see WI-645 discussion.)

So interpreter and compiler agree on every Float comparison, which is the WI-645 acceptance.

### Relationship to `===` (unchanged)

`===`/`struct_eq` stays the total, carrier-agnostic **structural identity** test (051): needs no instance, `nan === nan = true`, `-0.0 === +0.0` is bit/`OrderedFloat`-structural. The three notions are now cleanly separated and independently selectable:

| want | operator / requirement |
|---|---|
| literal same structure | `===` (`struct_eq`) — no instance |
| partial value equality (may be non-reflexive) | `eq` / `requires PartialEq[T]` |
| lawful (reflexive) equality | `requires Eq[T]` (Float excluded) |

### Selecting among the three notions (canonical instances)

The split gives three distinct symbols/obligations — `===` (structural), `PartialEq.eq` (partial), and the `Eq` requirement (lawful) — and a module selects which by what it `import`s and what it `requires`; no context silently gets IEEE where it wanted lawful, or vice-versa. Each is a **single, globally-coherent** instance per `(spec, carrier)` (Anthill enforces this today — `load.rs` rejects an "ambiguous witness", two providers for one `(spec, carrier)`). That is all this proposal needs for the `Float` problem.

**Out of scope — modular typeclasses.** Supplying a *non-canonical, per-use* instance — the standing example being a `SortedSet` / `Map` ordered by a *chosen* comparator rather than the carrier's default `Ord` (Scala's `SortedSet(...)(Ordering)`, Haskell's newtype-per-order) — requires relaxing global coherence to a **scoped/named instance** mechanism. That is a separate, larger feature and is **tracked as its own issue (linked with `SortedSet`)**, not resolved here. this proposal is deliberately built on canonical instances so it neither needs nor forecloses it: a later modular-typeclass mechanism supplies an alternate `Ord`/`Eq` witness at a use site without changing this hierarchy.

## Migration — an intent audit, not a rename

The mechanical part is large but shallow, and mirrors 051's `===` migration:

1. **Rename the base + add the marker.** `eq`/`neq` and `neq<=>not(eq)` move to a new `sort anthill.prelude.PartialEq`; `sort anthill.prelude.Eq` becomes `requires PartialEq[T]` + `eq_refl`. Re-register the builtins (`anthill.prelude.PartialEq.eq -> SemEq`, `.neq -> SemNeq`); keep `Eq.eq` resolving to the inherited `PartialEq.eq` via the requires-chain (WI-614 dispatch) so most call sites are source-compatible.
2. **`Ordered -> Ord`; add `PartialOrd`.** `compare`/laws stay on `Ord` (`requires Eq, PartialOrd`); the `gt/lt/gte/lte` surface + numeric-builtin registration move to `PartialOrd` (they answer `false` on `none`).
3. **Audit `requires Eq` / `requires Ordered` sites** (stdlib + tests): the reflexivity-dependent ones — `Set`, `Map` keys, dedup, sort — stay `requires Eq` / `requires Ord`; comparison-only ones weaken to `requires PartialEq` / `requires PartialOrd`. This is the judgement part; most stdlib sites are key/dedup (stay `Eq`).
4. **`Float`**: `provides PartialEq`/`PartialOrd` (IEEE); drop any `provides Eq`. Add `TotalFloat`.
5. **Resolver + codegen** per §above.

## Build order

1. **Specs + laws (stdlib) + conformance** — introduce `PartialEq`/`PartialOrd`, add `eq_refl`, re-parent `Eq`/`Ord`; confirm the conformance checker rejects a synthetic non-reflexive `provides Eq`. *Lands first, independent of the resolver fix; a decision-free restructuring.*
2. **Resolver soundness fix** — gate the `sem_eq_core` reflexivity shortcut + eval `builtin_eq` IEEE-for-Float path; un-ignore `wi645_float_nan_ieee_test.rs`. Delivers the WI-645 acceptance (interpreter == codegen on Float NaN).
3. **`Float` restructuring + `TotalFloat`** — `provides PartialEq/PartialOrd`, drop `Eq`; add `TotalFloat` with the total instances; migrate `Map`/`Set` key examples/tests.
4. **Codegen** — `Eq`/`Ord`/`TotalFloat` emit a total `operator==`/`<=>` (and the `= default` for entity structs); `PartialEq`/`PartialOrd` keep `==`/`<`.
5. **Docs** — `kernel-language.md` §equality: the three-notion table + the partial/total split; sync 051.

## Relationship to neighbouring work

- **051** delivered structural-vs-semantic; this proposal is its total-vs-partial continuation and is the **resolution of WI-644** (whose "drop the universal structural default" framing evolved into this split — structural is the default *only for the reflexive `Eq` layer*, and `Float` opts down to `PartialEq`; WI-644 is the implementation driver).
- **WI-645** is closed by build-step 2 (direction B); the interim direction A (make Float `eq` IEEE without the spec split) is unnecessary if this proposal lands, since the spec split is what *justifies* the IEEE answer.
- **WI-616** semantic-`eq` dispatch is reused unchanged — the carrier-override path (`Set.eq`/`Map.eq`) now lives under `PartialEq` and its consumers under `Eq`.
- **WI-642**'s `is_builtin` exclusion can then be revisited: once `PartialEq.eq`/`PartialOrd.*` are the honest partial ops (still builtin-backed, still no *missing*-instance failure mode), the exclusion stays correct — the static check gains teeth only for *lawful* `requires Eq`/`Ord` sites, which is exactly right.

## Non-goals

- **Modular typeclasses** — per-use *named/scoped* instances (the `SortedSet`-with-a-chosen-`Ord` case). Its own issue, linked with `SortedSet`; this proposal stays on canonical instances and neither needs nor forecloses it (see §"Selecting among the three notions").
- **`TotalFloat`'s `-0.0` convention** — that IEEE `==` is non-congruent on `-0.0`/`+0.0` is *in* scope (a stated reason `Float` is not lawful, §Motivation); what remains out of scope is only which convention `TotalFloat` picks for `-0.0` (IEEE-merge vs `OrderedFloat`-distinct) — an implementation choice, documented when it lands.
- Symmetry / transitivity **laws** beyond reflexivity — additive later; reflexivity is the one the `Float` split turns on.
- The **SLD→eval bridge** (WI-625) — this proposal's fix is in the raw interpreter/resolver builtins and does not need it.

## Open questions

1. **`TotalFloat` surface:** newtype `entity TotalFloat(raw: Float)` (explicit `.raw`) vs a carrier-bound host `struct` — the latter codegens to `OrderedFloat<f64>` directly. Default: newtype, revisit for codegen ergonomics.
2. **Reflexivity-shortcut gate cost:** deciding "does this carrier provide reflexive `Eq`" per `eq` firing must not re-scan providers per goal — cache the reflexive-carrier set (mirrors the WI-595 `sort_provides` cache decision; measure first).
