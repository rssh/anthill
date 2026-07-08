# 053: Per-Functor Fact Monotonicity

## Status: Implemented — Phases A+B (WI-666) + the external-store side (WI-667), on main. The one deferred piece, cache coherence, is explicitly out of scope (§"Out of scope" → WI-665).

## Tracks: WI-666 (reflect substrate + runtime guard, DELIVERED), WI-667 (external-store side — `retract` is a `NonMonotonicStore`-trait op; `Store.monotonicity` is the policy query; the owning store's materialized policy is the `fact_monotonicity` fallback — DELIVERED), WI-665 (the Rust KB cache follow-on — a separate implementation matter, §"Out of scope")

## Relates to: 007 (persistence — the store owns a functor and answers its monotonicity via `Store.monotonicity`; §2 defines the trait/policy capability model), 036 (domain store — the owning store provides its functors' monotonicity via its API), 037 (Modify framework — retraction is that effect on the KB), 038 (builtin sorts). Kernel spec §7 (Metadata), §8.3 (Rule Evaluation), reflect operations.

## Problem

We have a knowledge base, and facts in it. Both the default **in-memory** store and any **external** store hold **many functors of mixed policy**:

- an in-memory KB carries append-only reflection (`OperationInfo`, `SortProvidesInfo`) beside retractable domain data (`WorkItem`);
- 007 §8's one `FileStore` owns `WorkItem`, `Project`, `Feedback`, and `ToolDef` together;
- a single `SqlStore` owns `AuditEntry` and `Metric`.

So the policy is neither global nor store-level — it is **per functor**. And since a functor is owned by exactly one store (007's 1-to-1 routing), the natural home for the description is **that store**.

## Adding is not mutation; retracting is

`assert` (add a fact) is **monotone** — the KB only grows; it is the natural operation of a knowledge base. `retract` (remove) is **non-monotone** — the destructive one, which falsifies prior conclusions and anything cached over them. So each functor's fact-set has one of three **monotonicities**:

| monotonicity | assert | retract | meaning |
|---|---|---|---|
| **constant** | ✗ | ✗ | fixed — frozen after load (e.g. a read-only view) |
| **monotone** | ✓ | ✗ | append-only — grows, never shrinks (**the default**) |
| **non_monotone** | ✓ | ✓ | mutable — grows and shrinks (retract / update) |

Each functor has **exactly one**. There is no "appendable *and* mutable" overlap to puzzle over: a `non_monotone` functor may of course be appended to, but that is what the single value `non_monotone` *permits*, not a second classification. The value is one point on the ladder, not a set of flags.

## Proposal: one per-functor value, `fact_monotonicity`

The store that owns a functor (007 routing) gives its monotonicity — a **single value**, defaulting to `monotone`:

```anthill
namespace anthill.reflect
  enum Monotonicity {
    entity constant       -- neither asserted nor retracted at runtime
    entity monotone       -- asserted, never retracted (default)
    entity non_monotone   -- asserted and retracted
  }
  operation fact_monotonicity(functor: Symbol) -> Monotonicity
end
```

- **The in-memory default store** is the KB itself; its values are given by reflect rule:

  ```anthill
  rule fact_monotonicity(WorkItem) = non_monotone() [simp]   -- retracted / updated
  ```

  `AuditEntry`, `OperationInfo`, and every unlisted functor fall to the default `monotone`. Two points the WI-666 implementation pinned down: the `[simp]` tag is **required** (an untagged equational rule loads inert) and a nullary RHS needs parens (`non_monotone()`); and there is deliberately **no** catch-all `fact_monotonicity(?) = monotone` rule — under the current load-order simp firing (most-specific-first is deferred, 043 §4.6) it would load first and **mask every specific override**, so the `monotone` default is supplied by the runtime guard's "no rule fired" branch instead. An ordinary reflect rule (reflect already has `sort Symbol`), so **no new syntax**.

- **An external store** provides the same value through its **`Store.monotonicity(store, functor)`** operation (007 §2) — store-specific logic, the natural counterpart of the in-memory rule. The owning store (007 routing) answers for the functors it owns; a deletable work-item table is `non_monotone`, an append-only audit table `monotone`, a materialized view `constant`. Monotonicity is a genuine **storage property** — how that store manages the functor — but *decided by the store's logic*, not a static binding field. Whether the store's answer is materialized into the reflect predicate at registration or routed live per query is an implementation choice (WI-667).

## The owning store is the single authority

An earlier draft bounded the value by a store's *write capability* (`monotonicity ≤ capability` — reject a `non_monotone` functor on an append-only sink at load). **That is dropped** (007 §2 recasts capability as traits for provision + monotonicity for policy). Write policy is store-dependent logic that no fixed capability lattice captures — a SQL store retracts a table but not a materialized view, gated by grants; an API store deletes some resource types and refuses others — so a separate capability would be a second source of truth that either duplicates the monotonicity or lies about a dynamic reality. The owning store is the **single authority**: it *provides* the per-functor monotonicity (by reflect rule in memory, by its API externally), and that answer is definitive. The in-memory default store answers `monotone` by default, `non_monotone` where a rule says so.

The one real residual failure — a functor *declared* `non_monotone` whose backend cannot actually retract it — is **not** a static load check. It surfaces **loudly at the write**, via the store's own `retract` raising the `Error` effect (037), where the store-specific logic lives.

## Enforcement: retract is the only guard

- **`retract` of a functor whose monotonicity is not `non_monotone` → loud error.** This is the sole guard — the non-monotone step that desynchronizes re-derived structure from the program and falsifies caches over it.
- **`assert` of a `constant` functor → loud error.** Otherwise `assert` is permitted (the `monotone` default).

WI-666 implements this as a **runtime** guard — in the eval `Store.persist` / `Store.retract` builtins, surfaced via the `Error` effect (037 §"With Error"). Those builtins run at eval only, never during a load phase, so the guard cannot trip the loader establishing facts. (A static load-time `LoadError` variant, where the functor and its store are known at load, is a possible refinement — not implemented.)

## Out of scope

- **Cache coherence.** `monotone` → the cache extends on assert; `non_monotone` → it invalidates on retract; `constant` → build-once. Because the only guarded operation is retract, `non_monotone` marks exactly the cache-dangerous functors — but *which* indexes rebuild and *when* is Rust runtime engineering (WI-665), not this proposal.
- **Any grammar change.** The in-memory value is a reflect rule; the external one a field on the existing binding; the guard is runtime behavior. No `mutable sort` keyword, no `immutable` field syntax.

## Open decisions

1. **`constant` in-memory.** Whether a functor can be `constant` (no append) *in memory*, or whether `constant` only ever arises from a read-only external store. *Recommendation: store-bounded — nothing in the in-memory KB needs to forbid a monotone add, so in memory a functor is `monotone` (default) or `non_monotone`.*
2. **Description forms.** ~~Keep the in-memory reflect rule *and* the external binding field~~ — **RESOLVED**: the in-memory KB answers by reflect rule; an external store answers via its **`Store.monotonicity`** operation (store-specific logic), *not* a static binding field, because write policy doesn't reduce to a declared field (007 §2). Both surface as the one `fact_monotonicity(functor)` predicate — the single authority is always the owning store.

## Acceptance

1. `anthill.reflect.fact_monotonicity(functor: Symbol) -> Monotonicity` over `{constant, monotone, non_monotone}`, default `monotone`, one value per functor — given by the owning store (in-memory reflect rule; external store's API). *(A: WI-666.)*
2. `retract` of a functor that is not `non_monotone` is a loud error (the sole guard); `assert` is refused only for `constant`. *(B: WI-666, delivered.)*
3. Write policy is per-predicate and store-provided (`Store.monotonicity`, 007 §2) — **no** store-level capability bound; `retract` is a `NonMonotonicStore`-trait op, so an append-only store lacks it structurally, and a backend that cannot honor a declared `non_monotone` retract fails loudly at the write via the `Error` effect (037), not a static load check. *(WI-667.)*
4. Cache coherence stays an implementation matter (WI-665); no grammar change.
