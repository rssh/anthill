# 053: Per-Functor Fact Monotonicity

## Status: Draft

## Tracks: WI-665 (the Rust KB cache follow-on — a separate implementation matter, §"Out of scope")

## Relates to: 007 (persistence — the store that owns a functor gives its monotonicity; extends the per-functor binding of §6/§7), 036 (domain store — describes its functors' monotonicity; capability bounds and propagates down the backend stack), 037 (Modify framework — retraction is that effect on the KB), 038 (builtin sorts). Kernel spec §7 (Metadata), §8.3 (Rule Evaluation), reflect operations.

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
  sort Monotonicity {
    entity constant       -- neither asserted nor retracted at runtime
    entity monotone       -- asserted, never retracted (default)
    entity non_monotone   -- asserted and retracted
  }
  operation fact_monotonicity(functor: Symbol) -> Monotonicity
end
```

- **The in-memory default store** is the KB itself; its values are given by rule, like 007's `caps`:

  ```anthill
  rule fact_monotonicity(WorkItem) = non_monotone   -- retracted / updated
  rule fact_monotonicity(?)        = monotone       -- default: append-only
  ```

  `AuditEntry`, `OperationInfo`, and every unlisted functor fall to the default `monotone`. An ordinary reflect rule (reflect already has `sort Symbol`), so **no new syntax**.

- **An external store** gives the same value in its **per-functor binding**, which 007 already has: §7's `QueryBinding(sort_pattern, table, columns, …)` per SQL functor, §6's convention per file functor. Add a `monotonicity` field: a deletable work-item table is `non_monotone`, an append-only audit table `monotone`, a materialized view `constant`. Here monotonicity is a genuine **storage property** — how that store manages the functor.

## A store's capability bounds the value

A store's **write capability** — what it can `persist`/`retract` (007 §4) — is an upper bound: `non_monotone` needs a retract-capable store, `monotone` a persist-capable one, `constant` neither. So `monotonicity ≤ capability`, and a value exceeding it (a `non_monotone` functor on an append-only sink) is the loud inconsistency to reject.

Capability propagates **down a store's backend stack** (036): a `WorkItemStore` delegating to an `IndexedFileStore` inherits the backend's capability, as 037's `Modify[s]` reaches `s.backend`. That is propagation through one store's layers — distinct from the store↔its-many-functors relation. The **in-memory default store** has full capability, so it bounds nothing: its functors are `monotone` by default, or `non_monotone` where a rule says so.

## Enforcement: retract is the only guard

- **`retract` of a functor whose monotonicity is not `non_monotone` → loud error.** This is the sole guard — the non-monotone step that desynchronizes re-derived structure from the program and falsifies caches over it.
- **`assert` of a `constant` functor → loud error.** Otherwise `assert` is permitted (the `monotone` default).

Static where the functor and its store are known at load (a LoadError); dynamic otherwise (the `Error` effect, 037 §"With Error").

## Out of scope

- **Cache coherence.** `monotone` → the cache extends on assert; `non_monotone` → it invalidates on retract; `constant` → build-once. Because the only guarded operation is retract, `non_monotone` marks exactly the cache-dangerous functors — but *which* indexes rebuild and *when* is Rust runtime engineering (WI-665), not this proposal.
- **Any grammar change.** The in-memory value is a reflect rule; the external one a field on the existing binding; the guard is runtime behavior. No `mutable sort` keyword, no `immutable` field syntax.

## Open decisions

1. **`constant` in-memory.** Whether a functor can be `constant` (no append) *in memory*, or whether `constant` only ever arises from a read-only external store. *Recommendation: store-bounded — nothing in the in-memory KB needs to forbid a monotone add, so in memory a functor is `monotone` (default) or `non_monotone`.*
2. **Description forms.** Keep the in-memory reflect rule *and* the external binding field, or unify behind one per-(store, functor) predicate. *Recommendation: keep both — the in-memory KB has no binding to hang a field on; an external store's binding is where its schema already lives.*

## Acceptance

1. `anthill.reflect.fact_monotonicity(functor: Symbol) -> Monotonicity` over `{constant, monotone, non_monotone}`, default `monotone`, one value per functor — given by the owning store (in-memory reflect rule; external binding field).
2. `retract` of a functor that is not `non_monotone` is a loud error (the sole guard); `assert` is refused only for `constant`.
3. A store's write capability bounds the value (`monotonicity ≤ capability`) and propagates down the store's backend stack (036).
4. Cache coherence stays an implementation matter (WI-665); no grammar change.
