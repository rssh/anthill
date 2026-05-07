# 037: Anthill State Model — Foundations

## Status: Draft

## Tracks: foundations for WI-192, WI-200, WI-201 (time-travel candidate)

## Relates to: 027 (effect handlers and standard effects), 030 (proof cache; KB epoch / state_hash), 007 (persistence layer), 035 (typed constructors), 036 (domain store sorts — concrete consumer of the state model)

## Why this proposal exists

The conversation around WI-192 (domain store sorts) surfaced a pattern: anthill has *multiple state mechanisms* with *inconsistent identity schemes* and *inconsistent effect-dispatch*. Each mechanism arose for a specific use case; together they form an ad-hoc zoo with surprising interactions:

| Mechanism | Identity scheme | Dispatch | Used for |
|---|---|---|---|
| `Modify` cell (default handler) | functor symbol | effect handler | user-level state via `set` / `get` |
| `store_registry` (Box\<dyn Store\>) | canonical-form String | direct Rust call | persistence — FileStore, IndexedFileStore |
| KB (`assert_fact` / `retract`) | RuleId (host-internal) | direct Rust call | KB facts (no declared effect today) |
| Map arena | arena handle (u32) | direct Rust call | Map values |
| Substitution arena | arena handle | direct Rust call | logical query results |
| Stream arena | arena handle | direct Rust call | LogicalStream |
| Source map (IndexedFileStore) | RuleId → (Path, Span) | direct internal | retract by source span |

Different keys, different dispatch paths, different lifecycles. Adding a sixth (WorkItemStore via Modify) without addressing the disorder lands one more sediment layer instead of fixing the formation.

This proposal does *not* propose unifying all five into one mechanism — that would be too invasive at this stage. Instead it:

1. **Names the current mechanisms** explicitly so designers know what exists.
2. **Identifies the dimensions** that distinguish them (identity, dispatch, lifecycle, multi-instance, time-travel).
3. **Sets the rules** for which mechanism a new piece of state should use.
4. **Specifies forward-compatible invariants** so a future unification (proposal 040? 050?) doesn't require breaking changes to user code that lands meanwhile.

## The dimensions

Every "stateful resource" in anthill answers these five questions:

### 1. Identity

How is one resource distinguished from another?
- **Functor symbol**: same type → same identity (Modify default handler). Single instance per type.
- **Canonical form**: type + field values. Multiple instances possible if fields are stable (FileStore: `(root, convention)` doesn't change).
- **Host-allocated handle**: opaque id allocated at construction (Map / Substitution / Stream arenas). Multi-instance natively.
- **External index**: RuleId for KB rules — assigned at assert time, host-internal.

### 2. Dispatch

How does a user-level operation reach the underlying state?
- **Effect handler**: user calls op → effect raised → handler intercepts → handler manipulates state.
- **Direct builtin call**: user calls op → Rust builtin runs → directly mutates host state. No handler in the loop.

Today's surface: Modify is handler-dispatched; everything else (KB ops, persistence, arenas) is direct. The asymmetry isn't justified — it's accidental, growing out of which mechanism landed first.

### 3. Lifecycle

When does the resource come into existence and when does it go away?
- **Process-lifetime**: Modify cells, KB, FileStore registry — born at startup, die at process exit.
- **Construction-bounded**: Map / Substitution / Stream — created by an op; refcount-managed; dropped when no references remain.
- **Lexically-scoped** (proposed but not implemented): handler stack pushed/popped at boundaries.

### 4. Multi-instance support

Can two distinct resources of the same type coexist?
- **Yes natively**: arena handles (Map, Substitution, Stream).
- **Yes by canonical form**: store_registry — different field combinations route to different store impls.
- **No**: Modify default handler — functor-keyed; single instance per type.
- **Sort of**: KB — there's normally one KB per Interpreter, but the design admits multi-KB scenarios with explicit kb-handle threading.

### 5. Mutation visibility under nondeterminism (Branch coexistence)

When a Branch backtracks, what happens to writes done in the abandoned branch?
- **Sticky** (`Modify.set`): persists. The next branch sees the prior branch's writes.
- **Transactional** (`Modify.set_local`): rolled back via `register_undo`. Each branch sees only its own writes.
- **Designed but unwired** for KB: `KB.assume` was supposed to be transactional; the runtime register_undo plumbing exists but isn't generalized to user effect handlers.
- **Direct-mutation paths bypass the question entirely**: KB.assert, FileStore.persist — no `register_undo`; mutations always persist. This means using these *inside* a Branch is unsafe (writes leak across alternatives).

## Inconsistencies to call out

### Note 1: KB is intentionally outside the Modify effect system

`KB.assert(kb, term, sort) -> Option[FactId]` has no `effects` clause. `KB.execute(...) -> Stream` declares `effects Error` only. This is **deliberate**, not an oversight: KB has its own API surface, parallel to Modify, with its own semantics:

- **KB is "large structured state."** Modify cells hold a single Value. KB holds rules, fact indexes, discrimination trees, type-parameter scopes. Forcing the whole KB through `set(kb, new_kb)` is impractical (the value would be the entire KB; copy-on-set defeats the purpose).
- **KB operations are richer than get/set.** `assert` validates against constraints at insert time, fires guard checks, updates indexes; `retract` deallocates references; `execute` runs SLD resolution. None of these reduce to the Modify operation set.
- **KB has its own transactional layer**: `KB.assume` (designed; partially implemented) gives transactional asserts via `RuntimeAPI.register_undo`. The KB's transactional semantics live alongside the Modify cell's `set_local`, not under it.
- **KB lifetime is the Interpreter's lifetime.** It's not a value passed around or replaced — it's the persistent substrate the interpreter operates on. Modify cells are user-level resources that live and die at the user's request.

So KB-API-outside-Modify is the design. The five-mechanism table at the top of this proposal lists KB as a separate channel — that's how it stays. Proposal 037 doesn't propose folding KB into Modify; the asymmetry is justified by KB's role as foundational substrate vs Modify's role as user-level cells.

What this proposal *does* require: documentation. The stdlib spec for KB ops should explicitly say "KB mutations are not Modify-tracked; they use the KB's own consistency model." Without that note, future readers may try to "fix" the missing `Modify[kb]` annotation, breaking the intentional separation.

### Inconsistency 1: Modify identity is functor-only; FileStore identity is canonical form

Two `wis(...)` instances collide; two `FileStore(root: a, ...)` and `FileStore(root: b, ...)` don't. Same conceptual operation ("modify a resource"), different identity schemes. WI-200 is about closing this gap.

### Inconsistency 2: Effect handlers vs direct calls

`Modify.set(target, v)` raises a Modify effect → handler dispatch → handler mutates the cell. `Store.persist(store, fact, meta)` directly calls a Rust builtin → builtin mutates the registry. Both are "modify a resource." Why the asymmetry?

The answer historically: arenas/registries grew first as Rust-internal machinery; the Modify effect-handler architecture came later (proposal 027). The Rust ops were never refactored to go through handlers.

Net consequence: handler-installed test substitutions (e.g., logging Modify, capturing-stdio Console) work for some resources and not others. A test wanting to "log every persist call" can't install a Store handler — it has to monkey-patch the registry.

### Inconsistency 3: register_undo is half-built

`RuntimeAPI.register_undo` exists for `KB.assume` (assertion that's automatically retracted on snapshot abandon) but isn't exposed to general user effect handlers. So `Modify.set_local` is designed but unimplementable without first generalizing the undo machinery.

## Rules for new state (foundations level)

Pending a future unification (deferred), we set these rules now to prevent further drift:

### Rule 1: Effect declarations are honest *for Modify-channel state*

If an operation mutates a Modify-channel resource (Modify cell, FileStore, future per-instance Modify), it MUST declare an `effects` clause naming the resource. `Store.persist` declares `Modify[store]`. A future `WorkItemStore.commit` declares `Modify[s]`. The annotation is the type-level contract; whether dispatch goes through a handler today or directly to a builtin is an implementation detail that can be aligned later without changing the annotations.

KB ops are *outside* the Modify channel by design (see Note 1) and don't follow this rule. Their consistency model is the KB's own (constraints at assert, guards, retract semantics). A future `KB.assume` / `KB.assume_local` distinction handles transactional KB mutation without grafting Modify onto it.

### Rule 2: Multi-instance state declares its identity

A sort that admits multiple instances of distinct state must declare which entity field(s) carry instance identity (per WI-200). The Modify handler uses `(functor, identity_value)` as the cell key. Sorts without an identity declaration get the today-behavior (functor-keyed; single instance per type).

This rule applies before WI-200 lands by *convention* (designate an `id` field for any multi-instance sort) and after WI-200 by *enforcement* (typer warns on multi-instance state without identity).

### Rule 3: Mutation under Branch is transactional unless explicitly sticky

`set_local` is the default for code inside Branch handlers; `set` is the explicit opt-out. Today the priority is reversed (sticky default; transactional opt-in) because `set_local` isn't wired. After WI-X-set-local-implementation lands, the default flips.

Direct-mutation paths (KB.assert, Store.persist) need either (a) a transactional variant (`KB.assume_local`, `Store.persist_local`) or (b) an explicit warning at type-check time when used inside Branch context. Today, neither exists; using KB.assert inside Branch is unsafe.

### Rule 4: Time-travel forward compatibility (the five invariants from 036)

Re-stated here for visibility:
1. `set(target, v)` — observable contract is "next get returns v." Handler implementation hidden.
2. `get(target)` returns the current head. Time-travel queries (`get_at`) are a separate effect.
3. Modify[s] surface doesn't expose handler-internal structure.
4. `set` returns `Unit`, not the prior value.
5. Sticky vs transactional encoded in the operation, not the handler.

These hold for any new state mechanism (Modify cell, future per-instance Modify, future time-travel handler).

### Rule 5: Operations that take a resource take it by handle, not by value

`commit(s: WorkItemStore, w: WorkItem)` — `s` is the handle/identity; the actual state behind it is consulted by the handler. Operations DON'T reconstruct the resource entity from its fields and re-pass; they pass the handle and let the handler resolve.

For multi-instance support (WI-200 option a), the entity's identity field IS the handle; the handler keys cells by it. For option b, `Value::Resource(uid)` is the handle directly. Either way, ops take handles.

This avoids a class of bug where two passes through the same code path with different "values of the same type" interfere by colliding in the cell store.

## Concrete decisions to make before WI-192 lands

1. **Multi-instance for WorkItemStore**: pick option a/b/c from WI-200 now (so WI-192 is forward-compatible) or accept the single-instance limitation and design WI-200 in parallel?

2. **set_local timeline**: implement now (so WI-192 can use it for the retract+persist atomic) or stay sticky-only (and document that retract+persist isn't atomic on Error)?

3. **Handler vs direct dispatch for the new state**: WI-192's Modify[s] should go through the handler (matching proposal 027). Should we also start the migration of FileStore.persist to handler dispatch? Probably no — separate concern. KB.assert stays direct (Note 1).

4. **Stdlib spec note for KB**: add an explicit "KB mutations are outside the Modify channel" note to reflect.anthill so future readers don't try to add `Modify[kb]` annotations. Small doc-only change but prevents drift.

These decisions are the foundations to settle before WI-192 implementation. Without them, WI-192 ships with implicit answers that may be wrong.

## What this proposal does NOT decide

- The unification of all five state mechanisms (out of scope; deferred).
- The exact syntax for identity-by-field / opaque-handle / handler-scope (defer to WI-200).
- The implementation of `set_local` (defer to its own WI).
- The KB-as-resource refactor (defer; just decide whether to declare the effect).

## Acceptance

This is a *design* proposal, not an implementation one. Acceptance is:
1. The four decisions above are answered (yes/no/with-rationale).
2. The rules in §"Rules for new state" are accepted as binding for future state designs.
3. Proposals 027, 035, 036, and any future state-related proposals reference 037's rules.

Once accepted, WI-192 implementation can proceed under these rules without re-litigating fundamentals.
