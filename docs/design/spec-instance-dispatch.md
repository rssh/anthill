# Spec/impl call-site dispatch via fact

## Status: Draft (WI-210)

## Tracks: WI-203 phase 3 (bundle commands routing through `WorkItemStore.commit` etc.), proposal 036 (Domain Store Sorts) §"What the surface looks like"

## Relates to: WI-209 (parametric effect substitution at call sites — landed), WI-211 (sort-level type-param instantiation — landed; this WI builds on it), WI-186 (free-standing parametric ops — same shape, no fact indirection), WI-079 (typing-pass parity), proposal 027 (effect handlers — alternative architecture for the same problem), WI-119 (provides-discharge brainstorm).

## Problem

### The setting

Anthill supports a spec/impl split for interface-style programming (proposal 036, "Domain Store Sorts"). The interface is one sort; each implementation is another sort that carries the operation bodies. The two are tied together by a fact.

We use a concrete running example throughout this document: the work-item store in `anthill-todo/store.anthill`. The interface is `WorkItemStore`; the file-backed implementation is `FileBasedWorkitemStore`. The interface declares operations like `commit`, `lookup`, `next_id`; the implementation supplies their bodies plus a value-shape (`enum WIS`) for the interface's abstract `State` parameter.

### How spec and impl look in source

- **Spec** — declares operations + their signatures, with one or more abstract type parameters (e.g. `sort State = ?`). No operation bodies.
- **Impl** — picks a concrete value-shape for the spec's parameters via `fact Spec[State = T]`, and supplies operation bodies.

```anthill
-- Spec
sort WorkItemStore
  sort State = ?
  operation commit(s: Cell[V = State], w: WorkItem) -> Unit
    effects {Modify[s], Error}    -- declaration only, no body
  operation lookup(s: Cell[V = State], id: String) -> Option[T = Term]
end

-- Impl
sort FileBasedWorkitemStore
  enum WIS
    entity wis(backend: IndexedFileStore, id_counter: Int)
  end
  fact WorkItemStore[State = WIS]   -- "I implement WorkItemStore with State = WIS"
  operation commit(s, w) =          -- with body
    match Cell.get(s)
      case wis(b, c) -> let _ = persist(b, w, ...) ...
end
```

So in source there are now **two** definitions of `commit`: the spec's declaration (no body, abstract `State`) and the impl's body (concrete `WIS`).

### What goes wrong at the call site

A caller in another file (e.g. `main.anthill`) writes the natural thing:

```anthill
operation cmd_add(s: Cell[V = WIS], w: WorkItem) -> Unit
  effects {Modify[s], Error}
=
  commit(s, w)             -- which `commit` does this resolve to?
```

The user wants to think of `commit` as just "the commit operation on a workitem store" — they shouldn't have to know whether it's file-backed or GitHub-backed at the call site. But the typer sees two candidate symbols, neither of which can be picked naively:

- The **spec's** `commit` is the canonical *name* (the abstraction the user is programming against), but has **no body** — calling it directly would have nothing to run.
- The **impl's** `commit` has the body, but referring to it directly (`FileBasedWorkitemStore.commit(s, w)`) defeats the spec/impl split — every call site would hard-code an impl.

### What the typer needs to do

When the typer sees `commit(s, w)`, it must:

1. Recognize that `commit` names a spec operation.
2. Look at the actual arg types (`s : Cell[V = WIS]`) to figure out the State binding (`State = WIS`).
3. Find the fact `WorkItemStore[State = WIS]` in the KB.
4. Identify the sort that asserted that fact — `FileBasedWorkitemStore`.
5. Resolve `commit` *inside that sort* — the impl's body.
6. Rewrite the call to target that impl body.

This document calls that rule **"dispatch via fact"**. The rest of the document picks the simplest viable mechanism for the v1 (single-impl) world, and flags what changes when multi-impl scenarios arrive.

## Goal

Make `commit(s, w)` (and similar spec-op calls) dispatch from the spec to the right impl body, found via the chain:

> arg's static type → State binding → matching `fact Spec[State = T]` → impl sort that asserted the fact → impl op of the same name.

Today the typer leaves spec ops unresolved at call sites — there are multiple `commit` symbols (the spec's, each impl's), and name resolution either errors `AmbiguousSymbol` or picks one arbitrarily. Bundle phase 3 (rewriting `cmd_add` etc. to use spec ops) can't proceed until this lands.

## The shapes a call site can take

```anthill
operation cmd_add(s: Cell[V = WIS], a: AddArgs) -> Int =
  let id = next_id(s)              -- shape A: bare spec name
  let _  = WorkItemStore.commit(s, w)   -- shape B: qualified spec name
  let _  = FileBasedWorkitemStore.commit(s, w)  -- shape C: qualified impl name
```

Each has a different resolution story:

- **Shape A (bare)** — `commit` resolves through the operation's local scope chain. Inside `FileBasedWorkitemStore.cmd_add`, the impl's own `commit` is in scope — name resolution finds it directly without involving facts. *Trivial* if the impl has the op.

- **Shape B (qualified spec)** — `WorkItemStore.commit` names the spec's operation. The spec's `commit` has no body (it's the abstract declaration). The typer/resolver must rewrite the call to the impl's `commit` via `fact WorkItemStore[State = WIS]`. *This is the non-trivial dispatch case.*

- **Shape C (qualified impl)** — `FileBasedWorkitemStore.commit` names the impl directly. Resolves to that body. No dispatch mechanism needed. Works today if the call site can name the impl — but that requires the caller to know the concrete impl, defeating polymorphism.

The interesting question is **shape B** (and the implicit form of A from outside the impl, e.g. main.anthill calling `commit(s, w)` where it's not in scope).

> **Note: `WorkItemStore.commit(s, w)` is a qualified-name call, not method-call syntax.** Anthill's `.` is strictly field access (`docs/kernel-language.md` §6.7), not universal call syntax (UFCS). The grammar's disambiguator is the trailing `(...)`: `A.B(x)` parses as `fn_term(name: "A.B", args: [x])`, while `A.B` alone parses as `field_access(A, B)`. So `state.commit(w)` does **not** mean `commit(state, w)` — it would try to read a `commit` field on `state`'s sort, which is ill-formed for `Cell[V = WIS]`. Adding UFCS-style method dispatch (`x.f(y)` ≡ `f(x, y)` when there's no field `f`) is a separate language extension and out of scope here.

## Two related but distinct sub-problems

Worth separating these — they have different difficulty.

### Sub-problem 1: name resolution

When the typer sees `commit(s, w)`, **which operation symbol does the call resolve to**? This is purely about symbol lookup — finding *a* commit. Today multiple symbols compete (spec's, impl's, future impls'); the resolver may report `AmbiguousSymbol`.

### Sub-problem 2: spec → impl forwarding

Given the resolution lands on the spec's `commit` (which has no body), **how does the call actually run?** The resolver / runtime must follow the chain to find the impl's body and invoke it.

If the typer always resolves to the impl directly (sub-problem 1 with a "prefer impl" rule), sub-problem 2 evaporates — there's no spec→impl forwarding because the spec is never the target. But that requires the typer to know the State binding at resolution time, which requires the call's arg types.

The cleaner factoring:

- **Sub-problem 1**: at name resolution, the typer prefers the impl over the spec when:
  1. The call's arg types are known.
  2. The impl is uniquely determined by the State binding.
- **Sub-problem 2**: only fires when (1) holds and (2) doesn't yield a unique impl — i.e., the spec stays the resolution target, and we need runtime dispatch.

For a single-impl world (today's anthill-todo), **sub-problem 1 is sufficient.** WI-210 ships static dispatch; sub-problem 2 (dynamic dispatch / vtable) lands when multi-impl scenarios appear.

## Static dispatch (the proposed v1)

### Why look this up via a fact?

Two readings of "why a fact" — both deserve answers.

**Why use a KB fact at all (rather than a separate type-system table)?**

In Anthill, type-system data lives in the same KB as everything else — sort relations, instantiation bindings, satisfaction claims, even effect rows are *all* facts. There is no separate type registry. So "find the impl for this spec" reduces to "query the KB," and the natural shape of that query is `by_functor`. The index is built at load time and consulted at typer time — semantically static dispatch, despite being expressed via the same primitive that backs SLD resolution at runtime.

**Why `fact Spec[State = T]` specifically? It doesn't carry impl identity.**

Real gap. The bare fact `WorkItemStore[State = WIS]` records that *some* sort claims to satisfy `WorkItemStore` at `State = WIS`. It does not say which sort. The dispatch chain needs the asserting sort (`FileBasedWorkitemStore`) so it can resolve `commit` inside it.

Two ways to close the gap:

- **(a) Track the fact owner at load time.** When the loader loads `fact Spec[State = T]` *inside* `sort Impl { ... }`, the loader's `current_scope` is the impl sort. Add an internal index `fact_owner_sort: HashMap<RuleId, Symbol>` recording the impl. Dispatch: `by_functor(Spec)` → match bindings → `fact_owner_sort[rid]` → impl symbol.

- **(b) Auto-emit a tagged reflect entity.** When the loader sees the fact in an impl-sort body, emit a synthetic fact alongside it:

  ```anthill
  fact SpecImpl(
    spec     = WorkItemStore,
    impl     = FileBasedWorkitemStore,
    bindings = [(State, WIS)]
  )
  ```

  Dispatch queries `SpecImpl` directly: `by_functor(SpecImpl-sym)` filtered by `spec` and `bindings` → `impl`. The `SpecImpl` entity is also queryable from user code, codegen, and tools — it becomes the canonical "X realizes Y" predicate at the in-anthill level.

(Note: do not conflate with `Implementation` in `stdlib/anthill/realization/realization.anthill`. That entity binds anthill sorts to Rust/Scala/C++ host artifacts — a different concern. We need a separate, in-anthill `SpecImpl` reflect entity.)

**Recommendation: (b).** It costs one new reflect entity (~10 lines in `stdlib/anthill/reflect/`) plus loader auto-emission (~20 lines in `load_fact` when `current_scope` is a sort and the fact's functor names a spec sort). The win is a single source of truth for spec/impl mapping that everything downstream (typer dispatch, future codegen for `<impl>.<op>` thunks, persistence-side validation, doc tooling) can consume uniformly.

(a) is acceptable as a stop-gap if we don't want the new reflect entity for v1, but the side-channel index then has to be re-derived by every consumer. The implementation cost difference is small; (b) wins on architecture.

### The dispatch algorithm

At each call site `f(arg, …)` where `f` resolves (or could resolve) to a spec operation:

1. Type-check the arguments.
2. From the arg types, infer the spec's State binding(s). For the WorkItemStore case: `s : Cell[V = ?T]` → `?T` resolves via WI-211's machinery to the State binding.
3. Search KB for `SpecImpl(spec = Spec, bindings = [...])` facts (using `by_functor` on `SpecImpl`'s symbol). Filter by spec, then unify the recorded `bindings` against the inferred State binding.
4. If exactly one matching impl is found: rewrite the call's resolved symbol to that impl's operation symbol (`<impl>.f`).
5. If zero impls match: typer error ("no impl of `Spec.f` for `State = <T>`").
6. If multiple impls match: see "Coherence" below.

Step 3 reuses the existing `by_functor` index, keyed by the `SpecImpl` symbol — a single load-time index lookup, no SLD search loop. Step 4 is a textual rewrite at the typer's resolved-call layer (similar to how typeclass methods resolve in Rust trait dispatch).

This makes the dispatch a **typer pass**, not a runtime mechanism. The runtime sees a direct call to the impl's symbol — same path as any other function call.

## Dynamic dispatch (deferred)

Multi-impl scenarios — the same Spec satisfied by different impls keyed by something other than the State type — would need runtime dispatch. Examples:
- Two impls with the same State binding distinguished by a runtime predicate (e.g., "GitHub if env var set, file otherwise").
- A polymorphic op that takes `Cell[V = ?S]` where ?S is itself a parameter.

Anthill's runtime is interpreter-based, so the natural dynamic-dispatch shape is: store the spec→impl forwarding as a runtime-queryable fact, look it up at call time. This is essentially how proposal 027's effect handlers work for resources (KB / Store / Cell) — handlers are runtime-registered, dispatched per call.

For WI-210 v1: defer. File a follow-up if a real consumer surfaces.

## Coherence

What if two sorts assert `fact WorkItemStore[State = WIS]` (same Spec, same State binding)?

Three options, in increasing strictness:

| | What it does | Tradeoff |
|---|---|---|
| **A. Last-wins** | The most recently asserted fact's impl is picked. | Order-dependent; fragile across module loads. |
| **B. Scoped priority** | Local (project-side) impls override stdlib impls. | Lets users specialize; needs scope walk. |
| **C. Reject as ambiguous** | Typer error: "two impls for `WorkItemStore[State = WIS]`". | Forces explicit qualification; no surprises. |

(C) is what Haskell does (incoherent instances are an error). (B) is more flexible; Rust's orphan rules approximate it. (A) is the cheapest implementation but has order-of-load surprises.

Proposal: **(C) for v1.** The user can use shape C (qualified impl) to disambiguate. Add (B) when a real consumer needs to override.

## Coherence with WI-186 (free-standing parametric ops)

WI-186 handles polymorphic free-standing ops:

```anthill
operation id<T>(x: T) -> T = x
```

Resolution at `id(42)`: `T` instantiates to `Int` per arg-type unification. No fact lookup — `id` is the unique op named that. Compare to spec/impl:

```anthill
sort WorkItemStore { sort State = ?  operation commit(s: Cell[V = State], w: WorkItem) }
sort FileBasedWorkitemStore { fact WorkItemStore[State = WIS]  operation commit(s, w) = ... }
```

Resolution at `commit(s, w)` where `s : Cell[V = WIS]`:

- WI-186 alone would treat `commit` as needing a single source of truth, fail to find one, error.
- WI-210 adds the indirection: the spec's `commit` is *the* name; the fact tells the resolver *where to forward to*.

The instantiation step is the same (WI-211 binds State → WIS); the dispatch step is new.

The two systems can share: **a "polymorphic operation registry" that maps an operation symbol to its parameter-instantiation rules.** Whether a parameter is bound by direct unification (WI-186) or by fact-lookup (WI-210) is the only difference.

If the systems converge, the typer's call-resolution loop becomes:

1. Look up the op's instantiation rules.
2. For each parameter, run its resolution: direct unification, fact lookup, or both.
3. Bind, rewrite the call, type-check.

Out of scope to *unify* now, but worth flagging that the eventual structure may merge.

## Coherence with effect handlers (proposal 027)

Proposal 027 envisions effects like `Modify[s]` dispatched via runtime handlers — a per-effect-sort handler stack. KB / Store / Cell / WorkItemStore could each be effect resources with their own handlers.

In that world, `commit(s, w)` could be re-cast as an effect operation: the call raises a `WorkItemStore` effect; the runtime's handler stack picks the matching handler (identified by fact `WorkItemStore[State = WIS]`). This *is* dynamic dispatch.

Two ways the two designs interact:

- **Static-first**: WI-210 lands at typer time. Effect-handler dispatch (027) is the alternative for resources where dynamic swap is needed (test fixtures, time-travel, audit). Both coexist.
- **Effect-handler-first**: every spec op is a 027-style effect. The "fact" becomes a handler-registration record. Static dispatch optimizes the static-known case; dynamic is the default.

For WI-210 v1: keep them separate. Spec/impl ops resolve at typer time; the 027 framework is for explicit `Modify[c]` / `Branch` / `Error` style effects. We can converge later if the static path turns out too rigid.

## Worked example

```anthill
-- store.anthill (project-side)
sort WorkItemStore
  sort State = ?
  operation commit(s: Cell[V = State], w: WorkItem) -> Unit
    effects {Modify[s], Error}
  operation lookup(s: Cell[V = State], id: String) -> Option[T = Term]
end

sort FileBasedWorkitemStore
  enum WIS  entity wis(backend: IndexedFileStore, id_counter: Int)  end
  fact WorkItemStore[State = WIS]
  operation commit(s, w) = ...
  operation lookup(s, id) = ...
end

-- main.anthill (bundle-side)
operation cmd_add(args: AddArgs, s: Cell[V = WIS], agent: String) -> Int =
  let _ = commit(s, build_workitem(args))     -- ← shape A
  0
```

Resolution of `commit(s, build_workitem(args))`:

1. Bare name `commit` lookup. In `cmd_add`'s scope chain: WorkItemStore (via project-load), FileBasedWorkitemStore (via project-load). Both have `commit`. Resolver flags would-be-ambiguous.
2. **WI-210 step**: walk `commit`'s candidate symbols, find the one in the spec sort `WorkItemStore`. (Spec has no body; impl has body. Pick spec as the canonical name.)
3. Type-check args:
   - `s : Cell[V = WIS]` (from `cmd_add`'s param).
   - `build_workitem(args) : WorkItem` (from inference).
4. WI-211 binds State → WIS in the per-call subst.
5. **WI-210 step**: search `kb.by_functor(SpecImpl-sym)` for facts where `spec = WorkItemStore` and `bindings ⊇ [(State, WIS)]`. Find the auto-emitted `SpecImpl(spec=WorkItemStore, impl=FileBasedWorkitemStore, bindings=[(State, WIS)])`. Single match → impl is `FileBasedWorkitemStore`.
6. Rewrite the call's resolved symbol from `WorkItemStore.commit` to `FileBasedWorkitemStore.commit`.
7. Type-check the body call against `FileBasedWorkitemStore.commit`'s signature (which itself uses signature inheritance from the spec — see open question 1).

Result: the runtime sees a direct call to `FileBasedWorkitemStore.commit`. No vtable, no fact lookup at run time.

## Implementation plan (sketched)

1. **Define the `SpecImpl` reflect entity** (~10 lines, `stdlib/anthill/reflect/`):
   ```anthill
   entity SpecImpl(spec: Sort, impl: Sort, bindings: List[T = SortBinding])
   ```
   (Reuses existing `SortBinding` from the reflect layer.)

2. **Auto-emit SpecImpl in the loader** (~20 lines, `load.rs::load_fact`):
   When `current_scope` is a sort *and* the fact's functor names a sort that has at least one `sort <Param> = ?` declaration, emit a `SpecImpl(spec=<functor>, impl=<current_scope>, bindings=<fact's named args>)` fact alongside.

3. **Detect spec ops** (~30 lines, `kb/typing.rs`):
   A symbol is a "spec op" iff it's declared inside a sort that has at least one `sort <Param> = ?` declaration *and* the sort declares the op without a body. Helper:
   ```rust
   fn lookup_spec_op_dispatch(kb, op_sym) -> Option<DispatchSpec>
   ```
   Returning `(spec_sort_sym, state_param_names)`.

4. **Hook dispatch into `check_apply`** (~50 lines, `kb/typing.rs`):
   After arg unification (and WI-211's `unify_parameterized_with_sort_ref` populating the per-call subst):
   - Check if `fn_sym` is a spec op. If not, dispatch as before.
   - Read State's binding from the subst.
   - Search `by_functor(SpecImpl-sym)` facts; filter by `spec = spec_sort_sym` and unify recorded `bindings` against the inferred State.
   - If exactly one match: extract `impl` from the fact, look up `<impl>.<op-short-name>` symbol, rewrite the resolved call.
   - If zero/multiple: typer error per coherence rule (C).

3. **Tests**:
   - Direct: `commit(s, w)` where `s: Cell[V = WIS]` resolves to `FileBasedWorkitemStore.commit`.
   - Negative: same call where no `fact WorkItemStore[State = WIS]` exists — typer error.
   - Negative: two impls assert the fact — typer error (coherence rule C).

4. **Acceptance**: cargo-test green; bundle phase 3 prerequisites cleared (a smoke test where `commit(s, w)` from main.anthill dispatches to the right body).

## Open questions

### 1. Signature inheritance for impl ops

The impl's `commit(s, w) = ...` has no explicit signature; today's typer treats this as "impl is a fresh declaration." The spec's signature is the *contract*; the impl's signature should derive from it via substitution (State → WIS).

This was originally part of WI-209 ("signature inheritance"); split out as a follow-up. WI-210 doesn't strictly require it (the impl can write the explicit signature), but the surface gets verbose without inheritance:

```anthill
-- with inheritance:
operation commit(s, w) = ...

-- without:
operation commit(s: Cell[V = WIS], w: WorkItem) -> Unit
  effects {Modify[s], Error}
=
  ...
```

Open: should WI-210 also implement signature inheritance, or stay minimal and assume the impl writes full signatures? **Lean: assume full signatures for v1**, file inheritance as a follow-up. The bundle's store.anthill already writes full signatures; works today.

### 2. State inference from non-Cell carriers

The recipe assumes State appears in the spec's params via `Cell[V = State]`. What if the spec uses a different carrier?

```anthill
sort QueryableStore
  sort T = ?
  operation retrieve(store: Self, pattern: Term) -> Stream[T = T, E = Error]
end
```

Here `Self` (the implementing sort) plays State's role; `store: Self` is the dispatch key. Anthill doesn't have `Self` as a kernel concept, but parameterized sorts naturally express it: `IndexedFileStore` is a sort, and `fact QueryableStore[IndexedFileStore]` (no `State = …`) asserts the impl. Then `retrieve(store, ...)` where `store : IndexedFileStore` dispatches via the fact.

WI-210 should support both shapes:
- **Cell[V = State]** (data via cell wrapping).
- **bare Self-like impl sort** (resource directly typed).

The dispatch algorithm extracts the relevant bindings from the spec's first param's type — works for both.

### 3. Where does signature inheritance + dispatch live in the typer pipeline?

Today's `check_apply` does (a) arg type-check, (b) param unification, (c) effect substitution (WI-209), (d) deep walk_type for return resolution (WI-211). WI-210 inserts (e) spec→impl rewrite. Order matters:

- (b) builds subst including State binding.
- (e) reads subst, finds impl, rewrites.
- Re-do (a)-(d) against the impl's signature?

Cleanest: rewrite the resolved op at step (e), then redo (b)-(d) against the impl's actual signature. Costs a re-unify but keeps the architecture clean. Or: trust that the impl's signature is the spec's substituted form (signature inheritance), so (b)-(d) need not be re-run. **Lean: re-run for safety; cheap at typer time.**

### 4. Visibility — is `WorkItemStore.commit` callable from outside the impl sort?

Today's name resolution scopes ops to their declaring sort. From `cmd_add` inside `FileBasedWorkitemStore`, `commit` resolves to the impl's commit (already in scope). From `main.anthill` (different file, namespace `anthill.todo`), what's in scope?

- If `main.anthill` imports `WorkItemStore`, then `WorkItemStore.commit` is resolvable.
- The fact `WorkItemStore[State = WIS]` is in the KB regardless of imports.
- WI-210's dispatch fires regardless of which scope the call site is in.

No new visibility rules; existing import / scope mechanism handles it.

### 5. What about call sites that *want* the spec (don't want dispatch)?

E.g., generic code that takes a `Cell[V = ?S]` for any `?S`. The dispatch can't fire (no concrete State). Two stances:

- Reject the call until ?S is bound at a higher call site (call-site monomorphization).
- Defer dispatch to runtime (sub-problem 2 — dynamic dispatch).

For v1: reject. The bundle's commands all pin State to WIS via the cell handle they receive.

### 6. Recursion through dispatch

If `commit(s, w)` inside one impl calls another spec op (`forget(s, id2)`), the inner call also dispatches via the fact. If the resolution machinery is purely typer-time, this works (typer recurses through call type-checks). If it's dynamic, runtime recursion through dispatch lookup needs care for tail calls / TCO. v1 (static) sidesteps this.

### 7. Diagnostics

What does the error message look like?

```
error: no impl of WorkItemStore.commit for State = WIS
  --> main.anthill:204:11
   |
204 |     commit(s, build_workitem(args))
   |     ^^^^^^
   |
   = note: WorkItemStore.commit requires a `fact WorkItemStore[State = …]`
   = help: either declare an impl sort with `fact WorkItemStore[State = WIS]`,
           or call FileBasedWorkitemStore.commit directly if you intend to
           bypass dispatch.
```

Plus the dual: "ambiguous: WorkItemStore.commit has impls in {FileBasedWorkitemStore, GitHubBasedWorkitemStore}." Mention coherence rule (C).

## Acceptance

When WI-210 lands:

1. `commit(s, w)` from outside the impl sort dispatches to `FileBasedWorkitemStore.commit` when `s: Cell[V = WIS]` and `fact WorkItemStore[State = WIS]` exists.
2. Zero matching impls → typer error with diagnostic above.
3. Multiple matching impls → typer error per coherence rule (C).
4. WI-203's bundle commands (phase 3, separate WI) can use spec ops directly.
5. `cargo-test` green; new typing test asserts the dispatch resolution.

## Out of scope

- Dynamic dispatch (vtable / runtime fact lookup) — file as follow-up if needed.
- Convergence with proposal 027 effect handlers — separate proposal.
- Convergence with WI-186 free-standing parametrics — incremental opportunity, not a hard dependency.
- Signature inheritance for impl ops (per open question 1) — follow-up; WI-210 ships under explicit-signature assumption.
- Coherence rule (B) (scoped priority override) — start with (C); revisit when a consumer needs override.
- Self-typed specs (where the spec uses `Self` rather than `Cell[V = State]`) — handled in principle by extracting bindings from any param; not specifically tested in v1.

## Recommendation

Land WI-210 as **static dispatch + coherence rule (C) + explicit impl signatures**. Defer dynamic dispatch and signature inheritance as separate WIs. Bundle phase 3 unblocks immediately.
