# The operation-call model

## Status: Decision (post-brainstorm)

## Tracks: WI-204 (port cmd_X), WI-218 (static-dispatch rewrite shipped — needs follow-up patch), WI-210 (spec/impl call-site dispatch)

## Brainstorm: see `operation-call-model-brainstorm.md` for the exploration. This doc is the resulting design only.

## Decision in one paragraph

An operation declared inside a sort with `requires X` (or whose signature uses the sort's open type-params) is implicitly a function over an X-resolution **environment**. We materialize the environment as **parameter insertion** (Scala `using` / Lean instance arg / GHC dictionary-passing): the typer adds an explicit env slot to apply / ho_apply / constructor / lambda IR forms; envs become first-class runtime values flowing through regular arg-passing; the eval gains a `frame.envs` field structurally parallel to `frame.locals`. No body cloning, no side-table dispatch, no instantiation-context threading.

## The IR

Four IR variants gain an env channel; the env-less forms become canonical aliases for `_within(..., envs=[])` and are eliminated after migration:

```
apply_within(fn, args, envs)
ho_apply_within(pred, args, envs)
constructor_within(name, args, envs)
lambda_within(params, body, captured_envs)
```

`envs` (or `captured_envs`) is a positional vector of resolved env values. Each value is a sort-tagged entity: `Value::Entity { functor: <impl_sort_name>, ... }`.

Body references to spec ops use indexed access: `env_at(i).foo(x)` — i is the position in the enclosing scope's env slot. Position is canonicalized at signature time (sorted by bound's qualified name, or declaration order).

## Compile-time representation

Every scope (sort or operation) carries:

```
(sort_id, substitution, Vec<resolved_requires>)
```

- `sort_id` — the enclosing sort.
- `substitution` — the type-arg bindings.
- `Vec<resolved_requires>` — for each `requires` bound, the resolved `(bound_spec, impl_sort)` pair plus the sub-substitution that pins it.

### Body walking is necessary

Bodies can contain qualified calls like `C.foo(x)` where C is a different sort with its own requires. When B's body calls `C.foo`, the call needs an env for whatever C requires. But C's requires aren't in B's syntactically-declared `Sort.requires` — they're discovered by walking B's body.

So body walking is necessary to discover the full env requirements implied by a sort's operations. Sort-level closure (over explicit `requires` declarations only) is insufficient — it can't surface env needs that come from qualified calls inside bodies.

### Op.required_envs computation

For each operation, `required_envs` has two contributions:

```
op.required_envs =
    direct:    {env_for(callee.spec_sort) | callee in body, callee is a spec op}
  ∪ transitive: ⋃ { other_op.required_envs | other_op in body, callee is in this sort or another }
```

Transitive includes calls to ops in the SAME sort (mutual recursion → fixed-point) AND calls to ops in OTHER sorts (qualified `C.foo` calls — pull in C.foo's required_envs).

This is real analysis. Two implementation choices:

- **Eager**: explicit pre-pass that walks per-sort call graphs, computes SCCs, runs fixed-point. Output: per-op `required_envs` map across all loaded sorts.
- **Demand-driven**: when typing a body's call, recursively type the callee's body first; memoize. Cycle detection for mutual recursion.

Either is valid. Lean's elaborator and GHC's constraint inference both do this (eagerly).

### Sort-level envs

Once per-op `required_envs` is computed, the sort-level full set is the union across the sort's ops. This must equal (or be a subset of) `Sort.requires` declared in source — if a body uses an env not in the declared `Sort.requires`, that's an error: "B's body calls C.foo which needs env_Z, but B doesn't declare `requires Z`."

The sort-level union ISN'T a separate analysis output — it's just the union of computed per-op values. The validity check is per-op (each op's required_envs ⊆ Sort.requires).

### Could we avoid body walk by inferring requires?

In principle yes: instead of declaring `Sort.requires` source-explicit and validating, we could let body walking *generate* the sort's requires. The user's sort declaration would be: list operations and bodies; the typer infers what envs the sort needs.

This is what Haskell GHC does for type-class methods (constraint inference). It's a possible future direction, but it makes the source less self-documenting (a user reading the sort declaration must walk all bodies to know what's required). For v0, keep `Sort.requires` source-explicit and validate via body walk.

### Runtime is unaffected

The envs slot of a frame is **already populated** by the caller before the body executes. The body never recomputes anything; it just indexes into `frame.envs[i]` via `env_at(i)`. All analysis is at compile time; runtime is pure lookup.

### Runtime is unaffected

The envs slot of a frame is **already populated** by the caller before the body executes. The body never aggregates; it just indexes into `frame.envs[i]` via `env_at(i)`. Aggregation is an analysis fact at compile time, not a runtime operation.

## CallKind classification

At typing time, every apply/lambda gets classified:

```rust
enum CallKind {
    Direct,                                  // qualified, fn = impl op
    EnvFullyPinned { impl_op: Sym },         // env resolved locally; rewrite at body site (today's WI-218)
    EnvOpen { spec_op: Sym, source: Source } // env not pinned; insert env-arg from caller's env scope
}

enum Source {
    OpenTypeParam { spec_param: VarId },     // per-call subst's value is a Var
    OpenBound { bound: SortRef, ... },       // reached via `requires` whose impl pick is outer
}
```

A call is **EnvOpen** iff *either* condition holds: open-T (per-call subst has a Var) OR open-bound (reached via `requires`). Both must trigger; the open-T check alone misses ground-via-requires (the WI-218 latent bug).

## Resolution

Instance synthesis is an SLD query over `SortProvidesInfo` facts. Conditional instances (`fact Spec[…] :- subgoals`) are clauses with bodies; resolution composes via existing SLD machinery. This is the Lean-style search-based synthesis, expressed in anthill's existing primitives.

Coherence at the outermost site: ambiguous `requires` resolution rejects at the instantiation that introduces the choice (per WI-210's coherence rules — priority table or reject-as-ambiguous).

## Runtime: frame and closure

```rust
struct Frame {
    expr: TermId,
    locals: SmallVec<[(Symbol, Value); 4]>,
    envs:   SmallVec<[Value; 2]>,
    awaiting: Option<AwaitState>,
    ...
}

struct Closure {
    body: TermId,
    params: SmallVec<[Symbol; 2]>,
    captured_locals: SmallVec<[(Symbol, Value); 2]>,
    captured_envs:   SmallVec<[Value; 1]>,
}
```

`envs` and `captured_envs` are structural fields parallel to `locals` / `captured_locals`. The eval treats them symmetrically:

- Direct invocation (`apply_within`): new frame's `envs` = the call's `envs` slot.
- Closure invocation (`ho_apply_within(closure, args, envs=[])`): new frame's `envs` = `closure.captured_envs`.
- Lambda construction (`lambda_within`): closure's `captured_envs` = enclosing frame's `envs[i]` indexed by the IR's `captured_envs` field.

Body access `env_at(i).foo(x)` reads `frame.envs[i]`, dispatches `foo` against the value's functor — the existing entity-dispatch mechanism handles this. No new dispatch path.

**Why `captured_envs` is essential**: passing a lambda to a higher-order function is the canonical case. The HO function's frame may have a totally different env scope than the lambda's creation scope, but when the lambda's body runs, it needs envs from where it was *created*, not from where it's *invoked*. The closure carries its env vector with it. Same mechanism as captured locals; same reason.

## Codegen

Each target picks how to render the env slot per its idiom:

- **Rust**: emit env as explicit `&impl Trait` parameter; or monomorphize on emit (re-substitute, eliminate the env param) when T is fully ground at the Rust call site.
- **Scala**: emit `using` clause.
- **C++**: emit extra constructor parameter pack or template-deduced argument.
- **Lua / dynamic targets**: emit positional argument.

The KB stays canonical (one body per spec op); each codegen pass chooses its surface materialization.

## Soundness invariants

1. **No silent dispatch**: every spec-op call either resolves to EnvFullyPinned (rewrite at body), EnvOpen (env-arg inserted from caller), or fails with a clear diagnostic.
2. **Static dispatch preserved**: every dispatched call's resolution is known at compile/load time. Runtime carries env values; it does not synthesize instances.
3. **Coherence at outermost site**: ambiguity in `requires` chains is rejected at the instantiation that introduces the choice.

## Implementation roadmap (WIs to file)

| Phase | Scope |
|-------|-------|
| **WI-218 soundness patch** | In `find_unique_impl_op`, return `Deferred` (skip rewrite) when the call is EnvOpen (open-T OR open-bound). Generic bodies become unsound-but-explicit instead of silent-mis-rewrite. ~50 lines. |
| **CallKind classification** | Populate `dispatch_kind: HashMap<TermId, CallKind>` at typing time. Required by all subsequent phases. |
| **IR variants** | Introduce `apply_within`, `ho_apply_within`, `constructor_within`, `lambda_within`. Migration: existing terms get rewritten to `_within` form with empty envs. The eval handles both forms during the migration window; env-less forms removed after. |
| **Body rewrite + env aggregation** | Inside generic bodies, spec-op calls become `apply_within(fn=env_at(i).<op>, args=…, envs=[])` — i is the position of the relevant bound in the enclosing scope's env slot. Env aggregation (per-op + per-sort `required_envs`) falls out as a side effect of the body-typing walk; not a separate pass. |
| **Call-site rewrite** | Callers fill in env args. The typer at the caller's site walks the caller's env scope to find the resolved impl, builds the env value, inserts into the apply term's `envs` slot. |
| **Frame `envs` field** | Add to `Frame` struct; populate on call entry; read for `env_at(i)` access. |
| **Closure `captured_envs` field** | Add to `Closure`; snapshot at lambda construction; restore on closure invocation. |
| **Eval entity-dispatch generalization** | `env.foo(args)` already works for entity-typed values; verify all spec-op call paths route through this. |
| **Per-target codegen** | Each codegen target adds env-slot rendering logic. |

## Out of scope (this design)

- **Per-operation env declarations** (Lean `[A T]` per-op style). Anthill keeps per-sort `requires` for now; per-op refinement is a future optimization.
- **Explicit instantiation syntax** (OCaml functor style). Future surface-syntax extension if user feedback requests it.
- **`dyn Spec` dynamic dispatch**. Opt-in escape hatch for genuinely runtime-decided cases (heterogeneous collections of trait objects). Not v0.
- **Recursive instance expansion** (`F[T = F[T = ...]]`). Naturally handled by parameter insertion (env passes through recursion as a regular value); no combinatorial explosion. No special handling needed.
- **Specialization at the codegen level** (M-style mono on emit for native targets). Each target's codegen pass decides; not a KB-level concern.

## References

- `operation-call-model-brainstorm.md` — the exploration this doc resolves.
- `spec-instance-dispatch.md` — WI-210 design.
- WI-218 — current static-dispatch rewrite (needs soundness patch from this design).
- proposal 030 — specialization witnesses; consume env metadata for proof records.
- proposal 036 — Domain Store Sorts; the use case driving this design.
