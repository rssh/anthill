# The operation-call model

## Status: Decision (post-brainstorm)

## Tracks: WI-204 (port cmd_X), WI-218 (static-dispatch rewrite shipped — needs follow-up patch), WI-210 (spec/impl call-site dispatch)

## Brainstorm: see `operation-call-model-brainstorm.md` for the exploration. This doc is the resulting design only.

## Decision in one paragraph

An operation declared inside a sort with `requires X` (or whose signature uses the sort's open type-params) is implicitly a function over an X-resolution **environment**. We materialize the environment as **parameter insertion** (Scala `using` / Lean instance arg / GHC dictionary-passing): the typer adds an explicit env slot to apply / ho_apply / constructor / lambda IR forms; envs become first-class runtime values flowing through regular arg-passing; the eval gains a `frame.active_env` field structurally parallel to `frame.locals`. No body cloning, no side-table dispatch, no instantiation-context threading.

## The IR

Four IR variants gain an env channel; the env-less forms become canonical aliases for `_within(..., envs=[])` and are eliminated after migration:

```
apply_within(fn, args, envs)
ho_apply_within(pred, args, envs)
constructor_within(name, args, envs)
lambda_within(params, body, capture_env)
```

`envs` (or `capture_env`) is a positional vector of resolved env values. Each value is a sort-tagged entity: `Value::Entity { functor: <impl_sort_name>, ... }`.

### The `env_ref` primitive

A single new term form serves as the through-line for env-related references:

```
env_ref(env_index)              -- value form: yields frame.active_env[env_index]
env_ref(env_index, op_short)    -- fn-position form: yields the op resolved through frame.active_env[env_index]
```

Two arities, two uses, one primitive. The two-arg form looks up `frame.active_env[env_index]`, reads its functor, and resolves `<functor>.<op_short>` to the actual impl op symbol. The one-arg form just reads the env value at the slot.

`env_ref` appears in three IR positions:

1. **As the fn of an apply** (env-dispatched call):
   ```
   apply_within(fn = env_ref(0, "eq"), args = [x, y], envs = [])
   ```
   This is body-level dispatch through an env slot.

2. **Inside `envs` slots of an apply** (passing envs forward):
   ```
   apply_within(fn = B.bar, args = [x], envs = [env_ref(0)])
   ```
   D's body forwards its own env_ref(0) to B.bar.

3. **Inside `capture_env` of a `construct_env`** (env value construction):
   ```
   construct_env(IntEq, capture_env = [env_ref(0), env_ref(1)])
   ```
   The constructed env value's capture_env at slot i comes from the constructor's frame.active_env[0/1].

Same primitive everywhere — wherever the IR needs to refer to an env in the constructor's frame, it uses `env_ref`.

### Construction site

Building an env value:

```
construct_env(impl_functor, capture_env)
```

`capture_env` is a list of expressions (each evaluating to an env value at runtime). The expressions can be:

- `env_ref(j)` — read the constructor's frame.active_env[j].
- A load-time-constant reference — for envs resolvable from project facts.
- A nested `construct_env(...)` — for chained sub-envs.

The typer at the construction site walks the impl's `required_envs` and emits one expression per slot, choosing the source from the constructor's available env scope (frame slots + project facts).

### Eval handling for env_ref

When the eval reduces `env_ref(env_index)` (value form):

```
return frame.active_env[env_index]
```

When the eval reduces an apply whose fn is `env_ref(env_index, op_short)`:

```
env_value = frame.active_env[env_index]
impl_sym  = resolve(env_value.functor + "." + op_short)
// then the apply proceeds as if fn were impl_sym
```

The eval's existing apply path consumes `impl_sym` for the OperationInfo lookup and frame push.

### Dispatch produces a new frame using env_value.capture_env

When apply_within(fn = env_ref(i, op_short), args, envs = []) reduces:

1. Read `frame.active_env[i]` → env_value.
2. Resolve `env_value.functor.op_short` → impl_sym.
3. Evaluate args (existing AwaitState path).
4. Push new frame:
   - `locals` = zip(impl_sym.params, evaluated_args)
   - `envs` = env_value.capture_env   ← the env value's bundle
   - `expr` = impl_sym.body

The new frame's envs comes entirely from env_value.capture_env. The apply's own envs slot is `[]` for env-dispatched calls because there's nothing for it to add — the env value already carries everything the impl's frame needs.

### Env values carry their own sub-envs

Each impl sort has its own `required_envs` — the impl's body might use envs beyond what the spec dictates. `IntEq.eq`'s body might use Numeric and Show, even though `Eq.eq`'s spec doesn't mention them.

Therefore env values are recursive: they bundle their impl's resolved sub-envs at construction time:

```rust
// Conceptually (extending Value::Entity):
Value::Entity {
    functor: IntEq,
    pos: ...,
    named: ...,
    capture_env: SmallVec<[Value; 2]>,    // resolved sub-envs for IntEq.required_envs
}
```

When the typer at a caller's site builds the IntEq env value (to pass to a body that has `requires Eq`), it walks `IntEq.required_envs` and resolves each from the caller's own env scope:

```
env_value = construct_env(
    impl_sort = IntEq,
    capture_env = [<resolved Numeric[T=Int]>, <resolved Show[T=Int]>]
)
```

Recursive: if `Numeric[T=Int]` (e.g., IntNum) has its own required_envs, IntNum_value bundles them too. Walk terminates at impls with no requires.

### Dispatch reads bundled envs from the env value

When `apply_within(fn = env_ref(0, "eq"), args = [x, y], envs = [])` reduces:

1. Read `frame.active_env[0]` → the IntEq env value V.
2. Resolve `<V.functor>.eq` → IntEq.eq's symbol.
3. Push new frame: `frame.locals` from args, `frame.active_env` from **V.capture_env** (NOT from this apply's envs slot, which is typically empty for env-ref-dispatched calls).
4. Invoke IntEq.eq's body.

So env values are essentially closure-like: each one carries the sort + the resolved sub-envs needed to invoke any of its ops. The dispatch through `env_ref(i, op_short)` reads the env value's bundled envs as the source for the called op's frame.

This matches Haskell dictionaries (records of methods + sub-dictionaries) and Lean instances (instance values carry resolved sub-instances). It's the natural shape once we accept that impls have their own requires.

### Why separate slots and not collapse-into-args

An alternative is to encode envs as the leading N entries of a regular `args` list (Scala / Lean / GHC style — env params are just function parameters). That avoids new IR variants and AwaitState extension at the cost of structural visibility. We chose separate slots because:

- **Reinterpretation independence**: future analyses (re-derive env requirements, recompute resolution after a SortProvidesInfo change, swap an env at a debug breakpoint) operate on the env channel without touching args. With collapsed-into-args, every reinterpretation pass has to re-partition based on op metadata.
- **Codegen flexibility**: each target chooses how to render the env channel (Scala `using`, Rust `&impl Trait`, Lua positional). A separate slot in the elaborated IR lets each codegen pass decide its own surface; collapsing pushes that decision earlier.
- **Reflection / proof records**: distinguishing "this is an env" from "this is a regular arg" is information proposal-030 specialization witnesses can use; preserving it structurally is cheap.
- **Hash-consing of bodies is preserved either way**: bodies access envs by position (`env_ref(i)`) or by name in source (`env_A`); they don't bake in concrete env values. So generic bodies share TermIds across instantiations regardless of which encoding we pick. The separate-slot encoding doesn't lose this.

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

### Impls have their own requires from day one

A spec like `sort Eq { sort T = ?; operation eq(a, b) -> Bool }` declares the protocol. Each impl has its own requires set, derived from its body. **This is not a future case** — it's the ground-zero shape.

The canonical example is `Eq[List[List[X]]]`. The conditional instance `fact Eq[T = List[T = ?A]] :- Eq[T = ?A]` has its `:-` body declaring a subgoal — that's the impl's own requires. The body uses both Self (recursion on `List[?A]`) and the subgoal (inner element's Eq). Two distinct envs, both resolved at construction time.

For any concrete `Eq[List[List[Int]]]`, the resolution chain is:
- `Eq[List[List[Int]]]` matches conditional with `?A = List[Int]`.
- Subgoal: `Eq[List[Int]]` — matches same conditional with `?A = Int`.
- Subgoal: `Eq[Int]` — matches `IntEq`.

Three env values constructed, chained:
- `env_LLI` (functor=EqList, capture_env=[<Self ref>, env_LI])
- `env_LI` (functor=EqList, capture_env=[<Self ref>, env_I])
- `env_I` (functor=IntEq, capture_env=[])

The chain depth equals the nesting depth of the type. Recursion through Self is handled by knot-tying at construction (env_X.capture_env[Self_slot] = env_X itself).

Env values therefore aren't simple sort tags — they're recursive records carrying the impl's resolved env scope. This is the anthill analog of Haskell dictionaries / Lean instances.

**Same shape applies to non-conditional impls too**:

```anthill
sort IntEq
  fact Eq[T = Int]
  requires Numeric[T = Int]
  requires Show[T = Int]
  operation eq(a, b) = ...      -- body uses add() and show()
end
```

`IntEq.eq`'s required_envs = [Self?, Numeric[T=Int], Show[T=Int]] — Self if the body recurses, plus the explicit requires. Each env value bundles these at construction.

See "Env values carry their own sub-envs" below in the IR section.

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

### Two different things to distinguish

(1) **Conditional instance derivation**: `fact Eq[T = List[T = ?A]] :- Eq[T = ?A]` — derive `Eq[List[Int]]` from `Eq[Int]`. Anthill **already has this** via Horn-clause facts; SLD resolution handles it natively. Same mechanism as Haskell's `instance Eq a => Eq [a]`. Not a future feature — first-class today.

(2) **Constraint inference of sort.requires from bodies**: instead of declaring `Sort.requires` source-explicit and validating, let body walking *generate* the sort's requires. The user lists operations and bodies; the typer infers what envs the sort needs and prints them as the inferred signature. This is what Haskell GHC does for top-level let bindings (`foo x = show (x + 1)` → inferred `(Show a, Num a) => a -> String`).

(1) is about resolution; (2) is about signature inference. Different mechanisms.

For anthill v0: keep `Sort.requires` source-explicit and validate (need body walk for validation regardless). (2) is a possible future direction — less syntax, but less self-documenting (a user reading a sort declaration must walk all bodies to see what's required).

### Runtime is unaffected

The envs slot of a frame is **already populated** by the caller before the body executes. The body never recomputes anything; it just indexes into `frame.active_env[i]` via `env_ref(i)`. All analysis is at compile time; runtime is pure lookup.

### Runtime is unaffected

The envs slot of a frame is **already populated** by the caller before the body executes. The body never aggregates; it just indexes into `frame.active_env[i]` via `env_ref(i)`. Aggregation is an analysis fact at compile time, not a runtime operation.

## Call rewrite cases

At typing time, the body-rewrite pass examines each call and chooses one of three actions. This is **typer-internal logic**, not a persistent IR or analysis output — after the rewrite, the IR shows the result and the classification is consumed.

| Case | Trigger | Rewrite |
|---|---|---|
| Direct | fn is already an impl op | leave the call alone |
| Pin-now | fn is a spec op AND per-call subst is fully ground AND not via `requires` | resolve to impl, rewrite `fn` to that impl symbol (today's WI-218 path) |
| Defer-to-env | fn is a spec op AND per-call subst has a Var that is the body's open type-param OR fn is reached via `requires` | rewrite to access through env: `apply_within(fn = env_ref(i).<op>, args, envs = [])` where `i` is the position of the relevant bound in the enclosing scope's env slot |

The defer-to-env case has two triggers (open-T and open-bound). Both must fire — the open-T check alone misses the ground-via-requires case (WI-218's latent bug). See the "Body walking is necessary" section above for why both triggers exist.

## Resolution

Instance synthesis is an SLD query over `SortProvidesInfo` facts. Conditional instances (`fact Spec[…] :- subgoals`) are clauses with bodies; resolution composes via existing SLD machinery. This is the Lean-style search-based synthesis, expressed in anthill's existing primitives.

Coherence at the outermost site: ambiguous `requires` resolution rejects at the instantiation that introduces the choice (per WI-210's coherence rules — priority table or reject-as-ambiguous).

## Runtime: frame and closure

```rust
struct Frame {
    expr: TermId,
    locals:     SmallVec<[(Symbol, Value); 4]>,
    active_env: SmallVec<[Value; 2]>,             // env scope currently in use
    awaiting: Option<AwaitState>,
    ...
}

struct Closure {
    body: TermId,
    params: SmallVec<[Symbol; 2]>,
    captured_locals: SmallVec<[(Symbol, Value); 2]>,
    capture_env:     SmallVec<[Value; 1]>,        // env scope to use when invoked
}
```

**Two distinct concepts:**

- **`capture_env`** — on env values and closures. The env scope frozen at the value's construction time. Survives the value as it's passed around.
- **`active_env`** — on call frames. The env scope currently in use during execution. Set when the frame is pushed; consumed by `env_ref(i)` lookups.

When a frame is pushed, its `active_env` comes from one of:
- An apply_within's `envs` slot (direct invocation).
- The env value's `capture_env` (env-ref dispatched invocation).
- The closure's `capture_env` (ho_apply invocation).

Same data shape (vector of env values) but distinct roles: `capture_env` is saved state on a value; `active_env` is the live state on the executing frame. Naming makes the distinction clear.
- Lambda construction (`lambda_within`): closure's `capture_env` = enclosing frame's `envs[i]` indexed by the IR's `capture_env` field.

Body access `env_ref(i).foo(x)` reads `frame.active_env[i]`, dispatches `foo` against the value's functor — the existing entity-dispatch mechanism handles this. No new dispatch path.

**Why `capture_env` is essential**: passing a lambda to a higher-order function is the canonical case. The HO function's frame may have a totally different env scope than the lambda's creation scope, but when the lambda's body runs, it needs envs from where it was *created*, not from where it's *invoked*. The closure carries its env vector with it. Same mechanism as captured locals; same reason.

## Eval mechanics: AwaitState with envs

The eval's `AwaitState` continuation mechanism currently handles arg evaluation via something like `ApplyArgs { target, buffered, remaining }`. With env-aware IR, the apply path has two sub-evaluation lists (args and envs).

### Unified `ApplyWithin` state

```rust
enum AwaitState {
    ApplyWithin {
        target: Symbol,
        buffered_args: Vec<Value>,
        remaining_args: Vec<TermId>,
        buffered_envs: Vec<Value>,
        remaining_envs: Vec<TermId>,
    },
    ...
}
```

Evaluate envs first (typically trivial — env values are inserted by the typer as `Term::Ref` to interned Entity values, one reduce-expr step each), then evaluate args, then push the new frame:

- `frame.active_env = buffered_envs`
- `frame.locals` from zipping `buffered_args` with the op's param symbols.

### Per-IR-form behavior

| IR form | Eval-time env work |
|---|---|
| `apply_within(fn, args, envs)` | Eval envs (usually trivial); eval args; push frame with both populated |
| `ho_apply_within(closure_expr, args, envs=[])` | Eval closure; eval args; push frame with `frame.active_env = closure.capture_env` (call's own envs slot typically empty since closure carries them) |
| `constructor_within(name, args, envs=[])` | envs always empty; constructors don't dispatch through envs. IR carries the slot for shape uniformity. |
| `lambda_within(params, body, capture_env)` | One-shot: snapshot locals + envs from enclosing frame using indices in `capture_env`; deliver `Value::Closure`. No new AwaitState needed. |

### Closure invocation detail

When `ho_apply_within(closure_value, args, envs=[])` runs:
1. Evaluate the closure expression to a `Value::Closure`.
2. Evaluate args.
3. Push new frame: `frame.active_env = closure.capture_env` (NOT the call site's envs slot — closures carry their env requirements with them).

The call site's `envs` slot is typically empty for closure invocation. If it's non-empty (a context override, rare), v0 ignores the override and uses the closure's captured envs — preserves the lexical-scoping property.

### Why this is the right shape

The unified state makes the env / arg distinction explicit through to the eval-state level. Alternative designs (treating envs as a prefix of args, or splitting into two AwaitState variants) are simpler but lose the structural distinction. The unified state is the cleanest pairing with the IR's three-slot apply.

### A note on hash-consing and side-tables

If we chose a side-table approach (env mapping kept outside the term) instead of separate IR slots, the side-table would need to be keyed on `OccurrenceId` (positional source identity), NOT `TermId`. Reason: hash-consing collapses structurally-identical calls in different bodies (e.g., `foo(x)` in B's body vs C's body) to the same TermId, but those calls live in different env scopes. Side-table indexing by TermId can't disambiguate; OccurrenceId can.

The separate-slots approach (this design) avoids this entirely. Generic bodies don't bake env values into the apply term — they carry `env_ref(i)` references that read from the frame's env slot at runtime. Same TermId across two bodies is fine because each body's frame has its own envs populated by the call site. No occurrence-level keying is needed.

This is part of why separate slots beats side-table: simpler indexing scheme, no new positional keys, runtime distinction handled by existing per-frame state.

## Codegen

Each target picks how to render the env slot per its idiom:

- **Rust**: emit env as explicit `&impl Trait` parameter; or monomorphize on emit (re-substitute, eliminate the env param) when T is fully ground at the Rust call site.
- **Scala**: emit `using` clause.
- **C++**: emit extra constructor parameter pack or template-deduced argument.
- **Lua / dynamic targets**: emit positional argument.

The KB stays canonical (one body per spec op); each codegen pass chooses its surface materialization.

## Soundness invariants

1. **No silent dispatch**: every spec-op call either resolves at typing time (Pin-now: rewrite to impl) or has its env-arg inserted from the caller's env scope (Defer-to-env), or fails with a clear diagnostic.
2. **Static dispatch preserved**: every dispatched call's resolution is known at compile/load time. Runtime carries env values; it does not synthesize instances.
3. **Coherence at outermost site**: ambiguity in `requires` chains is rejected at the instantiation that introduces the choice.

## Implementation roadmap (WIs to file)

| Phase | Scope |
|-------|-------|
| **WI-218 soundness patch** | In `find_unique_impl_op`, return `Deferred` (skip rewrite) when the call is defer-to-env (open-T OR open-bound). Generic bodies become unsound-but-explicit instead of silent-mis-rewrite. ~50 lines. |
| **IR variants** | Introduce `apply_within`, `ho_apply_within`, `constructor_within`, `lambda_within`. Migration: existing terms get rewritten to `_within` form with empty envs. The eval handles both forms during the migration window; env-less forms removed after. |
| **Body rewrite + env aggregation** | Inside generic bodies, spec-op calls become `apply_within(fn=env_ref(i).<op>, args=…, envs=[])` — i is the position of the relevant bound in the enclosing scope's env slot. Env aggregation (per-op + per-sort `required_envs`) falls out as a side effect of the body-typing walk; not a separate pass. |
| **Call-site rewrite** | Callers fill in env args. The typer at the caller's site walks the caller's env scope to find the resolved impl, builds the env value, inserts into the apply term's `envs` slot. |
| **Frame `envs` field** | Add to `Frame` struct; populate on call entry; read for `env_ref(i)` access. |
| **Closure `capture_env` field** | Add to `Closure`; snapshot at lambda construction; restore on closure invocation. |
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
