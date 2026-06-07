# The operation-call model

## Status: Brainstorming draft

## Tracks: WI-204 (port cmd_X via spec ops), WI-218 (static-dispatch rewrite), WI-210 (spec/impl call-site dispatch via fact)

## Relates to: spec-instance-dispatch.md (the WI-210 design); proposal 030 (specialization witnesses); proposal 036 (Domain Store Sorts)

## The core insight

An operation declared inside a sort with `requires X` is **implicitly a function over an X-resolution environment**. Calling that operation requires the caller to supply a resolved environment — the impl picks for X (and X's transitive requires) at the call's resolution scope.

The same is true for operations whose signature uses the enclosing sort's open type-params: those bodies are implicitly polymorphic over the type-arg environment.

**How that environment is delivered is an implementation choice**, downstream of the semantics. The two main options are body cloning (Rust-style monomorphization) and side-table dispatch keyed on environment (Haskell-class / Scala-`using`-style). The type system and language surface describe the environment *requirement*; the runtime/compile machinery is downstream.

This framing came out of brainstorming and reframes WI-218: today's typer commits to a dispatch decision before the environment is fully resolved. That's a soundness bug regardless of which materialization we eventually pick.

## Language analogs

The shape we're describing already exists in mainstream languages, with different choices on three axes: **(R) resolution** (how is the right impl found?), **(M) materialization** (how is the body delivered to runtime?), and **(C) compositionality** (can instances be derived from other instances?).

### Scala 3 `using` / `given`

```scala
def bar[T](x: T)(using a: A[T]): String = "B" + a.foo(x)
given intA: A[Int64] = new A[Int64] { ... }
```

- **R**: implicit-resolution rules over `given` declarations at the call site.
- **M**: dictionary-passing — body is shared, instance is a runtime value.
- **C**: yes — `given listEq[T](using Eq[T]): Eq[List[T]] = ...`.

### Haskell type classes

```haskell
class Show a where show :: a -> String
instance Show Int64 where show n = ...
foo :: Show a => a -> String   -- "Show a =>" is the dictionary parameter
```

- **R**: class-resolution at compile time, instances looked up by type.
- **M**: dictionary-passing by default; SPECIALIZE pragma opts into monomorphization.
- **C**: yes — `instance Show a => Show [a] where show xs = ...`.

### OCaml functors

```ocaml
module B (A : ASIG) = struct
  let bar (x : A.t) = "B" ^ A.foo x
end
module BInt = B(IntA)   (* explicit instantiation *)
```

- **R**: explicit. The user spells out `B(IntA)`. No search.
- **M**: shared bodies + applied modules pointing at them. Closer to D than M.
- **C**: yes via functor application chains, but explicit at every step.

### Rust traits

```rust
trait Eq { fn eq(&self, other: &Self) -> bool; }
impl Eq for i32 { ... }
fn foo<T: Eq>(a: T, b: T) -> bool { a.eq(&b) }
```

- **R**: trait-resolution at compile time, instances looked up via `impl Trait for Type` declarations.
- **M**: monomorphization per `<T>` instantiation; `dyn Trait` opts into vtable.
- **C**: yes — `impl<T: Eq> Eq for Vec<T> { ... }`.

### C++20 concepts (≈ Rust traits, two key differences)

```cpp
template<std::equality_comparable T>
bool same(T a, T b) { return a == b; }
```

- **R**: ad-hoc overload resolution + concept satisfaction check. Concepts are pure *constraints* — they describe what's needed, not what's provided. The body source comes from the type's own member functions or free functions found via ADL.
- **M**: full monomorphization per instantiation, like Rust. Each `same<int>`, `same<string>`, etc. is a separate compiled function.
- **C**: yes via partial template specialization (`template<typename T> struct Hash<vector<T>> { ... }`), now constrainable with concepts.

C++ is "Rust's mono with messier resolution." For our design, C++ doesn't add new options beyond Rust — it confirms plan M is natural for native targets but doesn't suggest anything novel.

The structural difference C++ does highlight: concepts are *constraints*, separate from body source. Anthill's `requires X` is constraint-shaped (like a concept) but the body source comes from `fact Spec[T = X]` (structured, like a Rust impl block). So anthill cleanly separates the C++ "constraint" idea from the Rust "structured impl database" idea.

### Lean 4 instances

```lean
class A (T : Type) where foo : T → String
instance : A Int64 where foo := toString
def bar [A T] (x : T) : String := "B" ++ A.foo x
```

- **R**: search-based instance synthesis. The elaborator walks the global instance database with bounded backtracking. Composable, prioritized, with explicit decidability rules.
- **M**: dictionary-passing as the runtime model; native compilation specializes via inlining + LLVM optimization.
- **C**: yes, deeply — `instance [Eq T] : Eq (List T) := ...` is conditional instance derivation. The synthesized environment for the conditional's body has open slots filled by recursive search.

Lean's instance synthesis is **a structured search procedure**. Composable instances mean the runtime environment can be a *chain* of resolved instances built up by search:

```lean
-- Want: Eq (List (Int64 × String))
-- Search walks: instance [Eq T] [Eq U] : Eq (T × U), instance [Eq T] : Eq (List T)
-- Composes to: Eq Int64 + Eq String → Eq (Int64 × String) → Eq (List (Int64 × String))
```

For each step, the elaborator records the resolved instance. The composed environment carries all the resolutions.

### Per-operation environment declarations

Lean (and Scala) put the environment requirement on the **operation**, not just the sort:

```lean
def bar [A T] (x : T) : String := ...    -- bar needs A, but the enclosing module doesn't impose it
```

Anthill today puts `requires` on the *sort*. This is a granularity question: does B always require A, or do only some of B's operations? Per-operation envs are more granular but mean the env-requirement appears in the call signature; per-sort envs are simpler but coarser.

We don't have to pick now, but the design should leave room for per-op envs as a refinement.

## Anthill's structural fit

Plotting anthill against this matrix:

| | Resolution | Materialization (current) | Materialization (proposed) | Compositionality |
|---|---|---|---|---|
| Anthill | SLD over SortProvidesInfo (latent) | WI-218 broken rewrite | TBD (M / D / H) | yes — `fact Spec[…] :- subgoals` |

Anthill's resolution structure is **Lean-like**: SLD with bodies = instance synthesis with conditional instances. The KB is the instance database. We already have search-with-backtracking; we don't need to invent it.

The materialization choice is the open question. Each of M / D / H corresponds to a known mainstream language's choice:

- M ≈ Rust + C++ (clone bodies per type-arg)
- P ≈ Scala 3 + Lean 4 + Haskell GHC (insert env as a parameter; runtime sees regular args)
- D ≈ (no mainstream language — heavier than what they actually do)
- H ≈ P + per-target mono on emit (Lean's effective behavior under LLVM specialization)

Anthill's `requires` clause is structurally Scala's `using` parameter / Lean's instance argument / OCaml's functor parameter. The runtime semantics can be Rust-style (clone bodies) or Scala/Lean/Haskell-style (env as parameter) — same abstract model, different materialization.

## Problem (what's broken in WI-218 today)

Anthill currently has three syntactic shapes for an operation call:

1. **Bare name in a fully-pinned context** — `commit(s, w)` where `s : Cell[V = WIS]`. Environment is fully determined locally: WIS is ground, no `requires` is open. WI-218's static rewrite works.
2. **Bare name in an open environment** — `foo(x)` inside an operation body whose enclosing sort has either an open type-param OR an open `requires` chain that the body's sort doesn't pick. Environment isn't fully resolved here.
3. **Qualified impl name** — `C1.foo(x)`, `FileBasedWorkitemStore.commit(s, w)`. No dispatch needed; the impl is named directly.

WI-218 handles (1) and (3). It fails (2) in two distinct ways — both are environment-resolution failures:

- **Open-T**: per-call subst's value for the spec param is a `Term::Var` (the enclosing sort's open T). Environment's type-arg side isn't pinned.
- **Open-bound**: the call goes through a `requires A` (or `requires A[T = String]`) whose target's impl pick belongs to the enclosing sort's future instantiator, not to the enclosing sort itself. Environment's bound-resolution side isn't pinned, even if the type-args are ground.

Both share a root: **the environment's resolution scope is outer than B**. The body is wrong to commit.

### Concrete example

```anthill
sort A
  sort T = ?
  operation foo(x: T) -> String
end

sort B
  sort T = ?
  requires A
  operation bar(x: T) -> String =
    String.concat("B", foo(x))      -- shape (2): open env
end

sort C1
  sort T = ?
  fact A[T = T]
  operation foo(x: T) -> String = "c1"
end

sort C2
  fact A[T = String]
  operation foo(x: String) -> String = String.concat("c2", x)
end

sort ClientCall
  operation callFoos(x: String) -> String =
    let x1 = C1.foo(x)              -- shape (3): qualified
    let x2 = C2.foo(x)              -- shape (3): qualified
    String.concat(x1, x2)
end
```

WI-218 today rewrites B.bar's `foo(x)` to `C1.foo` (matching C1's universally-quantified candidate). But `B.bar` is meant to work for any T; the impl pick belongs to whoever instantiates B.

## Operation-call kinds (model-independent)

Each apply term in an operation body classifies into one of three kinds at typing time. This classification is independent of how we materialize the environment.

```
enum CallKind {
  Direct,                                 -- shape (3): qualified, fn = impl op
  EnvFullyPinned { impl_op: Sym },        -- shape (1): env resolved locally; rewrite at body site
  EnvOpen { spec_op: Sym, source: Source },  -- shape (2): env not pinned; defer to outer scope
}

enum Source {
  OpenTypeParam { spec_param: VarId },    -- per-call subst's value is a Var
  OpenBound { bound: SortRef, ... },      -- reached via `requires` whose impl pick is outer
}
```

A call is **EnvOpen** iff *either* condition holds:

1. **Open-T**: at least one per-call binding value resolves to a Var that is the enclosing sort's own open type-param.
2. **Open-bound**: the spec op is reached through a `requires` clause on the enclosing sort; the impl satisfaction is the future instantiator's responsibility, even if the requires' type-args are ground.

A call is **EnvFullyPinned** when neither condition holds: not via `requires`, all type-args ground.

A call is **Direct** when the fn symbol is already an impl op.

The two `EnvOpen` triggers correspond to the two failures in the Problem section. Detection has to cover both.

## Materialization: where the implementation choice lives

Once the call is classified, the environment has to be made available at runtime. There are several materialization strategies.

### (M) Body-cloning monomorphization (Rust-style)

At each instantiation site (`fact Spec[T = Bind]` with ground bindings), clone the generic operation bodies, substitute type-args, re-run dispatch classification, register cloned bodies as specialized OperationInfo facts. The eval invokes the specialized body directly.

- Term store grows: O(specs × instantiations × generic-op-count). Hash-consing offers no help since every clone differs by at least one substituted symbol.
- Eval per apply: direct symbol jump via OperationInfo lookup. No per-call indirection.
- Codegen-friendly: each (impl, type-arg) pair is its own first-class fact in the source-of-truth KB.
- Recursive cases (`F[T = F[T = Int64]]`) need bounded expansion or explicit `dyn` annotation.

### (P) Parameter insertion (what Scala 3 / Lean 4 / GHC actually do)

The crucial observation: Scala's `using` clause, Lean's `[A T]` instance arg, and Haskell's `(A a =>)` constraint are all **source-level sugar for an extra function parameter**. The compiler inserts the resolved env at the call site as a regular argument; the body accesses it as a regular param. The runtime sees nothing special — no per-frame env state, no lookup table, no environment-threading machinery.

For B.bar:

```anthill
sort B
  sort T = ?
  requires A
  operation bar(x: T) = String.concat("B", foo(x))
end
```

#### Compile-time env representation

At typing time, every scope (sort or operation) carries:

```
(sort_id, substitution, Vec<resolved_requires>)
```

- `sort_id` — the enclosing sort.
- `substitution` — type-arg bindings (B.T → Int64, etc.).
- `Vec<resolved_requires>` — for each `requires` bound, the resolved `(bound_spec, impl_sort)` pair plus the sub-substitution that pins it.

**Aggregation rule (bottom-up)**: per-op env requirement = explicit requires + requires inferred from called ops; per-sort env requirement = union over its ops. Vector ordering is canonicalized (sorted by bound's qualified name, or declaration order).

#### IR support: explicit env slot

To make the env channel structural, four new IR variants:

```
apply_within(fn, args, envs)
ho_apply_within(pred, args, envs)
constructor_within(name, args, envs)
lambda_within(params, body, captured_envs)
```

The env-less forms (`apply`, `ho_apply`, `constructor`, `lambda`) become canonical aliases for `_within(..., envs=[])` / `lambda_within(..., captured_envs=[])`. After migration, **only the `_within` forms exist** — one canonical shape with the env channel as a first-class slot. The eval handles one case, not two.

`lambda_within` is essential because anthill's bodies are lambda-heavy (every `do` block, every monadic continuation, every match-arm closure). The typer aggregates env requirements across the lambda's body and records them as `captured_envs`; at closure construction, the eval snapshots envs from the enclosing frame using this index, the same way it already snapshots captured locals.

Properties of the explicit IR:
- **One canonical shape** — every call carries an env slot; empty when no env is needed.
- **Reflection-clean** — fn / args / envs are distinct channels; useful for proof records, debug, codegen.
- **Codegen-friendly** — each target picks how to render the env slot (Rust merges into args or `impl Trait` bounds + mono; Scala emits `using`; Lua emits a separate positional list).

#### Frame and closure structure (runtime)

Mirroring the IR:

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
    captured_envs:   SmallVec<[Value; 1]>,    // NEW
}
```

`envs` and `captured_envs` are just additional structural fields. **Not new runtime machinery in the bad sense** — they're the runtime forms of the IR's env slots, mirroring how `locals` and `captured_locals` are the runtime forms of the args slots. The eval treats them symmetrically.

Closure invocation: when `ho_apply_within(closure, args, envs=[])` runs, the closure's `captured_envs` populate the new frame's `envs` (the call's own envs slot is typically empty since the closure carries its env requirements). Closure construction: when `lambda_within` is reduced, the eval snapshots envs from the enclosing frame's `envs[]` indexed by the lambda's `captured_envs` field.

This handles the lambda chain in `\x -> bind(env_M, \y -> ...)` correctly: each lambda's closure captures env_M from its enclosing scope, the same way local capture chains work today.

#### Translation

After elaboration:

1. **Signature**: `bar` declares `requires A` aggregated. The IR encodes `bar.required_envs = [A]` (length 1 because B's only requires bound is A).
2. **Body rewrite**: `foo(x)` (a spec call) becomes `apply_within(fn=env_at(0).foo, args=[x], envs=[])` — A's env is referenced positionally by index 0.
3. **Call site rewrite**: `bar(arg)` from D's perspective becomes `apply_within(fn=bar, args=[arg], envs=[<D's resolved A as Value::Entity>])`. The typer at D's site walks D's `fact A[…]` to find the resolved impl, builds the env value, inserts it.
4. **Frame entry**: when bar's frame is pushed, `frame.envs[0]` = the A-impl value passed in. Inside the body, `env_at(0).foo(x)` reads `frame.envs[0]`, dispatches `foo` against its functor.
5. **Eval is unchanged structurally**: dispatch on a value via existing entity-dispatch machinery. Indexed access into `frame.envs` is constant-time.
6. **Closures capture envs the same way they capture locals**: snapshot both fields. Monadic continuations and lambdas handle envs via standard capture.

The env value at runtime is sort-tagged: `Value::Entity { functor: <impl_sort_name>, ... }`. Dispatching `env.foo(args)` resolves through `OperationInfo` lookup keyed on the impl sort's qualified name — anthill already does this for direct impl calls. No new dispatch path.

#### Properties

- **Term store**: bodies stay one TermId per spec op (shared across all instantiations). Apply terms gain an env slot but stay hash-consed.
- **Hash-consing preserved**.
- **Eval per apply**: indexed `frame.envs[i]` lookup + regular dispatch.
- **Codegen target**: trivial. Each target picks its preferred surface for the env slot.
- **Recursive cases**: env is just a value passed through recursion.

#### Diamond / multi-bound

`sort B { requires A; requires Eq[T = T]; ... }` — operations using both A's and Eq's ops have an `envs` slot of length 2:

```
apply_within(fn=bar, args=[x], envs=[<A_impl>, <Eq_impl>])
```

Inside bar's body: `foo(x)` (an A op) is `env_at(0).foo(x)`; `eq(x, y)` (an Eq op) is `env_at(1).eq(x, y)`. Position-indexed; ordering canonicalized at signature time.

#### Conditional / chained instances (monad transformers)

For `fact Monad[M = StateT[S = ?S, M = ?M]] :- Monad[M = ?M]`, SLD synthesis at the call site walks the chain. The env slot at any one call site holds the OUTERMOST resolution (StateT's instance). When that StateT's bind body internally calls `bind` on its inner M, that's a NEW call with its own env slot holding ExceptT's resolution. The chain materializes step-by-step as the call stack descends.

So the env slot at any one call carries one resolved instance per `requires` bound on the calling sort — finite, small, local. The chain doesn't have to be reified as one giant data structure; it spreads naturally across frames.

### (D) Side-table dispatch keyed on environment (the heavier alternative)

D was originally drafted as the "Haskell/Scala-style" path, but it's a heavier implementation than what those languages actually do. It keeps bodies completely un-rewritten and stores the dispatch decisions in a side table keyed on `(apply_tid, env_id)`. The interpreter carries env state per frame.

The split between KB-level (compile/load-time) state and interpreter-level (runtime per-frame) state:

**KB carries** (built at fact-load time, read-mostly thereafter):
```
dispatch_rewrites: HashMap<(TermId, EnvironmentId), TermId>
environments:      Vec<Environment>           -- interned envs; EnvironmentId indexes into this
env_for_op:        HashMap<Symbol, Vec<EnvironmentId>>  -- which envs each op can be invoked with
```

`Environment` is the resolved chain of `requires`-resolution decisions plus type-arg pins active at the resolution scope. Constructed by SLD synthesis over `SortProvidesInfo` facts at load time. Hash-consed (interned via `EnvironmentId`) so equal envs share one entry. The KB's role is exactly its current role for `OperationInfo`, `SortProvidesInfo`, etc. — a precomputed, queryable analysis result.

**Interpreter carries** (per-frame, runtime):
```
struct Frame {
    ...                        -- existing fields: locals, expr, awaiting, etc.
    env: EnvironmentId,         -- current resolution scope
}
```

Each frame remembers its env. Calling into a generic op pushes a frame whose env is the CALLER's env (Lean's convention) or the resolved env at the call site if the call needs a fresh resolution. Closures capture `env` along with their other state.

The interpreter never *constructs* envs at runtime — it only *carries* them through frames and consults the KB's `dispatch_rewrites[(current_apply_tid, current_env)]` lookup at apply sites. The static-dispatch invariant is preserved: all envs are built at load time via SLD synthesis; runtime is pure lookup.

- Term store grows: O(generic-apply-count × envs) of side-table entries (TermId pointers). Bodies stay one TermId per spec op.
- Hash-consing: bodies stay canonical; envs hash-consed via `EnvironmentId`.
- Eval per apply: one HashMap lookup keyed on `(apply_tid, env_id)`.
- Codegen for native targets: codegen step does its own clone-and-substitute on emit (target Rust doesn't have the side table at runtime). Per-target.
- Recursive cases: lazy population by actual runtime needs; `dyn` becomes optional.

This mirrors how WI-218 currently splits work between KB and interpreter: the KB carries the typing-time analysis result (`dispatch_rewrites`), the interpreter only consults it at `reduce_expr`. Plan D extends this: the map's key gains an env component, and frames learn to carry an `EnvironmentId`.

### (H) Hybrid

Side-table dispatch for the eval-driven path; codegen-time monomorphization per target. Each codegen target chooses its preferred materialization (Rust → mono; Scala → mono via `using`; Lua → dict-passing). The KB stays canonical.

### (E) Explicit-module style (OCaml-functor inspired)

Make the environment-supplying step explicit at the source level: `module BInt = B(IntA)` style, where the user spells out the instantiation. Trade implicit `using` resolution for explicit functor application. No silent dispatch, more verbose.

E doesn't strictly conflict with M, D, or H — it's a surface-syntax change that pairs with any runtime materialization. We could combine E with D (explicit instantiation, shared bodies) to maximize clarity at minimal runtime cost.

## Non-trivial cases

The simple B/C1/C2 example covers the basic shape but misses several patterns that real code hits.

### Default method override

```anthill
sort Eq
  sort T = ?
  operation eq(a: T, b: T) -> Bool
  operation neq(a: T, b: T) -> Bool = not(eq(a, b))   -- default body
end

sort IntEq
  fact Eq[T = Int64]
  operation eq(a, b) = ...
end
```

`neq`'s body calls `eq` — same Self bound, no explicit `requires`. Inside `IntEq` (which inherits the default neq), `eq` should dispatch to `IntEq.eq`. This is "Self-dispatch": the implicit bound is `Self : Eq[T]`. Both M and D handle this; the question is how the default body is registered (in Eq, then specialized; or pre-specialized at fact-load).

This pattern is widespread — every `Eq`, `Ordered`, `Numeric` impl in stdlib likely inherits at least one default body that calls a primitive method.

### Diamond dependency

```anthill
sort A
sort B requires A
sort C requires A
sort D { fact B[T = Int64]; fact C[T = Int64]; ... }
```

D must supply ONE `A[T = Int64]` satisfaction that's consistent for both the B-bound and the C-bound. Coherence at the outermost site, transitive across multiple bounds. If D supplies A inconsistently (or doesn't supply at all), error.

### Functor over parametric sort (higher-kinded)

```anthill
sort Functor
  sort F = ?           -- F is a parametric sort, not a value-type
  operation map(f: ?A -> ?B, xs: F[A]) -> F[B]
end

sort ListFunctor
  fact Functor[F = List]
  operation map(f, xs) = ...
end
```

F is a sort-with-its-own-arity. Dispatch on F's impl AND on the per-call A/B bindings. Higher-kinded — a strong test for whichever model we pick.

### Mutual recursion across requires

```anthill
sort B requires A; operation foo() = bar()
sort A requires B; operation bar() = foo()
```

B's instances need A; A's instances need B; circular. Either accept (M produces co-fixpoint specializations; D records lazy entries) or reject (require explicit `dyn` cycle-break).

### Phantom-only type-param

```anthill
sort Tagged
  sort Tag = ?
  sort T = ?
  entity tagged(v: T)
end
sort UserId  -- wants Tagged[Tag = User, T = Int64]
sort PostId  -- wants Tagged[Tag = Post, T = Int64]
```

`Tag` isn't used in operation bodies. M generates two clones differing only in dead `Tag`. D's side table can dedup if it hashes on the parts that affect dispatch. M needs a phantom-detection pass to avoid waste.

### Conditional / per-T defaults

```anthill
fact Display[T = Int64]    { ... }       -- explicit
fact Display[T = ?A]     { ... } where ?A : Numeric  -- conditional default
```

The dispatch table has rules with their own bounds. Resolving dispatch becomes a small constraint solve. Not a v0 concern but the model must accommodate.

### Existential / down-cast

```anthill
operation render_any(x: ?dyn Display) -> String = show(x)
```

`?dyn Display` is the "any thing satisfying Display" carrier — vtable territory. Anthill's plan is "`dyn` is opt-in"; this is where it has to be actually implemented.

### Abstract monad — instance chains, same-env multi-call, closure env capture

```anthill
sort Monad
  sort M = ?     -- M is a parametric sort, not a value-type
  operation pure(x: ?A) -> M[T = ?A]
  operation bind(m: M[T = ?A], f: ?A -> M[T = ?B]) -> M[T = ?B]

  -- Generic operation derived from pure + bind
  operation mapM(f: ?A -> M[T = ?B], xs: List[T = ?A]) -> M[T = List[T = ?B]] =
    match xs
      case nil() -> pure(nil())
      case cons(x, rest) ->
        bind(f(x), \y ->
          bind(mapM(f, rest), \ys ->
            pure(cons(y, ys))))
end

fact Monad[M = Option]    operation pure(x) = some(x)    operation bind(m, f) = ...

-- Conditional / chained instance: Monad transformer
fact Monad[M = StateT[S = ?S, M = ?M]] :- Monad[M = ?M]
operation pure(x) = ...
operation bind(m, f) = ...

fact Monad[M = ExceptT[E = ?E, M = ?M]] :- Monad[M = ?M]
operation pure(x) = ...
operation bind(m, f) = ...
```

This case adds four pressures the simpler examples don't:

- **Instance chains.** `StateT[Int64, ExceptT[Err, Option]]` triggers an SLD walk through three conditional clauses. The synthesized env IS a chain of resolved Monad instances (three levels deep). M can't enumerate this combinatorially; D handles it natively because env construction IS an SLD query.

- **Same-env multi-call within one body.** `mapM`'s body has five spec-op calls (pure, bind, bind, pure, plus recursive mapM) all dispatching against the same Monad env. Performance-relevant for D: cache the env lookup per frame rather than re-resolving each apply.

- **Closure env capture.** The lambdas `\y -> ...` are monadic continuations. When they invoke bind / pure later, they need the same env mapM's frame had. Closures must capture `EnvironmentId` at creation. Plan M clones lambdas alongside the body; plan D requires concrete env-capture in closure values.

- **Effect-tracking interaction.** StateT carries a `Modify` effect; ExceptT carries `Error`. The composed monad's effect row depends on the resolution chain. Dispatch and effect resolution become entangled. Not v0 work, but the model has to leave room.

Why this matters for the M-vs-D choice: monad transformers are the case where Rust's monomorphization approach famously breaks down. The Rust ecosystem doesn't have a thriving monad-transformer library precisely because the cost shape is wrong — every `StateT<S, ExceptT<E, M>>` combination clones bodies. Lean and Haskell handle this gracefully because their runtime threads dictionaries / environments. If anthill commits to plan M, transformer-style abstractions will be expensive to use; if it commits to D / H, they're free.

### Cross-bound interaction (a deeper case)

```anthill
sort B
  sort T = ?
  requires Eq[T = T]       -- B's instances must satisfy Eq for same T
  requires Ordered[T = T]  -- and Ordered too
  operation sort(xs: List[T = T]) -> List[T = T] = ... eq(...) ... lt(...) ...
end
```

`B.sort`'s body uses both `eq` (from Eq bound) and `lt` (from Ordered bound). At an instantiation `D { fact B[T = Int64]; fact Eq[T = Int64]; fact Ordered[T = Int64] }`, the environment has TWO impl picks (one per bound). Resolution must pin both.

This is the diamond pattern's inner mechanism: the environment is a *set* of resolutions, not a single one. M's specialized body has both rewrites baked in; D's side-table entry covers both apply terms, keyed on the same environment.

## Comparison

| Dimension | (M) Body cloning | (P) Param insertion | (D) Side-table | (H) Hybrid |
|-----------|------------------|---------------------|----------------|------------|
| Closest mainstream analog | Rust, C++ | **Scala 3, Lean 4, GHC** | (heavier than any actual lang) | per-target mix |
| Body shape | cloned per env | rewritten once (env-param indirection) | unchanged | per target |
| Term-store growth | O(K × N) — high | O(specs) — low | O(specs) — low + side-table | per target |
| Eval per apply | Direct symbol jump | Regular var lookup + dispatch | One HashMap lookup | Lookup or jump |
| Eval frame plumbing | None new | None new | Each frame carries an env_id | Each frame carries an env_id |
| New runtime machinery | None | **None** | Side-table + frame env | Side-table + frame env |
| Hash-consing | Defeated for generics | Preserved | Preserved | Preserved |
| Anthill KB idiom | Foreign | Native (env is a Value) | Native (side-table extends WI-218's) | Native |
| Codegen Rust target | Natural | Trivial (env as param) | Re-mono on emit | Re-mono on emit |
| Codegen Scala target | Natural | Direct (`using`) | Re-mono on emit | Direct |
| Codegen Lua / dynamic | Wasteful | Natural (regular arg) | Natural | Natural |
| Proof-record specialization | Each spec is a fact | Records reference (body, env-arg) | Records reference (body, env-id) | Either |
| Reflection | Specialized bodies are normal facts | Env is a value — reflectable | Reflection threads env | Either |
| Recursive instances | Combinatorial explosion at load | Env value passes through recursion | Lazy by runtime use | Lazy |
| Diamond / multi-bound | One specialized body bakes in all | Multiple env params (one per bound) | Side-table key includes all | Either |
| Conditional instances (`fact Spec[…] :- subgoals`) | Each derivation cloned | Resolved env value built once at call site | Side-table per env | Either |
| Reuses anthill's SLD machinery | No | Yes — call-site resolution is SLD query | Yes — env construction IS an SLD query | Yes |
| Implementation cost (first cut) | Substantial | **Modest** — typing-time rewrites only | Substantial | Substantial |

## Possible plans

### Plan M — body cloning at load time (Rust / C++ style)

1. WI-218 soundness patch (model-independent).
2. CallKind classification (model-independent).
3. Body clone + substitution pass at fact load.
4. Naming convention for specialized bodies (mangled vs sub-namespace).
5. Recursive-case detection (since plan M can't handle `F[T = F[T = ...]]` without explicit `dyn`).
6. Reflection updates.
7. Codegen consumes specialized bodies directly.

Plan M aligns with Rust's monomorphization and C++'s template instantiation. Both default to this. The cost shape is well-understood (binary growth, optimization opportunities) but defeats anthill's hash-consing canonicity.

### Plan P — parameter insertion (Scala 3 / Lean 4 / Haskell GHC actual implementation)

1. WI-218 soundness patch (model-independent).
2. CallKind classification (model-independent).
3. **Signature elaboration**: spec ops with `requires X` (or whose enclosing sort has open T's affecting the spec op) gain implicit env params. The KB stores the elaborated signatures; surface syntax is unchanged.
4. **Body rewrite**: spec-op calls inside generic bodies become env-param-indirected calls. `foo(x)` → `env_A.foo(x)` where `env_A` is the auto-inserted parameter. One body rewrite per generic op, not per env.
5. **Call-site rewrite**: callers fill in env args. The typer at the call site walks the caller's `fact A[…]` (potentially via SLD synthesis for conditional instances) to find the resolved impl and inserts a reference to it as the env arg in the apply term.
6. **Env value representation**: `Value::Entity { functor: <impl_sort_name>, ... }`. Existing eval dispatch on entity values handles `env.foo(args)`.
7. **Eval is unchanged**. No new state, no new lookup, no new closure machinery.
8. Per-target codegen: Rust target may opt into mono on emit (re-substitute env at compile time, eliminate the env param); Scala emits `using`; Lua emits a positional arg.

### Plan D — side-table dispatch (skip)

D was an over-engineered alternative to P. It invents per-frame env state and side-table lookups; P achieves the same observable behavior using only existing primitives. Skip D unless something rules out P.

### Plan H — hybrid

Plan P naturally generalizes to hybrid: the elaborated form has env params, but each codegen target can opt to monomorphize on emit (re-substituting env values into specialized bodies for native targets where that's preferred). The KB stays canonical; codegens pick their materialization.

1. Steps 1–7 of plan P.
2. Each codegen target chooses: emit envs as explicit params (P-style on the target side), or re-substitute and mono on emit (M-style on the target side).

## Recommendation (my current lean)

**Plan P (parameter insertion).** This is what Scala 3, Lean 4, and Haskell GHC actually do. It was originally subsumed under "plan D" in this doc, but the distinction matters: plan P needs no new runtime machinery, while plan D introduces frame-level env state and a side-table lookup at every apply.

Plan P:

- Term-store stays canonical. Hash-consing preserved.
- Eval unchanged. Env is a `Value::Entity` flowing through regular arg-passing. Closures capture env via standard variable capture.
- The work is entirely at typing time: signature elaboration (insert env params), body rewrite (spec-call → env-param indirection), call-site rewrite (insert resolved env arg).
- Each codegen target maps cleanly: Rust emits env as explicit param (or monos away if T is fully ground); Scala emits `using`; Lua emits a positional arg; C++ emits a constructor argument.
- The mental model is exactly what Scala / Lean / Haskell users already know — no new abstractions to teach.
- **Conditional / compositional instances come for free**. Anthill's SLD resolution is exactly Lean's instance synthesis. `fact Eq[T = List[T = ?A]] :- Eq[T = ?A]` is `instance [Eq T] : Eq (List T)`. The KB is the instance database; resolution at the call site is just a query.

No new runtime machinery. No frame-level env state. No side-table lookup. The interpreter doesn't need to know that dispatch happened — it just sees a `Value::Entity` arg flow into a function and the function calling methods on it.

The alternatives:

**Plan D (side-table dispatch)** is what I originally drafted as the "Haskell/Scala-style" path. It's strictly worse than P: it invents new runtime machinery (frame env state, side-table lookups) to achieve what P achieves with existing primitives (regular arg passing, regular dispatch on entity values). No mainstream language uses D as its primary materialization. Skip it.

**Plan M (Rust + C++ style)** is cleaner for codegen but:
- Defeats hash-consing for generic specs.
- Explodes the term store on stdlib-heavy projects (every Eq/Ordered/Numeric instance gets its own clones of derived methods, plus every conditional instance over Pair/List/Option/Tuple gets cloned per concrete combo).
- Requires explicit cycle-breaking for recursive instances (`F[T = F[T = ...]]`).
- **Breaks down on monad transformer stacks.** `StateT[S, ExceptT[E, M]]` style abstractions clone bodies per stack level × per type-arg combo — exponential. Rust's ecosystem reflects this: the monad-transformer pattern, ubiquitous in Haskell and natural in Lean, is rare in Rust precisely because the mono cost shape is wrong.
- Doesn't compose well with conditional instances at scale — Lean's experience here is instructive: GHC and Lean both default to dict-passing at runtime even though they have access to LLVM specialization.

Plan E (explicit-module / functor style, OCaml-inspired) is orthogonal to M/D/H. Worth considering as a layer on top of D for cases where the user wants explicit instantiation visible at the source level. Could be added later as syntax sugar.

### Why parameter insertion is the right level of abstraction

Three mainstream languages converge on this technique:

- **Scala 3**: `using` clauses are syntactic sugar for explicit parameters. After elaboration, the IR has the env as a regular function arg. The JVM runtime does not know about `using`.
- **Haskell GHC**: type-class constraints (`Show a =>`) compile to dictionary parameters. The runtime sees regular function args; class methods are field projections on the dict.
- **Lean 4**: `[A T]` instance args elaborate to explicit parameters. The runtime carries instance values; instance methods are field projections.

Three different language designs, one materialization technique. The reason is the same in each: **the env IS a value at runtime**. There's no need for a separate "environment" abstraction at the runtime level — values flow through arg-passing, fields are accessed normally, closures capture by reference. The runtime stays minimal.

Anthill's situation maps onto this directly: a resolved instance is a sort-tagged value (`Value::Entity { functor: <impl_sort>, ... }`). Anthill's eval already dispatches operations on entity values via `OperationInfo` lookup keyed on the value's functor. Plan P just leverages the existing dispatch mechanism by putting envs into the regular value flow.

Plan D (side-table + frame env) would invent new machinery to do what plan P does with existing primitives. There's no upside.

## Open questions

- **Environment representation in D**: linked list of `(spec, impl, args)` triples? Hash-consed for equality? Affects per-frame cost and side-table key cost.
- **Eager vs lazy population in D**: eager simpler, lazy bounded by use.
- **Default-body specialization**: when does a default body get its rewrites? Per-impl at fact-load, per-call-site at use time, or pre-computed?
- **Phantom-param optimization**: detect unused params and dedup environment keys.
- **Coherence resolution**: per-bound priority table, or a single project-wide priority? OCaml has explicit ordering via module application; Scala has implicit-resolution rules.
- **Interaction with proposal 030 (specialization witnesses)**: witnesses reference (body, env) tuples in D, individual specialized bodies in M.

## Migration path from current state

Whichever plan we pick, the first phase is model-independent:

1. **WI-218 soundness patch** — return `Deferred` for `EnvOpen` calls. Generic bodies become unsound-but-explicit (clear error) instead of unsound-and-silent (current state).
2. **CallKind classification** — populate `dispatch_kind: HashMap<TermId, CallKind>` at typing time. Required by both M and D.
3. **Pick M, D, or H** — based on benchmark on real workloads (stdlib's Eq/Ordered/Numeric chains, future server-side query workloads, the cmd_X port).
4. **Implement** the chosen model.
5. **Re-port** generic bodies that hit WI-218's limitation once the chosen model is in.

Steps 1 and 2 land independently of the M/D/H decision. They're worth doing soon; they fix the soundness bug and prepare the infrastructure for whichever materialization we pick.

## Soundness invariants (any plan)

1. **No silent dispatch**: every `apply` term whose `fn` is a spec op either gets resolved at typing time (EnvFullyPinned) or at the outer instantiation site (EnvOpen, after env materialization), or is rejected with a clear diagnostic.
2. **Static dispatch preserved**: every dispatched call's resolution is known at compile/load time. The eval's per-call lookup just reads a precomputed answer.
3. **Coherence at outermost site**: ambiguity in `requires` chains is rejected at the instantiation that introduces the choice, with the user-visible context to fix it.

## Acceptance for the design (this doc)

- This doc lands as a brainstorming reference.
- A new WI is filed for the WI-218 soundness patch (model-independent).
- A separate WI is filed for CallKind classification (model-independent).
- A design decision is made on M/D/H (plus possibly E), with rationale recorded as an addendum to this doc.
- The chosen-plan WI(s) are filed.

The implementation acceptance lives in the per-phase WIs.
