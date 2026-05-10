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
given intA: A[Int] = new A[Int] { ... }
```

- **R**: implicit-resolution rules over `given` declarations at the call site.
- **M**: dictionary-passing — body is shared, instance is a runtime value.
- **C**: yes — `given listEq[T](using Eq[T]): Eq[List[T]] = ...`.

### Haskell type classes

```haskell
class Show a where show :: a -> String
instance Show Int where show n = ...
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
instance : A Int where foo := toString
def bar [A T] (x : T) : String := "B" ++ A.foo x
```

- **R**: search-based instance synthesis. The elaborator walks the global instance database with bounded backtracking. Composable, prioritized, with explicit decidability rules.
- **M**: dictionary-passing as the runtime model; native compilation specializes via inlining + LLVM optimization.
- **C**: yes, deeply — `instance [Eq T] : Eq (List T) := ...` is conditional instance derivation. The synthesized environment for the conditional's body has open slots filled by recursive search.

Lean's instance synthesis is **a structured search procedure**. Composable instances mean the runtime environment can be a *chain* of resolved instances built up by search:

```lean
-- Want: Eq (List (Int × String))
-- Search walks: instance [Eq T] [Eq U] : Eq (T × U), instance [Eq T] : Eq (List T)
-- Composes to: Eq Int + Eq String → Eq (Int × String) → Eq (List (Int × String))
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

- M ≈ Rust + C++
- D ≈ Haskell + Scala (using/given)
- H ≈ Lean (dict-passing runtime + LLVM-time partial specialization)

Anthill's `requires` clause is structurally Scala's `using` parameter / Lean's instance argument / OCaml's functor parameter. The runtime semantics can be Rust-style (clone bodies) or Haskell/Scala/Lean-style (thread environments) — same abstract model, different materialization.

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
- Recursive cases (`F[T = F[T = Int]]`) need bounded expansion or explicit `dyn` annotation.

### (D) Side-table dispatch keyed on environment (Scala-`using` / Haskell-class style)

Bodies stay generic. The KB carries:

```
dispatch_rewrites: HashMap<(TermId, Environment), TermId>
```

where `Environment` is the chain of `requires`-resolution decisions and type-arg pins active at the resolution scope. At each apply, the eval consults the side table for the rewritten target.

- Term store grows: O(generic-apply-count × environments) of side-table entries (single TermId pointers each). Bodies stay one TermId per spec op.
- Hash-consing: bodies stay canonical.
- Eval per apply: one HashMap lookup keyed on `(apply_tid, environment)`.
- Codegen for native targets: codegen step has to do its own clone-and-substitute on emit (since target Rust's runtime doesn't have the side table). The codegen runs the same algorithm M would have run at load time, but per-target.
- Recursive cases: lazy population by actual runtime needs; `dyn` becomes optional.

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
  fact Eq[T = Int]
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
sort D { fact B[T = Int]; fact C[T = Int]; ... }
```

D must supply ONE `A[T = Int]` satisfaction that's consistent for both the B-bound and the C-bound. Coherence at the outermost site, transitive across multiple bounds. If D supplies A inconsistently (or doesn't supply at all), error.

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
sort UserId  -- wants Tagged[Tag = User, T = Int]
sort PostId  -- wants Tagged[Tag = Post, T = Int]
```

`Tag` isn't used in operation bodies. M generates two clones differing only in dead `Tag`. D's side table can dedup if it hashes on the parts that affect dispatch. M needs a phantom-detection pass to avoid waste.

### Conditional / per-T defaults

```anthill
fact Display[T = Int]    { ... }       -- explicit
fact Display[T = ?A]     { ... } where ?A : Numeric  -- conditional default
```

The dispatch table has rules with their own bounds. Resolving dispatch becomes a small constraint solve. Not a v0 concern but the model must accommodate.

### Existential / down-cast

```anthill
operation render_any(x: ?dyn Display) -> String = show(x)
```

`?dyn Display` is the "any thing satisfying Display" carrier — vtable territory. Anthill's plan is "`dyn` is opt-in"; this is where it has to be actually implemented.

### Cross-bound interaction (a deeper case)

```anthill
sort B
  sort T = ?
  requires Eq[T = T]       -- B's instances must satisfy Eq for same T
  requires Ordered[T = T]  -- and Ordered too
  operation sort(xs: List[T = T]) -> List[T = T] = ... eq(...) ... lt(...) ...
end
```

`B.sort`'s body uses both `eq` (from Eq bound) and `lt` (from Ordered bound). At an instantiation `D { fact B[T = Int]; fact Eq[T = Int]; fact Ordered[T = Int] }`, the environment has TWO impl picks (one per bound). Resolution must pin both.

This is the diamond pattern's inner mechanism: the environment is a *set* of resolutions, not a single one. M's specialized body has both rewrites baked in; D's side-table entry covers both apply terms, keyed on the same environment.

## Comparison

| Dimension | (M) Body cloning | (D) Side-table | (H) Hybrid |
|-----------|------------------|------------------|----------|
| Closest mainstream analog | Rust, C++ | Haskell, Scala 3 `using` | Lean 4, OCaml functors |
| Term-store growth | O(K × N) — high | O(call-sites × envs) — low | low (KB) + per-target mono on emit |
| Eval per apply | Direct symbol jump | One HashMap lookup | Lookup |
| Hash-consing | Defeated for generics | Preserved | Preserved |
| Anthill KB idiom | Foreign | Native (side tables exist) | Native |
| Codegen Rust target | Natural | Re-mono on emit | Re-mono on emit |
| Codegen Scala target | Natural | Re-mono on emit | Re-mono on emit |
| Codegen Lua / dynamic | Wasteful | Natural | Per-target choice |
| Proof-record specialization | Each spec is a fact | Records reference (body, env) tuples | Records reference (body, env) tuples |
| Reflection | Specialized bodies are normal facts | Reflection threads env | Reflection threads env |
| Eval frame plumbing | None new | Each frame carries an env | Each frame carries an env |
| Recursive instances | Combinatorial explosion at load | Lazy by runtime use | Lazy |
| Diamond / multi-bound | One specialized body bakes in all | Side-table key includes all | Same as D |
| Conditional instances (`fact Spec[…] :- subgoals`) | Each derivation cloned per concrete | One body, side-table per env | One body, side-table per env |
| Reuses anthill's SLD machinery | No — rewrites at typing time | Yes — env construction IS an SLD query | Yes |
| Implementation cost (first cut) | Substantial | Substantial | Substantial |

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

### Plan D — side-table dispatch (Lean 4 / Scala using / Haskell-class style)

1. WI-218 soundness patch (model-independent).
2. CallKind classification (model-independent).
3. Environment representation design (chain of `(spec, impl, args)` triples? Hash-consed? An SLD answer substitution + the resolved ProvidesInfo records?).
4. **Express instance synthesis as an SLD query** over `SortProvidesInfo` facts. Conditional instances (`fact Spec[…] :- subgoals`) become clauses with bodies; resolution composes via existing SLD machinery. This is the Lean-style search-based synthesis.
5. Side-table population at fact load (eager) or on demand (lazy).
6. Eval frame extension: thread environment.
7. Apply-time lookup keyed on `(tid, env)`.
8. Per-target codegen-time monomorphization (where the target needs it — Rust does, Lua doesn't).

### Plan H — hybrid

1. Steps 1–6 of plan D (interpreter primary path).
2. Each codegen target adds its own clone-and-substitute step on emit (if its target language requires it).

## Recommendation (my current lean)

Plan H, with D as the interpreter primary path. Or equivalently: **Lean's runtime model**.

- Term-store stays canonical. Hash-consing keeps working as the load-bearing property of the KB.
- Eval is simple-ish (one extra lookup per apply). Constant-time.
- Each codegen target picks its own materialization. Rust target re-monos on emit; future Lua target keeps dict-passing.
- The mental model is well-trodden (Scala `using`, Haskell type classes, OCaml functors, Lean instances). Easier to explain to new contributors.
- **Conditional / compositional instances come for free**. Anthill's SLD resolution is exactly Lean's instance synthesis. `fact Eq[T = List[T = ?A]] :- Eq[T = ?A]` is `instance [Eq T] : Eq (List T)`. We don't need to build an instance-search engine; we already have one.

The cost is the eval frame plumbing — every frame learns to carry an environment, every closure captures one. This is invasive but bounded; once in place, the model handles all the non-trivial cases (default override, diamond, functor over parametric, conditional instances, mutual recursion) without further machinery.

The alternative — plan M (Rust + C++ style) — is cleaner for codegen but:
- Defeats hash-consing for generic specs.
- Explodes the term store on stdlib-heavy projects (every Eq/Ordered/Numeric instance gets its own clones of derived methods, plus every conditional instance over Pair/List/Option/Tuple gets cloned per concrete combo).
- Requires explicit cycle-breaking for recursive instances (`F[T = F[T = ...]]`).
- Doesn't compose well with conditional instances at scale — Lean's experience here is instructive: GHC and Lean both default to dict-passing at runtime even though they have access to LLVM specialization.

Plan E (explicit-module / functor style, OCaml-inspired) is orthogonal to M/D/H. Worth considering as a layer on top of D for cases where the user wants explicit instantiation visible at the source level. Could be added later as syntax sugar.

### Why Lean's experience is the strongest data point

Of the language analogs above, Lean is the one whose internal model maps most directly to anthill:

- Anthill has SLD resolution; Lean has search-based instance synthesis. **Same machinery.**
- Anthill has hash-consed terms; Lean has elaborated terms with definitional equality. **Same canonicity property.**
- Anthill has facts with bodies (conditional rules); Lean has conditional instances. **Same compositionality.**
- Anthill has the proof-record specialization story (proposal 030); Lean has elaboration-time records of which instance was picked. **Same need for auditable resolution.**

When a language with closely-matching primitives (Lean) has settled on dict-passing-with-specialization-as-optimization (plan H equivalent), that's a strong design signal. Rust's monomorphization works because Rust doesn't have search-based instance synthesis or compositional instances at the same scale — the trade-offs are different there.

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
