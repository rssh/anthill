# The operation-call model

## Status: Decision (post-brainstorm)

## Tracks: WI-204 (port cmd_X), WI-218 (static-dispatch rewrite shipped — needs follow-up patch), WI-210 (spec/impl call-site dispatch)

## Brainstorm: see `operation-call-model-brainstorm.md` for the exploration. This doc is the resulting design only.

## Decision in one paragraph

An operation declared inside a sort with `requires X` (or whose signature uses the sort's open type-params) is implicitly a function over an X-resolution **environment**. We materialize the environment as **parameter insertion** (Scala `using` / Lean instance arg / GHC dictionary-passing): every operation gains an additional argument `requirements` — the *transitive closure* of requirement values its body needs. The typer adds an explicit requirements slot to apply / ho_apply / constructor / lambda IR forms; requirements become first-class runtime values; the eval gains a `frame.requirements` field structurally parallel to `frame.locals`. No body cloning, no side-table dispatch, no instantiation-context threading.

## One concept: `requirements`

There is **one** structural concept: a positional list of requirement values, in canonical order. It appears in several places — same data, different lifecycle:

| Location | Lifecycle |
|---|---|
| `frame.requirements` | Live during execution. Set when the frame is pushed; read by `requirement_at_current(i)`. |
| `requirement_value.requirements` | Saved on the value at construction. Used later (when the value is dispatched through) as a source for `requirement_at_sort(requirement_value, k)` projections. |
| `closure.requirements` | Saved on the closure at lambda construction. Becomes the new frame's `requirements` on invocation. |
| `apply_within(fn, args, requirements)` | Wire form — list of expressions evaluated at the call to produce the callee's `frame.requirements`. |
| `construct_requirement(impl, requirements)` | Wire form — list of expressions evaluated to bundle into the new requirement value. |

Same data shape (vector of requirement values) at every point. We just call it `requirements`.

## The IR

Four IR variants gain an requirements channel; the requirement-less forms become canonical aliases for `_within(..., requirements=[])` and are eliminated after migration:

```
apply_within(fn, args, requirements)
ho_apply_within(pred, args, requirements)
constructor_within(name, args, requirements)
lambda_within(params, body, requirements)
```

`requirements` is a positional vector of expressions producing requirement values. Each requirement value at runtime is `Value::Requirement(RequirementHandle)` — an arena handle into the RequirementArena (parallel to `Closure`/`Cell`/`Map`). The arena slot stores `{ functor: <impl_sort_name>, requirements: [<sub-handles>] }` — the impl identity plus the deps it was constructed with.

### Two primitives: `requirement_at_current` and `requirement_at_sort`

**IR-level grammar** for requirement-typed expressions:

```
requirement_chain ::= requirement_at_current(i)             -- bottoms out at a frame slot
           | requirement_at_sort(requirement_chain, k)    -- projection chain
```

`requirement_at_sort`'s first argument is restricted to an requirement_chain — it's never an arbitrary expression, a local variable, or a `construct_requirement`. The typer enforces this by construction: requirement-typed positions in the IR are filled only with chains rooted at a frame slot. This makes IR validation and eval mechanically simple — an requirement_chain always evaluates by descending a known path, never by reducing an arbitrary sub-expression first.


The body needs to refer to requirements in two scopes:

- **The body's own `frame.requirements`** — what the caller passed. Use `requirement_at_current(i)`.
- **The bundled `requirements` of an requirement value** — needed at dispatch sites to forward the requirement value's deps onward. Use `requirement_at_sort(requirement_expr, k)`.

```
requirement_at_current(i)                  -- value form: yields frame.requirements[i]
requirement_at_current(i, op_short)        -- fn-position form: dispatch op_short through frame.requirements[i]
requirement_at_sort(requirement_expr, k)         -- value form: yields requirement_expr.requirements[k]
```

`requirement_at_current(i, op_short)` looks up `frame.requirements[i]`, reads its functor, and resolves `<functor>.<op_short>` to the impl op symbol that fn-position will invoke.

`requirement_at_sort(e, k)` is structural projection into an requirement value — getting the k-th component of its bundled `requirements`. It composes: `requirement_at_sort(requirement_at_current(0), 1)` reads the second bundled requirement from the requirement at slot 0 of the current frame.

Where each appears in the IR:

1. **As the fn of an apply** (requirement-dispatched call):
   ```
   apply_within(fn = requirement_at_current(0, "eq"), args = [x, y], requirements = [...])
   ```
   The `requirements` list here is **not** empty in general — see the dispatch section below.

2. **Inside `requirements` slots of an apply** (passing requirements forward):
   ```
   apply_within(fn = B.bar, args = [x], requirements = [requirement_at_current(0), requirement_at_sort(requirement_at_current(1), 0)])
   ```
   This forwards the caller's requirement slot 0 directly, and the 0-th bundled requirement of the caller's requirement slot 1.

3. **Inside `requirements` of a `construct_requirement`** (requirement value construction):
   ```
   construct_requirement(IntEq, requirements = [requirement_at_current(0), requirement_at_sort(requirement_at_current(1), 0)])
   ```
   The constructed requirement value's `requirements[i]` is sourced from a mix of the constructor's frame requirements and projections from those frame requirements.

Together, `requirement_at_current` and `requirement_at_sort` cover every place an requirement-typed expression needs to reach in the IR.

### Construction site

Building an requirement value:

```
construct_requirement(impl_functor, requirements)
```

`requirements` is a list of expressions (each evaluating to an requirement value at runtime). The expressions can be:

- `requirement_at_current(j)` — read the constructor's frame.requirements[j].
- `requirement_at_sort(requirement_at_current(j), k)` — project from the k-th bundled requirement of an requirement value at slot j.
- A load-time-constant reference — for requirements resolvable from project facts.
- A nested `construct_requirement(...)` — for chained sub-requirements.

The typer at the construction site walks the impl's `requirements` (its transitive closure) and emits one expression per slot, choosing the source from the constructor's available requirement scope (frame slots + projections from those + project facts).

### Eval handling for requirement_at_current and requirement_at_sort

When the eval reduces `requirement_at_current(i)` (value form):

```
return frame.requirements[i]
```

When the eval reduces `requirement_at_sort(requirement_expr, k)`:

```
requirement_value = eval(requirement_expr)        // typically requirement_at_current(j), so frame.requirements[j]
return requirement_value.requirements[k]
```

When the eval reduces an apply whose fn is `requirement_at_current(i, op_short)`:

```
requirement_value = frame.requirements[i]
impl_sym  = resolve(requirement_value.functor + "." + op_short)
// then the apply proceeds as if fn were impl_sym
```

The eval's existing apply path consumes `impl_sym` for the OperationInfo lookup and frame push.

### Dispatch site: building the callee's requirements

The runtime rule is **uniform**: the callee's `frame.requirements` always equals the caller's `apply_within.requirements` (evaluated). This holds for direct calls AND requirement-dispatched calls — there is no special "requirements come from the requirement value" runtime path.

What changes between direct and dispatch is the **IR transform** at the call site, i.e. *what* expressions appear in the `requirements` slot. At a dispatch site `apply_within(fn=requirement_at_current(i, op_short), args, requirements)`:

- The callee is op_short of an impl reached through `frame.requirements[i]`.
- The callee's `requirements` is its impl-side transitive closure.
- Each slot of `requirements` is sourced as one of:
  - **Sort-level deps** of the impl — from the requirement value's bundled requirements: `requirement_at_sort(requirement_at_current(i), k)`.
  - **Op-level / extra deps** introduced by the op's own type-params or its body's calls outside the sort — from caller's frame: `requirement_at_current(j)`.

Worked example:

```anthill
sort Foo[T] requires Eq[T]
  op bar[U](u: U) requires Ord[U] -> Bool
end
```

`bar`'s `requirements = [Eq[T], Ord[U]]`. Dispatching `bar(u)` through a `Foo[T]` requirement value at caller's slot 0, with `Ord[U]` at caller's slot 3:

```
apply_within(
  fn   = requirement_at_current(0, "bar"),
  args = [u],
  requirements = [
    requirement_at_sort(requirement_at_current(0), 0),   -- Eq[T] from the Foo requirement value's bundle
    requirement_at_current(3),               -- Ord[U] from caller's frame
  ]
)
```

The runtime then pushes a new frame with `frame.requirements = [<Eq requirement>, <Ord requirement>]`, bound positionally per `bar`'s `requirements` order.

The trivial case where dispatch's `requirements = []` only happens when the callee's `requirements = []` — which means the dispatched op (and the impl's transitive closure for it) has no deps at all. This is rare; the realistic generic case (`eq` through `Eq[List[X]]`, `bar` above, anything with sort-level requires) always has at least one entry.

### Requirement values carry their own requirements

Each impl sort has its own `requirements` (its transitive closure) — the impl's body might use requirements beyond what the spec dictates. `IntEq.eq`'s body might use Numeric and Show, even though `Eq.eq`'s spec doesn't mention them.

Requirement values bundle their impl's resolved requirements at construction time. Representation: a **dedicated `Value::Requirement(RequirementHandle)` variant**, parallel to the existing arena handles (`Closure`, `Cell`, `Map`, `Stream`, `Substitution`):

```rust
pub enum Value {
    // ... existing scalars, Tuple, Entity unchanged ...
    Closure(ClosureHandle),
    Cell(CellHandle),
    Map(MapHandle),
    // ...
    Requirement(RequirementHandle),          // NEW
}

struct RequirementSlot {
    functor: Symbol,                  // the impl sort name (e.g., IntEq, EqList)
    requirements: SmallVec<[RequirementHandle; 1]>,  // bundled deps, refs into the same arena
    refcount: u32,
}
```

Why a separate variant instead of extending `Value::Entity`:

- Regular entities (`Pair`, `cons`, `Some`, every domain entity) don't carry an requirements slot — most values would pay for an unused field.
- Requirement values are constructed via a different IR primitive (`construct_requirement`) and used in different positions (`frame.requirements`, `apply_within.requirements`) — keeping them a distinct variant matches their distinct role.
- Pattern matches the codebase's existing arena scheme: `Closure`/`Cell`/`Map`/`Stream`/`Subst` all live in dedicated arenas with refcounted handles. `Requirement` joins as another arena.
- `RequirementHandle` is `Clone` (bumps refcount) / `Drop` (decrements; frees at zero, cascading drops on bundled handles).

The entries in `RequirementSlot.requirements` are arena handles, not embedded copies. Multiple requirement values can share the same sub-requirement via refcount sharing; underlying requirement data lives in the arena once and is referenced from many places.

### Why no substitution field on RequirementSlot

RequirementSlot carries `functor` and `requirements` — but no type-arg substitution (`?A = Int`, etc.). This is deliberate: **the substitution is consumed at IR-emit time** and never needs to live at runtime.

The reasoning chain:

1. Each call site has fully-substituted type-args at typing time (e.g., `T = List[Int]` is concrete, not a free var).
2. The IR transform resolves the bound (`Eq[List[Int]]`) via SLD synthesis, producing a tree of impls + their sub-bindings.
3. That tree is materialized as nested `construct_requirement` calls in the IR.
4. At runtime, `construct_requirement` allocates arena slots — each (functor, requirements) pair encodes the substitution implicitly in *which* impl was chosen and *which* sub-requirements were bundled.

Two different substitutions at the same source site → two different IR sub-trees → two different chains of arena slots:

| Source-level instantiation | IR | Arena chain |
|---|---|---|
| `Eq[List[Int]]` | `construct_requirement(EqList, [construct_requirement(IntEq, [])])` | `EqList → IntEq` |
| `Eq[List[String]]` | `construct_requirement(EqList, [construct_requirement(StringEq, [])])` | `EqList → StringEq` |

Same functor at the outer level (`EqList`) — same body, shared at runtime. Different bundled inner requirements encode the substitution. The body uses `requirement_at_current(0, "eq")` to dispatch through whatever inner requirement got bundled — `IntEq.eq` vs `StringEq.eq` — without ever consulting a stored substitution.

This matches the dictionary-passing contract: type-class machinery is compile-time, dictionaries are value-level. Anthill requirement values carry no runtime substitution — they ARE the substitution, encoded as a (functor, sub-requirements) pair.

**Phantom type-params** (params that don't appear in any `requires` and don't drive dispatch) would be the only case requiring an explicit substitution. v0 handles them by giving each phantom binding a distinct impl sort (e.g., `UserId : sort` and `PostId : sort` as separate sorts each with `fact Tagged[Tag = …, T = …]`). The phantom binding is encoded in the impl sort's identity — `functor` again. No RequirementSlot field needed.

If reflection (`meta(T)` returning the type as a runtime Term) becomes a feature, an explicit `subst` field on RequirementSlot is the natural extension. Out of scope for v0.

When the typer at a caller's site builds the IntEq requirement value (to pass to a body that has `requires Eq`), it walks `IntEq.requirements` and resolves each from the caller's own requirement scope:

```
construct_requirement(
    impl   = IntEq,
    requirements   = [<resolved Numeric[T=Int]>, <resolved Show[T=Int]>]
)
```

Recursive: if `Numeric[T=Int]` (e.g., IntNum) has its own requirements, IntNum's requirement value bundles them too. Walk terminates at impls with no requires. Sub-requirement values are referenced by multiple constructors as needed; no duplication.

### Putting it together: dispatch end-to-end

When `apply_within(fn = requirement_at_current(0, "eq"), args = [x, y], requirements = E)` reduces:

1. Read `frame.requirements[0]` → the IntEq requirement value V.
2. Resolve `<V.functor>.eq` → IntEq.eq's impl symbol.
3. Evaluate `args` and `E` (via existing AwaitState path; `E`'s entries may include `requirement_at_sort(requirement_at_current(0), k)` projections that read into V).
4. Push new frame:
   - `locals` = zip(impl.params, evaluated args)
   - `requirements`   = evaluated `E`        ← always from the apply's requirements slot
   - `expr`   = impl body

So requirement values are essentially closure-like: each one carries the sort + the resolved requirements needed to invoke its ops. The IR transform at the dispatch site reads from the requirement value (via `requirement_at_sort`) to construct the callee's `requirements` list. The runtime is uniform — `frame.requirements` always comes from `apply_within.requirements`, regardless of whether the call is direct or dispatched.

This matches Haskell dictionaries (records of methods + sub-dictionaries) and Lean instances (instance values carry resolved sub-instances). It's the natural shape once we accept that impls have their own requires.

### Why separate slots and not collapse-into-args

An alternative is to encode requirements as the leading N entries of a regular `args` list (Scala / Lean / GHC style — requirement params are just function parameters). That avoids new IR variants and AwaitState extension at the cost of structural visibility. We chose separate slots because:

- **Reinterpretation independence**: future analyses (re-derive requirements, recompute resolution after a SortProvidesInfo change, swap a requirement at a debug breakpoint) operate on the requirement channel without touching args. With collapsed-into-args, every reinterpretation pass has to re-partition based on op metadata.
- **Codegen flexibility**: each target chooses how to render the requirement channel (Scala `using`, Rust `&impl Trait`, Lua positional). A separate slot in the elaborated IR lets each codegen pass decide its own surface; collapsing pushes that decision earlier.
- **Reflection / proof records**: distinguishing "this is a requirement" from "this is a regular arg" is information proposal-030 specialization witnesses can use; preserving it structurally is cheap.
- **Hash-consing of bodies is preserved either way**: bodies access requirements by position (`requirement_at_current(i)`) or by name in source (`env_A`); they don't bake in concrete requirement values. So generic bodies share TermIds across instantiations regardless of which encoding we pick. The separate-slot encoding doesn't lose this.

## Compile-time representation

Every scope (sort or operation) carries:

```
(sort_id, substitution, Vec<resolved_requires>)
```

- `sort_id` — the enclosing sort.
- `substitution` — the type-arg bindings.
- `Vec<resolved_requires>` — for each `requires` bound, the resolved `(bound_spec, impl_sort)` pair plus the sub-substitution that pins it.

### Body walking is necessary

Bodies can contain qualified calls like `C.foo(x)` where C is a different sort with its own requires. When B's body calls `C.foo`, the call needs a requirement for whatever C requires. But C's requires aren't in B's syntactically-declared `Sort.requires` — they're discovered by walking B's body.

So body walking is necessary to discover the full requirements implied by a sort's operations. Sort-level closure (over explicit `requires` declarations only) is insufficient — it can't surface requirement needs that come from qualified calls inside bodies.

### Impls have their own requires from day one

A spec like `sort Eq { sort T = ?; operation eq(a, b) -> Bool }` declares the protocol. Each impl has its own requires set, derived from its body. **This is not a future case** — it's the ground-zero shape.

The canonical example is `Eq[List[List[X]]]`. The conditional instance `fact Eq[T = List[T = ?A]] :- Eq[T = ?A]` has its `:-` body declaring a subgoal — that's the impl's own requires. The body uses both Self (recursion on `List[?A]`) and the subgoal (inner element's Eq). Two distinct requirements, both resolved at construction time.

For any concrete `Eq[List[List[Int]]]`, the resolution chain is:
- `Eq[List[List[Int]]]` matches conditional with `?A = List[Int]`.
- Subgoal: `Eq[List[Int]]` — matches same conditional with `?A = Int`.
- Subgoal: `Eq[Int]` — matches `IntEq`.

Three requirement values constructed, chained:
- `env_LLI` (functor=EqList, requirements=[<Self ref>, env_LI])
- `env_LI` (functor=EqList, requirements=[<Self ref>, env_I])
- `env_I` (functor=IntEq, requirements=[])

The chain depth equals the nesting depth of the type. Recursion through Self is handled by knot-tying at construction (env_X.requirements[Self_slot] = env_X itself).

Requirement values therefore aren't simple sort tags — they're recursive records carrying the impl's resolved requirement scope. This is the anthill analog of Haskell dictionaries / Lean instances.

**Same shape applies to non-conditional impls too**:

```anthill
sort IntEq
  fact Eq[T = Int]
  requires Numeric[T = Int]
  requires Show[T = Int]
  operation eq(a, b) = ...      -- body uses add() and show()
end
```

`IntEq.eq`'s requirements = [Self?, Numeric[T=Int], Show[T=Int]] — Self if the body recurses, plus the explicit requires. Each requirement value bundles these at construction.

See "Requirement values carry their own sub-requirements" below in the IR section.

### Op.requirements computation

For each operation, `requirements` has two contributions:

```
op.requirements =
    direct:    {requirement_for(callee.spec_sort) | callee in body, callee is a spec op}
  ∪ transitive: ⋃ { other_op.requirements | other_op in body, callee is in this sort or another }
```

Transitive includes calls to ops in the SAME sort (mutual recursion → fixed-point) AND calls to ops in OTHER sorts (qualified `C.foo` calls — pull in C.foo's requirements).

This is real analysis. Two implementation choices:

- **Eager**: explicit pre-pass that walks per-sort call graphs, computes SCCs, runs fixed-point. Output: per-op `requirements` map across all loaded sorts.
- **Demand-driven**: when typing a body's call, recursively type the callee's body first; memoize. Cycle detection for mutual recursion.

Either is valid. Lean's elaborator and GHC's constraint inference both do this (eagerly).

### Sort-level requirements

Once per-op `requirements` is computed, the sort-level full set is the union across the sort's ops. This must equal (or be a subset of) `Sort.requires` declared in source — if a body uses a requirement not in the declared `Sort.requires`, that's an error: "B's body calls C.foo which needs env_Z, but B doesn't declare `requires Z`."

The sort-level union ISN'T a separate analysis output — it's just the union of computed per-op values. The validity check is per-op (each op's requirements ⊆ Sort.requires).

### Two different things to distinguish

(1) **Conditional instance derivation**: `fact Eq[T = List[T = ?A]] :- Eq[T = ?A]` — derive `Eq[List[Int]]` from `Eq[Int]`. Anthill **already has this** via Horn-clause facts; SLD resolution handles it natively. Same mechanism as Haskell's `instance Eq a => Eq [a]`. Not a future feature — first-class today.

(2) **Constraint inference of sort.requires from bodies**: instead of declaring `Sort.requires` source-explicit and validating, let body walking *generate* the sort's requires. The user lists operations and bodies; the typer infers what requirements the sort needs and prints them as the inferred signature. This is what Haskell GHC does for top-level let bindings (`foo x = show (x + 1)` → inferred `(Show a, Num a) => a -> String`).

(1) is about resolution; (2) is about signature inference. Different mechanisms.

For anthill v0: keep `Sort.requires` source-explicit and validate (need body walk for validation regardless). (2) is a possible future direction — less syntax, but less self-documenting (a user reading a sort declaration must walk all bodies to see what's required).

### Runtime is unaffected

The requirements slot of a frame is **already populated** by the caller before the body executes. The body never recomputes anything; it just indexes into `frame.requirements[i]` via `requirement_at_current(i)` (and projects bundled requirements via `requirement_at_sort`). All analysis — including transitive-closure aggregation of `requirements` — is at compile time; runtime is pure lookup.

## Pass structure: typer first, requirement-insertion separate

Two distinct passes — they must not be conflated:

| Pass | Input | Output | What it does |
|---|---|---|---|
| **Typer** | parsed body (uses spec ops by name) | typed body (still uses spec ops, with type info attached) + per-op `requirements` metadata | type-checks; computes transitive `requirements` per op; rejects bodies whose used envs aren't covered by `Sort.requires` |
| **Requirement-insertion** | typed body + `requirements` metadata | rewritten body with `apply_within` / `requirement_at_current` / `construct_requirement` filled in | rewrites every spec-op call into one of the three call-rewrite cases below; constructs requirement values at sites that need them; populates `requirements` slots |

Why separate them:

- **Generated / lifted code in pre-transformed form**. Meta-programming that synthesizes anthill expressions (e.g., a FreeArrows-style transformation that returns Arrow values from each operation) wants to emit code in the original spec-op-name shape and rely on the requirement-insertion pass to elaborate it. If the typer baked the rewrite in, every code generator would have to mimic the rewrite.
- **Alternative elaborations**. A future codegen target may want a different elaboration (different env representation, different dispatch shape, monomorphization). A clean pass boundary means alternatives plug in by replacing the requirement-insertion pass without touching the typer.
- **Inspectability**. The post-typing-pre-insertion form is a stable IR that's easy to read (no `requirement_at_*` clutter); useful for debugging the typer and for any tooling that wants to see "what does the body do, semantically".
- **Pass composition**. Other passes (constant folding, dead code elimination, partial evaluation) can run before or between typer and insertion as their semantics dictate. Forcing them to know about `apply_within` early is unnecessary coupling.

So `apply_within` / `requirement_at_*` / `construct_requirement` are **outputs** of the requirement-insertion pass, not artifacts inherent to typed anthill IR. A typed body with no insertion run on it is still a valid IR — it just hasn't been elaborated yet.

## Call rewrite cases

At requirement-insertion time, the rewrite pass examines each call and chooses one of three actions:

| Case | Trigger | Rewrite |
|---|---|---|
| Direct | fn is already an impl op | leave fn; populate `requirements` from caller's frame matching callee's `requirements` |
| Pin-now | fn is a spec op AND per-call subst is fully ground AND not via `requires` | resolve to impl, rewrite `fn` to that impl symbol; populate `requirements` from caller's frame |
| Defer-to-requirement | fn is a spec op AND per-call subst has a Var that is the body's open type-param OR fn is reached via `requires` | `apply_within(fn = requirement_at_current(i, op_short), args, requirements = [...])` where `i` is the position of the relevant bound. The `requirements` list is populated by the IR transform from a mix of `requirement_at_sort(requirement_at_current(i), k)` (sort-level deps) and `requirement_at_current(j)` (op-level deps), matching the callee's `requirements`. |

The defer-to-requirement case has two triggers (open-T and open-bound). Both must fire — the open-T check alone misses the ground-via-requires case (WI-218's latent bug). See the "Body walking is necessary" section above for why both triggers exist.

In all three cases, the requirements list at the call site is the **full transitive closure** the callee needs. The runtime never builds it from anywhere except the apply's requirements slot.

## Resolution

Instance synthesis is an SLD query over `SortProvidesInfo` facts. Conditional instances (`fact Spec[…] :- subgoals`) are clauses with bodies; resolution composes via existing SLD machinery. This is the Lean-style search-based synthesis, expressed in anthill's existing primitives.

Coherence at the outermost site: ambiguous `requires` resolution rejects at the instantiation that introduces the choice (per WI-210's coherence rules — priority table or reject-as-ambiguous).

## Runtime: frame, requirement value, closure

```rust
struct Frame {
    expr: TermId,
    locals:   SmallVec<[(Symbol, Value); 4]>,
    requirements:     SmallVec<[Value; 2]>,         // available during this body's execution
    awaiting: Option<AwaitState>,
    ...
}

// Requirement values extend the existing entity-value shape with their bundled requirements:
struct EntityValue {
    functor: Symbol,
    pos:     ...,
    named:   ...,
    requirements:    SmallVec<[Value; 1]>,          // present (possibly empty) on every entity value
}

struct Closure {
    body:            TermId,
    params:          SmallVec<[Symbol; 2]>,
    captured_locals: SmallVec<[(Symbol, Value); 2]>,
    requirements:            SmallVec<[Value; 1]>,  // requirement scope to use when invoked
}
```

All three holders carry the same kind of data — a positional vector of requirement values — at different points in execution.

**Where a frame's `requirements` comes from on push** is uniform: it's whatever `apply_within`'s `requirements` slot evaluated to. Slightly different sources at different call shapes:

| Call shape | What populates the apply's requirements slot at the IR level |
|---|---|
| Direct call | Caller emits a list of `requirement_at_current(j)` (and possibly `requirement_at_sort` projections) sourcing from caller's frame requirements. |
| Requirement-dispatched call | Caller emits a mix of `requirement_at_sort(requirement_at_current(i), k)` (deps from the requirement value) and `requirement_at_current(j)` (op-level extras). |
| Higher-order (closure) call | Typically empty; closure's saved `requirements` is used instead — see below. |

**Closures carry their own requirements**: passing a lambda to a higher-order function is the canonical case. The HO function's frame may have a totally different requirement scope than the lambda's creation scope, but when the lambda's body runs, it needs requirements from where it was *created*, not from where it's *invoked*. The closure carries its requirement vector with it. Same mechanism as captured locals; same reason.

For closure invocation specifically, the runtime overrides the uniform rule: `frame.requirements = closure.requirements` (the saved value), regardless of what's in the apply's requirements slot. This is the HO-call exception, and it preserves lexical scoping for closures.

Lambda construction (`lambda_within(params, body, requirements)`): the closure's saved `requirements` is built at construction time from the enclosing frame, with the IR's `requirements` field listing source expressions (each typically `requirement_at_current(j)` or `requirement_at_sort(requirement_at_current(j), k)`) — the same form used at call sites.

## Eval mechanics: AwaitState with requirements

The eval's `AwaitState` continuation mechanism currently handles arg evaluation via something like `ApplyArgs { target, buffered, remaining }`. With requirement-aware IR, the apply path has two sub-evaluation lists (args and requirements).

### Unified `ApplyWithin` state

```rust
enum AwaitState {
    ApplyWithin {
        target: Symbol,
        buffered_args: Vec<Value>,
        remaining_args: Vec<TermId>,
        buffered_requirements: Vec<Value>,
        remaining_requirements: Vec<TermId>,
    },
    ...
}
```

Evaluate requirements first (each entry is typically `requirement_at_current(j)`, `requirement_at_sort(requirement_at_current(j), k)`, or a small `construct_requirement` — all trivial reductions), then evaluate args, then push the new frame:

- `frame.requirements = buffered_requirements`
- `frame.locals` from zipping `buffered_args` with the op's param symbols.

### Per-IR-form behavior

| IR form | Eval-time requirement work |
|---|---|
| `apply_within(fn, args, requirements)` | Eval requirements; eval args; push frame with both populated. Same path for direct and requirement-dispatched calls. |
| `ho_apply_within(closure_expr, args, requirements=[])` | Eval closure; eval args; push frame with `frame.requirements = closure.requirements` (closures override; see below). |
| `constructor_within(name, args, requirements=[])` | requirements always empty; constructors don't dispatch through requirements. IR carries the slot for shape uniformity. |
| `lambda_within(params, body, requirements)` | One-shot: snapshot locals + requirements from enclosing frame (each `requirements` entry is an `requirement_at_current` / `requirement_at_sort` expression evaluated immediately); deliver `Value::Closure`. No new AwaitState needed. |

### Closure invocation: the one runtime exception

For `ho_apply_within(closure_value, args, requirements=...)`:
1. Evaluate the closure expression to a `Value::Closure`.
2. Evaluate args.
3. Push new frame: `frame.requirements = closure.requirements` (NOT the call site's requirements slot).

This is the only place the uniform "callee.frame.requirements = caller.apply_within.requirements" rule is overridden — closures must run in the requirement scope where they were *created*, not where they were *invoked*. The call site's `requirements` slot for closure calls is therefore typically empty; if non-empty (a context override, rare), v0 ignores the override.

### Why this is the right shape

The unified state makes the requirement / arg distinction explicit through to the eval-state level. Alternative designs (treating requirements as a prefix of args, or splitting into two AwaitState variants) are simpler but lose the structural distinction. The unified state is the cleanest pairing with the IR's three-slot apply.

### A note on hash-consing and side-tables

If we chose a side-table approach (requirement mapping kept outside the term) instead of separate IR slots, the side-table would need to be keyed on `OccurrenceId` (positional source identity), NOT `TermId`. Reason: hash-consing collapses structurally-identical calls in different bodies (e.g., `foo(x)` in B's body vs C's body) to the same TermId, but those calls live in different requirement scopes. Side-table indexing by TermId can't disambiguate; OccurrenceId can.

The separate-slots approach (this design) avoids this entirely. Generic bodies don't bake requirement values into the apply term — they carry `requirement_at_current(i)` references that read from the frame's requirement slot at runtime. Same TermId across two bodies is fine because each body's frame has its own requirements populated by the call site. No occurrence-level keying is needed.

This is part of why separate slots beats side-table: simpler indexing scheme, no new positional keys, runtime distinction handled by existing per-frame state.

## Codegen

Each target picks how to render the requirement slot per its idiom:

- **Rust**: emit requirement as explicit `&impl Trait` parameter; or monomorphize on emit (re-substitute, eliminate the requirement param) when T is fully ground at the Rust call site.
- **Scala**: emit `using` clause.
- **C++**: emit extra constructor parameter pack or template-deduced argument.
- **Lua / dynamic targets**: emit positional argument.

The KB stays canonical (one body per spec op); each codegen pass chooses its surface materialization.

## Soundness invariants

1. **No silent dispatch**: every spec-op call either resolves at typing time (Pin-now: rewrite to impl) or has its requirement-arg inserted from the caller's requirement scope (Defer-to-requirement), or fails with a clear diagnostic.
2. **Static dispatch preserved**: every dispatched call's resolution is known at compile/load time. Runtime carries requirement values; it does not synthesize instances.
3. **Coherence at outermost site**: ambiguity in `requires` chains is rejected at the instantiation that introduces the choice.

## Implementation roadmap (WIs to file)

| Phase | Scope |
|-------|-------|
| **WI-218 soundness patch** | In `find_unique_impl_op`, return `Deferred` (skip rewrite) when the call is defer-to-requirement (open-T OR open-bound). Generic bodies become unsound-but-explicit instead of silent-mis-rewrite. ~50 lines. |
| **IR variants** | Introduce `apply_within`, `ho_apply_within`, `constructor_within`, `lambda_within`. Migration: existing terms get rewritten to `_within` form with empty requirements. The eval handles both forms during the migration window; requirement-less forms removed after. |
| **Typer pass** | Type-check bodies (existing infrastructure) + compute per-op `requirements` metadata (transitive closure via body walk + fixed-point). Output: typed bodies still using spec-op names; per-op `requirements` map. |
| **Requirement-insertion pass** (separate from typer) | Walk typed bodies; for each spec-op call, emit one of the three rewrite cases (Direct / Pin-now / Defer-to-requirement). For calls that introduce requirement values, emit `construct_requirement` with the right deps. Output: rewritten body using `apply_within` and `requirement_at_*` primitives. Independent pass — generated code can skip it or substitute alternatives. |
| **Frame `requirements` field** | Add to `Frame` struct; populate on call entry; read for `requirement_at_current(i)` access. |
| **Closure `requirements` field** | Add to `Closure`; snapshot at lambda construction; restore on closure invocation. |
| **Eval entity-dispatch generalization** | `requirement.foo(args)` already works for entity-typed values; verify all spec-op call paths route through this. |
| **Per-target codegen** | Each codegen target adds requirement-slot rendering logic. |

## Out of scope (this design)

- **Per-operation requirement declarations** (Lean `[A T]` per-op style). Anthill keeps per-sort `requires` for now; per-op refinement is a future optimization.
- **Explicit instantiation syntax** (OCaml functor style). Future surface-syntax extension if user feedback requests it.
- **`dyn Spec` dynamic dispatch**. Opt-in escape hatch for genuinely runtime-decided cases (heterogeneous collections of trait objects). Not v0.
- **Recursive instance expansion** (`F[T = F[T = ...]]`). Naturally handled by parameter insertion (requirement passes through recursion as a regular value); no combinatorial explosion. No special handling needed.
- **Specialization at the codegen level** (M-style mono on emit for native targets). Each target's codegen pass decides; not a KB-level concern.

## References

- `operation-call-model-brainstorm.md` — the exploration this doc resolves.
- `spec-instance-dispatch.md` — WI-210 design.
- WI-218 — current static-dispatch rewrite (needs soundness patch from this design).
- proposal 030 — specialization witnesses; consume requirement metadata for proof records.
- proposal 036 — Domain Store Sorts; the use case driving this design.
