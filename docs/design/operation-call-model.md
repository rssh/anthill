# The operation-call model

## Status: Decision (post-brainstorm)

## Tracks: WI-204 (port cmd_X), WI-218 (initial static-dispatch rewrite landed; soundness patch pending — see Implementation roadmap), WI-210 (spec/impl call-site dispatch)

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

### Glossary — disambiguating overloaded terms

The word "requirements" is used at four distinct levels of the system. To avoid confusion, the doc uses these qualified forms when the level matters:

| Term | Level | Meaning |
|---|---|---|
| **`Sort.requires`** | source | The user-written `requires X` declarations on a sort. Plural reading: a list of source-level constraint declarations. |
| **`Op.requirements`** | typer metadata | The transitive closure of `SortGoal`s the op's body needs (computed by the typer; see Op.requirements computation). Positional list, declaration-order. |
| **`apply_within(..., requirements = [...])`** | IR (post-elaboration) | The expressions that evaluate to the callee's `frame.requirements` slot at runtime. |
| **`frame.requirements`** | runtime | The actual `RequirementHandle` vector populated when a frame is pushed. Read by `requirement_at_current(i)`. |

Whenever the word "requirements" appears unqualified in this doc, context makes the level clear; in cross-section references, the qualified form is used.

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

`requirements` is a list of expressions (each evaluating to a `Value::Requirement(handle)` at runtime). The grammar of allowed source expressions:

```
req_source ::= requirement_at_current(j)                    -- frame slot
            | requirement_at_sort(req_source, k)             -- projection chain
            | construct_requirement(impl, [req_source ...])  -- nested construction
            | const_requirement(symbol)                      -- load-time-constant ref to a registered impl
```

- **`requirement_at_current(j)`** — reads the enclosing frame's slot j. Used when the construction site has the needed dep already in its requirements scope.
- **`requirement_at_sort(req_source, k)`** — projects from a chain. Used at dispatch sites where sub-deps live inside the dispatching value.
- **Nested `construct_requirement(...)`** — used when the typer has resolved a sub-impl at this construction site (typical for conditional instances chains).
- **`const_requirement(symbol)`** — a reference to a globally-registered impl (e.g., a non-conditional `fact Eq[T = Int]` resolves to a single canonical IntEq value). At runtime this materializes as a single shared arena slot, identified by the symbol; only allocated lazily on first use.

The typer at the construction site walks the impl's `requirements` (its transitive closure) and emits one expression per slot, choosing the most direct source from the construction's available scope.

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
- Each slot of `requirements` is sourced from one of:
  - **The dispatching value's bundle** — for deps the impl declared as part of its sort-level `requires`: `requirement_at_sort(requirement_at_current(i), k)`.
  - **The caller's frame** — for deps that aren't covered by the dispatching value's bundle. In v0 this only happens for cross-sort deps that the body discovered (e.g., a body calls `C.foo` where C is in `Sort.requires` of the enclosing sort but not of the dispatched impl). In a future per-op-requires extension, op-level deps would also source here.

Worked example (using only sort-level requires, the v0 case):

```anthill
sort B[T]
  requires Eq[T]
  requires Ordered[T]
  op cmp(a: T, b: T) -> Int
end
```

`cmp`'s `requirements = [Eq[T], Ordered[T]]` (declaration order). Dispatching `cmp(x, y)` through a `B[T]` requirement value at caller's slot 0:

```
apply_within(
  fn   = requirement_at_current(0, "cmp"),
  args = [x, y],
  requirements = [
    requirement_at_sort(requirement_at_current(0), 0),   -- Eq[T] from B's bundle
    requirement_at_sort(requirement_at_current(0), 1),   -- Ordered[T] from B's bundle
  ]
)
```

The runtime then pushes a new frame with `frame.requirements = [<Eq requirement>, <Ordered requirement>]`, bound positionally per `cmp`'s `requirements` order.

> **Future extension (out of v0 scope)**: per-operation `requires` clauses (e.g., `op bar[U](u: U) requires Ord[U]`) would mix sort-level and op-level deps in `cmp`'s requirements list. The op-level slot would source from the caller's frame (`requirement_at_current(j)`) rather than from the dispatching value's bundle. Mechanism is the same; the only difference is where the slot's source comes from. Per-op requires is listed in "Out of scope" — see that section.

A dispatch site has `requirements = []` only when the callee is a **leaf op** with no deps — e.g., `IntEq.eq`, where IntEq's body uses nothing else. Realistic generic ops with sort-level requires (e.g., `Eq[List[X]]`'s eq, `cmp` above) always have at least one entry.

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

When `apply_within(fn = requirement_at_current(0, "eq"), args = [x, y], requirements = E)` reduces, the eval performs (in order):

1. **Resolve the impl symbol** — read `frame.requirements[0]` → the IntEq requirement value V; look up `<V.functor>.eq` → IntEq.eq's impl symbol. This step is the dispatch lookup. It happens **first** because steps 2 and 3 are driven by the impl's signature (param symbols, expected requirements length).
2. **Evaluate the apply's `requirements` slot** (`E`) via AwaitState. `E`'s entries may include `requirement_at_sort(requirement_at_current(0), k)` projections that themselves read into V. Each entry reduces to a `Value::Requirement(handle)` and is buffered.
3. **Evaluate `args`** via AwaitState, buffering Values.
4. **Push new frame**:
   - `locals` = zip(impl.params, evaluated args)
   - `requirements` = evaluated `E`        ← always from the apply's requirements slot
   - `expr` = impl body

(Step 1 is purely a lookup that doesn't reduce sub-expressions; it doesn't conflict with the AwaitState ordering in steps 2-3. The "Eval mechanics: AwaitState with requirements" section below details how steps 2-3 interleave under the unified `ApplyWithin` AwaitState variant.)

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

Three requirement values constructed, chained — **no Self entry**:
- `env_LLI` (functor=EqList, requirements=[env_LI])
- `env_LI` (functor=EqList, requirements=[env_I])
- `env_I` (functor=IntEq, requirements=[])

Each level's `requirements` references only its already-constructed inner level. The chain depth equals the nesting depth of the type. **No cycles** — the arena's refcount alone cleans up the chain when the outermost reference drops.

### No-cycles policy: how Self is handled

A naive design would put a Self-handle in each conditional impl's `requirements` so the body could recursively dispatch via `requirement_at_current(self_slot, "eq")`. That would create a refcount cycle (env_LX.requirements[Self_slot] = env_LX itself), and refcounting alone would never free the chain.

The design avoids this entirely:

- **Impl-side self-recursion** (e.g., `EqList.eq` recursing on the tail of a List) → emit a **direct call by impl op name** (form (1)): `apply_within(fn = EqList.eq, args = [rest_xs, rest_ys], requirements = [requirement_at_current(0)])`. The recursive frame's `requirements` is forwarded from the current frame; no Self in the requirement value's bundled list. See Examples doc, Example 7 and Example 8.

- **Spec default body needing the dispatching impl** (e.g., `Eq.neq`'s default calling `eq`) → caller passes the impl requirement value into the body's `frame.requirements[0]` and the body dispatches via `requirement_at_current(0, "eq")`. The impl requirement value itself isn't self-referential — IntEq's bundled requirements are its own deps (Numeric, Show), not IntEq itself. See Examples doc, Example 2.

Under this discipline, every entry in a `RequirementSlot.requirements` references only earlier-constructed slots — strictly outward, never inward. Plain refcount cleans up correctly, no cycle detector or weak references required.

Mutually recursive default bodies (e.g., `IntEq.eq` calling `Eq.neq` which calls `eq`) are handled the same way: `IntEq.eq`'s body is invoked through some caller's apply with `requirements = [<IntEq value>]`; if that body calls `Eq.neq` through `requirement_at_current(0, "neq")`, the IntEq value is just **passed forward** in the next call's requirements slot — not stored inside any other requirement value's bundled list. So no cycle arises from mutual recursion either.

**Same shape applies to non-conditional impls too**:

```anthill
sort IntEq
  fact Eq[T = Int]
  requires Numeric[T = Int]
  requires Show[T = Int]
  operation eq(a, b) = ...      -- body uses add() and show()
end
```

`IntEq.eq`'s requirements = [Numeric[T=Int], Show[T=Int]] — the explicit requires only. No Self entry. If the body recurses on `eq` directly, that's a direct call to `IntEq.eq` (form (1)).

See "Requirement values carry their own sub-requirements" below in the IR section.

### Op.requirements computation

For each operation, `requirements` is a **list** (positional, declaration-order) of `SortGoal` entries — see Resolution section for the type. Two contributions:

```
op.requirements (set view, before ordering) =
    direct:     { goal_for(callee.spec_sort, callee.type_args)
                  | callee in body, callee is a spec op }
  ∪ transitive: ⋃ { substitute(other_op.requirements, callee.subst_at_callsite)
                    | other_op in body, callee is in this sort or another }
```

**Substitution**: when calling `other_op` with type-args `subst`, that callee's required goals get `subst` applied before unioning into the caller's requirements. This is what makes `B.bar` calling `C.foo[T = Int]` add `Eq[T = Int]` (not `Eq[T = T]`) to B.bar's requirements.

**Ordering**: the set above is then **ordered by appearance in source** — for the sort's own `requires` clauses, declaration order applies; for goals discovered transitively, the order is the depth-first traversal of the body in source order. Result: a stable, deterministic positional list.

**Mutual recursion → fixed-point**: ops that recurse on each other (or via a cycle) form a strongly-connected component. The fixed-point of the equation above stabilizes (the set is monotone — only grows — and bounded by the union of all sorts' `requires` reachable from the SCC). Termination is guaranteed by monotonicity over a finite lattice.

**Implementation choices**:

- **Eager**: pre-pass walks per-sort call graphs, computes SCCs, runs fixed-point per SCC. Output: per-op `requirements` map across all loaded sorts. Memoizable.
- **Demand-driven**: when typing a body's call, recursively type the callee's body first; memoize. Cycle detection for mutual recursion (push the op-id on a stack; if a recursive call loops back, treat the as-yet-unfinished computation as the empty set and let the fixed-point absorb the additions on the way back up).

Both produce the same result. Lean's elaborator and GHC's constraint inference both do this (eagerly).

### Defer-to-requirement detection

The call-rewrite classification (Direct / Pin-now / Defer-to-requirement) needs a precise predicate. For a call `op_call(args)` with type-args `subst` at the call site:

```
classify(call):
    if op_call.target is already a concrete impl op symbol:
        return Direct

    # op_call.target is a spec op symbol; needs resolution.
    goal = (op_call.spec_sort, subst)

    if goal contains any free type-variable that's an open type-param of the enclosing scope:
        return DeferToRequirement   # OPEN-T trigger

    if op_call.spec_sort is in Sort.requires(enclosing_sort) for some matching binding:
        return DeferToRequirement   # OPEN-BOUND trigger
        # (we have a slot in frame.requirements that holds the right impl;
        #  use it instead of resolving statically)

    # Otherwise the goal is fully ground and not via requires — resolve to the impl now.
    return PinNow(resolve(goal, scope))
```

Both triggers (open-T and open-bound) must be checked; either one fires Defer-to-requirement. The open-bound trigger is what was missing in WI-218's original implementation — a call's type-args might be ground (e.g., `T = Int`), but if the dispatching path comes through `requires Eq[T]`, the impl to invoke depends on which env the caller passed in, not on the static type. Pin-now would silently mis-rewrite to a single impl; Defer-to-requirement is correct.

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

Instance synthesis is an SLD query over `SortProvidesInfo` facts. Conditional instances (`fact Spec[…] :- subgoals`) are clauses with bodies; resolution composes via existing SLD machinery.

### The `resolve` function — interface and contract

```
resolve(goal: SortGoal, scope: ResolutionScope) -> ResolutionResult

where:
  SortGoal           = (spec_sort: Symbol, type_args: Substitution)
  ResolutionScope    = (sort: SortId, subst: Substitution, available_requires: Vec<SortGoal>)
  ResolutionResult   = ResolvedTree | NoMatch | Ambiguous(Vec<ResolvedTree>) | Cyclic

  ResolvedTree       = leaf:    { impl: Symbol, type_args: Substitution }
                     | conditional: { impl: Symbol, type_args: Substitution, sub_resolutions: Vec<ResolvedTree> }
                     | from_scope:  { scope_index: usize }    // matched a scope-local available_require
```

- **`goal`** — the spec sort instance to resolve (e.g., `Eq[T = List[Int]]`).
- **`scope`** — the calling context: which sort we're resolving inside, its substitution, and what `requires` declarations are already in scope (for callers that have them — e.g., a generic body in sort B with `requires Eq[T]` has `Eq[T = T]` as an available_require at scope_index 0).
- **`ResolvedTree`** — the recursively-resolved chain. A `leaf` is a non-conditional impl; a `conditional` is an impl whose `:-` body produces sub-goals each resolved; `from_scope` means the goal matched something already in `available_requires` (no new construction needed).

### Algorithm

```
fn resolve(goal, scope):
    # Step 1 — try to match an available_require in scope (free).
    for (i, ar) in scope.available_requires.iter().enumerate():
        if unify(goal, ar):
            return from_scope { scope_index: i }

    # Step 2 — search SortProvidesInfo for impls whose head unifies with goal.
    candidates = sortprovidesinfo_lookup(goal.spec_sort, goal.type_args)
    matches = []
    for c in candidates:
        subst = unify(c.head_pattern, goal)
        if subst is not None:
            matches.append((c, subst))

    if matches.is_empty(): return NoMatch
    if matches.len() > 1:
        # Step 3 — coherence resolution. See "Coherence" subsection.
        chosen = pick_highest_priority(matches)  # rejects if priorities tie
        if chosen is None: return Ambiguous(matches.map(|m| build_tree(m, scope)))
    else:
        chosen = matches[0]

    # Step 4 — for conditional impls, recursively resolve the :- subgoals.
    sub_resolutions = []
    for subgoal in chosen.impl.requires_pattern_substituted(chosen.subst):
        # Cycle check — keep a stack of in-progress goals; reject if subgoal recurs.
        if subgoal in stack: return Cyclic
        sub = resolve(subgoal, scope)
        if sub is error: propagate up
        sub_resolutions.append(sub)
    return ResolvedTree::conditional { impl: chosen.impl, type_args: chosen.subst, sub_resolutions }
```

Output `ResolvedTree` is the direct input to the requirement-insertion pass: each node becomes either a `from_scope` reference (`requirement_at_current(i)` or a chain of `requirement_at_sort` from one) or a `construct_requirement(impl, [...])` term whose nested args are themselves emitted from the sub_resolutions.

### Termination — bounded recursion

Conditional instance bodies can in principle recurse forever (`Eq[F[T]] :- Eq[F[T]]`). The cycle check above (the in-progress `stack`) makes resolution terminate, but it's pessimistic: it rejects ill-founded chains rather than trying to find a structural decrease. v0 rejects cyclic resolution; that's enough to stop infinite loops without sophisticated decreasing-measure analysis. (Compare with Haskell's `UndecidableInstances`-protected lookups — same conservative principle.)

The SLD search itself is bounded by the size of the goal's term: each conditional instance's `:-` subgoals must be **structurally smaller** than the head (not enforced at v0, but a future strengthening would add this check, à la Haskell's `Paterson conditions`). For now, cycle detection on the stack is the only termination protection.

### Coherence

When step 2 finds multiple candidates, coherence picks among them or rejects:

- **Priority-based**: each `fact Spec[...]` may carry an explicit priority annotation (future surface syntax; not v0). Higher priority wins.
- **Specificity-based**: a more-specific instance head (fewer free variables) wins over a more general one (`fact Eq[T = List[Int]]` beats `fact Eq[T = List[T = ?A]]` for the goal `Eq[List[Int]]`). Standard subsumption ordering on patterns.
- **Reject-as-ambiguous**: if neither rule disambiguates, return `Ambiguous`. The typer rejects the program with a diagnostic listing all candidates.

Coherence at the **diamond join point** (caller D requires B and C, both with `requires A`): `resolve` is called twice — once with `goal = A[T_B]` for the B slot, once with `goal = A[T_C]` for the C slot. If the two resolved trees produce the same `ResolvedTree::leaf { impl: IntA, ... }` for the same type, they unify trivially (D supplies one IntA env). If they pick different impls (because D has `fact A[T = Int]` resolving differently in different scopes), the typer rejects with an "incoherent diamond" diagnostic. v0's rule: each goal independently resolves; coherence is enforced at D's load time by checking that all uses of A within D resolve consistently.

### Error reporting

- `NoMatch`: "no impl provides Eq[List[Int]] in scope; add `fact Eq[T = List[Int]] :- ...` or `requires Eq[T = List[Int]]`."
- `Ambiguous(candidates)`: "Eq[List[Int]] is ambiguous: matches IntListEq, GenericListEq[T=Int]. Disambiguate with priority annotation."
- `Cyclic`: "instance resolution for Eq[F[T]] is cyclic: F[T]'s impl requires Eq[F[T]] which requires Eq[F[T]] which..."

Each diagnostic should point to the source position of the ambiguity (the call site or `requires` declaration that introduced the open type-arg).

## Effects and requirements

Anthill operations can carry effect annotations (`effects (Modify[store])`, etc.). Specs declare an **effect upper bound** that any impl must satisfy. The interaction with requirements has three rules:

1. **Spec / impl effect compatibility**: an impl's `effects` must be a subset of the spec's declared effects (`impl.effects ⊆ spec.effects`). Validated at impl-load time, independently of requirement resolution.

2. **Defer-to-requirement call effects**: when a caller dispatches `requirement_at_current(i, "op")`, the call's effect contribution is the **spec's effect upper bound**, not the dispatched impl's specific effects. Reason: dynamic dispatch — the typer doesn't know which impl will be selected, so it has to assume the worst case. Conservative but sound.

3. **Pin-now call effects**: when the typer statically resolves a call to a specific impl (the Pin-now case), the call's effect contribution is **the impl's specific effects** (precise). This is one of Pin-now's wins over Defer-to-requirement.

4. **Default body effect inheritance**: a spec default body (e.g., `Eq.neq`'s body calling `eq`) is type-checked at the spec level using the **spec's effect upper bound** for the called spec ops. The default body's effect signature is fixed at the spec-declaration site. When inherited by an impl, the body's effects don't tighten: the impl pays the upper-bound cost in exchange for not re-typing the default body per impl.

**Effect parameters in `requires` is out of scope for v0.** Anthill's effect system supports polymorphic effects (`sort E = ?`), and one could imagine `requires E[some_effect]` carrying an effect-parameterized constraint. v0 sidesteps this — `requires` clauses constrain only on type sorts, not on effect sorts. Future work would integrate effect-parameterized requirements with the resolution machinery; the design above doesn't preclude it but doesn't define it either.

## Runtime: frame, requirement value, closure

```rust
struct Frame {
    expr: TermId,
    locals:   SmallVec<[(Symbol, Value); 4]>,
    requirements:  SmallVec<[RequirementHandle; 2]>,  // available during this body's execution
    awaiting: Option<AwaitState>,
    ...
}

// Regular Value::Entity is UNCHANGED — no requirements field added.
// Requirement values live in a separate arena (RequirementArena), accessed via Value::Requirement(handle):
struct RequirementSlot {
    functor:      Symbol,                              // the impl sort name (IntEq, EqList, ...)
    requirements: SmallVec<[RequirementHandle; 1]>,    // bundled deps, refs into the same arena
    refcount:     u32,
}

struct Closure {
    body:            TermId,
    params:          SmallVec<[Symbol; 2]>,
    captured_locals: SmallVec<[(Symbol, Value); 2]>,
    requirements:    SmallVec<[RequirementHandle; 1]>,  // requirement scope to use when invoked
}
```

All three holders (Frame, RequirementSlot, Closure) carry the same kind of data — a positional vector of `RequirementHandle` — at different points in execution.

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

This is the only place the uniform "callee.frame.requirements = caller.apply_within.requirements" rule is overridden — closures must run in the requirement scope where they were *created*, not where they were *invoked*. The call site's `requirements` slot for `ho_apply_within` therefore must be empty: **the typer rejects `ho_apply_within(closure, args, requirements = [<non-empty>])` at typing time.** Closures carry their full requirement scope via `closure.requirements`; a caller has no business injecting more.

This rejection rule keeps the IR honest: any non-empty requirements slot at a closure call site is a typer bug, not a silently-ignored override.

### Why this is the right shape

The unified state makes the requirement / arg distinction explicit through to the eval-state level. Alternative designs (treating requirements as a prefix of args, or splitting into two AwaitState variants) are simpler but lose the structural distinction. The unified state is the cleanest pairing with the IR's three-slot apply.

### A note on hash-consing

Hash-consing applies to two regions of the IR differently — important to understand which:

**1. Inside generic bodies (post-elaboration)** — hash-consing is preserved.

Generic bodies don't bake concrete requirement values into the apply terms; they reference frame slots via `requirement_at_current(i)` and project via `requirement_at_sort(...)`. The same `apply_within(fn = requirement_at_current(0, "eq"), args = [x, y], requirements = [])` term can appear in many generic bodies and share a single TermId — at runtime, each body's frame supplies its own requirements vector populated by the caller. No occurrence-level keying is needed for body interiors.

**2. At concrete call sites (post-elaboration)** — hash-consing is *not* preserved across callers.

A caller's `apply_within(fn = B.bar, args = [s], requirements = [<C2 requirement value>])` carries a literal resolved instance (or `construct_requirement(C2, ...)`) in the requirements slot. Different callers with different resolutions emit different terms. Two callers of `B.bar` resolving to `C1` vs `C2` produce two distinct apply TermIds.

This is unavoidable — the call site's resolution information IS part of the IR, and structurally different resolutions produce structurally different terms. **Term store growth scales with the number of distinct (callsite, resolution) pairs**, not just the number of distinct callsites. Profiling will tell whether interning resolved instances at load time (one canonical `<IntEq value>` per program) is worth it; the design doesn't preclude that as a v1 optimization.

### Side-table alternative (rejected)

If we chose a side-table approach (requirement mapping kept outside the term) instead of separate IR slots, the side-table would need to be keyed on `OccurrenceId` (positional source identity), NOT `TermId`. Reason: hash-consing collapses structurally-identical calls in different bodies (e.g., `foo(x)` in B's body vs C's body) to the same TermId, but those calls live in different requirement scopes. Side-table indexing by TermId can't disambiguate; OccurrenceId can.

The separate-slots approach (this design) avoids the side-table machinery entirely. Generic body interiors share TermIds across instantiations; concrete call sites get distinct TermIds, but that's the same situation any IR with embedded constants has.

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

- **Per-operation requirement declarations** (Lean `[A T]` per-op style). Anthill keeps per-sort `requires` for now; per-op refinement is a future optimization. The Resolution algorithm and dispatch shape extend cleanly when this is added — the only difference is where a slot's source comes from (caller's frame for op-level vs dispatching value's bundle for sort-level). Mechanism is forward-compatible.
- **Explicit instantiation syntax** (OCaml functor style). Future surface-syntax extension if user feedback requests it.
- **`dyn Spec` dynamic dispatch**. Opt-in escape hatch for genuinely runtime-decided cases: heterogeneous collections (`List[?dyn Display]`), existential return types, module-boundary erasure. Without `dyn`, **the typer rejects any program where T loses static identity at a `requires` site**. Diagnostic: "type T is open here but no `requires` covers it; add `requires Display[T]` or use `dyn Display`."
- **Effect-parameterized requirements**. Anthill's effects can be polymorphic (`sort E = ?`); v0's resolution mechanism only handles type-sort goals. `requires E[some_effect]` is conceivable but not built. See "Effects and requirements" section above for the sketch.
- **Higher-kinded instance synthesis with open inner type-params**. The conditional `fact Monad[M = StateT[S = ?S, M = ?M]] :- Monad[M = ?M]` resolves cleanly when called with ground `M = StateT[Int, Option]`. But meta-programs that synthesize StateT chains generically (where `?S` stays open through resolution) require additional rules: either ground all open type-params at the meta-program boundary, or extend resolution with a higher-rank substitution carry. v0 punts: open type-params at resolution time are an error.
- **Recursive instance expansion** (`F[T = F[T = ...]]`). Naturally handled by parameter insertion when the chain is finite at the call site — `Eq[List[List[Int]]]` resolves through three concrete construct_requirement calls. The Resolution algorithm's cycle check rejects ill-founded chains (e.g., `F[T] :- F[T]`). v0 has no support for productive co-inductive resolution.
- **Specialization at the codegen level** (M-style mono on emit for native targets). Each target's codegen pass decides; not a KB-level concern.

## Invariants and rejection rules

These are guarantees the typer / requirement-insertion pass enforces. Programs violating any of these are rejected with a diagnostic.

1. **No silent dispatch**: every spec-op call resolves cleanly via Direct / Pin-now / Defer-to-requirement. A spec op call in a context where neither requirement scope nor static resolution succeeds is an error.
2. **No bodyless dispatch leaks**: a Pin-now or Direct rewrite to a spec op symbol with no body is rejected. (If the typer would emit `apply_within(fn = Eq.eq, ...)` directly because `T = Int` is ground but no `IntEq` impl is registered, the resolution step earlier returns `NoMatch` and the program is rejected.)
3. **No open type-args at resolution**: SLD synthesis at a call site requires the goal's type-args to be ground or to match an `available_require`. Open type-vars at resolution are rejected with "type T is unconstrained at this call site".
4. **Closure call requirements slot must be empty**: `ho_apply_within(closure, args, requirements = [<non-empty>])` is rejected at typing time.
5. **Sort-level requirements coverage**: per-op `requirements` ⊆ Sort.requires + (transitively-derived from body calls outside the sort). If a body uses a goal not covered by the sort's `requires` and not derivable from the called op's spec, error: "sort B's body uses Eq[T] but `requires Eq[T]` isn't declared".
6. **Cross-namespace resolution**: `requires X` resolves against `SortProvidesInfo` records for `X` regardless of namespace; the resolver works on global symbol identity, not namespace-scoped name lookup. Importing the symbol is not required at the source level — `requires` is a constraint, not a name reference.

## References

- `operation-call-model-brainstorm.md` — the exploration this doc resolves.
- `spec-instance-dispatch.md` — WI-210 design.
- WI-218 — current static-dispatch rewrite (needs soundness patch from this design).
- proposal 030 — specialization witnesses; consume requirement metadata for proof records.
- proposal 036 — Domain Store Sorts; the use case driving this design.
