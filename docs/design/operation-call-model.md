# The operation-call model

## Status: Design decided — the **names model** (main body) is the agreed target; the implementation still runs the **positional model** (see §"Legacy: the positional model" and §"Implementation roadmap"). Migration pending.

## Tracks: WI-204 (port cmd_X), WI-218 (static-dispatch rewrite), WI-210 (spec/impl call-site dispatch), WI-222–WI-233 (elaboration / dictionary model)

## Brainstorm: see `operation-call-model-brainstorm.md` for the exploration. This doc is the resulting design only.

## Two models: target vs. current implementation

This doc describes **two models** for body-side requirement access, and the relationship between them:

- The **names model** — the main body below. Requirements are extra params with elaborator-synthesized names, accessed via ordinary `var_ref`, exactly like value-level params. **This is the agreed design target.**
- The **positional model** — §"Legacy: the positional model" near the end. Requirements are read positionally via `requirement_at_current(slot)` from a separate `frame.requirements` slot vector. **This is what WI-218–WI-236 actually implemented, and what runs today.**

The names model is the decision, reaffirmed after weighing both from first principles. The deciding factor is closure composition: a positional slot index is meaningless inside a lambda body — which runs in a different frame — whereas a requirement *name* is captured by the closure like any other free variable. Names compose with lexical scoping; positional slots do not.

Requirement *values themselves* (the dictionaries) are a distinct runtime kind in **both** models — their internal sub-instances are positional and nameless — so `requirement_at_sort(dict, k)` and `construct_requirement(impl, [subs])` survive as primitives either way.

**The implementation has not yet migrated.** The main body describes the target; §"Legacy: the positional model" and §"Implementation roadmap" describe the current state and the path.

## Decision in one paragraph

An operation declared inside a sort with `requires X` (or whose signature uses the sort's open type-params) is implicitly a function over an X-resolution **environment**. We materialize the environment as **parameter insertion** (Scala `using` / Lean instance arg / GHC dictionary-passing): every operation gains additional inserted params — one **slot** per top-level requirement (the direct `requires` declarations plus deps discovered by body walking). Each slot is filled with a **tree-shaped dictionary value**: a `(functor, sub_dicts)` pair whose sub-dicts are themselves dictionary values for the impl's own requires-chain. The typer adds an explicit requirements channel to apply / ho_apply / constructor / lambda IR forms; dictionaries become first-class runtime values; the eval gains a `frame.requirements` field structurally parallel to `frame.locals`. No body cloning, no side-table dispatch, no instantiation-context threading.

## One concept: `ResolvedSortNode` (sort instantiation)

Operations are defined on sorts. A **`ResolvedSortNode`** is a sort identity paired with the resolved list of its own requirements — recursively, since each sub-requirement is itself a `ResolvedSortNode`:

```
ResolvedSortNode {
    sort:          Symbol,                   // the impl sort (IntEq, EqList, ...)
    sub_requires:  Vec<ResolvedSortNode>,    // positional; one per the sort's own `requires` clause
}
```

This single tree-shaped concept appears at multiple lifecycles — typer metadata, IR, runtime — under different names:

| Where it appears | Name in code / IR | Lifecycle |
|---|---|---|
| Typer metadata (per-op slot trees) | `RequiresNode` (WI-230) | Compile-time. Computed by body walk + resolution; one tree per top-level slot the op exposes. |
| Runtime value | `Value::Requirement(RequirementHandle)` → `RequirementSlot` in arena | Live during execution. The runtime materialization of a `ResolvedSortNode`. Also called a "sort instantiation" or a "dictionary." |
| Frame slot binding | `frame.requirements[<synthesized_name>]` | Live during execution. Each top-level slot in an op's signature is bound at frame push to one runtime `ResolvedSortNode`. |
| Closure capture | `closure.requirements` | Saved at lambda construction; restored on closure invocation. |
| IR — call site | `apply_within(..., requirements = [<expr>, ...])` | Wire form: list of expressions evaluated to produce `ResolvedSortNode`s for the callee's frame. |
| IR — construction | `construct_requirement(impl, [<expr>, ...])` | Wire form: builds a `ResolvedSortNode` with `sort = impl` and sub-tree from the expression list. |

The two existing code names (`RequiresNode` typer-side, `RequirementSlot` runtime) are the same conceptual entity at two lifecycles. The doc uses **`ResolvedSortNode`** when speaking conceptually and the specific name when speaking about a specific layer.

### Why one concept matters

The same recursive structure governs:

- **Dispatch.** Given a `ResolvedSortNode`, you know which sort's ops to invoke (it's the `sort` field). The interpreter's `apply_within` dispatch rule on a spec-op `fn` reads the dispatching node's `sort` and looks up `sort_ops_table[sort][op_short]` (a direct table lookup; sort symbols carry their ops table).
- **Sub-requirement supply.** When invoking an op on a `ResolvedSortNode`, the callee's frame is populated from the node's `sub_requires` (its impl-side requirements), zipped against the impl's synthesized requirement param names.
- **Construction.** Building a `ResolvedSortNode` (via `construct_requirement` at the IR level) is exactly the operation of *instantiating a sort* with its resolved sub-instances — the SLD resolution chain materialized.

### Two access mechanisms

A body reaches into the `ResolvedSortNode` structure two ways:

- **Top-level slots** (the body's own inserted requirement params) — named by the elaborator, read via ordinary `var_ref(<synthesized_name>)`. Same mechanism as regular value-level params.
- **Sub-nodes inside a `ResolvedSortNode`** — positional and nameless (impl-side `requires` clauses have no source-level names). Projected via `requirement_at_sort(node_expr, k)`.

### Glossary — disambiguating overloaded terms

The word "requirements" is used at several levels of the system; underneath, they all reference instances of the one structural concept (`ResolvedSortNode`). To avoid confusion, the doc uses these qualified forms when the level matters:

| Term | Level | Meaning |
|---|---|---|
| **`Sort.requires`** | source | The user-written `requires X` declarations on a sort. Plural reading: a list of source-level constraint declarations. |
| **`Op.requirements`** | typer metadata | The positional, declaration-order list of top-level slots the op exposes. Each entry is a `RequiresNode` (the typer-side form of `ResolvedSortNode`) — tree-shaped, with sub-requirements nested inside. The elaborator assigns a synthesized symbol name to each top-level entry for body-side `var_ref` access. |
| **`apply_within(..., requirements = [...])`** | IR (post-elaboration) | The expressions that evaluate to the callee's `frame.requirements` slot at runtime. Each expression evaluates to one `ResolvedSortNode`. |
| **`frame.requirements`** | runtime | The `ResolvedSortNode`s populated when a frame is pushed. Stored as `[(Symbol, Value)]` keyed by the elaborator-synthesized names from `Op.requirements`. Read from the body via `var_ref(name)`. |
| **`ResolvedSortNode`** | conceptual | The unifying entity — `(sort, sub_requires)`. Manifests at the levels above. Called `RequiresNode` at typer side, `RequirementSlot` at runtime arena, "dictionary" / "sort instantiation" informally. |

Whenever the word "requirements" appears unqualified in this doc, context makes the level clear; in cross-section references, the qualified form is used.

## The IR

Four IR variants gain a requirements channel; the requirement-less forms become canonical aliases for `_within(..., requirements=[])` and are eliminated after migration:

```
apply_within(fn, args, requirements)
ho_apply_within(pred, args, requirements)
constructor_within(name, args, requirements)
lambda_within(params, body, requirements)
```

`requirements` is a positional vector of expressions producing dictionary values (one per `Op.requirements` entry in the callee). Each dictionary value at runtime is `Value::Requirement(RequirementHandle)` — an arena handle into the RequirementArena (parallel to `Closure`/`Cell`/`Map`). The arena slot stores `{ functor: <impl_sort_name>, requirements: [<sub-handles>] }` — the impl identity plus the deps it was constructed with.

Dictionary values are a distinct runtime kind, not entities — their internal sub-instances are positional and nameless, so they need a dedicated projection primitive (`requirement_at_sort`) that doesn't exist for entities.

### How bodies refer to requirements

Requirement params are **named variables**, exactly like value-level params. The elaborator inserts them into each op's signature with synthesized symbol names; the body reads them via ordinary `var_ref(<name>)`.

A body's inserted requirement params are:

1. **`__req_self_<spec>`** (or just `__req_self`) — by convention, the name of the **first** inserted requirement param. Bound to the `ResolvedSortNode` the body is running under (the dispatching dictionary). "Self" is a naming convention only — there's nothing structurally special about it beyond being the first argument.
2. **One named param per entry in the enclosing op's `requires`-chain** — bound to the corresponding sub-instance of the Self dictionary at frame push. E.g., for an op of a sort declaring `requires Eq[T], requires Ord[T]`, the body has `__req_eq` and `__req_ord` (or similarly-named) params, bound to `Self.sub_requires[0]` and `Self.sub_requires[1]` respectively.

The runtime populates all of these named bindings at frame push by expanding the dispatching dictionary's sub-tree. The body never sees explicit projection — it just uses `var_ref(__req_eq)` for the Eq dictionary, `var_ref(__req_ord)` for the Ord dictionary, etc.

`requirement_at_sort(dict_expr, k)` is *not* used inside bodies in the common case. It appears at the IR level only at **call sites** when the caller needs to project a sub-instance out of a wrapping dictionary to supply as the apply's `requirements[0]`, or inside `construct_requirement` when building a dictionary from sub-pieces.

There is **no** `requirement_at_current(i)` primitive. There are no positional slot reads. Future per-operation `requires` would add more inserted requirement params alongside the sort-level ones; in source surface they might appear as named requirement parameters (e.g., `op foo[...] requires (eq_b: Eq[B])`).

### The one primitive: `requirement_at_sort`

Sub-instances *inside* a dictionary value remain positional and nameless — they correspond to the impl's own `requires` clauses, which have no source-level names. To project the k-th sub-instance out of a dictionary value, the IR has one primitive:

```
requirement_at_sort(dict_expr, k)    -- yields dict_expr.requirements[k]
```

`dict_expr` is any expression evaluating to a `Value::Requirement` — typically `var_ref(<some_req_param>)`, but composes freely (`requirement_at_sort(requirement_at_sort(var_ref(__req_0), 1), 0)` reads a sub-sub-instance).

### Channel cardinality (v0)

For v0 (sort-level `requires` only, no per-operation `requires`), every `apply_within`'s `requirements` channel has **exactly one entry** — the dispatching `ResolvedSortNode` (dictionary):

- **Defer** (`fn` = spec-op qualified symbol): the dict's functor determines which impl is invoked.
- **Pin-now / Direct** (`fn` = impl-op qualified symbol): no runtime dispatch, but the same single-entry shape carries the impl's own dictionary so the callee's frame can be populated from its sub-tree at frame entry.

Short example — Defer dispatch with var_ref to a caller's own requirement param:

```
apply_within(fn = Eq.eq, args = [x, y], requirements = [var_ref(__req_self_eq)])
```

The single dictionary expression can be sourced as:

- **`var_ref(<name>)`** — one of the caller's own inserted requirement params (the typical case).
- **`requirement_at_sort(<dict_expr>, k)`** — the k-th positional sub-instance of a caller-scope dictionary (used when the dispatching dict is one level deep in a wrapping dictionary's sub-tree).
- **`construct_requirement(impl, [...])`** — a literal built at elaboration time when the typer statically resolves the impl tree (Pin-now).

The callee's other inserted slot bindings come from this dictionary's `sub_requires` at frame entry — the impl's `requires` chain materialized as bundled sub-instances.

For complete worked-out scenarios — Self-bound default bodies, conditional impls, monad transformer chains, Pin-now sub-trees — see `operation-call-model-examples.md`.

> **Future extension**: per-operation `requires` clauses would let the channel hold more than one entry (the dispatching dict for the call's spec, plus one per per-op require). The separate-slot encoding scales naturally; see §"Why separate slots and not collapse-into-args" for the trade-off vs. folding into `args`.

### Operation type arguments (proposal 042)

[Proposal 042](../proposals/042-explicit-type-parameters-on-operations.md) introduces operation-level type parameter declarations (`operation foo[T1, T2](...)`) and call-site type argument bindings (`foo[T1 = Int](args)`). These are interpreted as additional entries in the frame, sequenced **after** the sort-specific requirements:

```
frame.requirements = [
  // ---- Sort-specific requirements (existing) ----
  (__req_self_<spec>,        Self_dict),                          // dispatching dictionary
  (<sort-requires[0] name>,  Self_dict.sub_requires[0]),          // expanded sub-instances
  (<sort-requires[1] name>,  Self_dict.sub_requires[1]),
  ...,

  // ---- Operation type arguments (proposal 042) ----
  (T1, type_arg_1),            // op[T1 = X] binds the declared T1 to X for this call
  (T2, type_arg_2),
  ...
]
```

Two channels, deterministic ordering: every sort-level entry from §"How bodies refer to requirements" comes first, then one entry per declared `[T_i]` parameter in declaration order. Mixing produces no name collisions in practice because sort-level entries are synthesized names (`__req_self_<spec>`, etc.) and operation-level type-argument entries use the surface names from the operation's `[T1, T2, ...]` head.

**IR form.** `apply_within` gains an additional positional channel for type arguments:

```
apply_within(fn, args, requirements, type_args)
```

`type_args` is a positional vector of type expressions, one per declared type parameter, in declaration order. Named-form call-site bindings (`foo[T2 = X]`) are reordered to positional during elaboration. Positions the caller leaves unbound (the call relies on inference) carry a typer-supplied entry — either the type the typer inferred, or a fresh logical variable for the resolver to fill at runtime via unification.

**Construction site sources.** `type_args` entries are type-valued expressions, so the source grammar is simpler than `req_source`:

```
type_arg_source ::= type_literal(sort_ref)            -- concrete type bound by the call site (foo[Int](...))
                  | var_ref(name)                     -- forward a caller-scope type parameter
                  | type_at_sort(req_source, name)    -- type-arg projection from a dictionary
```

The `type_at_sort` form lets an op forward a sort-level type parameter into a callee's operation-level slot — necessary when the callee's `[T]` aligns with the caller's enclosing `sort T = ?`.

**Body interpretation.** A body of `operation foo[T](x: T) -> T` references `T` in type position; the typer normalizes those references to `var_ref(T)` against the frame's type-argument entries — the same lookup path as sort-level requirement params, just hitting a different entry by name. The body never distinguishes the two channels; the elaborator separates them only because the population sources differ.

**Closures.** A `lambda_within(...)` constructed inside an operation captures the enclosing `frame.requirements` map whole — both the sort-level entries and the operation type arguments. No new closure machinery for type args; same captured-scope mechanism as requirements.

**Erasure.** Whether `type_args` entries are stripped at codegen depends on the host target. For Rust (proposal 029 forward mapping), most operation-level type parameters erase to nothing — the host's monomorphizer takes over. For SMT-LIB and any backend doing type-driven dispatch at runtime (e.g., `term_as_entity[E]`'s entity-shape selection), the entries must persist. The frame layout is uniform — the design above carries the entries; backends decide what to elide.

**Test fixture** (acceptance for proposal 042 + this design): a synthesized op `operation foo[T](x: T) -> T` with body `x` is called as `foo[Int](42)`. After frame push, the test inspects `frame.requirements` and asserts:

- The sort-level Self entry, if any, occupies the leading positions.
- An entry keyed `T` exists with the type-value for `Int`.
- The order in the frame is sort-level entries first, then `T`.
- A second call `foo[String]("hi")` produces a fresh frame whose `T` entry holds `String` — the two calls do not share `T` (per-call binding, contra sort instantiation).

A negative case: `foo(42)` (no type-arg list, type inferred) produces a `T` entry the typer filled to `Int` via inference; the frame contents are identical to the explicit call.

### Construction site

Building a dictionary value:

```
construct_requirement(impl_functor, requirements)
```

`requirements` is a list of expressions (each evaluating to a `Value::Requirement(handle)` at runtime). The grammar of allowed source expressions:

```
req_source ::= var_ref(name)                                 -- caller-scope requirement param
            | requirement_at_sort(req_source, k)             -- positional projection from a dictionary
            | construct_requirement(impl, [req_source ...])  -- nested construction
            | const_requirement(symbol)                      -- load-time-constant ref to a registered impl
```

- **`var_ref(name)`** — references one of the enclosing scope's requirement params (synthesized by the elaborator from the enclosing op's `Op.requirements`). Used when the construction site has the needed dep already in its requirements scope.
- **`requirement_at_sort(req_source, k)`** — projects the k-th sub-instance out of a dictionary value. Used when sub-deps live inside another dictionary already in scope.
- **Nested `construct_requirement(...)`** — used when the typer has resolved a sub-impl at this construction site (typical for conditional-instance chains).
- **`const_requirement(symbol)`** — a reference to a globally-registered impl (e.g., a non-conditional `fact Eq[T = Int]` resolves to a single canonical IntEq value). At runtime this materializes as a single shared arena slot, identified by the symbol; only allocated lazily on first use.

The typer at the construction site walks the impl's `requirements` (its transitive closure) and emits one expression per slot, choosing the most direct source from the construction's available scope.

### Eval handling for requirement_at_sort and apply_within dispatch

When the eval reduces `requirement_at_sort(dict_expr, k)`:

```
dict_value = eval(dict_expr)        // typically var_ref(<req_name>), so frame.requirements lookup
return dict_value.requirements[k]
```

Body-side requirement reads (`var_ref(<req_name>)`) are the ordinary local-variable lookup path — no new eval logic. The runtime looks up the symbol in `frame.requirements` (or in a unified frame.locals; see Runtime section); both options are runtime layout choices that don't affect the IR or the eval verbs.

When the eval reduces an `apply_within(fn, args, requirements)` (single-entry channel under v0):

```
dict_value = eval(requirements[0])           // the dispatching ResolvedSortNode
if fn is an impl-op symbol (e.g., IntEq.eq):
    impl_sym = fn                            // no dispatch — fn names the impl
else (fn is a spec-op symbol, e.g., Eq.eq):
    impl_sym = sort_ops_table[dict_value.sort][fn.op_short]

push new frame for impl_sym:
    locals       = zip(impl.params, eval(args))
    requirements = bind impl's inserted requirement param names to:
                     [0] dict_value                        (the Self slot)
                     [i+1..] dict_value.sub_requires[i]    (one per impl's `requires`)
```

**Sort symbols carry their own operations table.** Each sort symbol (e.g., `IntEq`, `EqList`) is associated in the KB with a mapping `op_short → impl_op_symbol` recording its declared operations. The dispatch lookup `sort_ops_table[dict_value.sort][fn.op_short]` is a direct table lookup, not a string concatenation + name resolution. (Conceptually equivalent to a C++ vtable / Haskell dictionary's method slot.)

The dispatching dictionary at `requirements[0]` is both:
1. **The dispatch key** for spec-op `fn` — its `sort` field selects which impl's operations table to consult.
2. **The source of the callee's frame requirements** — bound to the callee's Self param, with its sub-tree expanded to the callee's per-`requires` inserted param names.

This is **the** dispatch rule. No fn-position requirement form, no separate dispatch metadata. The single `requirements[0]` entry does both jobs.

### Dispatch site: supplying the dispatching dictionary

The runtime rule is **uniform**: at every `apply_within`, `requirements[0]` is the dispatching `ResolvedSortNode`; the callee's frame is populated from it (Self + sub-tree expansion). This holds for Direct, Pin-now, and Defer alike.

What changes between the three call-rewrite cases is **how the caller sources that single dictionary**:

- **`fn`** — impl-op qualified symbol (`IntEq.eq`) for Direct / Pin-now; spec-op qualified symbol (`Eq.eq`) for Defer.
- **`requirements[0]`** — sourced from the caller's own scope as one of:
  - **`var_ref(<req_param_name>)`** — the caller has the right dictionary already as one of its inserted requirement params.
  - **`requirement_at_sort(var_ref(<req_param_name>), k)`** — the caller has a *wrapping* dictionary whose k-th sub-instance is the right one.
  - **`construct_requirement(impl, [...])`** — the caller's typer resolved the dictionary tree statically (Pin-now sub-tree).

Worked example:

```anthill
sort B[T]
  requires Eq[T]
  requires Ordered[T]
  op cmp(a: T, b: T) -> Int
end
```

In a generic caller `op outer(...) requires B[T]` (the elaborator synthesizes `__req_self_b` for the inserted B-dictionary param), dispatching `cmp(x, y)` becomes:

```
apply_within(
  fn   = B.cmp,                              -- spec-op symbol (Defer)
  args = [x, y],
  requirements = [var_ref(__req_self_b)]     -- the dispatching B-dictionary
)
```

The interpreter sees `fn` is a spec-op, evaluates `requirements[0]` to a `ResolvedSortNode` `V`, reads `V.sort` (some impl of B, e.g. `BImpl`), looks up `sort_ops_table[BImpl][cmp]` → `BImpl.cmp`, and pushes the callee's frame with:

- `locals = [a → x, b → y]`
- `requirements = [__req_self_b → V, __req_eq → V.sub_requires[0], __req_ord → V.sub_requires[1]]`

`BImpl.cmp`'s body uses `var_ref(__req_eq)` and `var_ref(__req_ord)` to access the Eq and Ord dictionaries — they're already named bindings on the frame.

> **Future extension (out of v0 scope)**: per-operation `requires` clauses (e.g., `op bar[U](u: U) requires Ord[U]`) would let the apply's `requirements` channel hold more than one entry — one for the dispatching dict, one per per-op require. Mechanism stays uniform; cardinality grows.

For Pin-now where the impl is statically resolved, the same shape applies — `requirements[0]` is a `construct_requirement` literal:

```
apply_within(
  fn   = BImpl.cmp,                                        -- impl-op symbol (no dispatch)
  args = [x, y],
  requirements = [construct_requirement(BImpl, [           -- statically constructed dict
    construct_requirement(IntEq, []),
    construct_requirement(IntOrdered, [])
  ])]
)
```

`BImpl.cmp`'s frame is populated identically: Self bound to the literal, sub-instances bound from its sub-tree.

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

Same functor at the outer level (`EqList`) — same body, shared at runtime. Different bundled inner requirements encode the substitution. The body uses `apply_within(fn = Eq.eq, ..., requirements = [requirement_at_sort(var_ref(__req_self), 0)])` to dispatch through whatever inner requirement got bundled — `IntEq.eq` vs `StringEq.eq` — without ever consulting a stored substitution.

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

When `apply_within(fn = Eq.eq, args = [x, y], requirements = [E])` reduces (Defer case), the eval performs (in order):

1. **Evaluate `E`** via AwaitState → a single dictionary value `V`. (`E` is typically `var_ref(<req_name>)`, `requirement_at_sort(...)`, or a small `construct_requirement`.)
2. **Evaluate `args`** via AwaitState, buffering Values.
3. **Resolve the impl symbol** — read `V.sort` and look up `sort_ops_table[V.sort][eq]` → the impl-op symbol to invoke. (A direct table lookup, not name resolution; sort symbols carry their own operations table.)
4. **Push new frame**:
   - `locals` = zip(impl.params, evaluated args)
   - `requirements` = `[(Self_Eq, V)] ++ [(impl_req_name_i, V.sub_requires[i]) for i in impl.requires]`
   - `expr` = impl body

For Pin-now / Direct (`fn` is already an impl-op symbol), step 3 is skipped — `impl_sym = fn`. Steps 1, 2, 4 are identical.

So a dictionary is essentially closure-like: each carries the sort identity + the resolved sub-instances needed to invoke its ops. The IR transform at the dispatch site references the dictionary (via `var_ref`, projection, or literal construction) as the single `requirements[0]` entry. The runtime is uniform — `frame.requirements` always comes from expanding `requirements[0]`'s sub-tree, regardless of whether the call is direct or dispatched.

This matches Haskell dictionaries (records of methods + sub-dictionaries) and Lean instances (instance values carry resolved sub-instances). It's the natural shape once we accept that impls have their own requires.

### Why separate slots and not collapse-into-args

An alternative is to encode requirements as the leading N entries of a regular `args` list (Scala / Lean / GHC style — requirement params are just function parameters). That avoids new IR variants and AwaitState extension at the cost of structural visibility. We chose separate slots because:

- **Reinterpretation independence**: future analyses (re-derive requirements, recompute resolution after a SortProvidesInfo change, swap a requirement at a debug breakpoint) operate on the requirement channel without touching args. With collapsed-into-args, every reinterpretation pass has to re-partition based on op metadata.
- **Codegen flexibility**: each target chooses how to render the requirement channel (Scala `using`, Rust `&impl Trait`, Lua positional). A separate slot in the elaborated IR lets each codegen pass decide its own surface; collapsing pushes that decision earlier.
- **Reflection / proof records**: distinguishing "this is a requirement" from "this is a regular arg" is information proposal-030 specialization witnesses can use; preserving it structurally is cheap.
- **Hash-consing of bodies is preserved either way**: bodies access requirements via `var_ref(<synthesized_name>)`; they don't bake in concrete requirement values. So generic bodies share TermIds across instantiations regardless of which encoding we pick. The separate-slot encoding doesn't lose this.

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

A naive design would put a Self-handle in each conditional impl's `requirements` so the body could recursively dispatch via a Self slot. That would create a refcount cycle (env_LX.requirements[Self_slot] = env_LX itself), and refcounting alone would never free the chain.

The design avoids this entirely:

- **Impl-side self-recursion** (e.g., `EqList.eq` recursing on the tail of a List) → emit a **direct call by impl op name**: `apply_within(fn = EqList.eq, args = [rest_xs, rest_ys], requirements = [var_ref(__req_inner_eq)])`. The recursive frame's `requirements` is forwarded from the current frame; no Self in the dictionary's bundled list. See Examples doc, Example 7 and Example 8.

- **Spec default body needing the dispatching impl** (e.g., `Eq.neq`'s default calling `eq`) → caller passes the impl dictionary into the body as one of its requirement params (`__req_self_eq`); the body dispatches via `apply_within(fn = Eq.eq, args = [...], requirements = [var_ref(__req_self_eq)])`. The dictionary itself isn't self-referential — IntEq's bundled requirements are its own deps (Numeric, Show), not IntEq itself. See Examples doc, Example 2.

Under this discipline, every entry in a `RequirementSlot.requirements` references only earlier-constructed slots — strictly outward, never inward. Plain refcount cleans up correctly, no cycle detector or weak references required.

Mutually recursive default bodies (e.g., `IntEq.eq` calling `Eq.neq` which calls `eq`) are handled the same way: `IntEq.eq`'s body is invoked with the IntEq dictionary as a requirement param; if that body calls `Eq.neq`, the IntEq dictionary is just **passed forward** in the next call's requirements slot via `var_ref(<its_param_name>)` — not stored inside any other dictionary's bundled list. So no cycle arises from mutual recursion either.

**Same shape applies to non-conditional impls too**:

```anthill
sort IntEq
  fact Eq[T = Int]
  requires Numeric[T = Int]
  requires Show[T = Int]
  operation eq(a, b) = ...      -- body uses add() and show()
end
```

`IntEq.eq`'s requirements = [Numeric[T=Int], Show[T=Int]] — the explicit requires only. No Self entry. If the body recurses on `eq` directly, that's a Direct apply with `fn = IntEq.eq`.

See "Requirement values carry their own sub-requirements" below in the IR section.

### Op.requirements computation

For each operation, `Op.requirements` is a **`RequiresNode` tree** describing the dispatching dictionary the op runs against. Each node:

```
RequiresNode {
    entry:         RequiresEntry,                  // (spec_sort, type_bindings)
    sub_requires:  Vec<RequiresNode>,              // the impl's own requires — populated when an impl is resolved
}
```

For v0, this is a **single tree** (rooted at the enclosing sort's spec), corresponding to the single dispatching dictionary the op gets at runtime. The elaborator synthesizes named requirement params for the body — one for the root (`__req_self_<spec>`) and one for each entry in the sort's own `requires`-chain (named e.g. `__req_eq`, `__req_ord`).

The tree's structure comes from the sort's declared `requires` chain plus what body walking discovers:

```
op.requirements_tree(sort) =
    RequiresNode {
        entry:        (sort, current_type_args),
        sub_requires: [
            requirements_tree(req_spec) for req_spec in
                Sort.requires(sort) ∪ discovered_from_body(sort)
        ]
    }
```

`discovered_from_body` captures cross-sort calls inside bodies (e.g., `B.bar`'s body calling `C.foo` where C is a separate sort with its own requires). Each discovered spec must already be in `Sort.requires(B)` or this is a coverage-rule violation rejected at typing.

**Substitution**: when computing requirements for a particular type-args binding, the sub-tree's bindings inherit the substitution. E.g., `requirements_tree(B[T = Int])` produces a tree whose Eq sub-node has `T = Int` (not `T = T`).

**Ordering** within `sub_requires`: source declaration order in the sort's `requires` block, then depth-first traversal for body-discovered specs.

**Mutual recursion → cycle break**: if an op's requirements-tree computation visits the same `(sort, bindings)` it's currently computing, the back-edge is recorded but not expanded — a `RequiresNode::CycleBack` variant (or omitted entirely, by the WI-230 design). Termination guaranteed.

**Per-op `requires` (future)**: per-operation `requires` clauses would add additional top-level requirement params to the op's signature alongside Self. The op's runtime would have multiple inserted requirement param names, all populated from corresponding entries in the apply's `requirements` channel.

**Implementation choices**:

- **Eager**: pre-pass walks per-sort call graphs, computes SCCs, runs fixed-point per SCC. Output: per-op requirements-tree map across all loaded sorts. Memoizable. (Current: WI-230's RequiresNode tree, computed eagerly during typing.)
- **Demand-driven**: when typing a body's call, recursively type the callee's body first; memoize. Cycle detection on a stack.

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

The requirements slot of a frame is **already populated** by the caller before the body executes. The body never recomputes anything; it just reads its inserted requirement params via `var_ref` (and projects bundled sub-instances via `requirement_at_sort`). All analysis — including transitive-closure aggregation of `requirements` — is at compile time; runtime is pure lookup.

## Pass structure: typer first, requirement-insertion separate

Two distinct passes — they must not be conflated:

| Pass | Input | Output | What it does |
|---|---|---|---|
| **Typer** | parsed body (uses spec ops by name) | typed body (still uses spec ops, with type info attached) + per-op `requirements` metadata | type-checks; computes transitive `requirements` per op; rejects bodies whose used envs aren't covered by `Sort.requires` |
| **Requirement-insertion** | typed body + `requirements` metadata | rewritten body with `apply_within` / `var_ref` (to inserted req params) / `requirement_at_sort` / `construct_requirement` filled in | rewrites every spec-op call into one of the three call-rewrite cases below; constructs requirement values at sites that need them; populates `requirements` slots |

Why separate them:

- **Generated / lifted code in pre-transformed form**. Meta-programming that synthesizes anthill expressions (e.g., a FreeArrows-style transformation that returns Arrow values from each operation) wants to emit code in the original spec-op-name shape and rely on the requirement-insertion pass to elaborate it. If the typer baked the rewrite in, every code generator would have to mimic the rewrite.
- **Alternative elaborations**. A future codegen target may want a different elaboration (different env representation, different dispatch shape, monomorphization). A clean pass boundary means alternatives plug in by replacing the requirement-insertion pass without touching the typer.
- **Inspectability**. The post-typing-pre-insertion form is a stable IR that's easy to read (no `requirement_at_*` clutter); useful for debugging the typer and for any tooling that wants to see "what does the body do, semantically".
- **Pass composition**. Other passes (constant folding, dead code elimination, partial evaluation) can run before or between typer and insertion as their semantics dictate. Forcing them to know about `apply_within` early is unnecessary coupling.

So `apply_within` / `requirement_at_*` / `construct_requirement` are **outputs** of the requirement-insertion pass, not artifacts inherent to typed anthill IR. A typed body with no insertion run on it is still a valid IR — it just hasn't been elaborated yet.

## Call rewrite cases

At requirement-insertion time, the rewrite pass examines each call and chooses one of three actions:

All three cases emit `apply_within(fn, args, requirements = [<single dict expr>])`. They differ only in `fn` and in how the single dictionary expression is sourced:

| Case | Trigger | `fn` | `requirements[0]` |
|---|---|---|---|
| Direct | fn is already an impl op (e.g., a self-recursive call inside an impl body) | impl-op qn (`EqList.eq`) | `var_ref(<caller's own requirement param>)` — typically forwarding Self |
| Pin-now | fn is a spec op AND per-call subst is fully ground AND not via `requires` | impl-op qn (statically resolved) | `construct_requirement(impl, [...])` — literal tree, statically built |
| Defer-to-requirement | fn is a spec op AND per-call subst has a Var that is the body's open type-param OR fn is reached via `requires` | spec-op qn (`Eq.eq`) | `var_ref(<caller's req param>)` or `requirement_at_sort(<...>, k)` — sources the dispatching dict from caller scope; the interpreter reads the dict's `sort` at runtime and looks up `sort_ops_table[sort][op_short]` for the impl op |

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

Output `ResolvedTree` is the direct input to the requirement-insertion pass: each node becomes either a `from_scope` reference (`var_ref(<inserted_req_name>)` or a chain of `requirement_at_sort` projections from one) or a `construct_requirement(impl, [...])` term whose nested args are themselves emitted from the sub_resolutions.

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

2. **Defer-to-requirement call effects**: when a caller dispatches `apply_within(fn = <spec_op>, ..., requirements = [..., <dict>, ...])`, the call's effect contribution is the **spec's effect upper bound**, not the dispatched impl's specific effects. Reason: dynamic dispatch — the typer doesn't know which impl will be selected at runtime, so it has to assume the worst case. Conservative but sound.

3. **Pin-now call effects**: when the typer statically resolves a call to a specific impl (the Pin-now case), the call's effect contribution is **the impl's specific effects** (precise). This is one of Pin-now's wins over Defer-to-requirement.

4. **Default body effect inheritance**: a spec default body (e.g., `Eq.neq`'s body calling `eq`) is type-checked at the spec level using the **spec's effect upper bound** for the called spec ops. The default body's effect signature is fixed at the spec-declaration site. When inherited by an impl, the body's effects don't tighten: the impl pays the upper-bound cost in exchange for not re-typing the default body per impl.

**Effect parameters in `requires` is out of scope for v0.** Anthill's effect system supports polymorphic effects (`sort E = ?`), and one could imagine `requires E[some_effect]` carrying an effect-parameterized constraint. v0 sidesteps this — `requires` clauses constrain only on type sorts, not on effect sorts. Future work would integrate effect-parameterized requirements with the resolution machinery; the design above doesn't preclude it but doesn't define it either.

## Runtime: frame, requirement value, closure

```rust
struct Frame {
    expr: TermId,
    locals:        SmallVec<[(Symbol, Value); 4]>,  // regular params
    requirements:  SmallVec<[(Symbol, Value); 2]>,  // requirement params (synthesized names → dictionary values)
    awaiting:      Option<AwaitState>,
    ...
}

// Regular Value::Entity is UNCHANGED — no requirements field added.
// Dictionary values live in a separate arena (RequirementArena), accessed via Value::Requirement(handle):
struct RequirementSlot {
    functor:      Symbol,                              // the impl sort name (IntEq, EqList, ...)
    requirements: SmallVec<[RequirementHandle; 1]>,    // bundled deps, refs into the same arena
    refcount:     u32,
}

struct Closure {
    body:            TermId,
    params:          SmallVec<[Symbol; 2]>,
    captured_locals: SmallVec<[(Symbol, Value); 2]>,
    requirements:    SmallVec<[(Symbol, Value); 1]>,  // requirement scope at creation time
}
```

`frame.requirements` is keyed by elaborator-synthesized names — `Self_<spec>` and one name per entry in the impl's `requires`-chain. The body reads either slot (locals or requirements) uniformly via `var_ref(<name>)`. Implementations may merge into a single `frame.locals` map — they're structurally identical; the separate slot is preserved as metadata for codegen / reflection.

The dictionary values themselves (the `Value::Requirement(handle)` payloads) are a distinct runtime kind because their sub-instances are positional/nameless. `RequirementSlot` is a separate arena entry from `Value::Entity`. `requirement_at_sort(dict, k)` is the projection primitive that walks one level of the tree.

**How a frame's `requirements` is populated on push**: the apply's `requirements` channel has one entry (the dispatching `ResolvedSortNode`). The runtime evaluates it, then expands the dict's sub-tree into the callee's named param bindings:

```
dict_value = eval(apply.requirements[0])
frame.requirements = [
  (Self_<spec_name>, dict_value),
  (<impl's requires[0] name>, dict_value.sub_requires[0]),
  (<impl's requires[1] name>, dict_value.sub_requires[1]),
  ...
]
```

Sources for the single `requirements[0]` expression at the IR level:

| Call shape | What goes in `requirements[0]` |
|---|---|
| Direct call (impl-op self-recursion) | `var_ref(<own Self param>)` — forward the current dict. |
| Pin-now (statically resolved impl) | `construct_requirement(impl, [...])` — literal dict, built at elaboration time. |
| Defer-dispatched call | `var_ref(<own req param>)` or `requirement_at_sort(var_ref(<...>), k)` — sources the dispatching dictionary from caller scope. |
| Higher-order (closure) call | Typically empty; closure's saved `requirements` is used instead — see below. |

**Closures carry their own requirements**: passing a lambda to a higher-order function is the canonical case. The HO function's frame may have a totally different requirement scope than the lambda's creation scope, but when the lambda's body runs, it needs requirements from where it was *created*, not from where it's *invoked*. The closure carries its requirement scope with it. Same mechanism as captured locals; same reason.

For closure invocation specifically, the runtime overrides the uniform rule: `frame.requirements = closure.requirements` (the saved value), regardless of what's in the apply's requirements slot. This is the HO-call exception, and it preserves lexical scoping for closures.

Lambda construction (`lambda_within(params, body, requirements)`): the closure's saved `requirements` is built at construction time from the enclosing frame, with the IR's `requirements` field listing source expressions (each typically `var_ref(<enclosing_req_name>)` or `requirement_at_sort(var_ref(<...>), k)`) — the same form used at call sites.

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

Evaluate `requirements[0]` (typically `var_ref(<req_name>)`, `requirement_at_sort(var_ref(<req_name>), k)`, or a small `construct_requirement` — all trivial reductions), then evaluate args, then push the new frame:

- `dict_value` = the evaluated `requirements[0]`
- If `fn` is a spec-op, resolve `impl_sym = <dict_value.functor>.<fn.op_short>`; otherwise `impl_sym = fn`.
- Push frame with target = `impl_sym`:
  - `frame.locals` = zip(impl's value-param symbols, evaluated args)
  - `frame.requirements` = `(Self_<spec>, dict_value)` followed by one entry per impl's `requires`, sourced positionally from `dict_value.sub_requires`.

### Per-IR-form behavior

| IR form | Eval-time requirement work |
|---|---|
| `apply_within(fn, args, requirements)` | Eval requirements; eval args; (if fn is a spec-op, resolve via dispatching dictionary); push frame with both populated. |
| `ho_apply_within(closure_expr, args, requirements=[])` | Eval closure; eval args; push frame with `frame.requirements = closure.requirements` (closures override; see below). |
| `constructor_within(name, args, requirements=[])` | requirements always empty; constructors don't dispatch through requirements. IR carries the slot for shape uniformity. |
| `lambda_within(params, body, requirements)` | One-shot: snapshot locals + requirements from enclosing frame (each `requirements` entry is a `var_ref` / `requirement_at_sort` expression evaluated immediately); deliver `Value::Closure`. No new AwaitState needed. |

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

**1. Inside generic bodies (post-elaboration)** — content hash-consing happens automatically; it is not a property the elaborator must protect.

Generic bodies don't bake concrete requirement values into the apply terms; they reference requirement params via `var_ref(<synthesized_name>)`. Whether two structurally-identical elaborated bodies share a `TermId` is just the `TermStore` doing its usual job on `alloc` — a memory nicety, not a correctness property. The elaborator should *not* contort to maximize it: name a requirement param after its spec (`__req_eq` for `Eq`, `__req_ord` for `Ord`) — the obvious scheme, deterministic by nature — and let the store hash-cons whatever it hash-cons. Non-deterministic naming (e.g. a per-op counter) is the thing to avoid, and it is also simply unnecessary.

**2. At concrete call sites (post-elaboration)** — hash-consing is *not* preserved across callers.

A caller's `apply_within(fn = B.bar, args = [s], requirements = [<C2 requirement value>])` carries a literal resolved instance (or `construct_requirement(C2, ...)`) in the requirements slot. Different callers with different resolutions emit different terms. Two callers of `B.bar` resolving to `C1` vs `C2` produce two distinct apply TermIds.

This is unavoidable — the call site's resolution information IS part of the IR, and structurally different resolutions produce structurally different terms. **Term store growth scales with the number of distinct (callsite, resolution) pairs**, not just the number of distinct callsites. Profiling will tell whether interning resolved instances at load time (one canonical `<IntEq value>` per program) is worth it; the design doesn't preclude that as a v1 optimization.

### Side-table alternative (rejected)

If we chose a side-table approach (requirement mapping kept outside the term) instead of separate IR slots, the side-table would need to be keyed on `OccurrenceId` (positional source identity), NOT `TermId`. Reason: hash-consing collapses structurally-identical calls in different bodies (e.g., `foo(x)` in B's body vs C's body) to the same TermId, but those calls live in different requirement scopes. Side-table indexing by TermId can't disambiguate; OccurrenceId can.

The separate-slots approach (this design) avoids the side-table machinery entirely. Generic body interiors share TermIds across instantiations; concrete call sites get distinct TermIds, but that's the same situation any IR with embedded constants has.

## Legacy: the positional model (current implementation)

The implementation as of WI-236 uses a **positional model** for body-side requirement access — *not* the names model the main body describes. The names model is the agreed target; this section records what actually runs today, so the doc is honest about the gap. The migration removes everything here — see §"Implementation roadmap".

In the positional model, a body reads its own requirements positionally:

- **`requirement_at_current(slot)`** — positional read of the body's own `frame.requirements[slot]`. `frame.requirements` is a positional `SmallVec<RequirementHandle>` (slot 0 = Self; slots 1..N = the requires-chain in declaration order) — parallel to `frame.locals` but *indexed*, not named.
- **`requirement_at_current(slot, op_short)`** — an fn-position fused form (slot read + functor extraction + method resolution in one node). Already dropped even within the positional model; dispatch is the interpreter rule on `apply_within` when `fn` is a spec-op symbol.

Why it is being replaced: a positional slot index is relative to the *current activation*, so it does not survive constructs that introduce a different frame — most sharply, a `let` body or a lambda body. A requirement *name* is an ordinary lexically-scoped variable; it composes with `let`, closures, and hoisting for free. See §"Two models" for the rationale.

`requirement_at_sort(dict, k)` and `construct_requirement(impl, [...])` are **not** legacy — they project/construct *inside* a dictionary value (whose sub-instances are positional and nameless in both models) and survive the migration unchanged.

## Host-to-entry-op boundary

> **Describes the current (legacy positional) implementation.** This section uses `requirement_at_current(slot)` and positional `frame.requirements`. Under the names-model migration the *concepts* are unchanged — the host still seeds the entry frame's requirements — but the access form moves from positional slots to named bindings. See §"Implementation roadmap".

The operation-call model assumes every body runs inside an activation frame whose `requirements` channel is populated by some caller's `apply_within` reduction. That covers all *in-program* calls — but the **outermost** call comes from the host (Rust, in the current realization) and there is no anthill-side caller to populate the frame.

The runtime currently exposes two host APIs for the boundary; the choice depends on whether the entry op's parent sort uses *same-sort* or *cross-sort* requires.

### Same-sort recursion → `Interpreter::call(qname, args)`

If the entry op's parent sort declares `requires` only of itself (the dominant CLI case — a bundle's `sort Main { requires anthill.cli.Main; … }` where `anthill.cli.Main` is the same sort the entry is defined inside), the runtime seeds `frame.requirements` with **self-referential placeholders**: each slot is `Requirement { functor: <parent_sort>, sub_requires: [] }`. Body-side `requirement_at_current(slot=k)` reads return a placeholder whose `functor` equals the parent sort — adequate when the body's only dispatch path is back into the same sort's ops.

Slot layout: slot 0 is **Self** (the enclosing op's dispatching dict); slots `1..=N` are the parent sort's flattened `requires` chain, in declaration order. All entries are self-referential placeholders.

### Cross-sort requires → `Interpreter::call_with_requirements(qname, args, chain_dicts)`

When the parent sort declares `requires X[…]` for a different sort `X` (e.g. `sort Main { sort State = ?; requires WorkItemStore[State]; … }`), the self-referential placeholder is **not enough**: the body's `WorkItemStore.lookup(s, id)` call dispatches through slot 1, whose placeholder has `functor = Main` rather than `functor = FileBasedWorkitemStore`. Either the lookup mis-resolves (the dispatching-dict's `sort` is wrong) or the impl's body reads sub-instances that the placeholder's empty `sub_requires` doesn't contain.

The fix is for the host to supply **real impl-rooted dictionaries** for the chain entries:

```rust
// Build a dictionary for `WorkItemStore[State = WIS]` rooted at FileBasedWorkitemStore.
let filebased = interp.kb_mut().intern("anthill.todo.store.FileBasedWorkitemStore");
let dict = interp.alloc_requirement(filebased, SmallVec::new());

// Invoke Main.main with the dictionary in slot 1.
// Slot 0 (Self) is auto-allocated by the runtime as a self-referential placeholder.
let mut chain_dicts: SmallVec<[_; 2]> = SmallVec::new();
chain_dicts.push(dict);
interp.call_with_requirements("anthill.todo.Main.main",
                              &[args_val, store_val, wis_cell_val, agent_val],
                              chain_dicts)?;
```

The caller supplies one handle per entry in the parent sort's flattened `requires` chain (in declaration order); the runtime prepends the Self slot automatically. Handle structure must reflect each impl's own `requires` chain — an impl that itself has `requires Y` is allocated with `sub_requires = [<Y dictionary>]`, recursively.

The host API is value-level only; the **typer** doesn't see the caller's intent. The caller must shape the dictionaries to match what the body dispatches through. Mismatches surface as opaque slot reads or `unknown operation` errors mid-body; the boundary's arity check (`chain_dicts.len() == requires_chain_flat(parent).len()`) catches the obvious case at the entry.

### When to pick which

- `interp.call` is the default. Use it for any op whose parent sort declares only same-sort `requires`, or no `requires` at all. The seeded placeholders sit unused by such bodies and cost nothing.
- `interp.call_with_requirements` is mandatory when the entry op's parent sort declares cross-sort `requires`. Without it, dispatch through those slots fails at runtime.

Inference of the right dictionary from the value-level args (e.g. peek at the `wis(...)` functor inside a `Cell[?S]` argument to deduce `State = WIS` and select FileBasedWorkitemStore) is a future direction — `call_with_requirements` is the explicit-impl baseline that ships first.

(WI-236 — landed alongside this section.)

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

WI-218 through WI-236 landed the **positional model** (frame.requirements as a positional slot vector, `requirement_at_current` primitives, fn-position dispatch fusion, multi-entry requirements channel). The migration moves the implementation to the **names model** (single-entry channel, named requirement params, tree expansion at frame push):

| Phase | Scope |
|-------|-------|
| **Redesign WI (new — supersedes WI-229)** | (1) Remove `requirement_at_current(i)` and the fn-position `(i, op_short)` form from the elaborated IR. (2) For Defer call sites, emit `apply_within(fn = <spec_op_qn>, args, requirements = [<single dispatching dict expr>])` — one entry, no slot-baking in `fn`. (3) Change `build_projected_requirements_list` to return a single dictionary expression rather than the impl's sub-instance list. (4) Move the dispatch step into the interpreter's `apply_within` reduction (spec-op branch). |
| **Frame.requirements rekeyed + expanded at push** | Change `Frame.requirements` to `SmallVec<[(Symbol, Value); N]>`, parallel to `frame.locals`. At frame push, expand `requirements[0]`'s sub-tree: Self_<spec> bound to the dict, plus one binding per the impl's `requires` chain sourced positionally from `dict.sub_requires`. |
| **Hoist obsoleted (WI-229 close)** | The let-binding hoist for repeated projections is no longer needed: the body's sub-instance accesses are `var_ref(<named_binding>)` (frame-pre-expanded), not repeated `requirement_at_sort` chains. Close WI-229 with a "superseded by redesign" rationale. |
| **Typer pass (already landed; minor revision)** | Type-check bodies + compute per-op requirements-tree. Output unchanged; the elaborator now synthesizes a Self name plus one named binding per the impl's requires-chain. |
| **Requirement-insertion pass (revised)** | Existing pass continues to emit one of the three rewrite cases per call. Each emits the single-entry shape per the redesign WI above. |
| **Eval frame-push generalization** | Replace existing frame-push logic for `apply_within` to expand `requirements[0]`'s sub-tree into the callee's named requirement bindings. Add spec-op dispatch branch (look up `sort_ops_table[dict.sort][op_short]`). |
| **Closure.requirements rekeyed** | Mirror Frame.requirements change for closure capture. Closures save their full requirement scope (Self + sub-instances by name). |
| **Per-target codegen** | Each codegen target adapts to the new IR shape (var_ref for named req params; spec-op fn position for Defer; single-entry channel). |

## Out of scope (this design)

- **Per-operation requirement declarations** (Lean `[A T]` per-op style). Anthill keeps per-sort `requires` for now; per-op refinement is a future optimization. The Resolution algorithm and dispatch shape extend cleanly when this is added — the only difference is where a slot's source comes from (caller's frame for op-level vs dispatching value's bundle for sort-level). Mechanism is forward-compatible.
- **Explicit instantiation syntax** (OCaml functor style). Future surface-syntax extension if user feedback requests it.
- **`dyn Spec` dynamic dispatch** (surface syntax). Opt-in escape hatch for genuinely runtime-decided cases: heterogeneous collections (`List[?dyn Display]`), existential return types, module-boundary erasure. Not in v0's surface grammar.

  **Forward-compatible with this design**: `dyn Spec` is a thin layer over the static mechanism. A `dyn Spec` value is just `(value, RequirementHandle)` packed — like Rust's fat pointer or Lean's instance value. To use one, unpack and dispatch via the bundled handle by feeding it as a requirement param to a spec-op `apply_within` (the interpreter's existing Defer rule does the rest). Adding dyn requires only: a `Value::Dyn` variant, a coercion from `(T, RequirementHandle)`, and an unpack primitive. No changes to `apply_within`, `resolve`, or the rest of the design.

  **Without dyn**, programs that would need it fail to type-check for ordinary reasons: an open type-var not covered by any `requires` and not ground at the call site → resolution returns `NoMatch`. This isn't a special rejection — it's the existing resolution algorithm finding nothing to dispatch through. The diagnostic suggests adding `requires Display[T]` (cover it) or, in a future version, `dyn Display` (defer it to runtime).
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
