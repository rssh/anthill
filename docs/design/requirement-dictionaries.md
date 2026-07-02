# Requirement dictionaries — first-class runtime values, reflective expression construction & rule-body requirement goals

## Status

Design — **origin** 2026-07-01 (this session). Covers two coupled tickets:

- **WI-577** — "First-class Dictionaries + OpRefs" (the substrate: give the
  runtime dispatch value a first-class anthill face). **These are RUNTIME sorts**
  (`Dictionary[S]` / `OpRef[A]`) in **`anthill.realization.runtime`** — the runtime
  dual of `realization`'s `Obligation`/`Implementation` — *not* reflect objects;
  reflect enters only for the separate expression-construction layer (§2.6). Surfaced
  during the WI-502 typed-value carrier review.
- **WI-300** — "Requirement goals in rule bodies" (the consumer: `requires(X)`
  as a rule-body goal). Surfaced during the WI-246 Phase 3c review. **Depends on
  WI-577**, on **WI-292** (*delivered*), and on **WI-613** (*delivered* — the
  same-spec/different-param **attribution** fix WI-300's requirement weave reuses;
  §3.4).

They are one document because they are one topic: a rule-body `requires(X)`
dispatches through, and reasons about, the requirement **dictionary**, so it
needs that dictionary exposed as a first-class (runtime) value with typed
accessors. WI-577 is the substrate; WI-300 is the consumer; the ordering is
**WI-577 → WI-300**.

**Builds on:** the runtime dictionary machinery
([`operation-call-model.md`](./operation-call-model.md) §"Runtime: frame,
requirement value, closure"), the op-body requirement weave
(`anthill-core/src/kb/req_insertion.rs`), and the defer-to-requirement
**attribution** matchers that map each body spec-op call to its `requires` slot
(`find_requires_slot` / `find_requires_location`, σ-class-disambiguated per
WI-613, §3.4). **Adjacent:**
[`constrained-term-substrate.md`](./constrained-term-substrate.md) (typed
values; runtime monomorphization dispatches on a value's carried type — the same
"make dispatch introspectable" goal; and WI-292, the resolve-or-suspend engine
WI-300 reuses).

**Not a storage change.** The dictionary value already exists at runtime. WI-577
lifts it into a first-class *reflect* object — a pure structural **view** over
storage that is already there, consistent with the reflect principle *reflect is
an operational interface over a term, not new storage*.

---

## 1. What the runtime dictionary *is* today

A requirement value is the materialization of a **resolved spec impl** — textbook
dictionary-passing. Storage is a per-interpreter **`RequirementArena`**
(`anthill-core/src/eval/requirement_arena.rs`), refcounted, mirroring
`CellArena` / `MapArena` / `SubstArena`. Each slot is:

```rust
struct Slot {
    functor:      Option<Symbol>,                          // the resolved impl's identity (e.g. IntEq)
    requirements: Option<SmallVec<[RequirementHandle; 1]>>, // its sub-requirement dicts (positional)
    refcount:     u32,
}
```

So the value is a **recursive `(functor, [sub-requirements])` tree**: an impl
symbol plus an array of child dictionaries. Concretely:

| Aspect | Today |
|---|---|
| **Runtime value** | `Value::Requirement(RequirementHandle)` (`eval/value.rs:125`) |
| **Built by** | the IR form `construct_requirement(impl, [...])` — the `Expr::ConstructRequirement { impl_functor, requirements }` occurrence (`node_occurrence.rs:772`) |
| **Dispatched through** | `requirement_at_current(i, op_short)` (read a slot's op) |
| **Sub-deps projected via** | `requirement_at_sort(chain, k)` — `Expr::RequirementAtSort { chain, slot }` (`node_occurrence.rs:767`) |
| **Carried in** | `frame.requirements`, `closure.requirements`; snapshotted into `Value::OpRef { op, dict }` (`eval/value.rs:89`, WI-420) |
| **Lifetime** | refcounted; no-cycles policy; `Clone` bumps, `Drop` frees at zero |

This shape — `functor + sub-requirements` — **is** exactly what WI-577 names as
"RequirementHandle: the requirement DICTIONARY."

**The slot is thin — operations are resolved, not stored.** It holds the impl
identity and its sub-dicts, **not** a vtable of operations. To get an operation,
the runtime resolves `(functor, op_short)` on demand: `impl_sym = dict.functor()`
→ `sort_ops_lookup(impl_sym, op_short_sym)` (the load-time `sort_ops_table`,
WI-240) → an `instance_fact_op_binding` fallback for retroactive instance facts.
That is `dispatch_via_sort_ops_table` (`eval.rs:589`). Consequence for §2: the
reflect `Dictionary` must expose an **op-resolution** operation — projecting
sub-dictionaries is not enough, since the operations themselves are the point of
a method dictionary.

But today they have **no reflect interface**: there is no `sort` and no
operations over `Value::Requirement` / `Value::OpRef`, so anthill cannot name,
read, or reason about a dictionary at all. (They are also `ViewHead::Opaque`,
`term_view.rs:1081`, and unlowerable, `execute.rs:331` →
`LowerError::UnsupportedVariant("Requirement")` — but the accessor face below
needs *neither* changed; see §4.)

**Two levels: an abstract requirement (in the code) vs. a concrete dictionary
(the value).** An operation body is compiled **once, polymorphically, without the
receiver** — no body cloning, no per-type monomorphization
([`operation-call-model.md`](./operation-call-model.md) §"Decision in one
paragraph"). So the *code* genuinely does not depend on any concrete dictionary:
the body's `eq(x, x)` is classified `CallClass::DeferToRequirement` and
elaborated to `apply_within(fn = Eq.eq, requirements = [var_ref(__req_eq)])`,
referencing the **abstract requirement param** `__req_eq` by name. Dispatch is
performed **dynamically on each execution** — `dispatch_via_sort_ops_table` reads
the passed dict's functor — so the concrete impl op is never baked into the body.
This is late-bound dictionary-passing. (When the typer *statically* knows the
concrete receiver it may instead **pin** the call — `CallClass::PinNow`, static
dispatch — but the abstract-requirement case stays dynamic.)

What is *not* abstract is the **dictionary value** occupying `__req_eq` in a given
frame: dispatch resolves by `dict.functor()` → `sort_ops_lookup(impl_sort,
op_short)`, which needs a concrete functor, and a live `Slot.functor` is always
`Some(concrete impl)`. So the two levels coexist — the code abstracts *over* the
dictionary (one polymorphic body, referencing `__req_eq`); the value passed *in*
at runtime is concrete (supplied by the caller). **"Calling an op on an abstract
dictionary"** therefore means: reference the abstract requirement param
(`var_ref(__req_*)`) in the apply's requirements channel, and let the polymorphic
code dispatch dynamically against whatever concrete value the caller bound.

Where the concrete value comes from:

1. **Inside an operation body — the caller supplies it (dictionary-passing).** The
   caller binds `__req_eq` to a concrete dictionary at dispatch (expanded into
   `frame.requirements` at frame push). A polymorphic caller forwards its *own*
   `__req_*` — concrete-by-then from *its* caller — and the chain bottoms out at a
   concrete call.
2. **In a rule body / query with an under-determined type — nobody supplies it, so
   suspend.** A free rule has no caller to thread a dict (§3.3); if `T` is not
   ground you cannot `construct_requirement` a concrete dict, so you **suspend as
   residual** (WI-067 / WI-519, never NAF-decide) until `T` binds, then construct
   and dispatch.

So the *code* is abstract (polymorphic, late-binding via `var_ref`); the
*dictionary value* it dispatches against is concrete at execution — supplied by
the caller (op bodies) or awaited via suspend (rule bodies). This is why WI-300's
weave is *construct-or-suspend* (§3.3), and why `resolveOp` on a reflect
`Dictionary` always resolves (a `Dictionary` *value* is concrete by
construction).

Note this is **not** a stdlib `Map`. The data-structure dictionary
(`prelude/map.anthill`, `Value::Map`) is a different concept — key→value storage;
the requirement dictionary is the instance/method **witness**.

---

## 2. First-class dictionaries: the runtime `Dictionary[S]` / `OpRef[A]` values (WI-577)

`Dictionary[S]` and `OpRef[A]` are **runtime** sorts, in **`anthill.realization.runtime`**
— the anthill face of the runtime dispatch values `Value::Requirement` /
`Value::OpRef`. They belong there because a dictionary is the **runtime dual of an
`Obligation`**: the value that discharges a `requires` by carrying its resolved
`Implementation` — and `Obligation`/`Implementation` already live in
`anthill.realization`. The `.runtime` sub-namespace separates these runtime *values*
from realization's static *declarations*; the host sub-namespaces
(`realization.rust_std`, …) then describe how a `realization.runtime.Dictionary`
renders per host (a Rust `&dyn Trait`, a Scala `using`). You *use* them: resolve,
project, dispatch, pass. Reflect enters only in §2.6, the separate
expression-*construction* layer that builds code over them.

### 2.1 Why

Making `Value::Requirement` / `Value::OpRef` first-class runtime values buys:

1. **Uniform typing.** Each carries the same two-type split `reflect.Type` already
   has: a **reflect type** (it *is* a `Dictionary` / an `OpRef`) plus a **denoted
   type** — carried as a TYPE PARAMETER (`Dictionary[S]`, `OpRef[A]`): the spec
   instance it witnesses (`Eq[Int]`), or for an `OpRef` the op arrow. Tracked
   statically by the typer (§2.5), so the WI-502 typed-value review resolves
   `OpRef`/`Requirement` uniformly by reading the *type* — not by cracking open the
   opaque value — instead of ad-hoc per-handle decisions.

2. **Introspectable dispatch.** *Which* impl did this dispatch to, *what*
   sub-requirements does it carry — enabling first-class dictionary-passing,
   proofs *about* dispatch, and "why did `eq` resolve here" debugging. Runtime
   monomorphization stops being a black box.

**Sound** because both are **immutable resolved values** — no identity/mutation
hazard (unlike `Cell`), so a structural reflect view is a pure view.

### 2.2 How it is visible from anthill

The value is **not** exposed as a copy. It is
exposed the way `Substitution` / `Map` / `Cell` already are: a named `sort` whose
operations are **native Rust builtins reading the live handle in place**. The
anthill-visible `Dictionary` value *is* the `Value::Requirement(handle)` the
runtime already carries.

**The wiring — the `Substitution` precedent.** Three pieces, all already
exercised in the codebase:

**(1) anthill side** — a named `sort` in `reflect.anthill` (not `= ?` opaque, not
an `enum` with entities):

```anthill
-- Parameterized by S — the spec instance this dict witnesses (e.g.
-- `Dictionary[Eq[Int]]`, `Dictionary[Stream[Int]]`). S IS the "denoted type" of the
-- two-type split (2.5): it rides as an ordinary type parameter, tracked STATICALLY
-- by the typer — never read off the opaque value. The runtime slot still stores only
-- `(functor, sub-handles)`; the spec lives in the type. Bare `Dictionary` (S unknown)
-- is the existential form (2.5). A pure VIEW: inspect / navigate / resolve — no
-- term-construction ops (those are the Term layer, 2.6).
sort Dictionary[S]
  -- the resolved impl identity (arena slot's `functor`)
  operation impl(d: Dictionary[S]) -> Symbol

  -- RESOLVE a spec operation against this dict's impl sort, as a callable
  -- handle: the impl op symbol plus this dict as its dispatch environment.
  -- Keyed by the SPEC OP SYMBOL (e.g. `Eq.eq`) — the same key the interpreter
  -- dispatches on — NOT a short-name string. The reflect face of the runtime
  -- `dispatch_via_sort_ops_table(specOp, dict)` (eval.rs:589):
  -- `sort_ops_lookup(impl(d), op_short(specOp))` with the instance-fact fallback,
  -- wrapped as `OpRef { op: target, dict: Some(d) }`.
  operation resolveOp(d: Dictionary[S], specOp: Symbol) -> OpRef
  -- BULK view: all the dict's operations as a LAZY iterable of callable OpRefs
  -- (a view over the SortOpsTable slice; materializes only if collected). The
  -- enumeration face to resolveOp's keyed-lookup face.
  operation ops(d: Dictionary[S]) -> FiniteStream[T = OpRef]

  -- number of sub-requirement dicts
  operation arity(d: Dictionary[S]) -> Int
  -- project the i-th sub-requirement — no copy. Its denoted type S_i is the i-th
  -- `requires` of S's impl, so the return is a VALUE-DEPENDENT type (proposal
  -- 011/027): `Dictionary[S_i]`, S_i determined by the value `i`.
  operation sub(d: Dictionary[S], i: Int) -> Dictionary[S_i]
  -- NB no `denotedType` op: the denoted type IS the parameter S, which the typer
  -- already has statically. Reifying S to a runtime `Type` VALUE is Type-reflection
  -- — a meta-layer op (2.6), not a view accessor.
end
```

`resolveOp` is the reflect face of dispatch. Native impl reads `h.functor()`,
does `kb.sort_ops_lookup(impl_sym, op_short(specOp))` (fallback
`instance_fact_op_binding`), and returns `Value::OpRef { op, dict: Some(h) }` so
the resolved op stays callable under *this* dictionary. It is keyed by the **spec
op symbol** — the same key the interpreter dispatches on (`start_apply_within` →
`dispatch_via_sort_ops_table(functor, dict)`, `eval.rs:850`) — never a
short-name string.

**Where the operations live — not in the dictionary.** The arena slot stores only
`functor + sub-requirements` (§1). A dictionary's operations are a **thin index**
into a shared KB table, `SortOpsTable` (`mod.rs:267`):
`by_impl: HashMap<impl_sort, HashMap<op_short, target_op>>`, built once at load.
Resolving one op is `by_impl[dict.functor()][op_short] → target op Symbol`; the
map is **shared** by every dictionary with the same functor, so nothing is
duplicated per dictionary. An individual operation bottoms out at a `Symbol`,
whose content is its `OperationInfo` fact / `OpInfoRecord` (`op_info.rs:30`) and
body (`op_bodies[symbol]`); `Value::OpRef` is its first-class handle.

**Calling a resolved op — one machinery, two entry points.** Both end in
`expand_dispatching_dict(op, dict)` (build the name-keyed `frame.requirements`) →
`dispatch_*_with_requirements(op, …)` (push frame, run body):

- **static call site** — `apply_within(fn = specOp, requirements = [dict])`
  (`start_apply_within`, `eval.rs:850`): resolves (`dispatch_via_sort_ops_table`)
  *and* calls in one reduction. What op-bodies and the WI-300 weave emit.
- **first-class handle** — a `Value::OpRef { op, dict }` applied like any function
  value (`eval.rs:1215`): applying it installs its captured `dict` and runs `op`.

`resolveOp` returns an `OpRef`, so **its result is callable** — you call it by
applying it, which re-enters the very same machinery as `apply_within`. It is
therefore the *reflective / first-class* way to obtain a callable resolved op
(and it also serves the payoff-#2 inspection uses: "which impl did this resolve
to," proofs about dispatch). The WI-300 weave simply doesn't *need* it — it emits
the static `apply_within` form directly — but the two doors open onto the same
call. `impl` / `sub` / `arity` describe the dictionary; `resolveOp` yields
a callable/inspectable resolution.

**Bulk view: `ops(d) -> FiniteStream[OpRef]`, a lazy iterable — not a `List`, not
a `MapReader`.** When a consumer wants *all* of a dictionary's operations (not one
by name), expose them as a **lazy iterable of `OpRef`s**, reusing the existing
finite-stream machinery. This beats the alternatives:

- **not an eager `List[OpRef]`** — that materializes, against the zero-copy stance;
  a `FiniteStream` over the `SortOpsTable` slice materializes only if collected.
- **not a keyed `MapReader[Symbol,Symbol]`** — keyed lookup is already
  `resolveOp`'s job (O(1) into `SortOpsTable`), so a bulk *map* would add a whole
  stdlib abstraction for no gain here; and its bare-`Symbol` values are poorer than
  callable `OpRef`s.

Each element is a callable `OpRef` (identity via `op(r)`, dict attached), so the
stream is both inspectable and callable. `resolveOp` (one, by name) and `ops`
(all, lazy) are the keyed and bulk faces of the same resolution. NB the *set of op
names* is still fundamentally a property of the spec (the denoted type, via
`OperationInfo`); `ops` is the convenience of walking them already-resolved
against `d`.

**(2) registration** — each op's qualified name binds to a native fn, exactly as
`eval/builtins.rs:95` does for `Substitution.lookup`:

```rust
register_if_present(interp, "anthill.reflect.Dictionary.impl", dict_impl)?;
register_if_present(interp, "anthill.reflect.Dictionary.sub",  dict_sub)?;
```

**(3) the builtin** — reads the arena slot in place and returns a `Value`
(mirrors `subst_lookup` at `builtins.rs:1554`):

```rust
fn dict_sub(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [d, idx] = expect_args::<2>("Dictionary.sub", args)?;
    match d {
        Value::Requirement(h) => {
            let child = h.sub(as_int(idx)?);   // refcount bump on the child slot
            Ok(Value::Requirement(child))      // wrap the SAME handle — no structural copy
        }
        other => Err(type_mismatch("Dictionary", &other, None)),
    }
}
```

**Zero-copy guarantees to hold:**

- A `Dictionary` value = the same `RequirementHandle` (`Rc` into the arena).
  Passing it around is a refcount bump, not a deep copy.
- `sub(d, i)` = clone a child handle (refcount bump), wrap as
  `Value::Requirement`. Never a structural copy.
- `impl(d)` = read `slot.functor`; `arity(d)` = `slot.requirements.len()`.

### 2.3 Accessor-only — no pattern-match face

`Dictionary` (and `OpRef`) are exposed through **operations only** — the
`Substitution`/`Map`/`Cell` model: a `sort` whose ops are native builtins over the
live handle. There is deliberately **no** pattern-match face like
`match d case dict(functor: ?f, requirements: ?rs)`, because anthill has **no
user-defined extractors** (no Scala-`unapply` / active patterns): a `match`
pattern is a *declared* `entity`/`enum` constructor (grammar `pattern_constructor`)
or a tuple/literal/var/wildcard. `Dictionary` is a `sort` with operations, not an
`entity dict(...)`, so no `dict` constructor exists to match against.

Making it matchable would need either a **new language feature** (user-defined
extractors) or a **core-matcher special-case** that fabricates a `dict` view over
the opaque `Value::Requirement` (teaching `TermView` to project it as
`ViewHead::Constructor` instead of `ViewHead::Opaque`). Neither is justified: the
accessor ops (`impl` / `sub` / `arity` / `resolveOp` / `ops`) plus the denoted-type
parameter already expose everything the value holds; a pattern-match face would add syntax,
not capability. (If anthill ever gains extractors, a structural-match face could
be revisited — noted, not planned.)

### 2.4 OpRef

`Value::OpRef { op: Symbol, dict: Option<RequirementHandle> }`
(`eval/value.rs:89`) is a **resolved operation reference**: a fully-qualified op
symbol plus — **only when the op is requires-carrying** — the dictionary that
supplies its requirements at apply (`none()` for a requires-free op). The `op` is
already resolved; the `dict` provides the op's *own* requirements, it does not
resolve `op`. `resolveOp` (§2.2) returns one. It is exposed as a `sort OpRef[A]`
(the view; `A` = the denoted arrow) with the same accessor face as `Dictionary[S]`:

```anthill
-- A resolved operation reference, parameterized by A — the op's callable ARROW
-- (its DENOTED type, e.g. `(Int, Int) -> Bool`). Same two-type-split shape as
-- `Dictionary[S]`: reflect type `OpRef`, denoted type the parameter A, tracked
-- statically. Value form `Value::OpRef { op, dict }` (eval/value.rs:89). An OpRef
-- IS a callable function value (runtime carrier = anthill.prelude.Function,
-- eval.rs:1907); applying it dispatches `op` under `dict` (eval.rs:1215). A pure
-- VIEW — building a CALL from it (the old `genApply`) is term construction, so it
-- lives in the Term layer (2.6) as the general `mkApply`, not a method here.
sort OpRef[A]
  -- the resolved operation's identity; its Symbol has a fully-qualified name
  operation op(r: OpRef[A]) -> Symbol
  -- the captured dispatching dictionary — none() only for a requires-free op
  -- (enclosing sort has no `requires`) or a namespace-level op. A
  -- requires-carrying eta captures a dict at mint — INCLUDING a same-sort eta,
  -- which captures its sort's `__req_self` because the OpRef escapes to a
  -- foreign apply frame that would otherwise leave `__req_*` unbound (WI-420).
  operation dict(r: OpRef[A]) -> Option[T = Dictionary]
  -- NB no `denotedType` op: the denoted arrow IS the parameter A (static). A
  -- *reflectively* resolved OpRef has A unknown (existential `OpRef`), and reifying
  -- A to a runtime `Type` value is Type-reflection — a meta-layer op (2.6).
end
```

**Identity vs. callable.** `op(r)` is the resolved op's *identity* — a `Symbol`
with a fully-qualified name (`anthill.prelude.IntEq.eq`); enough for "which impl
did this resolve to." To *call* it you need the whole `OpRef`: applying it —
ordinary function application, since an `OpRef` provides `Function`
(`eval.rs:1907`) — installs `dict`'s sub-requirements into the callee frame and
runs `op` (`eval.rs:1215`). A **bare symbol cannot invoke a requires-carrying
op**, because it carries no dict to thread the op's own sub-requirements. That is
why `resolveOp` returns `OpRef`, not `Symbol`: the dict is what keeps the
resolved op runnable.

`dict(r)` reuses the `Dictionary` view (§2.2), so `Dictionary` and `OpRef` land
together and `resolveOp` closes the loop: `Dictionary` → (`resolveOp`) → `OpRef`
→ (`dict`) → `Dictionary`.

**Everything *constructive* lives in the Term layer (§2.6), not here.** Building a
call from an `OpRef`, or turning a dictionary into a term (by reference or by
rebuild), is *term construction*, not a view operation — so it is not a method on
`Dictionary`/`OpRef`. §2.6 covers the Term / meta layer (`quote`/`ref`, `mkApply`,
`reify`, `execute`, Type-reflection), which subsumes the earlier `genRef`/`genApply`
as general, value-agnostic primitives.

### 2.5 The two-type split, precisely

The split is carried by the **type parameter**, not an operation:

- **reflect type** — `Dictionary` / `OpRef` (the value *is* the handle).
- **denoted type** — the **parameter**: `S` in `Dictionary[S]` (the spec instance,
  `Eq[Int]` / `Stream[Int]`), `A` in `OpRef[A]` (the op's arrow). It rides as an
  ordinary type parameter, tracked STATICALLY by the typer — which is what lets a
  dict reference or a var-bound dict type-check as a requirement, with no read of the
  opaque value.

The denoted type is **not** stored on the runtime slot and is **not** "a pure read
over `slot.functor`" (an earlier framing this doc corrected): the slot carries only
`(functor, sub-handles)`, and `functor` is a *carrier* that provides many specs
(`List` provides 12), so the witnessed spec is *not* recoverable from the value. It
need not be — the spec lives in the **type** (`S`), which the typer already has.

Two consequences:
- **Bare `Dictionary` (S unknown) is the existential form** — a dict whose spec is
  not statically known (a heterogeneous collection, a fully dynamic source).
- **Reifying the denoted type to a runtime `Type` value** — the old `denotedType(d)`
  op — is Type-reflection, a meta-layer op (§2.6), gated on a consumer. Only *it*
  would need `S` threaded to runtime (the type-args channel, WI-272/383) or, for the
  existential case, stored on the slot. The static split needs neither. (This is what
  dissolves the "store the spec on the slot" cost the review flagged.)

### 2.6 The Term layer — constructing expressions (anthill, over the `Expr` enum)

Term *construction* — producing occurrences — is a different concern from the
`Dictionary`/`OpRef` **views**, and it lives at the **anthill layer**: reflect
operations that build reflect **`Expr` data** and materialize it. The `Expr` enum in
`reflect.anthill` already defines *every* occurrence form as an entity —
`apply_within`, `construct_requirement`, `var_ref`, `requirement_at_sort`, `apply`,
`if_expr`, `let_expr`, … — so constructing an expression is *constructing those
entities in anthill*. Nothing dict-specific is native.

**One native primitive — the occurrence dual of `reflect`.** reflect already has the
term-build direction; the only thing missing is its occurrence twin:

```
reflect(kb, r: TermRepr)                     -> Term            -- EXISTS: build a logical term
reflect_expr(kb, e: Expr, pos: SourceSpan)   -> NodeOccurrence  -- ADD: build a live occurrence
```

`reflect_expr` materializes an `Expr` (whose children are already `NodeOccurrence`s)
into a live, typed occurrence at span `pos`. It must be native — a raw occurrence
must be typed/classified before it can run — but it is the *whole* native surface;
everything above it is anthill. (`NodeOccurrence` is the general occurrence node,
`kind: NodeKind` = `Expr` | `RuleHead` | `Pattern` | `Type` | `EffectExpr`;
`reflect_expr` builds the **`Expr`-kind** occurrence — analogous builders would
materialize the other kinds.)

**The constructors are anthill operations over the `Expr` entities** — anthill bodies
composing `reflect_expr` + the enum:

```anthill
-- reference a dict (identity-preserving) — a LEAF, so pos is explicit
operation genRef(d: Dictionary[S], pos: SourceSpan) -> NodeOccurrence =
  reflect_expr(quote(d), pos)                    -- quote(d): the value-reference leaf

-- a dispatched call over an OpRef — compound; threads pos to children
operation genApply(r: OpRef[A], args: List[T = ApplyArg], pos: SourceSpan) -> NodeOccurrence =
  reflect_expr(apply_within(op(r), args, requirements: [genRef(dict(r), pos)]), pos)

-- a dict recipe from parts (the structural rebuild)
operation genConstruct(impl: Symbol, subs: List[T = NodeOccurrence], pos: SourceSpan) -> NodeOccurrence =
  reflect_expr(construct_requirement(impl, subs), pos)

-- build the occurrence that resolves/constructs a dict for spec type `t`
-- (t: TypeTerm — the spec instance Eq[Int]/Stream[Int] as a term). Executing the
-- built occurrence runs the WI-300 resolver (provides-resolution + construct +
-- suspend). Build-side here; eval-side is WI-300 — two stages of one `Expr` form.
operation findDictionary(t: TypeTerm, pos: SourceSpan) -> NodeOccurrence =
  reflect_expr(find_dictionary(t), pos)
```

`TypeTerm` = the spec instance as a term (a `Term` in type position; reflect's
`sort_as_term(s: Type) -> Term` produces one). It is the queryable form the WI-300
resolver matches against `provides` facts.

Every body is anthill — the dictionary logic is `apply_within(op(r), …, [genRef(dict(r))])`,
not a builtin. `mkApply`/`mkVar`/`mkLit` are the same shape over the general `Expr`
forms, **value-agnostic** (`quote` builds a `Cell`/`Map` reference identically).

**Positions.** Every occurrence carries a `SourceSpan` (`occurrence_span`), so every
constructor takes `pos`. A **leaf** (`genRef`, `mkVar`, `mkLit`) has no child to
derive from → explicit `pos`; a **compound** (`genApply`, `genConstruct`) derives its
span from its children or takes an explicit one. `pos` is where a diagnostic on the
generated node points, and its provenance — the source it was generated *for* (a
rewrite's original site, a macro's trigger). NB `SourceSpan` today has only a real
byte-range variant; genuinely synthetic code either reuses the trigger's span or
motivates a `generated(from: SourceSpan)` variant (a small follow-on).

**Reference vs. rebuild (the value→term boundary).** `genRef`/`quote` = a *reference*
to THIS dict handle (identity, sub-dict sharing) — for execution-bound terms. `reify`
(the general value→term rebuild) produces the structural `construct_requirement`
recipe — `DiscrimKey`-able, for terms that must be keyed, at the cost of a new
structurally-equal value. Because construction always goes through a reference
(`genRef`/`var_ref`) or a recipe (`genConstruct`/`reify`), a raw `Value::Requirement`
handle **never** rides as an opaque leaf inside a keyed occurrence. Binding a dict to
a var is then ordinary — `let a = genRef(d, pos)` (or `= findDictionary[Spec]`,
`= resolveOp(…).dict`) — and `a` threads as a requirement through the *unified*
`var_ref` lookup; the `__req_*` names are just the weave's special case of a
user-named `a`.

**What's genuinely new.** `genRef`/`genApply`/`genConstruct`/`mkApply` reuse
**existing** `Expr` entities → they need only `reflect_expr`. `findDictionary` adds
the one new `Expr` form `find_dictionary(spec: TypeTerm)` + its resolver — scoped to WI-300.
Type-reflection (reify a denoted parameter `S`/`A` to a runtime `Type` value, the old
`denotedType`) and `execute(t)` (runtime OpRef invocation is `execute(genApply(…))`,
never a primitive `invoke`) round out the layer.

**Layering & phasing.** A *separate concern* from WI-577's views — anthill operations
over the `Expr` enum, value-agnostic, gated on a metaprogramming consumer. **Not**
part of WI-577's ship-now scope; its own follow-on WI, next to `reflect`/`reify`/
`execute`. WI-577 proper = the pure views `Dictionary[S]` / `OpRef[A]`.

---

## 3. Rule-body requirement goals (WI-300)

### 3.1 The gap

A requirement cannot be expressed as a **rule-body goal** today. Written in a
rule body:

```anthill
something(?x, ?y) :- eq(?x, ?y), requires(Eq[T])
```

this parses — keywords are soft (`grammar.js:23`) — as an ordinary
`Expr::Apply { functor: requires, pos_args: [Eq[T]] }` goal. `convert_rule_body`
(`anthill-core/src/parse/convert.rs:2136`) has **no special case**, so at
resolution it is just an undefined predicate that **fails**.

Requirements live only in two places today: the standalone `requires <Type>`
**sort declaration** → a `SortRequiresInfo` fact (`load.rs`, `Item::RequiresDecl`
at ~`load.rs:1628`); and an operation's `requires`/`ensures` **clause** →
`OperationInfo` reflect fields, woven into `kb.op_bodies` as `*Within`
occurrences by `req_insertion::run` (which walks **only** `kb.op_bodies`, never
rule `body_nodes`).

> **Stale-premise note.** The WI-300 ticket cites
> `is_requires_resolved`/`mark_requires_resolved` (`kb/mod.rs`, now ~`:671`) as
> scaffolding to build on. Those flags track **`SortRequiresInfo` fact
> finalization** (`resolve_requires_bindings`), *not* per-rule requirement-goal
> resolution — there is **no** existing rule-body requirement scaffolding to
> extend. Line refs in the ticket body (`req_insertion.rs:41`,
> `convert.rs:1647`, `mod.rs:456`) have drifted; the pointers here are current as
> of 2026-07-01.

### 3.2 Semantics (settled)

`requires(X)` in a rule body means: **spec X's operations become usable inside
that rule, dispatched through X's dictionary.** This is the operation-level
`requires` semantics, lifted to rules. When the body calls `eq(?x, ?y)`, that
call dispatches through X's requirement dictionary — the **dictionary wrapper**,
i.e. `Value::Requirement` / the `construct_requirement(impl, [...])` occurrence
(§1).

This **unifies** two readings that first looked distinct:

- **guard reading** — the rule fires only when X holds at the current binding;
- **dictionary reading** — the rule threads a dictionary the body's ops dispatch
  through.

They are the same mechanism: **the guard *is* the dictionary-resolution, and the
guard succeeding *yields* the dict.** So WI-300 needs both substrates — WI-292
(resolve-or-suspend) and WI-577 (the wrapper as a first-class, typed reflect
value with accessor ops, §2).

### 3.3 Where the dictionary comes from: `findDictionary` into a Γ slot

An **operation** gets its dictionary from its **caller** — threaded into
`frame.requirements` at frame push, read via `var_ref(__req_*)`.

A **rule has no caller.** SLD fires it against a *query* that supplies concrete
**values**, from which types are read. So the rule must resolve its own
dictionary — and the `requires T` goal *is* that populator:

> `requires T` ≡ **`∃x. x = findDictionary[T]`** — resolve/construct the dictionary
> for `T` at the current substitution and bind it into a **requirement environment
> carried in the resolver's Γ** (`Env`, WI-537 / the WI-328 constraint store): the
> SLD analog of eval's `frame.requirements`. `findDictionary[T]` = provides-
> resolution at the current binding (WI-292's `provides` query) →
> `construct_requirement(impl, [subs])`; **suspend as residual** if the binding is
> under-determined (WI-519 / WI-067 — never NAF-decide).

So the op-body weave transfers to rules **in full**, not partially: `findDictionary`
is the `construct_requirement` (run once, at the goal, instead of emitted by a
caller), and a body spec-op **reads the Γ slot** — the `var_ref` analog.
`requirement_at_sort` still projects sub-dicts out of a Γ-slot dictionary as usual.
(An earlier draft claimed "only `ConstructRequirement` transfers; `VarRef` has no
source" — that was wrong: **the Γ slot is the source**, populated by `requires T`
rather than by a caller.)

This holds for **sort-scoped rules** (Set/Map) too: the sort's `requires` resolves
into the Γ slot at fire time, driven by the carried type (WI-292) — same mechanism
as an explicit `requires` goal.

### 3.4 Implementation shape — desugar to requirement kernel primitives

`requires T` is *surface*; it desugars to the **requirement kernel vocabulary**
already used by the op-body weave — `construct_requirement`, `requirement_at_sort`,
requirement-env reads — plus **one new resolver primitive**, `findDictionary[T]`
(provides-resolution + `construct_requirement` + suspend). Concretely:

1. **`convert_rule_body`** (`convert.rs:2136`) *distinguishes* `requires(X)` from an
   ordinary goal (today it becomes an inert `Expr::Apply { functor: requires }`).
2. It desugars to **`findDictionary[X]` → bind into the Γ requirement slot**.
3. Each covered spec-op call in the body (`eq(?x, ?y)`) is woven to **dispatch by
   reading the Γ slot** — the rule-body analog of the op-body
   `apply_within(fn, requirements = [...])`.
4. **Bridge:** when a body op is actually invoked (SLD→eval), copy its dict from the
   Γ slot into the op's fresh `frame.requirements` — which already exists on the
   eval side, so nothing new there.

**Dispatch-if-concrete:** a Γ-slot dictionary is used iff it resolved to a concrete
impl; if `findDictionary` suspended (abstract binding), the requirement rides as
residual and the rule does not fire yet (§3.5).

One decision is settled, one remains:

- **[Resolved] Slot keying = the op-body names model, reused wholesale.**
  Elaboration synthesizes a name per requirement (`synth_req_names`,
  `typing.rs:20467`) and wires each covered body op to its slot by **type-param
  matching** (static) — reusing `frame.requirements`'s `SmallVec<[(Symbol,
  RequirementHandle)]>` (`frame.rs:119`), the bridge, and a shared
  `RequirementArena`. **Not** a runtime type-hash key: in the resolver a type
  carries a substitution and may be non-ground, so it is not a stable key; the type
  enters only as `findDictionary`'s groundness-gated input (§3.3). (This is the same
  conclusion the WI-613 analysis reached independently — the matching identity is
  *substitution-relative* and *elaboration-time*, not a ground-type hash.)

  **Same-spec / different-param** (`requires Eq[A], requires Eq[B]`) needs BOTH
  halves right, and they are distinct axes — an earlier draft of this bullet
  treated *naming* alone as sufficient, but WI-613 showed *attribution* is where the
  work is:
  - **Naming — no collision.** When two entries share the base `__req_eq`,
    `synth_req_names` disambiguates by the full spec `TermId` (`entry.spec.raw()`,
    `typing.rs:20485`) — `Eq[A]`/`Eq[B]` are distinct terms → distinct names, at
    elaboration and at runtime.
  - **Attribution — the harder half.** Wiring a body call `eq(y:B)` to the *right*
    slot is not naming: it matches the call's per-call type against the `requires`
    entries. A naive wildcard match mis-attributes — both `Eq[A]` and `Eq[B]`
    wildcard-cover *any* call, so first-match reads the `Eq[A]` slot's name for a
    call over `B`, and the correctly-distinct name is never selected. **WI-613**
    (*delivered*) fixes this: attribution routes through **σ-class** disambiguation
    (`SigmaCtx` / `sigma_class` / `pick_precise`, in `find_requires_slot` /
    `find_requires_location`), matching by element identity — bridging the enclosing
    param's per-body skolem to its canonical var so `A` and `B` are told apart.
    WI-300's rule-body weave reuses this attribution wholesale, so it **depends on
    WI-613** (§Status).
- **[Open] Whole-rule vs. positional `requires`.** As an `∃`-goal it reads
  positionally (ops *after* it see the slot); "bring X into scope for the rule"
  wants it whole-body. Either hoist `requires X` to a rule-level populator, or
  require it to precede the ops it covers.

### 3.5 Suspend, by construction

When `requires(X)` cannot resolve — `X`'s type params not ground at fire time —
`findDictionary` **suspends**: the requirement rides as a residual constraint and
the rule does not fire until the binding is determined; it is **never** NAF-decided
(WI-519 / WI-067). This is not a policy bolted on — it *falls out* of
`findDictionary` being a resolver goal over the `provides` facts: an
under-determined query is *undecided*, the resolver's third outcome (success /
failure / residual — see
[`constrained-term-substrate.md`](./constrained-term-substrate.md) and
`reflect.Solution`). Failing instead would silently drop a rule that could fire
once the type is bound. **Decision: suspend.**

### 3.6 Worked example

```anthill
-- fires only when T provides Eq; eq inside dispatches through the resolved dict
related(?x, ?y) :- requires(Eq[T]), eq(?x, ?y)
```

- Query `related(1, 1)` — `T = Int`; `findDictionary[Eq[Int]]` resolves the
  `provides Eq[Int]` fact and constructs the dictionary into the Γ slot; `eq(1,1)`
  reads the slot and dispatches through the concrete `Eq[Int]` dict → fires.
- Query `related(?a, ?b)`, `?a`/`?b` unbound — `T` under-determined →
  `findDictionary[Eq[T]]` **suspends**; the requirement is residual, the rule does
  not decide.
- A type with no `Eq` provider — `findDictionary` finds no provider at a ground
  type → the rule does not fire (sound: a well-typed use would have `Eq`).

### 3.7 Relationship to WI-292

WI-292 (delivered) honors **sort-level** `requires` on equational `[simp]` rules by
reading the carried type and **checking** `provides` — the resolve-or-suspend
engine. WI-300 reuses that `provides` query as the front half of `findDictionary`,
but goes further: it **produces** the dictionary value (WI-577) into the Γ slot and
dispatches the body's spec-ops through it. WI-292 checks; WI-300 finds, binds, and
dispatches.

---

## 4. Phasing (ordering: WI-577 → WI-300)

1. **Dictionary — runtime sort (WI-577)** — `sort Dictionary[S]` in
   `anthill.realization.runtime` (`impl` / `sub` / `arity` / `resolveOp` / `ops`;
   `S` = the denoted spec instance, a type parameter) + native builtins over the
   arena, plus the `Value::Requirement → anthill.realization.runtime.Dictionary`
   carrier-type mapping. The builtins match the handle in Rust and read the arena
   directly, so `Value::Requirement` can **stay `ViewHead::Opaque`** — no de-opaquing
   (that was only for the dropped structural-match face, §2.3). A runtime sort (like
   `Cell`/`Map`), not reflect. **This is the ready unit** (the review's read/inspect
   core). Unblocks WI-300.
2. **OpRef — runtime sort (WI-577)** — the sibling `sort OpRef[A]` (`op` / `dict`;
   `A` = the denoted arrow), reusing the `Dictionary` view. A `resolveOp` / `ops`
   result is directly **callable** (§2.2): WI-577 taught the eta apply path
   (`spread_eta_args`) to read a body-less op's arity from its signature
   (`OperationInfo.params`), so an OpRef whose resolved impl is a *native builtin*
   (`Eq.eq`, the primitives) dispatches the builtin instead of erroring. This is
   the direct-application half; the Term-layer `execute(genApply(…))` / `invoke`
   (§2.6) — building *and* running a call from reflect `Expr` data — stays the
   deferred follow-on.
3. **Reflect Term layer (separate follow-on WI, NOT WI-577)** — the one native
   primitive `reflect_expr(kb, e: Expr, pos: SourceSpan) -> NodeOccurrence` (the
   occurrence dual of the existing `reflect(TermRepr) -> Term`), plus the anthill
   constructors over the `Expr` enum — `genRef` / `genApply` / `genConstruct` /
   `findDictionary(TypeTerm, pos)` / `mkApply`, all taking `pos` — and Type-reflection,
   next to `reify`/`execute` (§2.6). Value-agnostic, **gated on a metaprogramming
   consumer** (like the deferred `invoke`); the runtime sorts (1–2) do not depend on
   it. Only `find_dictionary` (the `Expr` form + WI-300 resolver) is genuinely new.
4. **Rule-body requirement goals (WI-300)** — the `findDictionary[T]` resolver
   primitive (provides-resolution + `construct_requirement` + suspend); the Γ
   requirement slot; the `convert_rule_body` desugaring of `requires(X)` →
   `findDictionary` into Γ; body spec-ops dispatch by reading Γ; and the SLD→eval
   bridge populating `frame.requirements` from Γ. Suspend-if-abstract is by
   construction (§3.5). **Open before start:** decide §3.4's whole-rule-vs-positional
   `requires`, and confirm the Γ-slot substrate (WI-537 / WI-328) is in place.
5. **Bridge (WI-577, optional)** — codegen-emitted host bridge for the two view
   sorts, if/when a host consumer needs them (cf. the generated KB bridge, WI-540).

## 5. Soundness & non-goals

- **Immutable.** Resolved dictionaries never mutate (no `Cell`-style identity
  hazard), so views cannot observe tearing.
- **No new storage.** The runtime `Dictionary`/`OpRef` sorts are views over the existing arena.
- **Never NAF-decide** an under-determined requirement (§3.5).

## 6. Acceptance

Design (this doc) + (WI-577) the two runtime sorts (`Dictionary[S]` / `OpRef[A]`) +
builtins + carrier mapping + optional bridge; (reflect Term layer, follow-on)
`reflect_expr` + the constructors; (WI-300) rule-body requirement goals;
`cargo-test` green.
