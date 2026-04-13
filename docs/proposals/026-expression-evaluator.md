# Proposal 026: Expression Evaluator

**Status:** Draft
**Depends on:** [018-expressions-and-operation-implementation](018-expressions-and-operation-implementation.md) (expression syntax + IR)
**Related:** [013-abstract-effects](013-abstract-effects.md), [025-proof-constructs](025-proof-constructs.md) (Suspension/Branch semantics)
**Affects:** `rustland/anthill-core/src/eval/` (new), CLI (`anthill run`)

## Motivation

Expressions are parsed and type-checked but not executed. To make anthill programs runnable we need an evaluator for operation bodies. The goal is a minimum-viable interpreter that:

1. Runs `main`-like entry points from the CLI.
2. Exposes a library API so Rust hosts can call anthill operations.
3. Interops cleanly with KB queries — which produce `LogicalStream[T]`, not a plain value.
4. Has a migration path to a resumable VM for `Suspension` / `Branch` without redesigning the value model.

Non-goals for v1: bytecode, JIT, distributed evaluation, hot-reloading, persistent continuations across process restarts.

## Architecture overview

A **tree-walking interpreter** over `TermId`-encoded expression bodies, with an **explicit heap-allocated activation stack** (no native recursion). Runtime values use a `Value` enum with unboxed scalars, transient tuples/entities, and a `Value::Term(TermId)` variant for data already hash-consed in the KB — see the Values section for the full rationale.

```
rustland/anthill-core/src/eval/
  mod.rs          Interpreter, public API
  frame.rs        Frame, ActivationStack
  eval.rs         step(), run() — tree walk
  stream.rs       LogicalStream runtime representation
  builtins.rs     standard builtin registrations
  effects.rs      effect-handler registry
```

### Why tree-walker first

- Lands in days, runs end-to-end tests, pins down reference semantics.
- Hash-consed IR means "the tree" is the KB — zero conversion cost.
- Doesn't preclude a VM later; in fact defines the semantics a VM must match.

A VM becomes necessary when `Suspension` / `Branch` need real support: those need a saveable/forkable stack, which is awkward to build on the Rust call stack. The heap-allocated frame stack we adopt on day one gives us 80% of that machinery already.

## Values

Runtime values are represented as a Rust `Value` enum, not uniformly as `TermId`. Hash-consing (`TermStore::alloc`) performs a hash-index lookup on every allocation, which is real overhead for hot scalar paths. `TermId` is reserved for values that either originate in the KB or must be persisted back into it; everything else has a cheaper representation.

```rust
enum Value {
    // Unboxed scalars — zero alloc, zero hash lookup
    Int(i64),
    Float(f64),
    Bool(bool),
    Unit,

    // Anonymous tuple (no functor) — Pair(a, b), (Int, String), and
    // the shape of operation argument tuples in flight.
    Tuple {
        pos:   SmallVec<[Value; 2]>,
        named: SmallVec<[(Symbol, Value); 4]>,
    },

    // Constructed entity (has a functor; transient until persisted).
    // Zero TermStore allocation unless/until it crosses a KB boundary.
    Entity {
        functor: Symbol,
        pos:     SmallVec<[Value; 2]>,
        named:   SmallVec<[(Symbol, Value); 4]>,
    },

    // Interpreter-owned handles (arena-backed anyway)
    Closure(ClosureHandle),
    Stream(StreamHandle),
    Lazy(LazyHandle),

    // KB-sourced or already-committed data (hash-consed)
    Term(TermId),
}
```

### Lineage-based representation

Entity values carry two representations distinguished by *lineage*:

| Source | Representation |
|---|---|
| **In-memory KB** — fact field, body literal, query result over facts already in `TermStore` | `Value::Term(TermId)` (already hash-consed upstream; free) |
| **External-backed KB** — DB, network, file-streamed, or lazy source | `Value::Entity { functor, pos, named }` — **skips `TermStore` entirely** |
| **Constructed in this operation** — `Some(x)`, `WorkItem { id: "X" }`, `cons(h, t)` | `Value::Entity { .. }` (no TermStore alloc) |

### Promotion and demotion

**Promotion (`Entity → Term`) happens only at KB boundaries**: `assert_fact`, `Modify` store write, insertion into a cached `LogicalStream` source. One recursive `kb.alloc` pass at the boundary; free everywhere else.

**Demotion is lazy and usually unneeded.** Pattern matching on `Value::Term(tid)` reads the underlying `Term::Fn` via `kb.get_term(tid)` and binds sub-pattern vars to `Value::Term(sub_tid)` — no eager materialization. The Term layer is already a fine runtime representation for anything hash-consed.

### Pattern-match uniformity

A constructor pattern matches against `Value::Entity { functor: F, .. }` **and** `Value::Term(tid)` where `kb.get_term(tid) = Term::Fn { functor: F, .. }`. Three-line dispatch; consumers don't care which flavor they got.

### Scale: queries against external-backed KBs

The lineage split is what makes the evaluator viable over large external stores. Consider a DB-backed KB with 1M `WorkItem` entities, and a query that iterates them.

If every row materialized into the hash-consed `TermStore`, we'd pay:

- 1M `Term` slots + 1M `hash_index` entries at peak, even if they drop after.
- One hash compute + map lookup + insert per row — and since distinct-keyed entities never structurally dedupe, the work buys nothing.
- `Vec<Option<Term>>` capacity retained permanently after release.

Instead:

- A DB-backed store serves `LogicalStream<Value::Entity>` directly from cursor rows. Each row flows in as a `Value::Entity`, is processed, and drops. Peak memory = one row, not N.
- Hash-consing occurs only when the program **explicitly** routes a value back into the in-memory KB (`assert_fact`, `Modify` cell insert, `SharedStream` caching). Then and only then does that one row get hash-consed.
- External stores own their runtime representation. The interpreter bridges via pattern-match uniformity — operations written against `Some(x)` work identically regardless of source.

### TermStore compaction (follow-up, not v1 evaluator)

Even with the lineage split, programs that legitimately hash-cons many transient terms grow the `TermStore` vec without shrinking it (`terms: Vec<Option<Term>>` retains capacity after `release`). A standalone `kb.compact_terms()` pass would:

1. Walk `terms`, swap live slots toward the front, update a `TermId` remap.
2. Rebuild `hash_index`, `refcounts`, `free_list`.
3. Remap all `TermId` references held by the KB (facts, rules, indexes) through the remap table.

Explicit, not automatic. Filed as a separate follow-up to this proposal — not required for v1 evaluator correctness.

### Why `Value::Tuple` exists

Operations in anthill are defined over named tuples: `operation combine(a: T, b: T) -> T`. Every call site constructs an arg tuple and passes it in. Routing every call through `TermId`-backed tuples would hash-cons each arg set — pure overhead for a transient.

`Value::Tuple` is the runtime representation for:

- Operation-call argument tuples in flight.
- First-class tuple / pair values (`Pair[A, B]`, anonymous `(a, b)`).
- Intermediate builds before a value crosses into the KB.

Named args follow the project-wide convention: **stored sorted by field name** for canonical ordering, matching how `Term::Fn` stores them.

Entity values like `WorkItem(id: "WI-001", status: Open)` can be either `Value::Tuple` + a stored entity functor *or* `Value::Term` — we pick based on whether they're in flight (Tuple) or heading into the KB (Term). Conversion is cheap and localized to the boundary. If profiling shows entity ops are hot, we can add a dedicated `Value::Entity { functor, pos, named }` variant later.

### Cost model

| Boundary | Direction | Cost |
|---|---|---|
| Source literal → runtime | `Term::Const(Int(1))` → `Value::Int(1)` at eval entry | once per literal, amortized |
| Arithmetic / logic on scalars | `Value::Int` / `Value::Bool` stay unboxed | zero |
| Construct anthill data (`Some(x)`, `cons(h, t)`) | build `Term::Fn` → `TermStore::alloc` → `Value::Term` | one hash-cons at construction |
| `assert_fact` / resolver input | `Value → TermId` (hash-cons if not already) | only at KB/effect boundary |
| KB query result | `TermId → Value::Term` | zero (just wraps) |
| Pattern match | peek at either form | per-variant dispatch |

Hash-consing cost is paid only when values cross into **persistent KB state** (fact assertion, query, `Modify` cells). Pure eval-side work runs as fast as any ordinary interpreter.

### Equality

- Same-variant scalars: native `==`.
- Both `Value::Term(a)` and `Value::Term(b)`: `a == b` — O(1) thanks to hash-consing (sound because equal `TermId`s are structurally equal).
- Cross-variant (e.g. `Value::Int(1)` vs `Value::Term(tid_int_1)`): promote the scalar side to `TermId` once and compare. Rare; occurs only when something force-compares heterogeneous representations.

### Closures, streams, lazies

Each lives in its own arena, referenced by a typed `Copy` handle. The handle sits inside the `Value` enum directly (not hidden inside a `Term::Fn`) — simpler than funneling everything through hash-consing. Conversion to `TermId` (needed only when one of these escapes into a fact) allocates a `Term::Fn { functor: <ClosureRepr>, payload: handle_bits }` once; the round-trip is rare and explicit.

### When in doubt, stay scalar

Builtins and core primitives operate on `Value` directly. We only promote to `TermId` when the value is about to cross a boundary that needs structural sharing (the KB, a `Modify` cell, or a value being asserted as a fact).

## Activation stack

```rust
struct Frame {
    op: Symbol,                    // operation being evaluated
    expr: TermId,                  // current expression node (AST term from KB)
    locals: SmallVec<[(VarId, Value); 4]>,
    cont: Continuation,            // what to do with the result
}
```

Note: `expr: TermId` is the AST node under evaluation — expression bodies are stored as hash-consed terms in the KB, so the code pointer is a `TermId`. The **locals and intermediate results** are `Value`, not `TermId`.

`Continuation` enum enumerates the contexts where a sub-expression's result is consumed (if-arm, match-scrutinee-done, let-bound-var, apply-next-arg, …). Evaluation proceeds as `step(&mut self)` repeatedly until the stack is empty.

**Tail-call optimization**: when the current frame's `cont` signals "result is the frame's result," the implementation replaces the top frame instead of pushing.

**Depth cap**: configurable limit (default 1024) prevents runaway recursion.

This shape is also what a future stack-VM wants; migration is "replace `expr: TermId` with `pc: usize` and add an opcode dispatcher."

## KB queries and `LogicalStream`

KB queries are first-class values of type `LogicalStream[T]`. The interpreter represents a `LogicalStream` as `Value::Stream(StreamHandle)`, where `StreamHandle` indexes a side table of lazy sources.

```rust
enum StreamSource {
    Resolver(ResolverState),       // wraps kb::resolve::SearchStream
    Empty,
    Pure(Value),                   // yields a single Value
    MPlus(StreamHandle, StreamHandle),
    Native(Box<dyn StreamImpl>),   // Rust-side user streams
}
```

`splitFirst` is a builtin: given a `Value::Stream(handle)`, it advances the source by one step and returns `Value::Entity { functor: Option.some, named: [Pair(...)] }` or `None`. The remaining `Stream` operations (`head`, `tail`, `collect`, …) are already implemented in stdlib as rules over `splitFirst`, so the interpreter gets them "for free" once `splitFirst` works.

This design means:

- Non-determinism is never an interpreter concern — a non-deterministic computation is just a first-class `LogicalStream` value.
- The resolver becomes an effect-free producer of `LogicalStream`. The interpreter drives it via `splitFirst` calls.
- The laziness story is explicit and matches what the type system already says.

## Memory management

The hash-consed `TermStore` is already a refcounted DAG — and it is structurally acyclic by construction (hash-consing requires knowing a term's hash before allocation, so self-reference is impossible for pure constructor data). Memory management splits by `Value` variant:

- `Value::Int`/`Float`/`Bool`/`Unit` — stack, no management needed.
- `Value::Tuple`/`Value::Entity` — owned inline (SmallVec payload); dropped with the `Value`.
- `Value::Closure`/`Stream`/`Lazy` — handles into arenas, refcounted per arena.
- `Value::Term(TermId)` — `TermStore`'s existing refcount mechanism.

Cycles can only form through three doors, none of which touch `TermStore`:

1. **Mutually recursive closures** sharing an env chain.
2. **`Modify` effect cells** holding closures that capture the same store.
3. **Shared corecursion** (e.g. `ones = cons(1, ones)` implemented as a single reused cell).

All three involve the interpreter's **runtime side-tables** — closure envs, stream sources, store cells. These are the only candidates for cycles, so they're the only targets for GC when/if we need one.

### Tiered strategy

| Tier | Mechanism | Handles |
|---|---|---|
| **v1** | Refcount + arena handles for closures, envs, stream sources. No cycle detection. | Pure data, non-shared lazy streams, simple closures. |
| **v2** | Cycle detection on `Modify`-store inserts → `EvalError::CyclicReference`. | `Modify` effect with a cycle-free invariant. |
| **v3** | Mark-sweep GC over the runtime side-table graph (not `TermStore`). | Shared corecursion, mutual recursion through refs, saved `Suspension` continuations. |

Key insight: **do not GC the hash-consed term store.** It is already optimal. GC, when it arrives, scans only the heap-allocated runtime arenas — a much smaller graph.

### v1 rule

> Closures, stream sources, and store cells live in arenas keyed by typed `Copy` handles. Handles are stored directly in `Value::Closure` / `Value::Stream` / `Value::Lazy` variants (not hidden inside `Term::Fn`). Dropping a `Frame` / `StreamHandle` / `StoreRef` decrements the arena's refcount. Cycles, when introduced by `Modify`, surface as explicit `CyclicReference` errors — loud failure rather than silent leak.

### GC backend choice (v3)

When v3 mark-sweep is needed, three candidate implementations, evaluated honestly:

| Approach | Lifetime pollution | Trait boilerplate | Code volume | Maturity |
|---|---|---|---|---|
| [`gc_arena`](https://crates.io/crates/gc-arena) | Yes — `'gc` on every type touching GC'd data (`Value<'gc>`, `Env<'gc>`, …) | Minimal — `#[derive(Collect)]` | Small (crate carries the weight) | Production (powers [Ruffle](https://ruffle.rs)) |
| Own GC + `Trace`/`GCable` trait | None | Manual per-type impls (could derive-macro our own) | Medium | New |
| Own GC + **concrete tracer** (no trait) | None | **None** — tracing lives in one function | Small-medium | New |

**Concrete tracer.** Because `Value`, `Env`, `StreamSource`, etc. are owned by the `eval` module (closed world), we don't need a `Trace` trait. Put the tracer as a plain function that knows the enum shapes:

```rust
fn trace_value(v: &Value, t: &mut Tracer) {
    match v {
        Value::Closure(h) => t.mark_closure(*h),
        Value::Stream(h)  => t.mark_stream(*h),
        Value::Lazy(h)    => t.mark_lazy(*h),
        Value::Tuple { pos, named } |
        Value::Entity { pos, named, .. } => {
            for v in pos { trace_value(v, t); }
            for (_, v) in named { trace_value(v, t); }
        }
        _ => {} // scalars and Value::Term carry no GC roots
    }
}
```

No `#[derive]`, no lifetime parameter, no trait impls on `Value`. Adding a new `Value` variant requires updating `trace_value` — a property, not a bug: "which variants the GC cares about" becomes a single reviewable decision. This is the Lua-reference-interpreter style, and it's the right shape when the type set is closed.

**`gc_arena`** remains the most robust choice long-term: collection safepoints are enforced by the borrow checker, and the arena guarantees no UB. Its cost is the pervasive `'gc` lifetime parameter, which affects every signature in the eval module. Worth prototyping alongside the concrete-tracer option before committing.

### Swappable arenas

Whatever GC backend we pick in v3, the v1 arenas are designed to be swappable. Each arena exposes a minimal handle-based API:

```rust
trait Arena<T> {
    fn alloc(&mut self, value: T) -> Handle<T>;
    fn get(&self, h: Handle<T>) -> &T;
    fn get_mut(&mut self, h: Handle<T>) -> &mut T;
    // v3 adds: fn sweep(&mut self, live: &HashSet<Handle<T>>);
}
```

v1 `Arena` is `Vec<Slot<T>> + free_list + refcount`. v3 backs it with whatever tracer we pick. Consumers (interpreter, builtins) see only handles — the allocation strategy is invisible to them.

## Laziness

Because the evaluator supports lambdas, thunks (call-by-name) come for free: `λ(). expr` is the defer, function application is the force. No special language construct needed. The existing `Stream` / `LogicalStream` sorts are already call-by-name in this style — `splitFirst` produces fresh handles on demand.

**Default evaluation strategy: strict (call-by-value).** Opt-in laziness via the type system, not pervasive.

### When λ is not enough: memoized laziness

Call-by-name recomputes on each force. For shared work — "three consumers pull the same stream head; compute it once" — we need call-by-need, which requires a mutable one-shot slot. Introduce a stdlib sort:

```anthill
sort anthill.prelude.Lazy
  sort T = ?
  sort E = ?

  operation delay(f: Function[Unit, T]) -> Lazy @E
  operation force(l: Lazy) -> T effects E
end
```

The interpreter backs this with a `LazyArena`:

```rust
enum LazySlot {
    Unforced { thunk: ClosureHandle },
    Forced   { value: Value },
}
```

First `force(l)` evaluates the thunk, stores the result, overwrites the slot. Subsequent forces read the cached value.

### Effects flow through `force`

A lazy value of type `Lazy[T, E]` carries the effect row `E` of its deferred computation. Forcing it propagates `E` into the caller's effect signature. This falls out of the existing effect system; no new machinery.

Pragma: a thunk that invokes effects still runs those effects *at the force site*, not the `delay` site — which is the correct semantics and matches the type-level story.

### Stream variants (post-v1)

`Stream` today is implicitly call-by-name. For shared-work use cases we can add a memoized variant in stdlib:

- `Stream[T, E]` — non-sharing (current), `splitFirst` produces a fresh tail handle each call.
- `SharedStream[T, E]` — sharing, tail handles are cached in a `Lazy`-like memo arena.

Both satisfy the abstract `Stream` spec. Consumers pick based on work-sharing requirements.

### No pervasive laziness

Anthill commits to strict-by-default, explicit opt-in laziness via `Lazy[T, E]` and stream sorts. Reasons:

- Evaluation order is predictable — no space-leak class of bug from pervasive thunks.
- Effects stay explicit — no surprise effects triggered by forcing a pattern match deep in someone else's expression.
- Implementation is ~50 lines of arena bookkeeping, not a runtime overhaul.
- Spec-oriented character: "this is lazy" is a type, not an implicit property of position.

## Effects

`Effect` is a typed resource (e.g. `IO`, `Modify[store]`, `Suspension`, `Branch`). The interpreter carries an effect-handler registry:

```rust
type EffectHandler = Box<dyn FnMut(&mut Interpreter, Symbol, &[Value]) -> Result<Value, EvalError>>;
struct Interpreter {
    handlers: HashMap<Symbol, EffectHandler>,
    ...
}
```

An effectful operation call dispatches through the registry:

- Handler present → call it.
- No handler → `EvalError::UnhandledEffect`.

For v1 we implement `IO.print` and enough of `Modify` to mutate a user-provided store. `Suspension` and `Branch` are stubs that return `UnhandledEffect` until the VM lands.

## Rust interop

### Anthill calling Rust (builtins)

```rust
impl Interpreter {
    pub fn register_builtin<F>(&mut self, qname: &str, f: F)
    where F: Fn(&mut Self, &[Value]) -> Result<Value, EvalError> + 'static;
}
```

Builtins back operations by qualified symbol. Arithmetic, string ops, collection primitives, `splitFirst`, `println` all come in this way. Mirrors `kb::resolve::builtins` in shape.

### Rust calling Anthill (embedding)

```rust
impl Interpreter {
    pub fn new(kb: KnowledgeBase) -> Self;
    pub fn call(&mut self, op: Symbol, args: &[Value]) -> Result<Value, EvalError>;
    pub fn kb(&self) -> &KnowledgeBase;
    pub fn kb_mut(&mut self) -> &mut KnowledgeBase;
}
```

Consumers (CLI, tests, `anthill-todo`) drive the interpreter through `call`.

### Value marshaling

`persistence::term_ser` already converts between terms and Rust types for TOML/JSON; it operates on `TermId`, so values crossing this boundary first promote via `Value → TermId`. Direct builtins pattern-match on `Value` variants; promotion to `TermId` happens only when the builtin's work requires it.

## CLI: `anthill run`

```bash
anthill run <file.anthill> [--entry qualified.Name] [--arg '<term>']...
```

- Parses + type-checks (already wired via `load_all`).
- Locates entry operation by qualified name. Default: `main`.
- Instantiates an `Interpreter`, registers stdlib builtins.
- Calls entry. Prints the returned term.

## Open design decisions

1. **Pattern match completeness**: when no arm matches, runtime panic or dedicated `MatchFailed` effect? Suggest effect — composes with the error story for other failure modes.
2. **Variable scoping in `let`**: shadowing allowed? Suggest yes, mirrors host languages.
3. **Recursion semantics**: operations are recursive by default (no `rec` keyword). Mutual recursion across operations in the same sort: allowed.
4. **Tail calls across operation boundaries**: TCO works within a single frame today; cross-operation TCO requires a small protocol change. Defer to post-v1.
5. **`println` I/O**: single `IO` effect with `println(s: String)`, or a richer `IO` ADT? Suggest single `println` + `readline` for v1.
6. **Error representation**: `EvalError` is a plain Rust enum returned outward; not visible inside anthill as a sort. If programs need to handle errors, model with `Result[T, E]` and `fail` effect.

## Milestones

**M1: walking skeleton** — literals, variables, `if`, `let`, function call (no match, no collections). Can run `main() -> 42`.

**M2: full expression set** — match (exhaustive check already done in typer), lambda + closures, collection literals.

**M3: builtins** — arithmetic, comparison, string, list/set/map primitives, `println`.

**M4: `LogicalStream` + KB queries** — `splitFirst`, `collect`, resolver bridge. Can run a program that queries the KB and iterates.

**M5: effect handlers** — `IO`, `Modify`. Stubbed `Suspension`/`Branch`.

**M6: CLI** — `anthill run` command.

Each milestone lands independently with its own tests.

## Migration to a VM (post-v1)

When we implement `Suspension` / `Branch` properly:

1. Add an encoder: `TermId` body → `Vec<Op>` bytecode.
2. Replace `Frame::expr: TermId` with `Frame::pc: usize` + a frame-local bytecode handle.
3. `Suspension` snapshots the frame stack + substitution; `resume(handle, value)` restores them.
4. `Branch` clones the top N frames.

Values stay `Value`, builtins keep their signatures, effect handlers keep theirs. Only the frame step loop changes.

## Non-goals

- Persistent continuations across process restarts (needs serialization of handles; later).
- Native compilation from anthill (we already have `codegen/rust.rs` for compile-to-Rust; different path).
- JIT / specialization.
- Multi-threaded evaluation.
