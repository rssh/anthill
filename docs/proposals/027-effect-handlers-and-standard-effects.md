# 027: Effect Handlers and Standard Effects

## Status: Draft (handler dispatch partially implemented in `eval/effects.rs`; this proposal canonicalizes the handler model and the standard effect catalog)

## Depends on: 002 (arrow sorts with effect annotations), 013 (effects as sorts and facts), 026 (expression evaluator), 026.1 (value-integrated KB queries)

## Relates to: WI-050 (M5 effect handlers), WI-075 (resolver `push_choice` primitive — substrate for the `Branch` handler), 037 (Modify framework — supersedes the §4 "twin operations" approach for state mutation)

## Motivation

Proposal 013 establishes the static/declarative model for effects: effect kinds are sorts, an operation's effect row is a set of sort instantiations, effect checking is KB querying. 013 deliberately leaves *interpretation* — what running an effectful operation actually does — to the realization layer.

Proposal 026 (Effects) sketches a runtime handler registry on the `Interpreter` and notes that handlers exist. The Rust evaluator has implemented this for some cases (`stdio_console_*`, `default_modify_handler`).

What's missing — and what this proposal supplies — is:

1. A **canonical handler model**: what exactly a handler is, what it can and can't do, how it composes, how it's scoped.
2. A **standard effect catalog**: precise semantics for the well-known effects already declared in `stdlib/anthill/prelude/effects.anthill` (`Suspension`, `Modify`, `Error`, `Branch`) plus `Console*`. Each gets a contract: what operations it provides, what the default handler does, what alternative handlers can do.
3. The **`Branch` design** in detail: how an effect raised in a functional expression (`branch(a, b)`) is interpreted by the runtime through the resolver's `push_choice` primitive, unifying the rule-body disjunction story (WI-075) with the expression-level nondeterminism story.
4. Forward reference from 013.

Once landed, this proposal — together with 013 — is the complete story: 013 says what an effect *is*; 027 says what it *does*.

## Architecture: kernel vs host

Anthill is a kernel language with multiple host-language implementations: the Rust implementation (`rustland`, primary), the Scala 3 implementation (`scaland`, in progress), and a planned C mapping (targeting embedded environments — bare-metal and freestanding C, where C++ standard library facilities like `std::function` / `std::variant` / heap allocation may be unavailable). The kernel itself is host-independent — terms, sorts, rules, the resolver semantics, the value model, the effect-as-sort declarations from 013 — all of these are specified once and realized in each host.

Effect handlers belong to the *realization layer* (the unsafe boundary that 013 explicitly carves out as "outside the kernel"). That means handlers themselves cannot be host-independent values — each host has its own native callable type. But the *contract* a handler satisfies — what inputs it receives, what services it may call, what outputs it may produce — must be specified once in host-neutral terms, then realized per host.

### Terminology used in this proposal

To avoid the very common slip of using "resolver" as shorthand for "the whole anthill engine," this proposal pins the following names:

- **Runtime** (or "the anthill runtime") — the union of components that together execute an anthill program in a given host: the `KnowledgeBase` store, the resolver, the expression evaluator, the stream arena, and the effect-handler registry. This is what the `RuntimeAPI` exposes operations on; this is what handlers interact with.
- **Resolver** — strictly the SLD search engine inside the runtime (`anthill-core/src/kb/resolve.rs` in Rust): the choice-point machinery, frame stack, backtracking, `SearchStream`. The resolver owns choice points and continuations, but it is one component of the runtime, not the runtime itself.
- **Evaluator** — the expression-evaluation component (`eval/` in Rust): closures, pattern matching, builtin dispatch, effect-handler invocation.
- **`RuntimeAPI`** — the abstract operation surface that handlers call into. It exposes operations on all five runtime components (KB access, resolver-level `push_choice` and `fail_branch`, eval-level stream allocation, etc.) under one host-language handle. It is *not* "the resolver API" — calling it that would mis-name the layer.

When this proposal says "the resolver does X" we mean the SLD search engine specifically. When it says "the runtime does X" we mean the broader engine acting as a coordinated whole.

This proposal therefore separates:

1. **The abstract handler contract** — what every host's handler implementation must satisfy. Specified in language-neutral terms.
2. **The runtime API surface** — the set of operations the kernel exposes to handlers (KB access, choice-point manipulation, stream allocation, error raising). Specified abstractly as an operation list.
3. **Per-host mappings** — how Rust, Scala, and C realize the contract using their native callable + reference types. Rust is shown in detail as the worked example; Scala and C are sketched. The C mapping targets embedded (bare-metal/freestanding) deployments and intentionally avoids any dependency on the C++ standard library — the contract must be expressible with C function pointers + explicit context structs, no closures, no exceptions, no dynamic allocation in the hot path.

## Abstract Handler Contract

### Inputs

A handler is invoked with three abstract inputs:

- **`op_sym: Symbol`** — the operation being invoked under this effect. Effects with multiple operations (e.g. `Console` has `print`, `println`, `read_line`) dispatch internally on this symbol. Effects with a single operation can ignore it.
- **`args: List[Value]`** — fully evaluated argument values. Argument arity and types match the operation's declared signature.
- **a `RuntimeAPI` handle** — a handle through which the handler can call runtime operations (described next). The handle's exact shape is host-specific; the *operations it exposes* are host-independent.

### Outputs — the `HandlerAction` carrier

A handler does **not** receive the continuation as an input parameter. Instead, the handler returns a structured carrier value — `HandlerAction` — that describes what the runtime should do with the implicit continuation. The runtime (which holds the continuation in its frame stack) interprets the carrier. This keeps the handler interface free of continuation reification while still expressing the full set of control-flow decisions a handler can make:

```
HandlerAction :=
  | Pure(value: Value)                            -- resume current path with this value (linear, common case)
  | Throw(payload: Value)                         -- raise an anthill-level error
  | Fail                                          -- abort current branch (resolver-level fail)
  | Choice(value: Value, alts: List[AltMarker])   -- resume now with `value`; on backtrack, try alts in list order
  | Suspend(snapshot: ContSnapshot)               -- paused; runtime returns to driver; resume later via snapshot
```

Where `AltMarker` is an opaque value the runtime understands (typically a snapshot the resolver can re-enter on backtrack), and `ContSnapshot` is a snapshot of the activation stack at the operation call site (cloned via the existing defunctionalized eval). The handler doesn't construct continuations; it labels what the alternative or suspended paths *are* in terms the runtime can re-enter.

**`Choice` is n-ary** — the alternatives list can be empty, singleton, or arbitrarily long:

- `Choice(v, [])` is observably equivalent to `Pure(v)` (no alternatives to backtrack to). `Pure(v)` remains as a separate variant for intent-clarity in handlers that genuinely have no branching.
- `Choice(v, [alt])` is the binary case: try `v` first, on backtrack try `alt`.
- `Choice(v, [alt1, alt2, ..., altN])` is n-ary: try `v` first, on backtrack try `alt1`, then `alt2`, then ... `altN`.

**Trial order:** list order = trial order on backtrack. The runtime installs alternatives so that the first list element fires first on the next backtrack, the second next, and so on. Implementation: push in reverse (LIFO push of `altN` ... `alt1` after registering `v` as the current path), so the resolver's LIFO backtracking yields the first list element first.

**The variants cover the canonical handler patterns:**

- `Pure` — Modify, Reader, most ordinary handlers. Linear single-shot.
- `Throw` — Error. Abort with a typed payload.
- `Fail` — Branch.fail (search-level failure that the resolver picks up).
- `Choice` — Branch (multi-shot via N paths). The runtime registers all `alts` as resolver choice points in trial order.
- `Suspend` — Async, Generator, Cooperative scheduling. The handler stashes `snapshot` somewhere reachable (host async runtime, stream-pull cell, scheduler queue) before returning. The runtime returns control to its driver (e.g., `interp.call` returns "incomplete"); whoever holds the snapshot resumes it later by calling `runtime.resume_with(snapshot, value)`.

This choice has three consequences worth being explicit about:

1. **The handler stays free of continuation values.** A Rust handler returns `HandlerAction`, not `Box<dyn FnOnce(Value) -> ...>`. A C handler returns the tagged-union carrier, not a function pointer to "the rest of the program." Continuations stay where they belong: inside the runtime, encoded by the resolver's frame stack.

2. **The runtime interprets the carrier.** When a handler returns `Pure(v)`, the runtime resumes eval normally with `v`. When it returns `Choice(v, alt)`, the runtime sets up a choice point on the resolver (the same mechanism `anthill.kernel.push_choice` exposes — see RuntimeAPI below) such that the current path proceeds with `v` and a backtrack will pick up `alt`. When it returns `Fail`, the runtime invokes the resolver's branch-fail. When it returns `Throw(p)`, the runtime aborts eval and surfaces the payload as an error.

3. **Direct `RuntimeAPI` calls and the carrier are complementary, not redundant.** The runtime exposes `snapshot_eval_state`, `resume_with`, `push_choice`, `fail_branch`, plus all the non-control operations (`kb_query`, `kb_assert`, `stream_alloc`, etc.). The carrier covers the *exit-time control-flow* shape; the API covers everything else. The composition rule is spelled out in the next subsection.

### Semantics

- A handler is invoked exactly once per operation call. Multi-shot resume is not handled by re-invoking the handler — it's handled by the runtime re-entering the eval at the resolver-installed choice point that the carrier (or `push_choice` API call) set up.
- A handler runs to completion (returns a `HandlerAction`) before control returns to the evaluator.
- A handler's only side effects on the kernel state are those it makes through the `RuntimeAPI` *during* its run, plus the action carried by its return value.
- The continuation is not visible to the handler as a value. It exists implicitly in the resolver's frame stack and is manipulated indirectly through the carrier or the `push_choice`/`fail_branch` API calls.

### Why the handler doesn't receive an explicit continuation

The natural design question: "shouldn't a handler that wants to resume execution receive `k: Continuation` as an argument?" Two reasons we didn't:

- **Continuations exist already, in the activation stack.** The defunctionalized evaluator (per 026/M1) holds the program state as cloneable data. A handler that wants to capture a continuation gets it via `RuntimeAPI.snapshot_eval_state()` (which clones the activation stack) and stashes the resulting `ContSnapshot`. No CPS transform, no fibers, no extension to the eval engine — the substrate is there.
- **Carrier captures what most handlers want.** The five `HandlerAction` variants directly encode the common patterns (`Pure` linear, `Throw` error, `Fail` branch-fail, `Choice` two-way fork, `Suspend` paused). Handlers in the canonical patterns return one of these; only handlers that need exotic shapes drop to imperative API.

`ContSnapshot` is the user-facing equivalent of an explicit `k`, exposed via `runtime.resume_with(snapshot, value)`. It just isn't passed as a handler input — handlers that want it call `snapshot_eval_state()` to get one.

### Carrier vs `RuntimeAPI`: the composition rule

The carrier and the imperative `RuntimeAPI` are not equivalent — they're complementary. Each covers a different responsibility:

- **The carrier covers handler *exit*** — what the runtime does with the implicit continuation when the handler returns. The five variants exhaust the canonical exit shapes.
- **The `RuntimeAPI` covers everything the handler *does during its run*** — KB queries, KB assertions, stream allocation, snapshotting, and (for the rare cases the carrier can't express cleanly) imperative resolver manipulation.

Where they overlap, the rule is:

1. **Prefer the carrier for the exit shape.** A handler that returns `Pure(v)` is clearer than one that calls `runtime.resume_with(snapshot, v)` followed by some null exit. A handler that returns `Choice(v, alt)` is clearer than one that calls `runtime.push_choice(alt)` and returns `Pure(v)`.

2. **Use the `RuntimeAPI` for non-control work** unconditionally. KB queries, asserts, stream allocation, snapshot creation are all imperative operations the handler does during its run, before returning. The carrier doesn't try to express them.

3. **Use imperative `RuntimeAPI` for control patterns the carrier doesn't cover cleanly.**
   - **Conditional branching based on mid-handler computation**: handler runs `kb_query`, branches in its own logic, returns the appropriate carrier variant. Carrier still suffices; the API was used for the query.
   - **Multiple snapshots in flight**: a Generator handler that pre-computes *several yielded values up front* before returning would call `snapshot_eval_state()` repeatedly, stash each, and return `Suspend(first_snapshot)`. Multi-snapshot management is API; the final exit is `Suspend`.
   - **Dynamically-sized choice list assembled by iteration**: handler iterates a query result, calls `runtime.push_choice(alt_i)` for each row, returns `Pure(default_value)` for the current path. The same effect could be achieved by building the list and returning `Choice(default, list)`; pick whichever reads better.
   - **Effects with no clean carrier shape**: the rare advanced handler that wants explicit ordering or conditional rollback of the resolver's choice-point stack drops to imperative API.

4. **Mixing carrier `Choice` with imperative `push_choice` in the same handler is allowed** but creates ordering subtleties. Specified rule: API-installed alts fire LIFO before the carrier's `Choice.alts`; within the carrier's `Choice.alts`, list order is preserved. The carrier's `Choice.value` is the current path. Documented in the runtime contract; handlers that mix should comment the intent. Discouraged in stdlib code; allowed for advanced handlers that genuinely need it.

5. **Handlers must always return a `HandlerAction`.** Even if the handler did all its work via imperative API calls, it must terminate with a carrier value. The simplest terminal is `Pure(unit)` (resume normally), or `Fail` (abort branch), or `Suspend(snapshot)` (pause).

This rule eliminates the ambiguity of "should this handler use carrier or API?" — *both*, with each used for the role it fits.

## Runtime API Surface

These are the operations the kernel exposes to handlers. Each must be realized by every host implementation under its own type names but with the same semantics:

### KB access
- **`kb_query(goals: LogicalQuery) -> SearchStream`** — run a query against the current KB. Same semantics as `kb.execute_logical_query` (per 026.1).
- **`kb_assert(term: Term, sort: Type) -> Option[FactId]`** — assert a fact under constraint checking. Same semantics as `KB.assert` (per reflect.anthill).
- **`kb_reify(term: Term, subst: Substitution) -> Term`** — walk a term substituting bound vars.

### Choice / search control
- **`push_choice(alt: AltMarker)`** — register an alternative continuation at the current frame. The substrate WI-075 introduces. Used by the runtime when interpreting `Choice`, and by handlers that need n-ary branching imperatively.
- **`fail_branch()`** — terminate the current search branch (resolver-level failure). Used by the runtime when interpreting `Fail`, and by handlers that abort imperatively.

### Continuation snapshot / resume
- **`snapshot_eval_state() -> ContSnapshot`** — clone the current activation stack as an opaque snapshot value. Use to capture "the rest of the computation past this operation call" for later resume. Returned snapshot is consumable (single-shot) or cloneable (multi-shot) depending on the runtime's contract; concrete hosts document which.
- **`resume_with(snapshot: ContSnapshot, value: Value) -> ...`** — re-install the snapshot's activation stack and continue evaluation as if the suspended operation had returned `value`. Used by external resumers (host async callback when a promise resolves; stream-pull function when a generator is pumped; scheduler when picking a parked fiber).
- **`register_undo(undo: HostCallable)`** — install a callback to fire when the current snapshot is abandoned (resumed from a sibling branch). Used by the runtime's **branch-handling machinery** (per proposal 037) to enforce the *resource's branch-interaction contract*: when entering Branch the runtime snapshots resources whose contract is branch-local-snapshot, and registers the undo via this hook. The callback runs at backtrack time in reverse-registration order for entries on the same snapshot. **This is not a handler concern** — Modify handlers are oblivious to whether they're writing to a snapshot or the parent state; they always write to "the active state" of the resource, and the runtime decides what active means.

### Streams
- **`stream_alloc(source: StreamSource) -> StreamHandle`** — allocate a stream in the eval-layer arena. Used to expose handler-produced sequences as anthill `LogicalStream` values.
- **`stream_split_first(handle: StreamHandle) -> Option[(Value, StreamHandle)]`** — pump a stream by one element.

### Error raising
- **`raise_error(payload: Value) -> Nothing`** — raise an anthill-level error. Used by the `Error` handler. Caller never returns.

### Symbol / value introspection (read-only)
- **`resolve_qualified_name(name: String) -> Option[Symbol]`** — look up a symbol.
- **`value_type_name(v: Value) -> String`** — for diagnostics.

This API is *itself a kernel concept* — the operations above are the same ones available to anthill code via `anthill.reflect.KB`, `anthill.kernel`, etc. A handler is essentially a host-language piece of code that can call the same KB-facing operations that anthill source code can. The host-language type signatures are different (a Rust handler holds a `&mut KnowledgeBase`; a Scala handler holds a `KnowledgeBase` reference), but the *operations* are the same.

A future direction: write handlers *in anthill itself* for derived effects that bottom out in primitive RuntimeAPI calls. The primitive effects (`Modify`, `Console*`, `Error`'s host-error fallback, `Branch`'s push_choice) must live in the host because they touch real-world resources or kernel internals. Everything above that could in principle be anthill code that calls the same RuntimeAPI surface. Out of scope for this proposal but the layering admits it.

## Host-Language Mappings

### Rust mapping (the worked example, partly implemented)

```rust
pub type EffectHandler =
    Box<dyn FnMut(&mut Interpreter, Symbol, &[Value]) -> Result<Value, EvalError>>;
```

- **`op_sym`** → `Symbol` (interned u32, identical to the kernel's symbol table).
- **`args`** → `&[Value]` (borrow into the evaluator's argument vector — handler may not retain past return).
- **`RuntimeAPI` handle** → `&mut Interpreter`. The interpreter implements every RuntimeAPI operation via inherent methods: `interp.kb_mut().execute_logical_query(...)`, `interp.alloc_stream(...)`, `interp.kb_mut().assert_fact(...)`, etc. Choice-point manipulation routes through `interp.kb_mut()` once `push_choice` lands (WI-075).
- **return** → `Result<Value, EvalError>`. Resolver-level failure for `Branch.fail` is conveyed by an internal `EvalError::ResolverFail` variant that the evaluator unwraps before propagating outward.

### Scala mapping (sketch)

```scala
type EffectHandler =
  (interp: Interpreter, opSym: Symbol, args: Seq[Value]) => Either[EvalError, Value]
```

Same shape: interpreter as the RuntimeAPI handle, opSym + args as inputs, `Either` for the outcome. Captured resources go in the closure, just as in Rust. Effectively a 1:1 port — the closure types differ (no `Box<dyn FnMut>` ceremony) but the contract is identical.

### C mapping (sketch — targets embedded / freestanding)

The C target is the strictest of the three: no closures, no exceptions, no `std::function`, no implicit allocation, no RTTI. The mapping uses the **function-pointer-plus-context** idiom (universal C closure approximation) and **tagged unions** for sum types.

```c
/* Outcome of a handler invocation — discriminated union (tagged) */
typedef enum {
    AH_RESULT_VALUE,   /* op returned a value */
    AH_RESULT_ERROR,   /* eval-level error */
    AH_RESULT_FAIL     /* resolver-level branch failure */
} ah_result_tag;

typedef struct {
    ah_result_tag tag;
    union {
        ah_value_t  value;     /* tag == AH_RESULT_VALUE */
        ah_error_t  error;     /* tag == AH_RESULT_ERROR */
        /* AH_RESULT_FAIL has no payload */
    } payload;
} ah_handler_result_t;

/* Argument view — pointer + length, no ownership transfer */
typedef struct {
    const ah_value_t *data;
    size_t            len;
} ah_value_span_t;

/* The handler function pointer type.
 *   ctx          — arbitrary user data captured at install time (closure-equivalent)
 *   runtime      — opaque handle for calling RuntimeAPI operations
 *   op_sym       — operation symbol being dispatched
 *   args         — view of evaluated argument values
 *
 * Returns the handler outcome by value (no heap allocation).
 */
typedef ah_handler_result_t (*ah_effect_handler_fn)(
    void                  *ctx,
    ah_runtime_t          *runtime,
    ah_symbol_t            op_sym,
    ah_value_span_t        args);

/* Installation pairs the function pointer with its context */
typedef struct {
    ah_effect_handler_fn  fn;
    void                 *ctx;   /* opaque to runtime; freed by host */
} ah_effect_handler_t;

void ah_install_handler(ah_runtime_t *rt,
                        ah_symbol_t   effect_sym,
                        ah_effect_handler_t  h);
```

**Key properties of this mapping:**

- **No `std::function` / no heap closure.** The `(fn, ctx)` pair is the universal C closure approximation. The `ctx` is whatever the embedder needs — a pointer into a static struct, an arena handle, a per-resource state block. The runtime never allocates or frees it; ownership stays with the embedder.
- **Result by value, not by exception.** No exception machinery is required (which embedded toolchains often disable or omit). The `ah_handler_result_t` discriminated union covers all three outcomes.
- **No `std::span`.** Argument view is the explicit `(pointer, length)` pair, the canonical C idiom.
- **RuntimeAPI is a struct-of-fn-pointers (or opaque handle).** `ah_runtime_t` is opaque to the handler; the runtime exposes operations through `ah_runtime_kb_query(runtime, ...)`, `ah_runtime_push_choice(runtime, ...)`, etc. Whether these are direct C function calls into the runtime library or function pointers in a vtable is an implementation choice — both are valid.
- **No allocation in the hot path.** The handler signature returns a fixed-size struct by value. `ah_value_t` itself may need to be copyable / trivially-relocatable for embedded targets — a separate design point in the value-representation story (out of scope here, but the implication for this proposal is: the handler contract doesn't introduce any allocation requirements beyond what `ah_value_t` already has).

**What embedded targets get:**

- A handler can be a static function taking a `ctx` pointing at a statically-allocated state struct — no dynamic memory needed.
- The runtime can be linked as a freestanding library (no libc/libstdc++ dependency) provided the kernel itself is built freestanding.
- All cross-host conformance tests (same Standard Effect Catalog semantics) apply unchanged; the embedded host just realizes the same contract with different syntax.

**What the C mapping deliberately excludes:**

- No automatic destructor invocation (handlers must explicitly tear down `ctx` on uninstall).
- No template-style genericity (effect-handler installation takes a specific function pointer type, not a generic callable).
- No exception-based error propagation (results are explicit return values).

### Common requirements across hosts

Every realization must:

1. Provide a way to install a handler keyed by effect-sort symbol (`install_handler` / `removeHandler` / equivalent).
2. Implement the full RuntimeAPI surface as inherent methods on the interpreter / runtime handle.
3. Convert resolver-level failure into the host's failure idiom (Result/Either/variant) so `Branch.fail` propagates correctly.
4. Carry handler closures with no implicit ownership constraints beyond what the host idiomatically requires (e.g. `'static` in Rust, GC-managed in Scala).

The semantics specified in the rest of this proposal are stated in terms of the abstract contract; each host implementation realizes them via its own mapping but should produce observably identical behavior.

### What kind of handlers are these — choice and rationale

The literature offers a spectrum:

- **One-shot, non-resumable** (Java-style exception handlers): handler runs, returns a value, control resumes after the call site. Cannot re-invoke the rest of the computation.
- **Multi-shot, resumable** (algebraic effect handlers à la Eff/Koka/Frank): handler receives a continuation, can call it zero, one, or many times. Required for nondeterminism, generators, ambient backtracking.
- **Deep vs shallow**: a deep handler re-handles the continuation under itself; a shallow one does not.
- **Lexical vs dynamic scoping**: lexical handlers are pinned to a syntactic region (`with H handle E`); dynamic handlers use a global registry.

Anthill's choice (already reflected in `eval/effects.rs`):

- **Dynamic scoping** — a global per-`Interpreter` registry keyed by effect-sort symbol. Handlers are installed before evaluation begins (typically by the embedder / CLI / test) and replaced wholesale, not stacked.
- **Non-resumable for most effects** — the handler computes a return value directly. This covers `Modify`, `Read`, `Error`, `Console*`, `Suspension` cleanly: none of them need to invoke the continuation themselves.
- **Multi-shot semantics for `Branch`** — but achieved *by the resolver*, not by capturing an explicit eval continuation. The `Branch` handler raises `anthill.kernel.push_choice` at the resolver layer, which forks the underlying `SearchStream`; the rest of the expression then evaluates twice (once per branch) under the search machinery, yielding a stream of values rather than a single value. This works because `Branch` declares `Suspension` as a sub-effect (per the catalog below) and the resolver's `SearchStream` is *the* implementation of `Suspension` in v1 — multi-shot continuation reuse without explicit continuation reification.

This is a deliberate choice with a sharp tradeoff:

**Pros**
- The handler interface stays simple — a `FnMut` returning a `Value`. No continuation reification, no CPS transform of operation bodies.
- Dynamic scoping matches what embedders need (install once, run many programs).
- Multi-shot semantics for `Branch` come for free from the existing resolver instead of requiring a second multi-shot mechanism in the evaluator.

**Cons**
- No user-definable resumable effects beyond `Branch` in v1 — no anthill-source way to write a `Generator`, `Async`, or custom resumable effect. The type-level vocabulary (`Suspension` as a sub-effect declaration) is available now; the implementation strategy (CPS-transformed eval, defunctionalized stack, or host-fiber-backed eval) is explicitly out of scope for v1. See the `Suspension` entry in the catalog for the three implementation paths and why we defer.
- Dynamic scoping makes lexical "with handler" blocks non-trivial to add later. Acceptable v1 limitation.
- `Branch` semantics depend on the resolver/`SearchStream` substrate — handlers for `Branch` only work in evaluation contexts that have a `SearchStream` available (which is all of them today, since `Interpreter` always has access to the KB).

### Dispatch path

For an operation call `f(args)` where `f` declares `effects (E1, E2, ...)`:

1. Evaluate `args` left-to-right.
2. For each `Ei` in the effect row (in declaration order), check the handler registry. The first effect with a registered handler claims the call.
3. If a handler is found, invoke it with `(interp, op_sym, args)` and use its return value.
4. If no handler is found for any declared effect AND `f` has no operation body, raise `EvalError::UnhandledEffect`. (If `f` has a body, the body runs — handlers override bodies, not the other way around.)

This means handlers shadow operation bodies. That is by design: a handler installed for `Modify` overrides the abstract `get` and `set` operations regardless of what (if any) default body they may have. Without a handler, operations on abstract effect kinds simply have no implementation and the `UnhandledEffect` error fires.

### Handler installation

```rust
impl Interpreter {
    pub fn install_handler(&mut self, effect_sym: Symbol, h: EffectHandler) -> Option<EffectHandler>;
    pub fn remove_handler(&mut self, effect_sym: Symbol) -> Option<EffectHandler>;
    pub fn has_handler(&self, effect_sym: Symbol) -> bool;
}
```

Returns the previously-installed handler (if any), so embedders can save-and-restore for scoped use.

The CLI (`anthill run`) installs default handlers for the standard effects below before invoking the entry operation. Tests install scripted/buffered variants. Embedders install whatever suits their use case.

## Standard Effect Catalog

The effects below are declared in `stdlib/anthill/prelude/effects.anthill` and `console.anthill` today. This section specifies the operational semantics each handler must provide.

### Suspension — continuation-capture marker

```anthill
sort Suspension end
fact Effect[T = Suspension]
```

**Operations:** none directly. `Suspension` is structural — its presence in an effect row marks an operation as one that may interact with its continuation in non-linear ways, rather than naming an operation of its own.

**Semantics:** `Suspension` declares that the operation **may interact with its continuation in non-linear ways** — capture it, resume it later, resume it more than once, abort it, or never resume it. Functions that do *not* carry `Suspension` in their effect row are guaranteed to return linearly: the call site receives the result and continues; the continuation was never reified, never escaped, never resumed twice.

This is a real type-level distinction with operational teeth:
- `effects ()` — pure, total, bounded. Compiler can inline freely; no stack preservation needed.
- `effects (Modify, Error)` — side-effecting but linear. The call returns at most once via the normal return path; on error it never returns.
- `effects (Suspension)` (or any effect whose declaration carries Suspension as a sub-effect) — may suspend. The call site must be prepared for the continuation to be reified, possibly resumed later, possibly resumed multiple times, possibly never resumed. Stack/state preservation requirements are stricter; certain optimizations (TCO across suspension points, stack-only continuation representation) become unsafe.

**Default handler:** there is no operation to dispatch on directly. `Suspension` is a marker that other effect handlers rely on — when a `Branch` (or `Generator`, or `Async`, or any resumable effect) handler returns a `Choice` carrier or invokes `push_choice`, it is doing so on operations whose effect rows include `Suspension` (transitively, via sub-effect derivation).

**Why it's the foundation for continuation-based effects:**

Every effect that needs to do anything beyond "compute a value and return" requires `Suspension`:
- **Branch** — needs to invoke its continuation once per alternative (multi-shot resume).
- **Generator / Yield** — needs to suspend with a value, resume later when the consumer pulls.
- **Async / Await** — needs to suspend until an async result is ready, then resume.
- **Soft-cut, ITE, custom backtracking** — need to capture the continuation as a value that can be discarded or invoked.
- **Resumable errors** — would need to capture the continuation so a handler can resume with a fallback value.

Each of these has its own surface effect (e.g. `Generator[T]`, `Async[T]`, `Branch`) but they all relate to `Suspension` as a sub-effect: an effect declaration like `Generator[T]` should derive `Suspension` so callers of generator-using operations see the suspension marker propagate up the effect row.

**Sub-effect derivation (analog of the `Read ⊑ Modify` pattern from 013):**

```anthill
-- Any effect that captures continuations implies Suspension
rule Effect[T = Suspension] :- Effect[T = Branch]
rule Effect[T = Suspension] :- Effect[T = Generator[?t]]
rule Effect[T = Suspension] :- Effect[T = Async[?t]]
```

Operationally: a function declared `effects (Branch)` is treated by typing as also having `effects (Suspension)` — call sites see "this may suspend" without needing to know the specific resumable effect.

**Implementation substrate: the activation stack already exists**

Per proposal 026 §Activation stack (`rustland/anthill-core/src/eval/frame.rs`, `eval/eval.rs`), the Rust evaluator is **already defunctionalized**: it runs as a single `step()` loop over an explicit `ActivationStack` of `Frame` values, with `AwaitState` enumerating the in-progress positions (`ChooseBranch`, `LetBind`, `MatchDispatch`, `ApplyArgs`, `ConstructorArgs`, `OperationResult`). Host Rust call depth stays O(1) for any program depth. The `eval.rs` header comment puts it plainly: "Tree-walking reducer — continuation-passing."

This means the eval state is **already data**, not host stack. Continuation-capturing effects (Branch, Generator, Async, …) don't require an interpreter refactor — the substrate is there. What they require is a small set of glue pieces on top:

1. **`Clone` for `Frame` and `ActivationStack`** — currently only `Debug`; needs `Clone` so a snapshot can be cloned for multi-shot resume. All field types (`Symbol`, `TermId`, `Vec<Value>` where `Value: Clone`, `AwaitState` variants over cloneable data, `ClosureHandle` which is already refcount-cloneable) support this; the change is mechanical.

2. **Snapshot / resume operations on the runtime** — `snapshot_eval_state() -> AltMarker` captures the current activation stack (clone); `resume(alt_marker, value: Value)` re-installs it and continues with `value` as the suspended call's return. The runtime owns this; handlers see only the `AltMarker` opaque value via the carrier (or via direct `RuntimeAPI` calls for imperative use).

3. **Carrier wiring** — when a handler returns `Choice(v, alt)`, the runtime: (a) installs `alt` as a resolver-level alternative via `push_choice` (WI-075), (b) resumes the current path with `v`. When a handler returns `Pure(v)`, just resume. When `Fail`, invoke resolver branch-fail. When `Throw(e)`, abort eval with the error.

4. **State semantics under multi-shot resumption** — the carrier's `Choice` with multi-shot semantics imposes a real constraint on what the runtime cloning model must guarantee. The activation stack is cloned per snapshot (item 1 above), but the *rest* of the runtime — `KnowledgeBase`, stream sources behind handles, handler registry, per-handler captured state — is mutable host state that is *not* automatically per-snapshot.

**The design principle (per proposal 037): one operation per mutation; rollback is the resource's branch-interaction contract, not the operation's or the handler's choice.**

> **Superseded by proposal 037.** The original draft of this section described a "twin operations" pattern — `assert`/`assume`, `set`/`set_local`, etc. — where each resource exposed a sticky variant and a transactional `_local` variant requiring `Branch` in its effect row. An intermediate refinement let the *handler* pick sticky-vs-transactional. Proposal 037 supersedes both: **Modify has no sticky semantics**, and rollback is **not** a handler concern. Modify means "mutate the named resource"; whether the mutation rolls back is the resource's branch-interaction contract, enforced at the runtime level via snapshot + `register_undo`.
>
> The reason "sticky-under-Branch" is rejected as a Modify mode (rather than just deprecated): a sticky write inside a logical branch produces an unspecified value from a sibling alt's perspective. If `set(c, 5)` in alt A leaks into alt B, B's observation of `c` depends on which alt ran first — execution order, not logical content. Logical branches must be logically independent.
>
> See proposal 037 §"Cell[V]", §"With Branch (resource contract drives snapshot)", and Rules 5 / 8 for the canonical framework. The historical content below is preserved for context; the `_local` variants, the "sticky vs transactional via handler" framing, and the paired-ops table no longer apply.

```anthill
-- Canonical (per proposal 037) — one operation; one semantics.
sort KB
  ...
  operation assert(kb: KB, term: Term, sort: Type) -> Option[T = FactId]
    effects Modify[kb]
end

sort Cell
  sort V = ?
  operation new(initial: V) -> Cell[V]                   -- construct
  operation get(c: Cell[V]) -> V                         -- read; type-pure
  operation set(c: Cell[V], value: V) -> Unit
    effects Modify[c]
end
```

`Modify[c]` says "this op mutates `c`." It does not say (and cannot say) whether the mutation rolls back — that is determined by `c`'s branch-interaction contract, not by any operation flag, handler swap, or row marker.

**Branch-interaction in v1 (per 037 §"Resource type plug-in" + per-resource contracts):**

| Resource | Operation | Branch-interaction contract |
|---|---|---|
| KB facts | `KB.assert` | **branch-local snapshot** (today's KB *behaves* sticky-under-Branch only because the snapshot machinery isn't wired yet — soundness gap, not contract) |
| Cells | `Cell.set` | **branch-local snapshot** (same gap as KB) |
| Persistence stores | `Store.persist` | **sticky-by-physics** (filesystem can't roll back atomically) — resolved either by a buffered handler that absorbs writes for the branch, or by a static constraint preventing the op inside Branch |
| Console output | `Console.print/println` | **sticky-by-physics** (irreversible) — same resolutions |
| Stream sources, pure (`Stream[T, ()]`) | source pull | per-snapshot independent positions (clone source on snapshot) |
| Stream sources, effectful (`Stream[T, E≠()]`) | source pull | use statically prevented inside `Branch` via Branch+Consumes constraint |
| Handler registry | install / `with_handler` | install is branch-local-snapshot when under Branch; `with_handler(...)` is always lexically scoped |
| Reader constant | `ask()` | immutable; no rollback applies |

Plain "sticky-under-Branch" is **not** an accepted contract — it's the soundness hazard sketched above. Today's implementations exhibit that hazard for Cell / KB / Map only because the snapshot/`register_undo` runtime hooks aren't yet in place; that is a gap to close, not a feature.

**Why one operation per mutation rather than paired sticky/transactional ops** (rationale per proposal 037):

- *One operation has one semantics: mutate the named resource.* Proliferating `_local` / `_atomic` variants duplicates the API surface for a concern that belongs to the resource type's contract, not the operation set.
- *Composition stays clean.* Adding `Branch` to a region doesn't force every `set` / `assert` call site to declare `Branch` in its effect row.
- *Time-travel forward-compatibility.* A future versioned handler swaps in transparently — operation signatures don't change because the handler varies state representation, not rollback policy.
- *Sound semantics fall out of the resource contract.* The runtime enforces the contract uniformly; user code doesn't need to know whether `c` is branch-local-snapshot or sticky-by-physics — the type system rejects the latter at the call site if used inside Branch.

**Implementation of the runtime-level Branch interaction (preserved from the original sketch):**

When entering Branch, the runtime walks the resources whose contracts are branch-local-snapshot, snapshots their state into per-branch slots, and registers undo callbacks via `register_undo`. When a sibling alt is resumed, the undo log for the abandoned alt is replayed in reverse-registration order, restoring the parent state before the sibling observes the resource.

The runtime exposes:
- **`register_undo(undo_action: FnOnce())`** — install a callback to run when the current snapshot is abandoned (resumed from a sibling). The mechanism is invoked by the *runtime's branch-handling machinery* on behalf of resources whose contract is branch-local-snapshot — not by Modify handlers, which are oblivious to whether they're writing to the parent or a snapshot.

The Modify handler is unchanged whether or not Branch is active. It always writes to "the active state" of the resource; the runtime presents the active state as parent-or-snapshot per the contract.

**Implementation requirement that the cloneability discussion surfaces:** at minimum, the activation stack (`Frame`, `ActivationStack`) must be `Clone`. Anything that an `AwaitState` variant transitively holds (closures, in-flight value buffers) must also be cloneable. The audit needed in Phase A is: walk every `AwaitState` field and confirm cloneability, or refactor to make it so. `Value` and `ClosureHandle` are already designed this way; the audit is mostly a confirmation step.

That's the entire implementation surface. None of this is the "refactor the evaluator" work I was earlier prescribing — that work was already done in 026/M1.

**What this enables, all in v1:**

- **Single-shot resumable** (Async/Await, Generator/Yield, Reader-with-late-binding): handler returns `Choice` or stashes the snapshot in a host callback / stream pull function. Cheapest case — snapshot used once.
- **Multi-shot resumable** (Branch, nondeterministic `Decide`): handler captures snapshot, returns `Choice(a, alt_for_b)`. Resolver runs both branches as choice points. Needs snapshot to be cloneable (item 1 above).
- **Cooperative scheduling** (multiple fibers, scheduler picks who runs next): same substrate plus a scheduler holding multiple snapshots. The scheduler is its own design but does not require new primitives.

**Why declare Suspension explicitly:**

`Suspension` as a type-level marker remains valuable independent of implementation status:
- Types `Stream.collect` and similar operations honestly (they suspend transitively).
- Validates that continuation-using effects integrate with the effect system correctly.
- Prevents designs that assume linear continuations everywhere.

### Consumes — sub-effect for shared-cursor pumping

```anthill
sort Consumes
end
fact Effect[T = Consumes]
```

**Operations:** none directly. `Consumes` is structural — like `Suspension`, it's a marker that gets added to an operation's inferred effect row in specific situations rather than appearing as an operation users call.

**Semantics:** an operation has `Consumes` in its row when it pumps a stream whose source is shared (i.e., a `Stream[T, E]` with non-empty `E`). Pumping such a stream advances a cursor that other holders of the same handle observe; under multi-shot branching, this is observably wrong (branch B sees branch A's consumption). Tagging the operation with `Consumes` lets the type system catch the misuse statically.

**Where it gets added (typing rule, declared in stdlib once typing-as-rules infrastructure is ready):**

```anthill
-- When splitFirst (or any pump-equivalent operation) is called on a Stream
-- with non-empty E, the call's inferred effect row picks up Consumes.
rule call_effect(?call, Consumes)
  :- ?call = splitFirst(?s),
     type_of(?s) = Stream[T = ?_, E = ?E],
     ?E ≠ ()
```

This relies on the typing-as-rules infrastructure from 011/022 and WI-011. Until WI-011 lands, the rule is hardcoded in the typing pass (`typing.rs`) as a temporary stub: when checking a call to `splitFirst`, if the stream's E is non-empty, add `Consumes`. Once WI-011 makes typing queryable as KB rules, the hardcoded check migrates to the stdlib rule above.

**The constraint that uses it:**

```anthill
-- Branch and Consumes cannot coexist in one operation's effect row.
-- Speculative search and shared-cursor consumption are mutually exclusive:
-- if you backtrack, you can't have already consumed bytes that the alt
-- branch would need to read.
constraint branch_consumes_incompatible
  :- declared_effect(?op, Branch),
     declared_effect(?op, Consumes)
```

Lives in `stdlib/anthill/prelude/effects.anthill`. The typer evaluates it against each operation's inferred effect row; violations are type errors.

**What this catches:**

```anthill
-- ❌ type error: declares Branch but inferred row includes Consumes
operation bad(lines: Stream[String, ConsoleInput]) -> List[String]
  effects Branch, ConsoleInput
=
  let chosen = branch(unit, unit)
  let line = splitFirst(lines)              -- splitFirst on non-pure Stream → adds Consumes
  ...                                        -- Branch + Consumes: constraint fires
```

The user's recourse: refactor so the consuming operation is separate from the branching operation. Code that branches doesn't pump shared-cursor streams; code that pumps shared-cursor streams doesn't branch. They communicate via values.

**Note on strictness:** this catches some cases where the user *could* have safely consumed (e.g., the stream was constructed inside the branch and never escaped). The over-strict v1 rule is preferable to no check; refinement to a use-site / lifetime-based analysis is future work if real code finds it painful.

### Read[T] — implied by Modify (and an explicit Reader effect for the configuration pattern)

`Read[T]` as a sub-effect of `Modify[T]` is currently *not* declared as a standalone effect in `effects.anthill`; the comment at the bottom of that file explicitly says "Read is not a separate effect kind — it's implied by Modify, and operations that only read should take immutable parameters."

This proposal preserves that decision for the read-vs-write distinction on a `Modify` resource. Read-only access to a mutable resource is encoded by *not* declaring `Modify[T]`. If a finer distinction is needed later (e.g., for an immutable-snapshot reader-vs-writer story), `Read[T]` can be added alongside `Modify[T]` with `rule Effect[T = Read[?r]] :- Effect[T = Modify[?r]]`, exactly as 013 sketches.

**Separately, a `Reader[T]` effect is worth shipping in v1 Phase 2.** Reader is the OCaml/Haskell-style pattern: a configured constant value that operations can `ask()` for, supplied by the handler. It's distinct from `Modify[T]` (no mutation) and from passing arguments explicitly (no plumbing through every call site).

```anthill
sort Reader
  sort T = ?
  operation ask() -> T effects Reader[T]
end
fact Effect[T = Reader[?]]
```

**Default handler:** captures a constant `T` in its closure state; returns `Pure(constant)` for every `ask()` call. Linear; no continuation manipulation.

**Use case:** configuration, dependency injection, ambient context that's pure-typed. A natural fit for the simple-handler shape.

### Modify[T] — typed mutable resource

> **See proposal 037 for the full framework.** This section gives the catalog-level summary; the Modify framework — `Modify[T]` as a uniform effect kind, `Cell[V]` as the standard small-state sort with `new`/`get`/`set`, type-specific handlers parameterized by `(Resource, IdentityKey)`, the seven per-resource interpreter contract concerns, the eight binding rules, the time-travel forward-compat invariants — is specified in **`docs/proposals/037-anthill-state-model.md`**. The brief catalog entry below is provided so that 027's effect catalog stays self-contained for handler-system context; for state-model questions, 037 is canonical.

```anthill
sort Modify
  sort T = ?
  -- (no operations on Modify itself; it's an effect annotation)
end
fact Effect[T = Modify[?]]

-- The standard small-state resource that exposes the get/set protocol:
sort Cell
  sort V = ?
  operation new(initial: V) -> Cell[V]                   -- construct; allocation-only
  operation get(c: Cell[V]) -> V                         -- read; type-pure
  operation set(c: Cell[V], value: V) -> Unit
    effects Modify[c]
end
```

**Operations** (Cell's protocol; resource-specific operations live on each resource type — KB, Store, WorkItemStore — per 037's per-resource contracts):
- `new(initial)` — allocate a fresh Cell with identity (opaque-handle scheme: each call yields a distinct cell). Construction is allocation, not mutation; no `Modify[anything]` effect (matches `Map.empty()`, `List.nil()`).
- `get(c)` — read the current value. Pure (no `effects` clause); observation of mutable state is type-pure (matches Haskell's `IORef.read :: IORef a -> IO a` distinction loosely — reads don't carry the mutation effect).
- `set(c, value)` — replace the cell's value. Carries `effects Modify[c]`. **Modify has one semantics: mutate.** Whether the mutation rolls back is Cell's branch-interaction contract (branch-local-snapshot per 037), enforced by the runtime — not a property of the operation, the handler, or any flag.

**Default handler:** a `ModifyHandler[Resource = Cell[V], IdentityKey = …]` keyed by Cell's identity (today: functor-only — single instance per V; multi-instance per WI-200). The host realization owns the arena (in Rust: `HashMap<Symbol, Value>` inside `default_modify_handler` at `rustland/.../eval/effects.rs:109`). See 037 §"Cell[V]" interpreter contract.

**Alternative handlers** (per 037 §"Type-specific Modify handlers" — handlers vary in *state representation*, never in *rollback policy*):
- *Direct*: the default; fast path with simple state.
- *Time-travel*: maintains a version graph; same operation surface, richer state.
- *Audit*: logs every write, then delegates to a wrapped handler.
- *Test*: substitutes a controlled state for the duration of a test.

(There is no "Branch-aware handler" — Branch interaction is a runtime mechanism per the resource's contract, not a handler kind.)

**Bidirectional correspondence** (037 Rule 8): `Modify[T]` may appear in an effect row only if T has a registered handler; a handler is meaningful only if some operation declares `Modify[T]`. Bare value types (Int, Bool, String) cannot carry Modify because they have no wrapper sort to attach a handler to — mutability is a property of the resource type. See 037 for the full rule.

**Subtleties** (highlights; 037 has the canonical list):
- The handler-stack model picks the topmost handler matching `Modify[T]`. Per-resource distinction is the framework's default, not a special pattern.
- Reading is intentionally pure-typed even though it observes mutable state.
- `set` has one semantics in all contexts. Outside Branch the mutation persists (because there is no scope to roll back to); inside Branch the runtime snapshots Cell per its contract and the same `set` call writes to the active snapshot. There is no `set_local`, no "sticky mode," no handler swap — and per 037 Rule 5, source-level `_local` / `_atomic` variants MUST NOT exist.

### Error[T] — typed failure / abort

```anthill
sort Error
  sort T = ?
  operation raise(error: T) -> Nothing effects Error[T]
end
fact Effect[T = Error[?]]
```

**Operations:**
- `raise(error)` — abort the current computation with `error`. Returns `Nothing` (uninhabited), so the call never produces a value — control transfers to the handler.

**Default handler:** propagates as a host-error carrying the raised payload to the embedder. The host's `interp.call(...)` (or equivalent) returns its failure idiom — `Result::Err` in Rust, `Either.Left` in Scala, the `AH_RESULT_ERROR`-tagged variant in C — carrying the reified payload.

**Alternative handlers:**
- *Try-catch*: install a handler scoped to a single `interp.call`, restore previous handler on return; the handler catches the value and converts to `Result[T, E]`.
- *Logging*: handler logs and re-raises (calls the previous handler).
- *Default value*: handler returns a fallback value; cast through `Nothing → T`'s coercion (impossible unless we extend the model — likely we want `Error` to be terminal and use a different effect for "produce a default").

**Subtleties:**
- `Error[T]` is non-resumable in this proposal — there's no operation to ask the handler "give me a T anyway." If we want resumable typed errors, that's a generalization that requires the multi-shot handler shape, which we've deferred.
- `MatchFailed` (`stdlib/anthill/prelude/effects.anthill:54`) is a payload sort designed to be raised through `Error[MatchFailed]` by the evaluator when `match` is non-exhaustive. The exhaustiveness checker removes `Error[MatchFailed]` from a `match`'s inferred row when all arms are covered.

### ConsoleOutput / ConsoleInput — I/O

Declared in `stdlib/anthill/prelude/console.anthill`, registered as effects there.

**Operations:**
- `print(c: Console, s: String)` / `println(c: Console, s: String)` — emit a string. (Operation symbols dispatch via the second argument inside the handler.)
- `read_line(c: Console) -> String` — read one line of input.

**Default handler (CLI):** writes to standard output / reads from standard input. Each host realizes via its native I/O facility — Rust uses `io::stdout()` / `io::stdin()` (`stdio_console_*` at `rustland/.../eval/effects.rs:29, 48`); Scala will use `Console.out` / `Console.in`. On the C target Console is *not* a guaranteed default: hosted environments with libc can wrap `fputs` / `fgets`; bare-metal targets (no libc, no stdio) must supply their own UART/RTT/SWO-backed implementation as the embedder's responsibility — Console becomes an embedder-provided handler rather than a runtime-shipped default.

**Test handlers:** captured-output (appends to a shared buffer) and scripted-input (drains a queue of pre-scripted lines) variants. Each host provides its own equivalent — Rust has `buffered_console_output_handler` / `scripted_console_input_handler` (`rustland/.../eval/effects.rs:68, 88`).

This is the "uninteresting" handler shape — input/output to a real or simulated channel. It exists in this catalog mainly to demonstrate that the standard pattern (dispatch on op symbol, mutate an Rc-held resource, return a value) covers I/O cleanly.

### Branch — nondeterminism (the multi-shot case built on eval-state-as-data)

```anthill
sort Branch
  operation branch(a: T, b: T) -> T effects Branch
  operation fail() -> Nothing effects Branch
end
fact Effect[T = Branch]
```

The current stdlib declaration has only `fail`. This proposal adds `branch(a, b)` as part of v1.

**Why Branch is the most complex effect:**

`Modify`, `Error`, `Console*`, `Reader`, `Suspension` all fit the simple non-resumable / single-shot-resumable handler shape: handler runs once, returns one value (or moves the eval state once), computation continues. `Branch` is multi-shot: a "collect all paths" handler must invoke the *rest of the computation* once for each alternative, then merge results. The eval state at the suspension point must be **cloneable**, because the same state has to be resumed twice with different values.

**How v1 handles it: the carrier on top of the existing activation stack**

The evaluator is already defunctionalized (per Suspension's "Implementation substrate" section above — the activation stack from 026/M1). The eval state at any operation call is the cloneable `ActivationStack`. The Branch handler:

```
branch handler invoked with op_sym = `branch`, args = [a, b]:
  let alt_b = runtime.snapshot_eval_state()         -- clone of the activation stack
  return Choice(value: a, alts: [alt_b])
  -- equivalently for n-ary: Choice(value: a, alts: [alt_b, alt_c, ...])
```

Under the hood:
- The handler calls `snapshot_eval_state()` to clone the current activation stack — `Choice` carries one snapshot per alternative path.
- `Choice(a, [alt_b])` returned by the handler tells the runtime: "resume the current path with `a`; on backtrack, resume the cloned snapshot, splicing in `b` as the call's return value."
- The runtime installs each snapshot in `alts` as a resolver-level alternative (via `push_choice`, in reverse list order so list order = trial order). When the resolver pumps backtrack, the first snapshot in `alts` fires, then the next, etc.

This is genuinely multi-shot because the activation stack is cloneable, and trivially extends to n-ary nondeterminism (a `decide([a, b, c, d])` operation lowers to `Choice(a, [alt_b, alt_c, alt_d])`). The same primitive (`push_choice`) underpins both rule-body disjunction (WI-075's `or`) and expression-body `branch` — the symmetry table earlier in this proposal is real.

```
fail handler invoked with op_sym = `fail`, args = []:
  return Fail.

(Equivalently, the handler could call RuntimeAPI.fail_branch() and never return.)
```

`fail()` discards the current eval state without resuming it. The resolver backtracks to the most recent choice point — exactly the disjunction backtracking semantics from WI-075.

**Default handler ("collect all"):**

The default Branch handler returns `Choice(a, alt_b)` for `branch(a, b)` and `Fail` for `fail()`, as above. The result of evaluating an expression containing `branch` under this handler is naturally a `LogicalStream[T]` (per WI-048), since the runtime exposes the multi-shot resumption stream as a value.

`1 + branch(10, 20)` under this handler evaluates to a stream `[11, 21]`. Inside the resolver, the choice point is registered; the eval state at the branch call is cloned; both branches pump lazily on demand.

**Alternative handlers:**

- *Pick first*: `branch(a, b)` returns `Pure(a)`; `fail()` returns `Throw(some_error)`. Equivalent to single-path execution — useful for deterministic test runs.
- *Oracle*: pre-supplied list of choices; each `branch` consumes one and returns the chosen value.
- *Beam search*: keep the top-k branches by some heuristic; prune the rest. Handler tracks pruning state in its closure.
- *Random*: flip a coin per `branch`.

**Why `Branch` is the bridge between functional expressions and the resolver:**

| Layer | Construct | Lowers to |
|---|---|---|
| Logic / rule body | `or(a, b)` | `push_choice(b), a` (via stdlib rule, WI-075) |
| Functional expression / operation body | `branch(a, b)` (with collect-all handler) | `push_choice` raised from the handler with the captured eval state as the alt |

Both meet at `anthill.kernel.push_choice`. The same primitive serves both surface forms. This is why getting `push_choice` and the eval-state-as-data refactor right matters beyond just disjunction — they are the substrate for the imperative-feeling `branch` / `amb` operator at the expression layer, and downstream constructs like `cut`, `once`, `if-then-else`, `findall` ride on the same foundation.

**Sequencing:**

Branch ships real (not stubbed) in v1, gated only on:
- WI-075 landing (resolver-side `push_choice` + `Continuation` candidate variant).
- `Frame` and `ActivationStack` getting `Clone` derivation in `eval/frame.rs`.
- The runtime's `snapshot_eval_state` / `resume_with` / `Choice` interpretation wiring.

None of these are large; the activation-stack substrate they build on is already in place.

**Alternative handlers:**
- *Pick first*: `branch(a, b)` returns `a`; `fail()` aborts. Equivalent to using `a` and ignoring `b`. Useful for deterministic execution where `branch` is a signal but not a search.
- *Oracle*: pre-supplied list of choices; each `branch` consumes one.
- *Beam search*: keep the top-k branches by some heuristic; prune the rest.
- *Random*: flip a coin on each `branch`.

**Why `Branch` is the bridge between functional expressions and the resolver:**

| Layer | Construct | Lowers to |
|---|---|---|
| Logic / rule body | `or(a, b)` | `push_choice(b), a` (via stdlib rule, WI-075) |
| Functional expression / operation body | `branch(a, b)` (with collect-all handler) | `push_choice` raised from the handler |

Both meet at `anthill.kernel.push_choice`. The same primitive serves both surface forms. This is exactly why WI-075's design has scope beyond just disjunction — it's the substrate for the imperative-feeling `branch` / `amb` operator at the expression layer.

**Stream connection:** the result of evaluating an expression containing `branch(...)` under the collect-all handler is naturally a `LogicalStream[T]` (proposal 026/M4 — already implemented as WI-048). The handler closes the loop by wrapping its `SearchStream` results back as a `Value::Stream`, exposable to caller code via `splitFirst` / `collect`.

## Comparison with other effect-handler systems

Effect handlers exist in several languages with meaningfully different design choices. This section maps anthill's design against the well-known systems so readers familiar with one can locate the others. The axes that matter are: (a) what a handler is, (b) how the continuation is exposed, (c) handler scoping, (d) multi-shot support, (e) effect declaration, (f) type-system integration.

### Quick comparison table

| Axis | OCaml 5 | Eff (original) | Koka | Frank | **Anthill (027)** |
|---|---|---|---|---|---|
| Handler shape | match expression with `effc` arm per effect, takes explicit `k` | first-class handler value, takes explicit `k` per op | function with `ctl` clauses, takes explicit `k` per op | match-style "adaptors" with operation arms, takes explicit `k` | host-language callable returning `HandlerAction` carrier; no explicit `k` parameter |
| Continuation in handler | yes — `(a, b) continuation` value, callable via `continue k v` / `discontinue k exn` | yes — first-class continuation value | yes — `ctl` exposes `resume(v)` | yes — `→ B!E` arrow in adaptor signature | no — handler returns carrier; if it wants the continuation, calls `RuntimeAPI.snapshot_eval_state()` to materialize one |
| Scoping | lexical (`match_with` / `try_with` wrap a block) | lexical (`with H handle E`) | lexical (`with H { E }`) | lexical | dynamic (per-`Interpreter` registry); push/pop API + future `with handler H for E do body end` syntax adds lexical |
| Multi-shot | yes (deep `match_with`); shallow option via `try_with` (must reinstall) | yes — handler can call `k` arbitrarily | yes (`ctl`); also `fun` (single-shot) and `final` (no resume) | yes — adaptor's effect arrow is the continuation | yes — via cloneable activation-stack snapshots; `Choice` carrier for binary, API for n-ary |
| Effect declaration | `type _ Effect.t += MyEff : ...` (extensible variant) | algebraic operation declarations | declared in handler signature, inferred at use | type-level effect rows | sorts + `fact Effect[T = Kind[?]]` (per 013) |
| Type-system integration | runtime (no static effect system in stock OCaml) | static effect rows | row polymorphism + effect inference | row polymorphism + effect-typed bidirectional checking | static effect rows (per 013), value-dependent typing (per 011) |
| Sub-effecting | none built-in | none built-in | yes via row subtyping | yes via row subtyping | yes via fact rules (`rule Effect[T = Suspension] :- Effect[T = Branch]`) |

### Where anthill is unusual

1. **Carrier-instead-of-explicit-`k`.** OCaml/Eff/Koka/Frank all hand the handler an explicit continuation value. Anthill returns a carrier and exposes the continuation as a `RuntimeAPI` operation (`snapshot_eval_state`). This is uncommon — closest analog is Plotkin–Pretnar's *generic effect interpreters* where the handler returns a "what to do next" sum type. The benefit is host-language portability (no need to reify continuations as host first-class values; the activation stack is host-data already). The cost is slightly more verbose handlers in the rare cases that need multi-snapshot manipulation.

2. **Effect declarations as KB facts** (per 013). All four comparison systems treat effects as first-class type-system entities — declared in the source language, checked by the compiler, often row-polymorphic. Anthill treats effects as KB facts (`fact Effect[T = Kind[?]]`), which makes them queryable from anthill code, extensible without grammar changes, and bridgeable to sub-effect rules. This is structurally different from any of the others.

3. **Resolver substrate for nondeterminism.** OCaml/Eff/Koka/Frank implement nondeterminism (Branch/Decide) by handler-driven multi-shot. Anthill *also* uses multi-shot via cloned snapshot, but the alternatives are registered as resolver-level choice points (`anthill.kernel.push_choice`, WI-075), unifying the rule-body disjunction (`or`) and expression-body branch (`branch`) under one machinery. None of the comparison systems share this — they don't have a logic-programming substrate to lean on.

4. **Dynamic scoping by default.** OCaml/Eff/Koka/Frank are all lexically scoped (`with H handle E` / `match_with`). Anthill defaults to dynamic scoping (per-`Interpreter` registry installed at startup), with lexical scoping available as an opt-in via `with_handler` / future `with handler H for E do body end` syntax. The dynamic default fits embedder use (host installs handlers around `interp.call`); lexical opt-in covers the common in-program case.

### Where anthill is conventional

- **Sub-effecting via row entailment.** `Suspension` as a marker that other effects propagate matches Koka and Frank's row subtyping in spirit (different mechanism, same outcome).
- **Multi-shot resumable for nondeterminism, single-shot for everything else.** Same default partition as Koka.
- **Lexical scoping when explicitly requested.** `with handler H for E do body end` is structurally identical to OCaml's `match_with` and Eff's `with H handle E`.
- **Effects in the function signature.** Operations declare `effects (E1, E2, ...)` in their type, exactly like Koka, Frank, and Eff.
- **Prolog-style state semantics across multi-shot branches.** Mutable state (KB, Modify cells, streams) is shared across branches; only the activation stack (substitution, locals) is per-snapshot. This matches Prolog `assert/1` semantics; opt-in transactional handlers can override per-resource. None of the four comparison systems take a position on this because they don't have a default-shared mutable substrate the way anthill does.

### What anthill cannot do (at least not without extension)

- **First-class handler values.** Eff treats handlers as values you can pass around, store, partially apply. Anthill handlers are host-language callables; they can be installed/replaced but aren't anthill values. No fundamental obstacle to adding this later, but out of v1 scope.
- **Handler types.** Koka and Frank have types like `<console, except<int>>` that can be manipulated at the type level. Anthill effect rows are sets of sort instantiations; the row-manipulation algebra is implicit in the typing pass rather than surfaced as types.
- **User-definable resumable effects with explicit `k` syntax.** A user writing a Generator handler in OCaml/Eff sees `continue k v`. In anthill, that handler instead calls `runtime.resume_with(snapshot, v)`. Same operation, different surface. Handler authors familiar with the OCaml literature will need a brief mental translation.

## Open Design Decisions

1. **`branch` arity** — binary (`branch(a, b)`) or n-ary (`branch_list([a, b, c])`)? The resolver's `push_choice` extends naturally to n-ary by chaining: `branch_list([a, b, c])` is `branch(a, branch(b, c))`. Binary is simpler; n-ary saves stack depth. Recommend binary for v1.

2. **Other resumable handlers (Generator, Async, soft-cut, transactional rollback, resumable errors)** — the substrate for these (defunctionalized eval, snapshot/resume) is already present per Suspension's "Implementation substrate" subsection, so they are not blocked on a major refactor. Each becomes a separate handler-shape design exercise (e.g., Generator wraps the snapshot in a stream pull function; Async stashes the snapshot in a host-async callback). A follow-up proposal (e.g. 028) catalogs them with the same level of detail this proposal applies to Modify/Error/Console/Branch. The work is *handler design*, not *evaluator design*.

3. **Scoped handler installation (push/pop / `with H handle E`)** — currently handlers are global on the `Interpreter`. Lexical `with H handle E` blocks are the standard OCaml/Eff/Koka pattern and unblock `bracket` / `finally`. Implementation: change the registry from `HashMap<Symbol, EffectHandler>` to `HashMap<Symbol, Vec<EffectHandler>>` (stack per effect); add `push_handler` / `pop_handler` to the `RuntimeAPI`; add a `with_handler(eff, h, body)` convenience. Language-level syntax `with handler H for E do body end` desugars to that convenience. Worth shipping in v1 alongside the other catalog entries.

4. **Effect inference vs declaration** — operations today declare their effects explicitly. Should `branch(a, b)` inside an operation body automatically add `Branch` to the operation's inferred effect row? Probably yes, but interacts with the typing pass that's already implemented. Tracked separately.

5. **`Read[T]` as a separate effect** — see catalog. Currently we don't have it; the design hook is in 013. Proposal recommends keeping Read implicit (i.e. encoded as the absence of `Modify`) until a use case justifies the granularity.

6. **Cut, soft-cut, if-then-else, once, findall** — all naturally downstream of `push_choice` once it exists. They can be added as either kernel primitives, stdlib rules, or both. Out of scope for this proposal but listed so the design space is visible.

## Implementation Status (as of 2026-04-23)

Status is per-host. The kernel-side artifacts (stdlib effect declarations) are shared.

**Shared (kernel-side):**
- Effect declarations in stdlib (Modify, Error, Suspension, Branch, Console*): present in `stdlib/anthill/prelude/effects.anthill` and `console.anthill`
- `Suspension`: nothing to implement at the host level (no operations); the stdlib declaration is the entire kernel-side artifact
- `branch(a, b)` operation declaration: not yet added to `Branch` sort
- Sub-effect derivation `Effect[T = Suspension] :- Effect[T = Branch]`: not yet added

**Rust implementation (`rustland`):**
- Activation stack / defunctionalized eval (the substrate for resumable effects): **already implemented** (`eval/frame.rs`, `eval/eval.rs` — per proposal 026/M1)
- Handler registry + dispatch: implemented (`anthill-core/src/eval/effects.rs:22, 232`)
- Console handlers (stdio + buffered + scripted): implemented (`eval/effects.rs:29, 48, 68, 88`)
- Modify default handler (arena-keyed by functor): implemented (`eval/effects.rs:109`)
- `HandlerAction` carrier type and `Choice`/`Throw`/`Fail` interpretation: not yet implemented (handler dispatch currently uses `Result<Value, EvalError>` directly)
- `Frame` / `ActivationStack` `Clone` derivation: not yet present
- `RuntimeAPI` snapshot/resume operations: not yet present
- `Branch` handler: not yet implemented (depends on the carrier wiring + WI-075)
- `Error` handler: not yet implemented (only the type infrastructure exists)
- `RuntimeAPI` surface for `push_choice` / `fail_branch`: not yet exposed (depends on WI-075)
- Push/pop handler stack (`with H handle E`): not yet implemented

**Scala implementation (`scaland`):**
- Effect handler infrastructure: not yet started; will mirror the Rust shape

**C implementation (embedded target):**
- Not yet started. Will use the function-pointer-plus-context idiom (no `std::function`, no exceptions, no implicit allocation). Console handler is *not* a default — embedded targets supply their own (UART/RTT/SWO/etc.) as part of board bring-up.

## Migration plan

The plan below is per-host except for steps explicitly tagged as kernel-side (shared across all hosts). Sequencing follows the principle "do risky / load-bearing work first" — the substrate-touching changes land before the surface-effect handlers that ride on them.

**Kernel-side (shared, do first):**
1. Add `operation branch(a: T, b: T) -> T effects Branch` to the `Branch` sort in `stdlib/anthill/prelude/effects.anthill`.
2. Add the sub-effect derivation `rule Effect[T = Suspension] :- Effect[T = Branch]` to `effects.anthill` so operations declaring `effects (Branch)` are typed as also carrying `Suspension`. Repeat for future continuation-using effects (`Generator[?t]`, `Async[?t]`, etc.) when they're added.
3. Add forward reference at the bottom of `013-abstract-effects.md` pointing to this proposal. *(Done.)*

**Rust implementation:**

*Phase A — substrate (do first):*
1. Add `Clone` to `Frame` and `ActivationStack` in `eval/frame.rs`. Audit `AwaitState` variants for any non-cloneable fields.
2. Define the `HandlerAction` carrier type (`Pure | Throw | Fail | Choice`) in `eval/effects.rs`. Update the handler signature to return `HandlerAction`. Migrate existing handlers (Console, Modify) — most just return `Pure(v)` or `Throw(e)`.
3. Add `RuntimeAPI` operations for `snapshot_eval_state` / `resume_with` / direct `push_choice` / `fail_branch`. Implement `Choice(v, alt)` interpretation: snapshot, register alt with resolver, resume current path with v.
4. Land WI-075 (`anthill.kernel.push_choice` primitive + `Continuation` candidate variant + `or` stdlib rule + `lower_query` disjunction wiring) in parallel — this is the resolver-side component the `Choice` interpretation depends on.

*Phase B — handlers and ergonomics:*
5. Implement default `Branch` handler returning `Choice(a, alt_b)` for `branch` and `Fail` for `fail`.
6. Implement default `Error` handler returning `Throw(payload)`, propagating to the host failure type.
7. Add Reader sort to stdlib + default Reader handler returning `Pure(constant)`.
8. Add push/pop handler stack: change the registry to `HashMap<Symbol, Vec<EffectHandler>>`, expose `push_handler` / `pop_handler` / `with_handler` on `RuntimeAPI`. Add `with handler H for E do body end` syntax to the grammar (small addition).
9. Add `bracket(setup, body, cleanup)` stdlib operation backed by `with_handler` for Error.
10. Tests: unit tests per standard handler; integration tests for `branch` inside `let`-bound expressions yielding `LogicalStream`; tests for nested `with handler` blocks; `bracket` correctness under success and error paths.

**Scala implementation:**
- Mirror the Rust handler infrastructure; same standard-effect catalog; same RuntimeAPI surface; tests should be structurally parallel to the Rust suite for cross-implementation conformance.

**C implementation (embedded target):**
- Same contract. Differs in mapping: function pointers + context structs in place of closures, tagged unions in place of `Result`/`Either`, runtime API as a struct of fn pointers (vtable) or as direct extern symbols. No Console default — embedder provides per-board.
- Standard effects to ship: Modify (heap-free arena variant — fixed-size slots over a static buffer is the embedded-friendly form), Error (propagates as the `AH_RESULT_ERROR` tag), Reader, Branch (depends on the C-side `push_choice` realization in the resolver, which has its own embedded considerations regarding `SearchStream` allocation strategy — out of scope here).

Track Rust-side steps as sub-WIs under WI-050 (M5 effect handlers); Scala-side and C-side under their respective implementation milestones.

## See also

- `013-abstract-effects.md` — the static/declarative side of this story.
- `026-expression-evaluator.md` §Effects — earlier sketch superseded in detail by this proposal.
- `026.1-value-integrated-kb-queries.md` — the `LogicalQuery` / `execute` machinery that `Branch`'s handler ultimately drives through.
- `037-anthill-state-model.md` — **the canonical state model.** Specifies `Modify[T]` as a framework: how resources plug in (interpreter contracts, identity schemes, dispatch paths, branch interaction, time-travel readiness), the per-resource Modify handler architecture, the eight binding rules, and the bidirectional `Modify[T]`↔handler correspondence. Supersedes the §Suspension "twin operations" (`assert`/`assume`, `set`/`set_local`) approach formerly proposed here.
- WI-050 (M5 effect handlers) — overall implementation milestone.
- WI-075 (`push_choice` and disjunction) — the resolver-side foundation.
- WI-200 (multi-instance Modify state) — multi-instance identity schemes for resources whose default is functor-only today.
