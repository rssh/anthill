# Proposal 047 — Effects as monads, realized by Filinski monadic reflection

## Status: Draft (2026-06-06)

> **Purpose.** Proposal 027 gives effect *handlers* an operational model (a `HandlerAction`
> carrier dispatched from a global registry) but deliberately defers the hard questions: what a
> handler *is* as a value, how to scope one to a region, and how resumable effects
> (`Suspension`, `Branch`) fit. This proposal answers all three with a single idea — **an effect
> is a monad, declared in the effect sort's own API, and the interpreter realizes it by Filinski
> monadic reflection** (`reflect`/`reify` over delimited control on the non-native activation
> stack). try/catch, transactions, nondeterminism, and suspension all become one mechanism, with
> no new surface syntax. It supersedes 027's *ambient-registry / scoping* section.

## Depends on
- 013 (effects as sorts and facts), 026 (defunctionalized expression evaluator — the non-native
  activation stack), 027 (effect handlers + `HandlerAction` carrier), 037 (Modify framework),
  045 (effect rows / row polymorphism — delivered as WI-307).

## Relates to
- WI-078 (land 027 phase B — the runtime substrate this builds on), WI-329 (typer effect-row
  *discharge* — the static dual), WI-069 (Suspension snapshot/resume), WI-075 (resolver
  `push_choice` — the lazy-choice substrate, Verified), WI-200 (multi-instance Modify state),
  WI-089 (`cpp_std` `effect_map` — the codegen realization).

## Supersedes
- Proposal 027 §"Handler scoping model" and the migration-plan steps 8–10 (the flat
  `HashMap<Symbol, EffectHandler>` registry, "no user-definable `with handler` in v1", and the
  bespoke `with handler … do … end` grammar). 027's effect *catalog* and `HandlerAction` carrier
  remain valid — this proposal reinterprets the carrier as defunctionalized reflection.

---

## 1. What 027 left open, and the unifying answer

027 canonicalized a runtime handler model: a handler is a host closure
`FnMut(&mut Interpreter, op, args) -> HandlerAction`, installed in a flat per-`Interpreter`
registry, and the runtime interprets the returned `HandlerAction` (`Pure`/`Throw`/`Fail`/`Choice`/
`Suspend`). Only `Pure`/`Throw` are wired today (WI-389/WI-073); the registry is global and
replaced wholesale; there is no scoped install, no first-class handler *value*, and resumable
effects are stubbed.

Three questions remained:

1. **What is a handler, as a value?** (Not a host closure — an anthill value.)
2. **How is a handler scoped to a region** (so try/catch and transactions can catch/roll back at a
   delimited boundary)?
3. **How do `Suspension` and `Branch` fit** the same model rather than being special cases?

The answer is one sentence: **an effect is a monad declared in its API; a handler is that monad's
`run`/fold; the interpreter realizes the effect by monadic reflection.** Everything else follows.

## 2. The model: effects are sorts; handlers are witnesses; the monad is in the API

`effects.anthill` already says it: *"Each sort defines its operations — the pseudo API that the
effect provides."* So:

- **An effect is a sort — a set of operations over types.** This is already true:
  `sort Error { sort T = ?; operation raise(error: T) -> Nothing effects Error[T] }`,
  `sort Branch { operation fail() -> Nothing effects Branch }`,
  `sort ModifyRuntime { operation get(target: T) -> V; operation set(target: T, value: V) -> Unit }`.
  Typeclasses (`Eq`, `Ordered`), effects (`Error`, `Modify`), and the resumable effects
  (`Suspension`, `Branch`) are **the same kind of thing**: a sort with operations. The only
  difference is what an operation *does*.

- **A handler is a witness — an entity implementing the effect sort's operations** (one closure
  per operation). That is exactly a typeclass/spec witness; an effect handler and a typeclass
  dictionary are the same shape.

- **The witness lives in the requirement slot.** anthill already threads requirement witnesses
  through the dynamic call tree (`Frame.requirements: SmallVec<[(Symbol, RequirementHandle)]>`,
  `call_with_requirements`, carrier-aware dispatch WI-350). An effect handler is a requirement
  witness keyed by the effect sort symbol. There is **one slot mechanism**, not two — installing a
  handler is providing a requirement witness, scoped to a region. (Replaces 027's separate global
  registry.)

- **Each effect declares its denotation monad in its API.** The monad is itself a sort (a set of
  operations: `pure`/`bind`/constructors), so "declare the monad" is still "a set of operations
  over types" — no new kind of entity. An effect operation **yields an effect-less value wrapped in
  the monad**:

  | effect | monad `M` | op denotation |
  |--------|-----------|---------------|
  | `Error` | `Result[_, T]` | `raise(x)` ≙ `Err(x)` |
  | `Branch` | `Stream[_]` (lazy, possibly infinite — the LogicalStream/SearchStream, **not** List) | `fail()` ≙ empty; choice ≙ multi-yield |
  | `Suspension` | `F[]:Suspend` (a suspension/continuation functor) | `await` ≙ a `Suspend` node holding the continuation |
  | `State` | `State[S, _]` | `set(v)` ≙ state threading |
  | `Reader` | `Reader[E, _]` | `ask()` ≙ `λe. e` |
  | `Modify[T]` | (State over the resource) | `set(target, v)` ≙ threaded mutation |

  `Branch ↦ Stream` (not List) is load-bearing: anthill nondeterminism is **lazy and potentially
  infinite** (SLD search; solutions pulled incrementally via `splitFirst`). List would wrongly
  imply finite eager enumeration.

## 3. Core mechanism: Filinski monadic reflection

The interpreter realizes effects by **monadic reflection** (Filinski, *Representing Monads*,
POPL '94):

```
reflect : M a -> a            -- inject a monadic value into the direct-style computation
reify   : (() -> a) -> M a    -- capture a direct-style computation as a monadic value
```

both implemented over a single delimited-control substrate (`shift`/`reset`). Filinski's theorem —
*any* monad `M` is representable this way — is exactly the guarantee we want: build the mechanism
once and it covers **all** effects, existing and future.

The mapping is exact:

- **effect operation = `reflect`.** `throw(x) = reflect(Err x)`; `await(…) = reflect(Suspend …)`.
  The op produces an effect-less value in its monad and reflects it into the computation.
- **handler / `provide` = `reify` / `reset`.** Installing a handler for an effect over a region
  *runs* that effect's monad over the region — it is the `reset` delimiter, i.e. **the prompt**.
  This settles "where is the prompt": at each effect's `reify`/`provide` boundary, and nowhere
  else.
- **a row of several effects = layered monads** (Filinski, *Representing Layered Monads*, POPL '99).
  Each effect's `provide` is its own reify layer — which is precisely the per-effect
  requirement-slot stack from §2. The layering needs no extra concept; it is the slot stack.

**The `HandlerAction` carrier is defunctionalized reflection.** The carrier in
`eval/effects.rs` is the per-monad, defunctionalized form of `reflect`:

| carrier | monad | meaning |
|---------|-------|---------|
| `Pure(v)` | `return v` | resume the perform site with `v` (inline today) |
| `Throw(v)` | `Result.Err v` | abort to the reify boundary (short-circuit) |
| `Choice(v, alts)` | `Stream` | yield lazily; resume per alternative |
| `Suspend(k)` | `F[]:Suspend` | stash the captured continuation |

So **declaring an effect's monad in its API is the same as specifying which carrier its operations
use.** Operational view (carrier) and denotational view (monad) are one design. The carrier is the
*specialized, cheap* realization (so first-order effects don't pay full `shift`/`reset` — `Throw`
is a cheap abort, not a general capture); reflection is the *general semantic spec and fallback*.

## 4. Why the non-native stack — this is its design purpose

Reflection requires delimited continuations as first-class, manipulable values. The interpreter has
exactly that **by design**: the defunctionalized, heap-allocated activation stack (proposal 026 —
`ActivationStack { frames: Vec<Frame> }`, where each `Frame.awaiting: Option<AwaitState>` *is* the
defunctionalized continuation; no Rust recursion; `depth_cap`/`DepthExceeded` instead of native
overflow).

A native-stack interpreter **cannot** reify/snapshot/resume continuations without host `call/cc` or
raw stack copying. The explicit heap stack makes continuations **data**:

- `reset` is a frame (a boundary marker on the stack);
- `shift` / capture is the **slice** of `frames` from the reset frame to the top;
- snapshot is a **clone** of that slice; resume is splicing it back.
  (`ContSnapshot` / `AltMarker` in `eval/effects.rs` are the placeholders for exactly this slice.)

So monadic reflection is the **intended payoff** of the architecture, not a retrofit. Committing to
the full model carries no foundational risk: snapshot/resume (WI-069) is a planned fill-in, not a
redesign. It is also the precise reason a *nested native sub-run* (running a handler body via a
re-entrant `run_to_value`) is the wrong implementation — it reburies continuations in the host
stack, defeating the stack's purpose.

## 5. The prompt only exists for lazy/resumable monads

- **First-order monads** (`Result`, `State`, `Reader`): the monadic value is plain data; `bind`/run
  is structural — the *degenerate* fragment of reflection (abort/return, no real `shift`). **No
  continuation capture, no prompt.** For `Error`, the monad genuinely is sufficient: try/catch is
  `Result` short-circuit.
- **Lazy / resumable monads** (`Branch ↦ Stream`, `Suspension ↦ F[]:Suspend`): the monad value
  *defers a continuation* (Stream's tail; Suspend's resume). The prompt is the reify/`provide`
  delimiter those continuations are relative to. Asymmetry worth noting: **Branch's lazy-choice
  substrate mostly already exists** (resolver `push_choice` WI-075 Verified, `SearchStream`,
  `splitFirst`), so surfacing it as the `Stream` effect-monad is largely wiring; **Suspension's
  snapshot/resume is the one genuinely-missing piece** (WI-069).

## 6. Realization split by target (reconciles "no transform" with codegen)

Same semantics, two realizations, chosen by where the code runs:

- **Interpreter → realize the monad at runtime** (we own the runtime). First-order monads need only
  the witness + structural bind/short-circuit; `Suspend`/`Stream` add activation-stack
  snapshot/resume. No compile-time transform.
- **Host backends → transform to the host's version of the monad.** Generated Rust/C++/C runs on a
  host runtime with no reflection substrate, so there the effect *must* be lowered to host form:
  `Error → Result`/`tl::expected`, `Modify → &mut`, `Suspension → host coroutine/future`
  (WI-089 `effect_map`). The monad declared in the API (§2) is the **spec both realizations honor**.

This is why the API-level monad declaration matters: it is the contract shared by the interpreter
and every codegen backend.

## 7. Surface: no new syntax

The boundary is an **ordinary higher-order operation**, not a language form:

- `provide(effect, witness)` — the core primitive: install a handler *entity* into the (requirement)
  slot for `effect`, scoped to a region; the install point is the reify boundary. The
  genuinely-new runtime piece is an *entity → witness-handle* constructor (today `RequirementHandle`s
  are minted by the requirement-insertion pass, not from an arbitrary value).
- `perform(effect, op, args)` — resolve the slot witness, run the op (≈ today's
  `invoke_effect_handler`, retargeted from the global registry to the slot).
- `handle` / `try_catch(body, recover)` / `bracket(setup, body, cleanup)` / `transaction(store, body)`
  are **library functions over `provide`/`perform`**. The body takes the effect's API (capability),
  not a `() -> T` Unit thunk. `transaction` = `bracket` over the store sub-buffer (subsumes the
  `transaction(store, body)` deferred in WI-194 part b).

No grammar change, no new `Expr` node. (An optional `with handler … do … end` sugar may be added
later as pure desugaring, but it is not the primitive.)

## 8. Build path and WI map

General mechanism, achievable for all effects; per-effect detail deferred.

1. **Substrate** — unify the effect-handler witness into the requirement slot; `provide` (entity →
   scoped witness) + `perform`. *(WI-078 runtime; the substrate slice.)*
2. **First-order effects** — wire `Throw ≙ Result` (abort/short-circuit to the `provide` point);
   `Pure` already resumes inline. Delivers **try/catch** and **transaction-rollback**. No
   continuation machinery. *(First green slice.)*
3. **Branch / Suspension** — `Choice ≙ Stream` rides the existing lazy-choice substrate
   (`push_choice` WI-075, `SearchStream`) — mostly wiring; `Suspend ≙ F[]` needs activation-stack
   snapshot/resume *(WI-069)*. Both via full reflection (`shift`/`reset`); no rework of 1–2.
4. **Sugar** — `handle`/`try_catch`/`bracket`/`transaction` as stdlib HO ops.
5. **Typer** — effect-row *discharge* (row − handled effect), the static dual *(WI-329, on WI-307's
   live row machinery)*.
6. **Codegen (separate track)** — the monad-to-host transform *(WI-089 `effect_map`)*; the API monad
   is its spec.

## 9. Open questions

- **Entity → `RequirementHandle` constructor**: confirm a runtime constructor (vs the insertion-pass
  origin) composes with carrier-aware dispatch (WI-350) and the row checker (WI-307).
- **Multi-instance witnesses** (WI-200): scoped `provide` is option (c) of WI-200 — confirm the slot
  keys by witness identity, not just functor symbol, so two `Modify` instances don't collide.
- **`Modify` as State vs direct store access**: `persist`/`retract` currently bypass the `Modify`
  handler (direct `store_registry`); decide whether `Modify` is realized as the State monad through
  the slot, or stays a direct carrier with `provide` only wrapping the sub-buffer for `transaction`.
- **Cost of reflection for first-order effects**: confirm the specialized carrier path (cheap abort
  for `Throw`) is taken so `Error` never pays general `shift`/`reset`.
