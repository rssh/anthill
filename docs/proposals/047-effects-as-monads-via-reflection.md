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
  Each effect is its own reify layer; the **order of the layers is fixed by an order over effect
  sorts** (§8 "Effect order is fixed, not nested" — numeric rank by default), *not* by the dynamic
  nesting of `provide`. The layering needs no extra concept — the per-effect requirement slot of §2
  stays keyed by effect symbol, and the tower at any point is the in-scope effects sorted by rank.

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

## 8. Type system: effect labels, the Monad interface (already sketched), stacks vs rows vs reflection

### Effect labels (routing in the layered case)

Reflection over a *stack* of effects needs each operation to carry its **effect label** — the
effect sort symbol — so a `reflect` routes to the correct reify boundary (the nearest `provide`
of that effect). The label is the open-union tag of extensible-effects, and it is exactly what
already keys the requirement slot and the reify/prompt. The interpreter has it implicitly in
`perform(effect, op, args)` / the slot key; making it explicit on operations is what lets several
effects coexist on one stack and disambiguates which layer a `reflect` targets.

### Defining the monads — the interface is already sketched, and HKT is expressible

Correction (verified 2026-06-06 against the design docs): the `Monad`/`Functor` interface is
already **sketched**, and higher-kinded parameters are part of the type-system design — *not*
absent (an earlier draft of this section wrongly claimed otherwise).

- `operation-call-model-brainstorm.md` §"Abstract monad" sketches
  `sort Monad { sort M = ?; operation pure(x: A) -> M[T = A]; operation bind(m: M[T = A], f: A -> M[T = B]) -> M[T = B]; operation mapM(…) = … }`,
  with a concrete instance (`fact Monad[M = Option]`) and **conditional/transformer instances**
  (`fact Monad[M = StateT[S, M]] :- Monad[M = ?M]`, likewise `ExceptT`).
- `expansion-during-unification.md §3.6` ("Higher-kinded parameters (Functor / Monad)") sketches
  `sort Functor { sort F { sort T = ? }; map(fa: F[T = A], f: (A) -> B) -> F[T = B] }` and notes it
  **parses cleanly (verified)**.

So HKT *is* expressible — a sort parameter that is itself parametric (`sort M = ?` /
`sort F { sort T = ? }`), applied `M[T = A]`. The grounding is the key insight: **it is provider
dispatch, not general higher-order unification.** At `map(xs, g)` with `xs : List[Int64]`, the carrier
`List` selects `fact Functor[F = List]`, binding `F := List`; then `F[T = A]` is first-order
`List[T = A]`. So the higher-kinded case **reduces to first-order once the carrier is dispatched** —
the same carrier-resolution as ordinary spec dispatch (WI-350). The only genuinely higher-order
residue (an unbound variable functor head `?M[…]` with no dispatch info) is confined to the
decidable **pattern fragment** (`check_ho_apply_pattern`); outside it, a loud error.

**Status:** designed + parses; the typer wiring (instantiate the higher-kinded carrier by provider
dispatch so `M[T=A]` reduces to first-order; bound the residue to the pattern fragment) is a
verify/implement item — `expansion-during-unification.md §6 Q7`, riding the WI-374/376 expansion
work. So a generic `Monad[M]` is **expressible by design**, not a missing concept.

Reflection (§3) sits **on top of** this interface: Filinski's `reflect`/`reify` are *defined using* a
monad's `pure`/`bind` (+ shift/reset). So the `Monad` sort above is a **companion/prerequisite** of
this proposal, not a competitor — it supplies the `pure`/`bind` the reflection runs over.

### Graded `DelayMonad` — captured effects in the type (delivered: typeclass; instance blocked on WI-516)

The `Monad` above is the **eager** monad: `flatMap` runs the continuation now, so its effect
surfaces in the operation's `effects` clause. The dual — a `Delay`/`IO`/`Suspend` monad — *captures*
an effectful computation as a pure value and performs it only later (the `reify` direction, §3; the
`Suspension ↦ F[]:Suspend` row of §2). Tracking *what it captured* in the carrier's type makes it a
**graded (effect-indexed) monad** (Katsumata, *Parametric Effect Monads and Semantics of Effect
Systems*, POPL 2014): a SECOND type parameter `E` holds the captured effect set.

```anthill
sort anthill.prelude.DelayMonad[M[T, E]]                       -- E : captured effect set
  operation pure[A](a: A) -> M[T = A, E = {}]                                  -- captures nothing
  operation delay[A, EffP](thunk: () -> A @ EffP) -> M[T = A, E = EffP]        -- capture: ambient row -> E
  operation flatMap[A, B, E1, E2](m: M[T = A, E = E1],
                                  f: (A) -> M[T = B, E = E2]) -> M[T = B, E = {E1, E2}]  -- compose; UNION
  operation force[A, Eff](m: M[T = A, E = Eff]) -> A effects Eff               -- perform (run at Eff = {})
end
```

The captured set is a **monoid**, and anthill's effect rows already *are* that monoid (`{}` unit,
`{E1, E2}` union — WI-307), so "track captured effects in the type" reuses the row algebra; it adds no
new mechanism. Contrast the eager `Monad`: there the continuation's effect rides the `effects` clause
(performed now); here it is captured into `E` and surfaced only at `force`.

**Effect-set-as-type, bridge = identity.** `E` is an ordinary type parameter holding an effect-set
*term*; types-are-terms makes that term a type-level value, so the *same* term serves as both an
arrow's effect row (`@ E`) and the type-param `E` — the reify bridge between "ambient effect" and
"captured effect" is the **identity** (verified: `delay`/`force` load with the same `EffP`/`Eff` in
both positions). A single captured row is the bare variable `E` (not `{E}`, which would read `E` as
one present label); `{E1, E2}` is a union, `{}` the empty row.

**Interpretation = lowering `E`** — this is what earns the second parameter. A handler/interpreter is
typed as *reducing* the captured set: `runError : M[T, {Error, ρ}] -> M[Result[T], ρ]` peels `Error`
off `E`; `force`/`run` is total only at `E = {}`. So §3's layered interpretation becomes a
**type-level invariant**: a computation cannot be `run` until every captured effect has been
interpreted away. `Delay` is the *free* graded instance (captures everything, interprets nothing);
concrete instances (a State/Error interpreter) give an effect a denotation and lower `E`.

**Aside, not a proposal.** The captured-effect set `E` is the same information a capture-checking type
system (Scala 3) tracks as a capture set — here it falls out of effects-as-rows × rows-as-type-parameters
rather than a bespoke checker.

**Status.** The `DelayMonad` typeclass is in stdlib (`anthill.prelude.DelayMonad`, `delay.anthill`) and
loads; `pure`/`delay`/`force` type-check. The canonical `Delay` instance (a suspended `() -> T @ E`
thunk) is **blocked on WI-516**: the typer represents an effect-set-valued row variable inconsistently
between `{E1, E2}` position (open tails) and forced/`effects` position (present labels), so `flatMap`'s
body cannot conform to its declared `E = {E1, E2}` return — only the merge fails. Landing WI-516 lands
the instance. (En route: a lambda is now admissible as a *named* argument, and lambda syntax is
specified in kernel-language.md §4.7.)

### Monad stacks (cheap here), effect rows, and reflection — all three, at different levels

"Monad or monad stack / MTL vs `Eff`?" — anthill can host **both**, at different levels:

- **Monad-transformer stacks** (MTL-style) are expressible as **conditional instances resolved by
  SLD**: `fact Monad[M = StateT[S, M]] :- Monad[M = ?M]`. Crucially, that SLD resolution is
  **compile-time machinery**: the typer/elaboration walks the instance chain once, and the
  interpreter carries the *resolved* witness/env — there is **no runtime SLD dispatch**. So
  transformer stacks cost nothing at runtime and don't blow up the way native *monomorphization*
  does (every `StateT<S, ExceptT<E, M>>` clones bodies — why Rust has no thriving transformer
  library): the chain is resolved ahead of time and threaded as a value.

  This exposes a clean **resolution-timing split**: compile-time SLD resolves the *type-level
  structure* (which monad / transformer stack, which requirement slots, statically-known witnesses);
  the only genuinely *runtime* parts are `provide` (dynamically installing a handler witness into a
  slot) and reflection (running it). So "effects unify with the `requires` slot" holds at the *slot*
  level, but the fill-timing differs: typeclass witnesses are compile-time-resolved (and can be
  baked in), effect-handler witnesses are runtime-installed by `provide`.

- **SLD's other face — an explicit runtime query returning a `Stream`, for genuine logical tasks.**
  Beyond compile-time dispatch, SLD is available as a first-class **runtime operation**:
  `query(...) -> Stream` (reflect / `LogicalQuery`, e.g. `pattern_query`), returning a *lazy* `Stream`
  of solutions. This is the interface you **reach for explicitly when the task is genuinely
  logical/relational** (search the KB, enumerate solutions) — not an ambient effect sprinkled into
  ordinary code. It shares the `Branch ↦ Stream` denotation, but the relationship is the WI-070 one:
  `query`/`LogicalStream` is the **external** interface; `Branch` is the **internal** effect
  mechanism. So nondeterminism is normally *explicit* (call `query`), and Branch's Stream substrate
  already runs at runtime (over `push_choice` WI-075 / `SearchStream`) — when the direct-style effect
  form is wanted it is mostly wiring over that, not new machinery.
- **Effect rows** (045 / WI-307) track the effect *set* — the `Eff` side, unordered, row-polymorphic
  — for effect *checking*.
- **Reflection** (§3) runs the composed monad in **direct style** (no explicit `bind` chains).

So the user's "is it not important when we have runtime reflect?" is right about the *syntactic*
MTL-vs-`Eff` encoding — reflection makes user code direct-style either way. The one thing that stays
real is the **semantic order of non-commuting effects** (`StateT∘ExceptT` vs the reverse — does a
raise roll back state?). anthill captures that order with a **fixed, declared order over effect
sorts** — see the next subsection — so user code stays direct-style and the composition order is
pinned without forcing the bureaucracy of a written transformer-stack type at each use.

### Effect order is fixed (numeric by default), not nested

The semantic order of non-commuting effects (does `raise` roll back state? does backtracking undo a
log?) is **fixed by an order over effect sorts**, not by the dynamic nesting of `provide`. By
default that order is **numeric**: each effect sort carries a default rank, and a computation's
effect *set* (045's unordered row) is realized into a monad *stack* by sorting its effects on rank
and folding the transformer instances (`fact Monad[M = StateT[S, M]] :- Monad[M = ?M]`) in rank
order. A numeric rank is *total*, so the realization is always defined — there is **no
ambiguous-ordering failure** to handle in the common case; the only `select_monad` failure is a
missing transformer instance. This is what runs now.

A richer **declared partial order** — a DAG of `effect_below` edges, topologically sorted — is a
*deferred* refinement, not part of the default. It is motivated only when an effect must be
positioned **because it knows about another's presence** — a genuine dependency (e.g. an effect that
must sit below `Branch` to survive backtracking *and* declares that constraint, rather than relying
on a default number). The DAG buys that explicitness at the cost of cycle / incomparability handling;
numeric ranks cover the standard catalog without it, so we start numeric and add edges only where a
real presence-dependency demands. (top-order vs numeric is then just a *configuration* of the same
"sort, then fold" mechanism — a DAG ultimately linearizes to numbers anyway.)

- **One runtime API — `select_monad(effects) -> M`** ("select a monad for these effects, or fail"):
  sort the co-occurring effects by rank, fold their transformer instances. It is **deterministic** —
  a given effect set has *one* canonical realization (good for type identity, for baking the tower,
  for caching). It **fails loudly** only when some effect has no `Monad` transformer instance (and,
  once the DAG refinement exists, when declared edges are cyclic or leave a non-commuting co-occurring
  pair incomparable). When the effect set is statically known, `select_monad` constant-folds to
  compile time (the §8 timing split); when handlers are installed dynamically it runs at runtime over
  the active set. The resolved tower is the value reflection runs `pure`/`bind` over.

- **Order comes from rank; `provide`-nesting controls scope only.** This decouples two things a
  nesting-driven design conflates: where a handler is *visible* (the dynamic extent of `provide`)
  versus *where its layer sits* in the monad tower (its declared rank). The tower at any program
  point is "the in-scope effects, sorted by rank"; partial scope overlap is fine (the tower is built
  over the region where the relevant effects are jointly in scope). This is exactly why the
  per-effect **requirement slot of §2 stays correct as-is** — order is recovered from the rank
  table, so the slot need not become a single ordered stack; it stays keyed by effect symbol.

- **"The other order" is a different effect, not a re-nesting.** A single fixed order means you
  cannot locally flip the order of the *same* pair — deliberately: when both orders are genuinely
  wanted, the two semantics are *different effects* and should be **named as such**. State×Branch is
  already this in anthill: persistent `Modify` (`persist`/`retract` bypass the handler, §10; ranked
  *below* `Branch`, so it survives backtracking) versus a backtrackable local state (ranked *above*
  `Branch`, undone on backtrack). **Logging is the clean illustration**: an audit/trace log that must
  survive backtracking is one effect (ranked below `Branch`); a speculative log that should be undone
  when a branch fails is a *different* effect (ranked above `Branch`). Reifying the order distinction
  as effect *identity* is louder and truer than hiding it in stack position — and matches the repo's
  prefer-an-explicit-error-over-a-silent-default principle.

This is the conservative, reversible choice: the numeric default can be *refined* to declared
`effect_below` edges where a presence-dependency demands, and either form can be *relaxed* to
`provide`-nesting later if local reordering ever proves necessary — without breaking what is baked
against the canonical form. **Alternative considered** — order from `provide`-nesting plus
`commutes` facts to permit reordering: strictly more expressive (both orders of a pair for free), but
it gives up the canonical realization (type identity must then carry order), conflates scope with
order, and can fail *ambiguously per-use* rather than once at declaration. Rejected as the default
for those reasons.

## 9. Build path and WI map

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

## 10. Open questions

- **Entity → `RequirementHandle` constructor**: confirm a runtime constructor (vs the insertion-pass
  origin) composes with carrier-aware dispatch (WI-350) and the row checker (WI-307).
- **Multi-instance witnesses** (WI-200): scoped `provide` is option (c) of WI-200 — confirm the slot
  keys by witness identity, not just functor symbol, so two `Modify` instances don't collide.
- **`Modify` as State vs direct store access**: `persist`/`retract` currently bypass the `Modify`
  handler (direct `store_registry`); decide whether `Modify` is realized as the State monad through
  the slot, or stays a direct carrier with `provide` only wrapping the sub-buffer for `transaction`.
- **Cost of reflection for first-order effects**: confirm the specialized carrier path (cheap abort
  for `Throw`) is taken so `Error` never pays general `shift`/`reset`.
- **Default rank assignment, and the partial-order refinement**: decide the default numeric ranks for
  the standard effect catalog and the tie / `commutes` policy when two effects share a rank. The
  declared-DAG refinement (`effect_below` edges, topologically sorted) is deferred; if/when added, a
  cycle or an incomparable non-commuting co-occurring pair is a **loud error**, never silently
  resolved by declaration order, and whether the order closes globally or per-import-scope is decided
  then.
