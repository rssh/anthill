# Effect catalogs across Haskell / Scala / OCaml — survey for anthill's catalog

> **Purpose.** Inform anthill's standard effect catalog (027 §"Standard Effect Catalog";
> `stdlib/anthill/prelude/effects.anthill`) by surveying what concrete effects the major effect
> systems in the Haskell, Scala, and OCaml worlds actually ship. Companion to proposals 013
> (effects as sorts), 027 (handler catalog), 045 (effect rows), 047 (effects as monads via
> reflection).

## The recurring core (what essentially every system ships)

The same handful reappears in all three ecosystems — this is the "standard catalog" worth
anchoring to:

| Effect | Haskell | Scala | OCaml |
|---|---|---|---|
| **Error / Exception** (raise/catch) | mtl `Except`/`MonadError`, polysemy `Error` | cats-mtl `Raise`/`Handle`, ZIO `E`, Kyo `Abort` | native exceptions, Eff |
| **State** (get/set) | mtl `State`, `ST`, `IORef` | cats `Ref`, ZIO `Ref`, Kyo `Var` | Eio refs, Eff `State` |
| **Reader / Env / DI** (ask/local) | mtl `Reader` | ZIO `R`+`ZLayer`, cats-mtl `Ask`, Kyo `Env` | Eio capabilities (`Stdenv`) |
| **Writer / Output / Log** (tell) | mtl `Writer`, polysemy `Output`/`Trace` | cats-mtl `Tell`, Kyo `Emit` | — (usually a capability) |
| **Nondeterminism / Choice** | `[]`, `MonadPlus`, polysemy/fused `NonDet`/`Choose`/`Cut`/`Cull` | Kyo `Choice` | Eff `Decide`, Koka `ndet` |
| **IO / side effects** | `IO`, effectful `Embed`/`Final` | cats-effect `Sync`/`Async`, ZIO | native |
| **Concurrency / Async / Fiber** | effectful `Concurrent`, polysemy `Async` | cats-effect `Spawn`/`Concurrent`, ZIO fibers, Kyo `Async` | **Eio `Fiber`** (flagship use) |
| **Resource / bracket / scope** | polysemy `Resource`, effectful `Resource` | cats-effect `Resource`, ZIO `Scope`, Kyo `Resource` | **Eio `Switch`** |
| **Continuation / Coroutine / Yield / Suspension** | mtl `Cont`, freer `Coroutine`/`Yield`, GHC `control0#` | Scala 3 `boundary`/`break` | native shallow/deep handlers |
| **Transactions / STM** | `STM` | ZIO `STM`, Kyo `STM` | — |
| **Clock / Time, Random, Fresh** | effectful, fused `Fresh` | cats-effect `Clock`, Kyo `Clock`/`Random` | Eio `Time` |

## Haskell

**mtl** (the classic, transformer-per-effect): `MonadState` / `MonadReader` / `MonadWriter` /
`MonadError` (`Except`) / `MonadCont` / `MonadIO`, plus `MonadFail`, `MonadPlus`/`Alternative`
(choice), and the `RWS` combo. Order is the transformer stacking order (`StateT`∘`ExceptT` etc.) —
exactly the non-commuting-order problem 047 §8 pins with a fixed numeric rank.

**Algebraic / extensible-effects libraries** ship a defined catalog as data types + interpreters:
- **polysemy**: `State`, `Reader`, `Writer`, `Output`, `Input`, `Error`, `NonDet`, `Trace`,
  `Fixpoint`, `Resource`, `Async`, `Fail`, `Embed`, `Final`, `AtomicState`.
- **fused-effects**: `Reader`, `Writer`, `State`, `Throw`/`Catch`, `Empty`,
  `NonDet`/`Choose`/`Cut`/`Cull`, `Fresh`, `Trace`, `Fail`, `Accum`, `Lift`.
- **effectful** (IO-backed, fast; closest to a "real-world stdlib"): `Reader`, `State`
  (Static/Dynamic × Local/Shared), `Writer`, `Error`, `NonDet`, `Fail`, `Resource`, plus
  `Concurrent`, `Process`, `FileSystem`, `Environment`, `Temporary`. GHC 9.6+
  `prompt#`/`control0#` delimited-continuation primops are the native substrate the newer ones
  build on — directly analogous to anthill's activation-stack reflection (047 §4).
- **base**: `IO`, `ST` (region-scoped mutability), `STM` (transactions), `Maybe`/`Either`/`[]`.

## Scala

- **Cats / cats-mtl**: typeclass effects `Ask`/`Local` (Reader), `Tell`/`Listen`/`Censor`
  (Writer), `Stateful` (State), `Raise`/`Handle` (Error), `Chronicle`; data types
  `Kleisli`/`Reader`, `WriterT`, `StateT`, `EitherT`, `OptionT`.
- **cats-effect**: capability typeclasses around `IO` — `Sync` (suspend), `Async` (FFI),
  `MonadCancel` (cancellation), `Spawn`/`Concurrent` (fibers), `Temporal` (sleep/timeout),
  `Clock`, `Resource` (acquire/release); primitives `Ref`, `Deferred`, `Semaphore`, `Queue`.
- **ZIO**: bakes three effects into `ZIO[R, E, A]` — `R` = Reader/environment (DI via `ZLayer`),
  `E` = typed errors, `A`/IO + async. Plus `Ref`/`FiberRef` (state), `STM` (transactions),
  `Scope` (resource), fibers, `Schedule`, `Queue`/`Hub`/`Promise`.
- **Kyo** (newest, direct-style algebraic effects — most relevant to 047's reflection goal):
  `Abort` (error), `Env` (Reader), `Var` (State), `Emit` (Writer), `Choice` (nondet),
  `Async`/`Fiber`, `Resource`, `STM`, `Memo`, `Clock`, `Console`, `Random`, `Loop`. Uses an
  `A < S` "pending effects" type — close to anthill's effect rows.
- **Scala 3 core**: experimental **capture checking** + the **Caprese** project; `gears`/`Async`
  for direct-style concurrency; `boundary`/`break` as delimited control.

## OCaml

- **OCaml 5 native effect handlers** (since 5.0, 2022) are a *mechanism*, not a catalog:
  `effect E : ty`, `perform`, `match … with effect E k → …`, with `Effect.Deep`/`Effect.Shallow`
  (one-shot by default). The stdlib defines almost no standard effects — they're user-defined; the
  runtime's own use is the **scheduler/concurrency**. Architecturally the closest to anthill:
  effects-as-the-substrate, catalog supplied by libraries.
- **Eio** is the de-facto catalog, capability-based: `Switch` (structured concurrency / resource
  scope), `Fiber` (concurrency), `Flow` (IO streams), `Net`, `Fs`/`Path`, `Time`/`Clock`,
  `Domain_manager` (parallelism), `Stdenv` (capability env), `Stream`,
  `Mutex`/`Condition`/`Semaphore`, cancellation. (Predecessors `Lwt`/`Async` are promise-based,
  pre-effects.)
- **Research languages** (the catalog source for the theory): **Eff** (Bauer/Pretnar) — `State`,
  exceptions, `Decide`/nondet, I/O as illustrative operations; **Koka** (Leijen) — a *typed*
  effect row with built-ins `exn`, `div` (divergence — unusually *tracked*), `ndet`, heap effects
  `alloc`/`read`/`write`/`st<h>`, `console`, `io`, plus `ctl`/`fun` user effects and `resume`;
  **Frank**, **Links**, **Effekt** (capability / second-class, `Exc`/`State`/`Choose`/`Fiber`).

## How this maps back to anthill

anthill's current catalog (`Suspension`, `Modify`/`ModifyRuntime`, `Error`, `Branch`, `Console*`,
`Clock`; `Read` deferred — `stdlib/anthill/prelude/effects.anthill` + 027) already covers the
load-bearing core, and the naming lines up:

- **`Error`** = Except / `MonadError` / `Raise` / ZIO-`E` / Koka-`exn` ✓ (047 §2 `Error ↦ Result`
  matches mtl's `ExceptT`).
- **`Branch`** = `NonDet` / `MonadPlus` / `Choice` / `ndet` ✓ (047's `Branch ↦ Stream` is the lazy
  version Haskell's broken `ListT` *wanted* to be; `Cut`/`Cull` in fused-effects ≈ anthill's
  soft-cut / `Scored Branch` proposal 034).
- **`Modify`/`ModifyRuntime`** = State / `Ref` / `Var` ✓.
- **`Suspension`** = the Cont / Coroutine / `control0#` / OCaml-handler family ✓ — OCaml 5 is the
  proof that this is *the* substrate, vindicating 047 §4.
- **`Console*`, `Clock`** = the I/O / Time capabilities ✓.

### Gaps worth a deliberate decision (everyone else ships them)

- **Reader / environment** — `Read[T]` is deferred in 027 (§"Read as a separate effect"). ZIO's
  `R` and Eio/Effekt capabilities show this is *the* dependency-injection effect; cheap to add and
  **always commutes**, so it sits at the bottom of the numeric rank (047 §8) with no ordering grief.
- **Writer / Output / Trace** — anthill has `Console*` but no abstract accumulating `Writer`. This
  is exactly the audit-vs-speculative **logging** example (047 §8 illustration) — so Writer is
  where the "log-position-relative-to-`Branch`" distinction actually bites, and where reifying "the
  other order" as a distinct effect pays off.
- **Resource / bracket / Scope** — 047 §7 lists `bracket`/`transaction` as library functions;
  cats-effect `Resource`, ZIO `Scope`, Eio `Switch` suggest this deserves first-class catalog
  status, not just sugar.
- **Concurrency / Async / Fiber** — universally present, entirely absent in anthill. Probably
  correctly out of scope for now, but it is the one big category everyone else treats as core.
- **Divergence (`div`)** — only Koka tracks non-termination as an effect. Almost certainly not
  worth it for anthill, but worth a one-line "explicitly not tracked" so the omission is deliberate.
