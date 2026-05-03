# WI-156 — scaland expression evaluator: design memo

**Status:** draft, pre-implementation
**Parent:** WI-151 (scaland resync umbrella) → WI-156
**Reference impl:** `rustland/anthill-core/src/eval/` (~3500 LOC across 11 files), proposal 026 + 026.1
**Author target:** scaland resync stack, post-WI-161

## 1. Scope

Port the rustland evaluator to scaland with **parity on the proposal-026 core fragment**:

- literals (Int / BigInt / Float / Bool / String / Unit)
- variables, `let` bindings
- `if`-`then`-`else`
- `match` with N arms; pattern shapes: var, wildcard, literal, tuple, named-tuple, constructor, nested
- lambdas + closures (variable capture by reference into the closure arena)
- positional + named function application
- entity construction
- operation-to-operation calls (anthill-defined and Rust/Scala-side builtin)
- list / tuple literals
- effect-tagged operations (Console / Modify / Error) — at least to dispatch through a registered handler

**Out of scope for v1:** `Suspension`/`Branch`, lazy values, `LogicalStream`/KB-query integration (proposal 026.1), Modify-store back-end, persistent continuations, the substitution arena beyond what closure pattern-matching needs.

The rustland delivery shipped as M1→M5 + Q3 phases; scaland mirrors the **M1 + M2** scope, with M3 (effects) reduced to "dispatcher exists, can call a Console handler", and M4 (KB integration) deferred to its own WI.

## 2. Reference implementation walk

`rustland/anthill-core/src/eval/`:

| File | LOC | Role |
|------|----:|------|
| `mod.rs` | 411 | `Interpreter`, public API (`call`, `run`), arena ownership, builtin registry |
| `value.rs` | 172 | `Value` enum: unboxed scalars, `Tuple`, `Entity`, `Closure(Handle)`, `Stream(Handle)`, `Term(TermId)` |
| `frame.rs` | 144 | `Frame` (locals + `awaiting: Option<AwaitState>`), `ActivationStack` |
| `eval.rs` | 850 | the `step()` loop — tree-walking interpreter dispatching on the `ExprOccurrence` shape |
| `pattern.rs` | 200 | match-arm test + binder extraction |
| `closure.rs` | 262 | `Closure` (captured env + body), `ClosureArena` (refcounted slots) |
| `subst_arena.rs` | 163 | first-class substitution handles (proposal 026.1, **out of scope for v1**) |
| `stream.rs` | 220 | `LogicalStream` runtime rep (**out of scope for v1**) |
| `effects.rs` | 351 | effect-handler registry, dispatch, contract enforcement |
| `builtins.rs` | 692 | standard `Numeric.add`, `String.concat`, `Eq.eq`, `Bool.ite`, etc. — Rust-side bodies |
| `error.rs` | 42 | `EvalError` enum |

**v1 port estimate (scope reduced):** ~1500 Scala LOC across 7 files. The deferrals (`subst_arena` + `stream` + most of `effects`) drop ~700 LOC; deferred parts of `builtins` drop another ~300.

## 3. Key design decisions for the Scala port

### 3.1 `Value` representation: enum sealed trait, not Scala native lambdas

**Decision:** use a sealed `enum Value` mirroring rustland's, *not* a representation that uses Scala native function values for `Closure`.

Rationale:
- The closure body is an `ExprOccurrence` (i.e. a `TermId` pointing at IR), not a JVM bytecode block. Storing it as a Scala native `Function1[Value, Value]` would force eager bytecode-level closure capture and lose the IR-walking semantics that the rest of the evaluator needs (debugging, suspension support later, effect-trace inspection).
- The `Term(TermId)` variant is essential — it's the cheap promotion to KB-resident form. Native lambdas can't host this without an awkward hybrid.
- Mirroring rustland's `Value` shape keeps cross-implementation testing straightforward — same trace shapes, same error-on-shape-mismatch semantics.

Concrete type:

```scala
enum Value:
  case IntV(v: Long)
  case BigIntV(v: BigInt)              // scala.math.BigInt
  case FloatV(v: Double)
  case BoolV(v: Boolean)
  case StrV(v: String)
  case UnitV
  case TupleV(pos: IndexedSeq[Value], named: IndexedSeq[(TermSymbol, Value)])
  case EntityV(functor: TermSymbol, pos: IndexedSeq[Value], named: IndexedSeq[(TermSymbol, Value)])
  case ClosureV(handle: ClosureHandle)
  case TermV(id: TermId)               // KB-resident, hash-consed
```

`StreamV` / `SubstitutionV` / `LazyV` are deferred to v2.

### 3.2 `Frame` representation: heap-allocated case class on an explicit stack

**Decision:** mirror rustland's `Frame` + `ActivationStack` exactly. `Frame` is a mutable case class held in a `mutable.ArrayDeque[Frame]`; `step()` is a single transition driven by the top frame's state.

Rationale:
- The JVM's recursion limit is much lower than the host C stack (typically 10–20K frames before `StackOverflowError`). User programs with deep non-tail recursion need an explicit stack.
- Keeping the same `AwaitState` ADT as rustland means integration-test traces line up across implementations — useful for cross-checking semantics during the port.
- TCO falls out naturally from "explicit stack + `OperationResult` await mode", matching rustland's WI-061. Implement TCO in v1 (small win, prevents trivial test failures).

Scala-specific note: prefer `mutable.ArrayDeque[Frame]` over `mutable.Stack` for stable indexed access. `Frame` carries its own `expr: TermId` mutable field — bytecode-level mutable case classes are fine in this internal-only context.

### 3.3 Closure arena: `RefCell<Map>`-equivalent via mutable

**Decision:** a `ClosureArena` class with an `ArrayBuffer[Slot]` and an integer free-list. `ClosureHandle` is a `case class(idx: Int)` plus a refcount on the slot.

Rationale:
- Mirror rustland's manual refcounting rather than relying on JVM GC. Reason: closures hold `TermId`s and captured `Value`s, and the TermStore's hash-consed terms should have predictable lifetimes at KB boundaries — predictable enough that we can detect leaks during tests.
- v1 doesn't need cycle detection; closures are tree-shaped (no closure-captures-itself patterns supported).
- Implement `Drop`-equivalent via Scala 3 `using` blocks or explicit `release(handle)` calls in the `step()` cleanup paths. (Resource: `scala.util.Using` if needed.)

### 3.4 Effect dispatch: a registry, not effect-as-monad

**Decision:** effect handlers are `Map[TermSymbol, EffectHandler]` registered on the `Interpreter`. `EffectHandler` is `(args: Seq[Value]) => Value` (or `IO`-equivalent if we want non-blocking later, but for v1 just a synchronous function).

Rationale:
- Rustland's effects subsystem is the most complex eval file (~350 LOC). The bulk of that is contract enforcement (handler arity, declared effect set, propagation through nested calls). v1 reduces to: "Console.println dispatches to the registered handler, errors propagate as `EvalError.HandlerFailed`." Defer contract enforcement to a follow-up.
- Effect-as-monad (cats-effect / ZIO) is tempting but brings a heavyweight dependency for a single use case; the registry approach is what rustland chose and we mirror.

### 3.5 Builtins: codegen vs. hand-written

**Decision:** hand-written for v1 (~10 builtins: `Numeric.add/sub/mul`, `Eq.eq`, `Bool.{and,or,not,ite}`, `Int.neg`, `String.concat`, `List.{nil,cons}`).

Rationale:
- Rustland's `builtins.rs` is ~700 LOC because it covers the full prelude. We need only the subset our test programs actually invoke. Adding more is mechanical.
- Codegen-from-stdlib would be overkill at this stage; revisit if the list grows past ~30.

### 3.6 Substitution arena (proposal 026.1) — explicitly deferred

`SubstHandle` and the substitution arena are first-class for KB-query integration. v1 doesn't run KB queries from expression bodies. **Defer to a separate WI** ("scaland eval — KB-query integration"); revisit when WI-157 (prove/check) needs `LogicalStream`.

## 4. Implementation plan

Five phases, each independently shippable; each phase ends with green sbt tests.

### Phase 1 — IR + Value + Frame skeleton (~1 day)

- New package `anthill.eval` under `scaland/core/src/main/scala/`.
- `Value.scala`, `Frame.scala`, `ActivationStack.scala`, `EvalError.scala`.
- `Interpreter` class with stub `call(qname: String, args: Seq[Value]): Either[EvalError, Value]` returning `EvalError.NotImplemented`.
- ParseTest case: construct an `Interpreter`, verify it instantiates, no-op `call` returns the expected error variant.

### Phase 2 — M1: literals, let, if, operation calls (~2 days)

- `Closure.scala` + `ClosureArena.scala` (closures are needed even for non-lambda operation calls — body of an anthill operation is essentially a closure with no captured env).
- `eval.rs:step()` Scala port for: `Const`, `Ident` (var lookup), `let`, `if`, plain `apply` to anthill-defined operations.
- Builtin registration scaffolding (no actual builtins yet).
- Tests: `eval_m1_test.rs` ported case-by-case to a new `EvalM1Test.scala`.

### Phase 3 — M2: pattern matching, lambdas, list/tuple literals (~3 days)

- `Pattern.scala`: pattern shape testers + binder extractors.
- `step()` cases for `match`, `lambda`, `Tuple`/`List` constructors.
- Hand-written builtins for `Numeric.add/sub/mul`, `Eq.eq`, `Bool.{and,or,not,ite}`, `String.concat`.
- Tests: `eval_m2_test.rs` port → `EvalM2Test.scala`.

### Phase 4 — M3: effect-tagged ops (Console only) (~1 day)

- `EffectHandler` trait, registry on Interpreter.
- `step()` case for `Effect`-annotated apply: route to registered handler; pass values through.
- One handler implemented: a `ConsoleHandler` that captures `println` calls into a buffer (for testability).
- Test: short program calling `Console.println("hi")` returns Unit and the buffer captured the right string.

### Phase 5 — TCO + cleanup (~1 day)

- `OperationResult` await mode + tail-call detection in `apply` lowering.
- Test: tail-recursive sum over a list of N=10K runs without `EvalError.DepthExceeded`.

**Total estimate:** ~7 working days for v1 parity on the M1+M2 fragment + a token effect dispatcher.

## 5. Test strategy

- Per-phase unit tests in `scaland/core/src/test/scala/anthill/eval/`.
- Parity test: run the same `.anthill` program through both rustland and scaland, assert identical `Value` shapes (modulo the Tuple `IndexedSeq` vs `Vec` cosmetic). Set up via env var pointing at rustland binary; opt-in (don't make CI depend on rustland being built).
- Acceptance per WI-156: at least one program from `examples/` running end-to-end through scaland's evaluator with the same observable output as rustland.

## 6. Open questions

1. **Should `Value.BigIntV` be `scala.math.BigInt` or `java.math.BigInteger`?** Scala's `BigInt` is a thin wrapper; java's avoids one indirection. Default to Scala's for ergonomics; revisit if JIT profiling shows the wrapper cost matters.
2. **How are anthill-defined operation bodies represented?** rustland uses `OccurrenceId → ExprOccurrence` lookup. Does scaland's loader emit equivalent `Operation.body: Option[TermId]` already? — likely yes (parser produces it), but verify in the Phase 1 spike.
3. **Modify (mutable KB writes) — fully out of scope?** Probably yes for v1; the prove/check use case (WI-157) reads the KB but doesn't mutate it during eval. Revisit if a use case surfaces.
4. **Closure `ho_apply` — do we go through the same path as ordinary apply?** v1 says yes — `ho_apply(?P, args)` resolves `?P` to a `ClosureV` from the local env, then dispatches normally. This was the WI-162 parser fix's intent.

## 7. Cross-references

- Proposal 026 + 026.1 (`docs/proposals/`): canonical semantics — read first.
- `rustland/anthill-core/src/eval/`: reference implementation (3500 LOC).
- `rustland/anthill-core/tests/eval_m1_test.rs` and `eval_m2_test.rs`: the test surface scaland will mirror in v1.
- `rustland/anthill-core/CLAUDE.md` — eval-specific notes.
