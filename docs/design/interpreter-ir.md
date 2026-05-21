# Interpreter IR — a lowered, resolved form for fast eval and codegen

## Status: Proposal — for review. Not yet scheduled.

## Motivation in one paragraph

The current evaluator tree-walks the typed `NodeOccurrence` AST directly,
re-deriving on **every reduction** things the typer already knows: it
resolves call targets by string, looks up locals by resolved name, reads
per-`Apply` dispatch classification out of a `RefCell`, and rebuilds frame
vectors. Profiling (this session) shows that once the gross algorithmic
costs are removed, **the per-reduction machinery is the dominant cost** —
builtins are <0.5 % of wall time. The fix that scales is to **lower each
operation body, once, into a resolved IR** in which names are slot indices,
call targets and dispatch kinds are baked in, and `match` is a decision
tree. That same IR is the natural input to **codegen** (emit Rust/C++ per IR
node). So one artifact serves both tracks: a faster interpreter and the
eventual native-compilation path. This doc proposes that IR and a phased
plan; it does not commit to a final encoding — that's what review is for.

## What this builds on (already landed)

This proposal is the *next* step after a round of measured fixes; it is not
a rewrite of working code:

- **`Value` payloads are `Rc<[…]>`** (commit `29890ed`). Cloning an entity /
  list is now O(1) rather than a deep spine copy. This removed an O(N²)
  term that dominated list-heavy bundle commands (`list` 1.85 s → 0.18 s).
- **`op_body_cache`** (commit `db07bf5`) memoizes `lookup_operation_body`,
  which otherwise linear-scans every `OperationInfo` fact per call.
- **`ANTHILL_PROFILE`** (commit `db07bf5`) — exact per-operation reduction
  counts + per-builtin wall time. This is the measurement tool; keep it.
- Bundle-side algorithmic fixes (merge sort, Map-keyed sets) — commit
  `77c9d89`.

After these, `anthill-todo --anthill list` on 267 items is ~0.18 s vs ~0.05 s
for the legacy compiled-Rust CLI. The residual ~3.5× is fixed KB-load plus
per-reduction interpreter overhead — the latter is what this IR targets.

## The measured problem (why an IR, not more patches)

`ANTHILL_PROFILE` on `list` after the Rc-wrap: ~linear reduction count in N,
builtins negligible, time concentrated in the reducer itself. The per-call
hot path (`eval/eval.rs::dispatch_call_with_requirements`) does, on **every**
call:

1. `self.kb.resolve_sym(target).to_string()` — a heap allocation per call.
2. `find_local(&self.kb, &top.locals, &target_name)` — a linear scan of the
   frame's locals comparing **resolved strings** (locals are keyed by
   `Symbol` but a callee `Symbol` may differ from a local binding's `Symbol`
   for the same name, so today the comparison must go through the string).
3. `classification.borrow().clone()` + `collect_resolved_type_args(occ)` —
   per-`Apply` `RefCell` reads of typer output.
4. Frame construction: `SmallVec` locals/requirements/type_args allocated
   and populated per call; variable reads (`reduce_var`) re-scan locals.

None of these depend on the *data*; they're constant re-work per node. They
can't be removed by tuning data structures — only by resolving them once,
ahead of execution. That "resolve once" pass is the IR.

## Current architecture (for reference)

```
.anthill → parse → ParsedFile → scan_definitions → load → KnowledgeBase
   KB stores each operation body as a typed `NodeOccurrence` tree
   (kb/node_occurrence.rs): Expr::{Const,Ref,Ident,VarRef,If,Let,Match,
   Lambda,Apply}, with RefCell side-channels (`classification`,
   `resolved_type_args`) written by the typer.
Interpreter (eval/) drives an activation stack of `Frame { op, expr:
   Rc<NodeOccurrence>, locals: SmallVec<(Symbol,Value)>, requirements,
   type_args, awaiting }`. `step()` reduces the top frame's expr; `deliver()`
   cascades results without re-entering `step()`.
```

The interpreter is correct and battle-tested (1163 tests). The IR does not
replace the typer or loader — it consumes their output.

## Proposed IR: `CompiledOp`

A per-operation, fully-resolved, immutable program produced by a new
**lowering pass** that runs after type-checking. One `CompiledOp` per
operation body, cached on the KB (or alongside `op_body_cache`).

Design goals, each addressing a measured cost:

1. **Slot-indexed locals/params.** A body is compiled against a fixed
   *slot map*: each param and `let`-binding gets a `u16` slot. Variable
   reads become `Local(slot)`; the runtime env is a flat `Vec<Value>` (or
   `SmallVec`) indexed by slot — no name, no scan, no string. (Replaces
   costs #1 partially and #2 and #4's `reduce_var`.)

2. **Resolved, pre-classified calls.** Each call site lowers to one of a
   small set of call instructions with the target and dispatch kind already
   decided by the typer — e.g. `CallStatic(op_id, args)`,
   `CallBuiltin(builtin_id, args)`, `CallLocalClosure(slot, args)`,
   `CallViaRequirement(req_slot, op_short, args)` (the names-model dispatch
   from `operation-call-model.md`). No per-call string resolution, no
   `RefCell` classification read. (Replaces costs #1, #3.)

3. **Match as a decision tree.** `Match` lowers to a tested dispatch on the
   scrutinee's functor/constructor plus binding extraction into slots,
   rather than re-walking branch patterns interpretively.

4. **Explicit channels.** Requirement dictionaries and operation type-args
   are positional slots in the IR, matching the names/positional model
   already designed in `operation-call-model.md` — so the IR is the natural
   place that decision becomes concrete.

Sketch (illustrative, not final):

```rust
struct CompiledOp {
    n_slots: u16,                 // params + lets
    n_params: u16,
    body: Box<Instr>,            // tree of instructions (or a flat block list)
}

enum Instr {
    Const(Literal),
    Local(u16),                  // read slot
    LetIn { slot: u16, value: Box<Instr>, body: Box<Instr> },
    If { c: Box<Instr>, t: Box<Instr>, e: Box<Instr> },
    Match { scrutinee: Box<Instr>, arms: Vec<MatchArm> }, // decision tree
    MakeEntity { functor: Symbol, pos: Vec<Instr>, named: Vec<(Symbol, Instr)> },
    CallStatic   { op: OpId,      args: Vec<Instr> },
    CallBuiltin  { b: BuiltinId,  args: Vec<Instr> },
    CallClosure  { slot: u16,     args: Vec<Instr> },
    CallViaReq   { req_slot: u16, op_short: Symbol, args: Vec<Instr> },
    Lambda(Rc<CompiledLambda>),  // captures by slot
}
```

Whether `Instr` stays a tree (cheap to build, still some pointer-chasing) or
becomes a **flat bytecode block** (one `Vec<Op>` per body, registers/stack,
best for the interpreter loop and trivial to codegen) is the central open
question — see below.

## Two consumers, one IR

**Interpreter-v2** executes `CompiledOp`: a flat `Vec<Value>` env indexed by
slot, a dispatch over `Instr`/opcodes with no string work and no `RefCell`
reads. The activation-stack discipline (`docs/design/...`, current
`run`/`deliver`) is preserved — only the per-node work shrinks. Expected:
the ~µs-scale per-reduction cost drops toward tens of ns; combined with the
already-landed Rc-wrap this should put bundle commands within a small factor
of native.

**Codegen** translates `CompiledOp` to a target language: each `Instr` maps
to an expression/statement; slots become locals; `CallStatic` becomes a
direct call; `Match` becomes a `match`/`switch`. This is the concrete input
that `anthill-rust-gen` (proposal 029) and the `rust+anthill` profile
(WI-164) need for the WI-009b "compile hot sorts to native" path. Sharing
the IR means dispatch/resolution semantics are defined once and can't drift
between interpreter and compiled output.

## Phased plan

1. **Spike / validate (small).** Before the IR, confirm the per-call costs
   are what profiling implies: make local lookup `Symbol`/slot-keyed and
   drop the per-call `to_string`, measure. De-risks the IR's premise.
2. **IR + lowering pass.** Define `CompiledOp`/`Instr`; lower
   `NodeOccurrence` → IR after type-checking; cache on the KB.
3. **Interpreter-v2 over the IR.** Retarget the reducer; keep the old path
   until parity (the 1163-test suite + bundle byte-identical output) holds.
   This is the proof the IR executes correctly and fast.
4. **Codegen over the IR.** Emit Rust from `CompiledOp`; wire into the
   `rust+anthill` profile for hot sorts (WI-009b).

Interpreter-v2 comes before codegen: it makes the IR fast as a side effect,
it's the cheapest correctness check for the IR, and codegen consumes the
same artifact.

## Open questions (for review)

- **Tree vs. flat bytecode for `Instr`.** Bytecode is faster to interpret
  and easier to codegen but more work to build and debug. A tree is a
  smaller step from today. Which do we commit to?
- **Where the lowering output lives.** A new KB-side cache, an extension of
  `op_body_cache`, or a separate compile step invoked by the host before
  `main`?
- **Closures and requirements.** The IR must encode the names-model
  dispatch (`operation-call-model.md`) — capture-by-slot for lambdas,
  `req_slot`/`op_short` for requirement dispatch. Confirm the slot model
  composes with closure capture before fixing the encoding.
- **Incremental vs. whole-program lowering.** Lower per-operation lazily on
  first call (like `op_body_cache`), or eagerly at load?
- **Reflection.** Some builtins (`body_of`, `args_of`, WI-242 `Value::Node`)
  walk `NodeOccurrence` directly. Decide whether they keep reading the AST
  (kept alongside the IR) or move to the IR.
- **Equation-defined operations (no body).** Some operations have no
  `NodeOccurrence` body — they are defined entirely by equational rules
  (`add_zero`, `first` today; `min`, AD's `diff`, etc. under the dot-syntax
  proposal in `docs/design/dot-macro-brainstorm.md`). The lowering pass has
  nothing to lower for them, yet eval-v2 hits `CallStatic(op_id, …)` for such
  a call. Two options, and **codegen forces the answer**: (a) compile the
  equation set into a `CompiledOp` (e.g. `min`'s rules → `if compare(a,b)<=0
  then a else b`, an `If` over a `CallViaReq`) — feasible for deterministic +
  complete sets, *required* for codegen since the resolver's equational
  fallback can't be emitted into native code; (b) keep an equational-fallback
  execution path for body-less ops — smaller interpreter step, insufficient
  for codegen. Likely both: compile where the set is deterministic +
  complete, fall back otherwise. The dot-syntax design depends on this path
  (its value-conditional rewrites residualize to runtime calls on such ops),
  but the question pre-dates it.

## Non-goals

- Replacing the parser, loader, or typer — the IR consumes their output.
- Changing language semantics or the operation-call model — the IR
  *implements* the agreed model, it doesn't redesign it.
- A bytecode VM with its own GC — `Value` + the arena handles stay.
