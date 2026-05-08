# Cell — Runtime Design

## Status: Draft

This is an **implementation design** doc, not a proposal. The user-facing interface is fixed by [proposal 037](../proposals/037-anthill-state-model.md) §"Cell[V]". This doc covers how that interface is realized in the Rust runtime, including identity, lifecycle, and the migration from v0.1's stop-gap to the target shape.

## Interface (recap from 037)

```anthill
sort anthill.prelude.Cell
  sort V = ?
  operation new(initial: V) -> Cell
  operation get(c: Cell) -> V
  operation set(c: Cell, value: V) -> Unit
    effects Modify[c]
end

fact Modifiable[T = Cell]
```

Three observations carried over from the proposal:

1. **Cell is a handle, not the value.** The Cell itself is stable; `get(c)` returns whatever value is currently held; `set(c, v)` replaces it.
2. **Allocation is anthill-side via `new`.** Each `new(initial)` should return a fresh, independent cell — not aliased with any prior cell.
3. **Modifiable is the typing-level marker.** A type T admits `Modify[T]` in effect rows iff it has a `Modifiable[T = T]` fact. For Cell, this is asserted in the same file.

## Goals of the runtime

- **Each `Cell.new` returns a distinct cell.** Repeated calls — including in deep recursion — produce non-aliased cells. This is non-negotiable for correctness; without it, recursive code mutating local cells silently breaks.
- **Slots are reclaimed when the Cell handle is no longer reachable.** No monotonic growth. Recursive allocation is a normal pattern; the arena must keep up.
- **Cycles are detectable** (a Cell holding itself, or two Cells referencing each other). Existing Modify handler code already does this; the new arena should preserve the check.
- **Branch-aware** (eventually). When the runtime grows snapshot/`register_undo` for `Branch`, Cell's slots participate per the framework's branch-local-snapshot contract. v1 of the arena does not implement this; it is a forward-compat constraint on the data layout.

## Runtime model

A Cell is a **handle** to a slot in an arena. Mirrors the existing `map_arena` / `subst_arena` / `stream_arena` machinery (`rustland/anthill-core/src/eval/{map_arena,subst_arena,stream}.rs`).

```rust
// rustland/anthill-core/src/eval/cell_arena.rs (new)

pub struct CellArena {
    slots: Vec<Slot>,
    free_list: Vec<u32>,
}

struct Slot {
    /// The held value. None during transient pumps (matches the
    /// stream arena's invariant) — should be Some between operations.
    value: Option<Value>,
    /// Refcount. Slot is reclaimed when refcount drops to zero.
    refcount: u32,
}

pub struct CellArenaRef(Rc<RefCell<CellArena>>);

pub struct CellHandle {
    raw: u32,
    arena: CellArenaRef,
}

impl Clone for CellHandle { /* incref */ }
impl Drop  for CellHandle { /* decref; reclaim at zero */ }
```

A new `Value::Cell(CellHandle)` variant identifies cells in user-visible Values. The variant carries the handle, and that's all — no functor-based key, no field-based key. Identity is the slot index (effectively allocation-time uid).

### Operations

`Cell.new(initial)`:
1. `interp.cells.alloc(Slot { value: Some(initial), refcount: 1 })` → fresh slot index.
2. Return `Value::Cell(CellHandle { raw, arena: arena.clone() })`.

`Cell.get(c)`:
1. Match `c` as `Value::Cell(h)` → `h.raw`.
2. `interp.cells.with_value(h, |v| v.clone())`.

`Cell.set(c, new)`:
1. Cycle-check `new` against `c` (transitively does `new` reference c?). Reuses the existing cycle detector from `effects.rs`.
2. Match `c` as `Value::Cell(h)` → set the slot's value to `new`.
3. Return `Value::Unit`.

The Modify effect row on `set` (`Modify[c]`) is satisfied because `Cell` has a `Modifiable` fact. Runtime dispatch routes `Cell.set` calls directly to the Cell builtin (no shared Modify handler involved); the framework's "per-resource handler" mechanism is realized as the Cell builtin owning its arena.

## Identity scheme

**Opaque-handle**, per [WI-200](../../anthill-todo/workitems.anthill) §"Multi-instance Modify state". The slot index is the identity; two slots with the same value are still distinct cells. This is what enables the recursive-allocation case: each `Cell.new` allocates a fresh slot.

This is a strict upgrade from v0.1's functor-only scheme:

| | v0.1 (current) | Target |
|---|---|---|
| `Cell.new` returns | `Value::Entity { functor: "Cell", named: [] }` | `Value::Cell(handle)` |
| Identity | The "Cell" symbol (one per process) | Slot index (one per allocation) |
| Aliasing | All Cells alias | None |
| Lifecycle | Slot lives forever | Refcount; reclaimed at 0 |
| Recursion-safe | No — mutually clobbers | Yes |

The functor-keyed Modify slot stays in place for *non-Cell* Modify-using resources (KB internal indexes when KB.assert routes through Modify, etc.) — the migration is per-resource, not all-at-once.

## Lifecycle

### Refcount

- `CellHandle::clone` increments. Cloning a `Value::Cell` (assigning to a let-binding, passing to a function, storing in a list) clones the handle.
- `CellHandle::drop` decrements. When the refcount reaches zero, the slot's `value` is taken out (releases any internal refs it held — recursive Drop), and the slot index is pushed onto the free list.
- `CellArena::alloc` reuses free-list slots before extending the `Vec`.

### Cycle handling

A Cell can hold a Value that transitively references the Cell itself — direct (`Cell.set(c, Value::Cell(c))`) or indirect (two cells holding each other through any number of levels of nesting). Refcounting alone does NOT reclaim cyclic structures: two cells that point to each other have refcount ≥ 1 forever. Two complementary mitigations:

1. **Cycle prevention at write time** — strict; rejects all cycles. v1 default.
2. **Cycle collection** (sweep, reachability-based) — permissive; allows cycles but periodically reclaims. Out of scope for v1; would arrive with a more general arena GC story (e.g. `gc-arena`).

The strict approach is consistent with anthill's current value model and matches the existing `detect_cycle` in `effects.rs` — but the existing detector is approximate (functor-symbol comparison, doesn't read through arena slots) and works only because v0.1's functor-only Cell is degenerate (one slot total, no second cell to form a back-edge). The cell_arena needs a stronger detector.

#### Why a graph walk is required

Two recursive `Cell.set` calls suffice to construct a cycle the symbol-walk misses:

```anthill
let a = Cell.new(0)
let b = Cell.new(0)
Cell.set(a, b)   -- a's slot ← Value::Cell(b);  walk on b finds: 0; OK
Cell.set(b, a)   -- b's slot ← Value::Cell(a);  walk on a finds: ?
```

For the second set's check to reject correctly, walking `a` must read a's *current slot contents* (`Value::Cell(b)`) and recurse into that — discovering b is the target. The walk has to traverse the arena, not just the value structure.

Worse, Cells can be nested arbitrarily inside other values:

```anthill
let a = Cell.new(0)
Cell.set(a, [some_entity{field: a}, ...])   -- a's slot holds a list whose first element is an entity whose `field` is a
```

The Cell reference is buried under a list element under an entity field. The detector must descend into Entity / Tuple / Map / List / Stream / Closure structure recursively, finding any `Value::Cell` reference at any depth.

#### The detector — distribute walk knowledge across Value and Term

Rather than one big `match` in `detect_cycle` enumerating every variant, give each value-shape its own walk method. The detector orchestrates; per-shape recursion logic stays local.

```rust
/// Visit each *directly* referenced Cell slot. Implementations
/// recurse through their own structural children (Entity fields,
/// Tuple positions, Map values, captured-env, term args, …) but do
/// NOT descend through Cell handles into their slot contents — the
/// caller orchestrates that, holding the visited-set.
pub trait WalkCells {
    fn walk_cells(&self, f: &mut dyn FnMut(SlotIdx));
}

impl WalkCells for Value {
    fn walk_cells(&self, f: &mut dyn FnMut(SlotIdx)) {
        match self {
            Value::Cell(h)                  => f(h.slot),
            Value::Entity { pos, named, .. }
            | Value::Tuple { pos, named, .. } => {
                for v in pos { v.walk_cells(f); }
                for (_, v) in named { v.walk_cells(f); }
            }
            Value::Map(h)     => arena_lookups.with_map(h, |body| {
                                     for (_, v) in body { v.walk_cells(f); }
                                 }),
            Value::Closure(c) => closure_arena.with_env(c, |env| {
                                     for v in env { v.walk_cells(f); }
                                 }),
            Value::Term(tid)  => kb.with_term(*tid, |t| t.walk_cells(f)),
            Value::Stream(_)  => { /* opaque — see open question */ }
            _                 => {}                       // primitives
        }
    }
}

impl WalkCells for Term {
    fn walk_cells(&self, f: &mut dyn FnMut(SlotIdx)) {
        match self {
            Term::Fn { pos_args, named_args, .. } => {
                for tid in pos_args { kb.with_term(*tid, |t| t.walk_cells(f)); }
                for (_, tid) in named_args { kb.with_term(*tid, |t| t.walk_cells(f)); }
            }
            // Term::Const, Term::Var, Term::Ref, etc. — no Cell refs
            _ => {}
        }
    }
}

/// Detector orchestrates: BFS through the cell graph, marking visited
/// slots, halting on target.
fn detect_cycle(
    arena: &CellArena,
    target: SlotIdx,
    initial: &Value,
) -> Result<(), CycleError> {
    let mut visited = HashSet::new();
    let mut worklist: Vec<Value> = vec![initial.clone()];
    while let Some(val) = worklist.pop() {
        let mut hit_target = false;
        val.walk_cells(&mut |slot| {
            if slot == target { hit_target = true; }
            else if visited.insert(slot) {
                worklist.push(arena.read(slot));
            }
        });
        if hit_target { return Err(CycleError); }
    }
    Ok(())
}
```

**Implementation note: walk_cells must be iterative too.**

The trait method `walk_cells` recurses through structural children (Entity fields, Map values, etc.). A pathologically deep value tree — 10 000 nested Tuples — would blow Rust's host stack. Each `walk_cells` impl on a multi-child variant must use an internal worklist, not recurse:

```rust
impl WalkCells for Value {
    fn walk_cells(&self, f: &mut dyn FnMut(SlotIdx)) {
        let mut stack: Vec<&Value> = vec![self];
        while let Some(v) = stack.pop() {
            match v {
                Value::Cell(h) => f(h.slot),
                Value::Entity { pos, named, .. }
                | Value::Tuple { pos, named, .. } => {
                    stack.extend(pos.iter());
                    stack.extend(named.iter().map(|(_, v)| v));
                }
                Value::Map(h)     => arena.with_map(h, |body| {
                                         for (_, v) in body { stack.push(v); }
                                     }),
                Value::Closure(c) => /* push captured env entries */,
                Value::Term(tid)  => /* push term children */,
                Value::Stream(_)  => { /* opaque */ }
                _                 => {}
            }
        }
    }
}
```

The outer `detect_cycle` already uses a worklist for cell-graph traversal; combined with the iterative `walk_cells`, the maximum recursion depth in Rust is O(1) regardless of value-tree depth or cell-graph size. The only resource bound is heap memory for the worklists themselves.

Two reasons to factor this way:

1. **Encapsulation.** Each `Value` variant's structural traversal is local to its impl, not buried in a giant `match` in cycle-detection code. New variants slot in by implementing the trait. Same goes for adding fields to existing variants.

2. **Reuse.** Other walks the system needs — type-driven skip analysis, snapshot for Branch, debug-print of reachable cells, GC mark-phase if we ever go that route — all want to enumerate Cell references inside a Value/Term. The trait method is the single source of truth for "what's reachable from here." Cycle detection is one consumer; future code is others.

3. **Testability.** `walk_cells` is independent of the detector — it can be unit-tested per variant ("a Value::Tuple visits each of its positional values exactly once") without setting up an arena.

#### Cost

Per `Cell.set(c, v)`: walks `v`'s value tree once, reads through each distinct Cell handle's slot once (visited-set bounded), recursively walks each slot's contents. Worst case: O(|value-tree| + Σ|cell-slot-contents reachable from v|).

For the dominant use cases — primitive-valued cells, cells holding small records — this is a few-node walk with no arena reads. For deep graph-shaped data, it's a real graph traversal.

There is no "fast-path bail." The naive bail "scan for any Value::Cell" is itself a recursive walk through the value tree (a Value::Cell may be buried under arbitrary Entity / Tuple / List nesting), so it does the same work as `detect_cycle` itself in the cell-free case. They tie.

The real optimization is **type-driven skip**: when the typer knows the cell's value type contains no Cell — e.g. `Cell[Int]`, `Cell[wis(IndexedFileStore, Int)]` where neither inner type carries Cell — skip the walk entirely. This requires the typer to compute and surface a "may-contain-Cell" flag per type. v1 of the cell_arena does NOT include this optimization; if perf measurements show the walk dominates, file a follow-up to add typer-driven skip.

For v1: every `Cell.set` runs `detect_cycle`. Programs that mutate primitive-valued cells in tight loops will see one pass over a small value per set — negligible. Programs that build complex graph structures pay the proportional cost.

#### Structurally walkable vs operationally accessible

The cycle detector only works on **structurally walkable** references — values reachable by descending through the value tree without calling user-level operations. A Cell stored as a positional or named arg of an Entity is walkable; a Cell stored inside a Map's body, or a Term's args, is walkable (the runtime exposes those structures via arena reads).

References reachable only by **calling an operation** are *not* walkable. Any sort whose values are opaque from outside — whose contents can only be inspected via operation calls — has this property:

- **Closure** — its body executes; what it returns may contain Cells, but the detector can't pre-compute that without running the closure.
- **Stream** — `splitFirst` yields elements; the next element might contain a Cell, but pumping the stream is a side-effecting operation the detector can't perform.
- **Any user-defined sort** with `entity Foo` plus `operation produce(f: Foo) -> SomeValue` and no structural fields exposing the inner state. Like Stream, like Closure, like Map (sort of — `Map` exposes its body via arena read, but the body isn't part of the Value's structural tree).
- **Term** with a `QuotedRepr` or other lazy form whose contents are only computed on demand.

These are all the same shape: opaque from a value-walk's perspective. A Cell holding such a value, where the value would *in principle* return a reference to the Cell when its operations are called, forms an "operational cycle" that structural walk cannot detect.

This is **not a Stream-specific gap**; it's a fundamental limit of structural cycle detection. Same constraint applies to Rust's `Rc<T>` cycle handling: detection there is also user responsibility (via `Weak`) because the runtime can't introspect closures or trait objects.

#### What v1 does and doesn't catch

The detector descends into:
- `Value::Cell` (reads slot contents).
- `Value::Entity` (positional + named fields).
- `Value::Tuple` (positional + named).
- `Value::Map` (via arena read of map body, then values).
- `Value::Term` (via term-store read of children).

The detector does **not** descend into:
- `Value::Closure` (captured env opaque from this layer; possibly addable but cost depends on env exposure).
- `Value::Stream` (no structural form; would require pumping).
- Any user-defined sort backed by an opaque arena handle without a structural reflection path.

Practical implication: cycles formed entirely through structural references (Cells in Entities, Tuples, Maps, Terms) are caught and rejected. Cycles formed through operationally-accessible references (Cells captured by closures, yielded by streams, hidden behind opaque user sorts) are **not** caught — they leak.

The strict approach rules out genuinely cyclic Cell graphs at write time for the design's target use cases (state cells, registries, counters, in-memory caches). Cycles through opaque sorts are a user-side concern, the same way Rust's Rc cycles are — document and move on. If a real consumer surfaces "I need to store closures-capturing-cells in cells without leaking," the answer is either explicit `Weak` (a future addition) or a tracing GC (the gc-arena option flagged earlier).

### Drop ordering

When a slot is reclaimed, its `value: Value` is dropped, which may transitively drop nested handles (e.g. a Cell holding a Map handle). Each handle's Drop decrements its respective arena. Standard Rust destructor flow; no special handling required.

## Branch interaction

Per proposal 037 §"Cell[V]" interpreter contract: **branch-local snapshot**. The arena is branch-local — mutations inside a `Branch` alt are reverted if the alt is abandoned (a sibling resumes); kept if the alt commits.

The mechanism is **per-mutation undo logging**, not full-arena clone. Pays only for what you change.

### Hooks via `register_undo`

Proposal 037 (and 027 §RuntimeAPI) describes `register_undo(undo: HostCallable)` — installs a callback to fire when the current branch snapshot is abandoned. The cell_arena hooks into this:

```rust
// Cell.set(target, new):
let prev = arena.read(target.slot);                     // read current
arena.write(target.slot, new);                          // write new
runtime.register_undo(move |arena| {
    arena.write(target.slot, prev);                     // restore if abandoned
});

// Cell.new(initial):
let slot = arena.alloc(initial);                        // fresh slot
runtime.register_undo(move |arena| {
    arena.dealloc(slot);                                // reclaim if abandoned
});
```

Refcount handling rides along: on abandon, restoring a slot's prior value drops the value that was there during the branch (which, since the slot itself is being restored, is the value to be discarded). The drop's `Drop` impl decrements the refcounts of any Cell handles inside the discarded value. On commit, the new value sticks; the prior value's refs are properly released by the `Drop` of `prev` when the closure goes away (since the closure owned `prev`).

### Allocation undo

`Cell.new` inside a branch allocates a fresh slot. On abandon, the slot must be reclaimed. The undo callback dealloc's the slot, returning its index to the free list. The handle returned by `Cell.new` is, on abandon, dangling — but since the branch is abandoned, no anthill-level binding to that handle survives (locals from the abandoned branch's frames are dropped normally as part of the resolver's snapshot rewind).

### What about handles that escape the branch?

A handle returned from inside a branch *upward* (to the resolver as a query result, say) survives even if the branch is abandoned in some technical sense. anthill's resolver doesn't typically pass values across branch boundaries — `Branch` is for nondeterministic search, not for value-returning operations. If a future construct lets a value flow out of a branch alt, the design assumes the COMMIT path is taken (not abandon), so the `register_undo` for that allocation never fires. If a runtime construct violates this invariant — value escape from an abandoned branch — that's a separate soundness gap to flag at the construct's introduction, not at the cell_arena layer.

### Tree-shaped exploration; stack-shaped log

Branches form a **tree**: each choice point has multiple alts; the resolver explores depth-first, abandoning failed alts and backtracking up. The undo *log* however is a **stack** — it tracks the **current DFS path** through the tree.

```
        root
        /|\
       A B C       -- choice with 3 alts
      /|
     a b           -- A's alts
```

DFS traversal + undo-log states:

| Step | Action | Markers on stack | What's reverted at this step |
|---|---|---|---|
| 1 | enter A | `[mark_A]` | — (mutations during A's body get logged above mark_A) |
| 2 | enter a | `[mark_A, mark_a]` | — |
| 3 | a's body fails | `[mark_A, mark_a]` → replay above mark_a, pop | a's mutations only |
| 4 | enter b | `[mark_A, mark_b]` | — |
| 5 | b's body fails | `[mark_A, mark_b]` → replay above mark_b, pop | b's mutations only |
| 6 | A exhausted (a + b both failed) | `[mark_A]` → replay above mark_A, pop | A's body mutations + any survivors |
| 7 | enter B | `[mark_B]` | starts fresh from pre-Branch state |
| … | etc. | | |

Each `register_undo` attaches to the topmost marker. Pop-and-replay restores the runtime to the state at that marker's entry. Multiple sibling alts of the same parent see the parent's pre-mutation state (because by the time the next sibling is entered, the previous sibling's mutations have been replayed).

### Solution-yield semantics

A subtlety: when an alt's body **succeeds** and yields a solution, what happens to the mutations along that path? Two stances, depending on what kind of "Branch" the resolver is implementing:

- **Pure search** (Prolog `assert`/`assume` style — proposal 027 §"Sticky vs transactional"): mutations are **per-search-path**. Yielding a solution doesn't commit; mutations stay only for the duration of that solution being inspected, then unwind on backtrack-to-find-more-solutions.
- **Speculative-then-keep** (rare; not the design's target): the first successful path's mutations are committed.

The cell_arena's `register_undo` is agnostic — it logs mutations and replays them when the resolver decides to abandon. The resolver's policy on "when does abandon happen" determines the semantics. For v1 (matching proposal 037 §"Cell[V]" — branch-local snapshot), the pure-search stance is correct: mutations made under a Branch never escape that Branch's scope.

### Branch commit

If the entire Branch construct (the outermost `branch(...)` invocation) terminates **normally** (without backtracking past it), the markers below the Branch's outer boundary become non-replayable — the state at that point is the new committed state. The undo-log entries for those depths are dropped (their closure `Drop` impls handle any owned cell-handles).

In effect, "commit" for the cell_arena is `pop without replay`. Nothing special; the undo callbacks are simply forgotten. Closures' `Drop` releases any captured handles cleanly.

### What this does NOT do

- **Snapshot the entire arena up-front.** Naive copy-on-entry is O(arena size) per branch entry; pay-per-mutation is O(mutations). For typical anthill code the arena is small but the branch nesting can be deep — pay-per-mutation wins.
- **Cross-arena coordination.** If a Cell mutation triggers a related mutation in another arena (Map, Substitution, etc.), each arena registers its own undo. The runtime's undo stack interleaves them in chronological order. Replay is also chronological-reverse.

### v1 status

- The cell_arena ships **with** `register_undo` integration from day one. Without it, the arena is unsound under any future Branch use; better to wire it up correctly while the implementation is fresh.
- Branch itself is only partially wired today (per 037 Open Decision 3). Until the runtime grows full Branch support, `register_undo` is a no-op (the runtime never abandons; the bundle is one-shot CLI). The cell_arena's `register_undo` calls happen and silently accumulate, then go away with the runtime at process exit. No behavior change visible to current programs; full correctness when Branch lights up.

## Migration from v0.1

Current state (commits `fd122fb`, `21d9938`):

- `Cell.new(v)` returns `Value::Entity { functor: "Cell", named: [] }`. Functor-keyed; aliases.
- `Cell.get` / `Cell.set` route through the existing single Modify handler.
- Functor-only identity; recursive-allocation broken.

Target state (this doc):

- `Cell.new(v)` returns `Value::Cell(handle)` — fresh per call.
- `Cell.get` / `Cell.set` builtins dispatch on `Value::Cell` and access the arena directly.
- Refcount-driven lifecycle, recursion-safe.

Migration steps:

1. **Add `Value::Cell(CellHandle)` variant** — `value.rs`. Ripple through pattern-match exhaustiveness, printers, arena diagnostics.
2. **Add `cell_arena.rs`** — slot pool, refcount on clone/drop, alloc/with_value/set, mirrors map_arena.rs.
3. **Add `cells: CellArenaRef` field on `Interpreter`** (eval/mod.rs).
4. **Rewrite `cell_new`/`cell_get`/`cell_set` builtins** to allocate from / dispatch through the arena instead of the Modify handler.
5. **Cycle detection** — port `detect_cycle` from effects.rs to operate on `Value::Cell` references.
6. **Tests** — recursion test (deep allocation, no aliasing); refcount test (slot reclaimed when handle dropped); cycle-prevention test.
7. **Diagnostics** — TermPrinter for Value::Cell (handle id, current value rendered).
8. **Update wi205_cell_test.rs** — same surface tests still pass under the new representation.

The Modify handler stays in place for non-Cell Modify users (Modify.get/set on plain entities; existing tests in `eval_m5_modify_test.rs`). Cell is a new dispatch path alongside, not a replacement of the Modify handler.

## Failure modes — what crashes vs what errors

A summary of how user-side mistakes manifest:

| What the developer does | Result |
|---|---|
| Tries to construct a cycle (`Cell.set(b, a)` after `Cell.set(a, b)`) | `EvalError::CyclicReference` returned to caller — controlled error, surfaceable as `Error[CyclicReference]` at anthill level. No crash. |
| Constructs a cycle through any *opaque* sort — Closure, Stream, or any user sort whose contents are accessed only via operations (see open question 5) | Slow leak. Slot stays alive; eventually OOM if the program loops creating such cycles. Not a crash at the operation level. Not Stream-specific — fundamental limit of structural cycle detection. |
| Writes infinite recursion (no Cell-specific concern) | `ActivationStack` grows in heap; no host-stack overflow. Eventually OOM → allocator panic → process abort. Same as any non-terminating program. |
| Constructs a 10 000-deep nested Tuple/Entity tree and Cell.sets it | Iterative `walk_cells` + iterative `detect_cycle` handle it — O(1) Rust stack. Bounded only by heap. |
| Allocates 10 000 Cells, drops the references | Each handle's `Drop` decrements the slot's refcount; 10 000 slots returned to free_list. No crash, no monotonic growth. |

The boundary between "controlled error" and "process abort" is set by:
- Stack-bounded operations (walk_cells, detect_cycle): never abort; iterative throughout.
- Heap-bounded operations (everything Vec/HashMap-backed): abort only on actual OOM, same as any Rust program.
- Cycle prevention: the explicit programmable error (`CyclicReference`) — the only "developer creates a loop" path that actually fires.

## Open questions

1. **Should the cycle-prevention check be opt-out?** The current Modify handler enforces it unconditionally with a depth bound. Some user code may legitimately want cyclic structure (e.g. doubly-linked nodes). v1 keeps strict; revisit if a real consumer surfaces the need.

2. **Interaction with `with_resource`/lexical scoping** (proposal 027 future direction). When that lands, cells allocated inside a `with_resource(...) { ... }` block die at scope exit regardless of refcount — this is a new code path on the arena (a "scope-bound free" mechanism). Out of scope for v1.

3. **Print form.** `Value::Cell(handle)` has no natural structural rendering — the arena holds the value, but printing through the handle would force a borrow on every print. Likely render as `Cell#<id>=<value>` (the slot index plus a snapshot of the held value at print time). Diagnostic-only; not part of the round-trip.

4. **Concurrency.** The arena uses `Rc<RefCell<...>>`, single-threaded. Same constraint as the rest of the evaluator. Multi-threaded anthill code is a separate (much later) story.

5. **Opaque-sort cycle gaps.** Detection only walks structurally-reachable values. Cycles through *operationally-accessible* references — anything reached by calling an operation rather than by descending into a value — are not caught. The canonical cases are Closures and Streams, but this generalizes: any user-defined sort whose contents are accessed only via its operations has the same property. Same constraint as Rust's `Rc<T>` cycle handling. If a real consumer surfaces a need, the answers are explicit `Weak` references (future addition) or tracing GC (`gc-arena`). v1 documents the gap and moves on; the target use cases (state cells, counters, registries) don't hit it.

6. **Type-driven walk skip** as a perf optimization: when the typer can prove a cell's value type contains no Cell, skip the runtime walk. Requires computing a "may-contain-Cell" flag per anthill type (transitive closure over field/element types). v1 does not include this; file as a perf follow-up if measurements warrant.

## Why this design and not alternatives

**Why not extend the existing Modify handler with a uid-keyed sub-map?** The single shared HashMap mixes resources of different types. Each resource type wants its own state representation (per proposal 037 §3). Cell-specific arena is the cleanest realization; it also matches the existing pattern for Map / Substitution / Stream — same shape, three precedents to copy.

**Why not use Rust's `Rc<RefCell<Value>>` directly inside `Value::Cell`?** That would make every Value::Cell its own little piece of shared state, no central arena. Three downsides: (a) no slot reuse across arena lifetimes — each cell's allocation/free is a separate heap op; (b) no central place to apply the cycle detector (each cell would need its own); (c) breaks consistency with the other arenas (Map/Substitution/Stream all use the slot-pool pattern). The arena pattern wins.

**Why not put Cell inside the existing map_arena / subst_arena?** They're typed for their domains (Map values, substitutions). A separate cell_arena keeps the typing tight; the structural similarity is a copy template, not a shared instance.

## Acceptance

When the cell_arena WI lands:

1. `Value::Cell(CellHandle)` exists; pattern-matches add a Cell arm.
2. `cell_arena.rs` provides `CellArena`, `CellArenaRef`, `CellHandle` mirroring map_arena.
3. `Interpreter::cells` field; arena lifecycle managed.
4. Cell.new/get/set builtins use arena, drop the Modify-handler delegation.
5. Recursion test: 1000 deep `Cell.new` calls each see their own value at unwind.
6. Refcount test: drop the only handle, verify slot reclaimed (free list grew).
7. Cycle-prevention test: `Cell.set(c, Value::Cell(c))` returns `EvalError::CyclicReference`.
8. All existing wi205_cell_test.rs tests still pass.
9. `Print` of a `Value::Cell` doesn't panic.

The Cell sort's anthill-side declaration in stdlib stays unchanged — the migration is purely under the dispatch builtin layer.
