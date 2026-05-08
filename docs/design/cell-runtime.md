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

#### The detector

```rust
fn detect_cycle(
    arena: &CellArena,
    target: SlotIdx,
    val: &Value,
    visited: &mut HashSet<SlotIdx>,
) -> Result<(), CycleError> {
    match val {
        Value::Cell(h) if h.slot == target => Err(CycleError),
        Value::Cell(h) if !visited.insert(h.slot) => Ok(()),  // already walked
        Value::Cell(h) => {
            let current = arena.read(h.slot);              // descend through slot
            detect_cycle(arena, target, &current, visited)
        }
        Value::Entity { pos, named, .. } | Value::Tuple { pos, named, .. } => {
            for v in pos.iter().chain(named.iter().map(|(_, v)| v)) {
                detect_cycle(arena, target, v, visited)?;
            }
            Ok(())
        }
        Value::Map(h)        => /* descend through map values */,
        Value::Stream(_)     => /* opaque; assume no Cell — see open question below */,
        Value::Closure(_)    => /* captured env may hold Cells; walk it */,
        Value::Term(tid)     => /* walk hash-consed term children */,
        _                    => Ok(()),
    }
}
```

#### Cost

Per `Cell.set(c, v)`: walks `v`'s value tree once, reads through each distinct Cell handle's slot once (visited-set bounded), recursively walks each slot's contents. Worst case: O(|value-tree| + Σ|cell-slot-contents reachable from v|).

For the dominant use cases — primitive-valued cells, cells holding small records — this is a few-node walk with no arena reads. For deep graph-shaped data, it's a real graph traversal.

There is no "fast-path bail." The naive bail "scan for any Value::Cell" is itself a recursive walk through the value tree (a Value::Cell may be buried under arbitrary Entity / Tuple / List nesting), so it does the same work as `detect_cycle` itself in the cell-free case. They tie.

The real optimization is **type-driven skip**: when the typer knows the cell's value type contains no Cell — e.g. `Cell[Int]`, `Cell[wis(IndexedFileStore, Int)]` where neither inner type carries Cell — skip the walk entirely. This requires the typer to compute and surface a "may-contain-Cell" flag per type. v1 of the cell_arena does NOT include this optimization; if perf measurements show the walk dominates, file a follow-up to add typer-driven skip.

For v1: every `Cell.set` runs `detect_cycle`. Programs that mutate primitive-valued cells in tight loops will see one pass over a small value per set — negligible. Programs that build complex graph structures pay the proportional cost.

#### Closures and Streams

Closures capturing cells *can* form cycles (cell holds a closure whose captured env contains the cell). The detector must descend into the captured environment when walking a `Value::Closure`. Doable but additional work.

Streams are opaque (the resolver pumps them lazily; we can't structurally walk a `SearchStream`). v1 treats Streams as cycle-opaque — a Stream holding a Cell that holds the Stream is undetectable at write time. Document the gap; the design assumes streams aren't a typical sink for Cells. If this becomes a real pattern, add a "stream cycle barrier" — disallow storing Streams in Cells or vice versa via typer rule.

The strict approach rules out genuinely cyclic Cell graphs at write time, which is fine for the design's target use cases (state cells, registries, counters, in-memory caches).

### Drop ordering

When a slot is reclaimed, its `value: Value` is dropped, which may transitively drop nested handles (e.g. a Cell holding a Map handle). Each handle's Drop decrements its respective arena. Standard Rust destructor flow; no special handling required.

## Branch interaction

Per proposal 037 §"Cell[V]" interpreter contract: **branch-local snapshot**. When execution enters a `Branch`:

1. The runtime walks resources whose contracts are branch-local-snapshot.
2. For each Cell handle in scope, the slot's current value is captured.
3. `register_undo` (proposal 027 §RuntimeAPI) installs a callback that restores the captured value if the branch is abandoned.

The arena layout supports this directly: snapshotting is a `Value::clone()` of the slot's contents, paired with the slot's refcount preserved. v1 of the arena does NOT implement this — `Branch` itself is partially wired (per 037 Open Decision 3) — but the design is forward-compat: snapshot/restore is a new method on the arena, called by Branch entry/exit machinery, with no schema change.

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

## Open questions

1. **Should the cycle-prevention check be opt-out?** The current Modify handler enforces it unconditionally with a depth bound. Some user code may legitimately want cyclic structure (e.g. doubly-linked nodes). v1 keeps strict; revisit if a real consumer surfaces the need.

2. **Interaction with `with_resource`/lexical scoping** (proposal 027 future direction). When that lands, cells allocated inside a `with_resource(...) { ... }` block die at scope exit regardless of refcount — this is a new code path on the arena (a "scope-bound free" mechanism). Out of scope for v1.

3. **Print form.** `Value::Cell(handle)` has no natural structural rendering — the arena holds the value, but printing through the handle would force a borrow on every print. Likely render as `Cell#<id>=<value>` (the slot index plus a snapshot of the held value at print time). Diagnostic-only; not part of the round-trip.

4. **Concurrency.** The arena uses `Rc<RefCell<...>>`, single-threaded. Same constraint as the rest of the evaluator. Multi-threaded anthill code is a separate (much later) story.

5. **Stream / Closure cycle gaps.** `detect_cycle` for v1 doesn't fully descend into Streams (opaque) or may not fully resolve closure-captured-cells (depending on how the closure runtime exposes its captured env). Document as "cycles via Streams or Closures are undetected at write time → leak risk for these specific patterns." If the patterns become real, either (a) extend the detector or (b) impose a typer rule prohibiting Streams/Closures inside Cells.

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
