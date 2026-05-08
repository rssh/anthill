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

### Cycle handling — type-level prevention

A Cell can hold a Value that transitively references the Cell itself — direct (`Cell.set(c, Value::Cell(c))`) or indirect (two cells holding each other through any number of levels of nesting). Refcounting alone does NOT reclaim cyclic structures: two cells that point to each other have refcount ≥ 1 forever.

The runtime answers — detect-and-error, or sweep-and-collect — are both *late*. A program that attempts to build a cycle either fails at runtime (detection) or silently leaks until collection (GC). Neither makes incorrect programs analyzable up front.

**v1 takes the type-level answer instead: cycles are inexpressible.**

#### The rule

`Cell[T]` is well-typed if and only if `T` is **Cell-free** — i.e., `T` does not transitively contain `Cell` anywhere in its structure (in any field of any entity, any element type of any container, any positional/named arg of any tuple).

Concretely, the typer computes a static `may_contain_cell : Type → Bool` predicate:

```
may_contain_cell(Cell[_])               = true
may_contain_cell(Int | Bool | String | Float | Symbol | Term | …)
                                        = false  (primitives)
may_contain_cell(Entity Foo(t1, …, tn)) = any may_contain_cell(ti)
may_contain_cell(Tuple t1 …)            = any may_contain_cell(ti)
may_contain_cell(List[T] | Option[T] | …) = may_contain_cell(T)
may_contain_cell(Map[K, V])             = may_contain_cell(K) ∨ may_contain_cell(V)
may_contain_cell(Closure | Stream | …)  = conservatively true (opaque)
```

The typer rule: **`Cell[T]` is rejected at typecheck time when `may_contain_cell(T)` is true.**

#### Consequences

- `Cell[Int]`, `Cell[String]`, `Cell[Bool]`: fine.
- `Cell[Record(name: String, count: Int)]`: fine — entity with primitive fields.
- `Cell[wis(backend: IndexedFileStore, id_counter: Int)]`: fine — neither field is cell-bearing. (This is exactly WI-203's WorkItemStore state.)
- `Cell[List[Int]]`, `Cell[Map[String, Int]]`: fine.
- `Cell[Cell[Int]]`: **rejected** — V is itself a Cell.
- `Cell[List[Cell[Int]]]`: **rejected** — list element type contains Cell.
- `Cell[Map[String, Cell[X]]]`: **rejected** — map value type contains Cell.
- `Cell[Closure]`, `Cell[Stream]`: **rejected** — opaque types are conservatively cell-bearing.

#### What this enables

- **No cycles can form.** Type-impossible. The runtime never has to detect or collect them.
- **Cell.set is O(1).** No walk, no detect_cycle. Just write the new value.
- **No `walk_cells` trait.** Not needed at runtime.
- **No `'gc` lifetime.** Not needed.
- **No GC pauses.** Not applicable.
- **Programs are statically analyzable.** A user's mistake is a typer error with a clear message ("Cell[T] requires T to be Cell-free; T = … contains Cell at …"); not a runtime exception, not a slow leak.

#### What this restricts

Cells cannot directly hold:
- Other cells (no `Cell[Cell[T]]`).
- Containers of cells (no `Cell[List[Cell]]`, no `Cell[Map[K, Cell[V]]]`).
- Closures or streams (opaque carriers, conservatively rejected).

Patterns that need "registry of cells" must use a different shape: a single `Cell[Map[String, V]]` with the map's values being non-cell V. Updates rebuild the map (immutable persistent data; cheap with hash-consed Maps). The single outer Cell carries the mutable state; map values are pure.

For more complex graph-shaped state with mutable internal references, the answer is "use a different sort with explicit operations" — design a domain-specific Modifiable sort whose operations express the graph operations safely. (This is exactly the proposal 037 §3 framework: per-resource handlers with their own representation.) Cell is the *simple* leaf-pointer; complex state needs its own sort.

#### Implementation plan changes

The runtime simplifies dramatically vs the earlier (detect_cycle-based) draft:

- ~~`WalkCells` trait~~ — not needed.
- ~~`detect_cycle` graph walk~~ — not needed.
- ~~Auto-derived walks for entities~~ — not needed.
- ~~Stream Native/External invariant by code review~~ — not needed (Stream excluded from Cell payload by typer).

What remains:

- `Value::Cell(CellHandle)` variant.
- `cell_arena.rs` (slot pool, refcount on clone/drop).
- Cell.new/get/set builtins.
- Refcount lifecycle as designed.
- Typer rule: `may_contain_cell` predicate and the `Cell[T]` rejection.
- Branch interaction via `register_undo` (unchanged).

The typer rule is the essential addition; the runtime arena work shrinks to ~150 LoC (vs ~400 LoC for arena + walks + detector). Net implementation is *less* code than the runtime-detection approach.

#### Typer enforcement: where the check happens

The static analysis fires at every site where a value enters a Cell — primarily `Cell.new(v)` calls, plus any code that ascribes a `Cell[T]` type explicitly (let-binding type annotations, operation signatures, fact heads).

**Predicate computation (`may_contain_cell`):**

Computed once after sort loading, cached per type symbol. Walk:

```
may_contain_cell(Cell)                      = true                      // base case
may_contain_cell(GCCell)                    = true                      // if GCCell variant lands
may_contain_cell(Int|Bool|String|Float|…)   = false                     // primitives
may_contain_cell(Symbol|Term|TermId|…)      = false                     // term-store types
may_contain_cell(Closure|Stream|…)          = true                      // conservatively (opaque)
may_contain_cell(Entity Foo(f1: T1, …))     = ⋁ may_contain_cell(Ti)    // any field
may_contain_cell(Tuple t1 …)                = ⋁ may_contain_cell(ti)
may_contain_cell(List[T] | Option[T])       = may_contain_cell(T)
may_contain_cell(Map[K, V])                 = may_contain_cell(K) ∨ may_contain_cell(V)
may_contain_cell(Pair[A, B])                = may_contain_cell(A) ∨ may_contain_cell(B)
```

For mutually-recursive entity definitions (A has field B, B has field A), iterate to fixed point:
1. Initialize all entity types to `false`.
2. For each entity, recompute based on its fields (using current values).
3. Repeat until no change.
4. Standard ascending-Kleene-iteration; converges in O(types × fields) total work.

**Hook point in the loader/typer pipeline:**

In `rustland/anthill-core/src/kb/`:
- After `scan_definitions` (entity declarations registered), but before `load` finishes.
- A new pass `compute_cell_freeness(kb: &mut KnowledgeBase)` walks all entity sorts, populates a `HashMap<Symbol, bool>` ("does T transitively contain Cell?"), iterates to fixed point.
- Cached on `KnowledgeBase` as `pub fn may_contain_cell(&self, ty: TermId) -> bool`.

**Check at `Cell.new(v)`:**

The typer's operation-call inference already infers the argument's type. The Cell sort's declared `new(v: V) -> Cell` operation has V as a type parameter; the typer has bound V to the inferred argument type at the call site. Insert:

```rust
// During typing of `Cell.new(v)`:
let v_type = infer_type(arg);
if kb.may_contain_cell(v_type) {
    return Err(TypeError::CellPayloadCycleRisk {
        site: call_site_span,
        v_type,
        offending_path: kb.cell_path_in_type(v_type),  // diagnostic
    });
}
```

The `cell_path_in_type` helper (used only in error messages) walks the type and reports where the Cell occurs — e.g. `"List[Cell[Int]] : list element type"`. Useful for clear errors, not for the predicate decision (which is just bool).

**Check at `Cell[T]` annotations:**

Same predicate, applied wherever a type expression resolves to `Cell[T]`:
- Let bindings: `let c: Cell[T] = …` — check at type-binding resolution.
- Operation params/returns: `operation foo(c: Cell[T]) -> …` — check at sort/operation declaration time.
- Fact heads with Cell-bearing parameters — check at fact loading.
- Generic instantiation: `MySort[T = Cell[U]]` — check that `Cell[U]` is well-typed (so U must be Cell-free).

The check is purely a guard on the type expression; it doesn't change any other typing rule.

**Diagnostics:**

Error message pattern:
```
error: Cell[T] requires T to be Cell-free
  --> example.anthill:14:13
   |
14 |     let c: Cell[List[Cell[Int]]] = …
   |             ^^^^^^^^^^^^^^^^^^^ T = `List[Cell[Int]]` contains Cell
   |                                  at element type of List
   |
   = note: cells nested inside cells could form cycles, which would
           leak. Consider:
   = help: refactor to Cell[List[Int]] (single outer cell, persistent
           list updated immutably);
   = help: use GCCell[List[Cell[Int]]] for graph-shaped state (if/when
           GCCell variant lands).
```

The error is the user-facing artifact. Three pieces: where the rejection fires, what type is offending, what the user can do about it.

**Tests:**

A focused test file for the typer rule:
- `Cell[Int]`, `Cell[String]`, `Cell[wis(IndexedFileStore, Int)]` — accepted.
- `Cell[Cell[Int]]`, `Cell[List[Cell[Int]]]`, `Cell[Map[String, Cell[X]]]` — rejected with a clear message.
- `Cell[Closure]`, `Cell[Stream]` — rejected (opaque carriers).
- Mutually recursive entities with no Cell anywhere — accepted.
- Mutually recursive entities where one path leads to Cell — `Cell[A]` rejected.

Drives the loader + typer integration end-to-end.

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

**Most walk implementations are auto-generated from type information.**

For entity sorts, anthill already has the field types in the KB (every entity has its `entity Foo(name: T1, name2: T2, …)` declaration). The walk is mechanical: visit each field's value, recursing via T's own walk. The loader generates a per-functor walk function at load time — no manual coding per sort. Same approach for tuples (positional + named field types known) and term arms (Term::Fn children are TermIds; walk recurses through `kb.with_term`).

Generated walks make the detector exhaustive *by construction*: every entity sort declared in the program (stdlib + user) automatically participates. New sorts don't need new walk impls — just new entity declarations.

Manual impls are reserved for the cases where structure isn't expressible in anthill types:
- `Value::Cell(h)` — visit the slot index (the orchestrator descends).
- `Value::Map(h)` — read arena, walk values.
- `Value::Closure(h)` — read closure arena, walk captured env.
- `Value::Stream(h)` — variant-by-variant: walkable variants (Pure, MPlus) recurse; opaque variants (Native, External, Resolver) covered by the runtime invariant on construction.
- Primitives — no descent.

That's six manual impls, total. Everything else — every entity sort the program declares — is derived.

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

#### Walkable values — the v1 invariant

The detector must catch every cycle a developer can construct. Letting some patterns slip past as a "leak risk" makes incorrect programs hard to analyze: a developer's bug becomes a slow OOM somewhere downstream rather than a clear write-time error. v1 closes the gap.

The invariant: **every Value variant is walkable for cells.** Each variant's `walk_cells` impl descends into the variant's contents through whatever runtime state holds them — even if that state is technically "opaque to anthill code." The runtime owns the data; it can introspect for the detector even when user code can't.

| Variant | How `walk_cells` reaches its cell-bearing children |
|---|---|
| `Value::Cell(h)` | Visits the slot; caller orchestrates descent into slot contents |
| `Value::Entity { pos, named, .. }` | Walks positional + named fields |
| `Value::Tuple { pos, named }` | Walks positional + named |
| `Value::Map(h)` | `arena.with_map(h, |body| …)` — walks each value |
| `Value::Term(tid)` | `kb.with_term(tid, …)` — walks Fn children, Ref/Const are leaves |
| `Value::Closure(h)` | `closure_arena.with_env(h, |env| …)` — walks each captured value |
| `Value::Stream(h)` | Walks variant-by-variant: `Pure(v)` walks v; `MPlus(l, r)` walks both children's handles; `Empty` no-op; `Resolver`/`Native`/`External` exposed via construction-time invariant (next paragraph) |

**Stream's `Native`/`External` / `Resolver` variants** hold Rust-side closures or trait objects whose internals aren't introspectable from anthill's runtime. The invariant we maintain instead: **builtins that construct these variants do not capture Value::Cell handles in the closures or trait objects.** This is enforceable by code review of the small number of builtins that allocate Streams (anthill-stl + eval/stream.rs), and provable: the captures are visible in the construction-site code. The invariant then says: a `Value::Stream` that the user can hold is guaranteed to not contain Cells (even invisibly), so `walk_cells` can return without recursing into the opaque tail.

**Rationale for this invariant over a runtime check:** the alternative would be making every native/external Stream constructor pass through a verifier that scans for Cells in its captured state. That's both expensive and brittle (Rust doesn't expose closure captures via reflection). Code-review enforcement of "no Cells in stream-state-closures" is cheaper, narrowly scoped, and verifiable.

**For user-defined entity sorts** (everything declared with `entity Foo(field: T, …)`): auto-generated walks. The loader scans field types when registering the sort, emits a walk function that descends into each field per its type's walk. Anthill code can declare arbitrary deeply-nested entity hierarchies and they all participate without per-sort coding.

**For future user-defined opaque sorts** (sorts with operations returning values, no structural reflection): the typer rule. When a user declares such a sort, the typer rejects type parameters that may contain Cell. E.g. `MyOpaque[Cell[Int]]` is rejected; `MyOpaque[Int]` is fine. The "may-contain-cell" analysis is a transitive closure over field/element types — the same data the auto-generated walks consume, used statically. (Filed as a parallel typer work item; v1 of cell_arena ships the runtime walks; the typer rule for opaque sorts lands separately.)

Net effect of the invariant: **no cycle a user can construct from anthill code escapes detection**. Programs are write-time correct or fail at write time with `EvalError::CyclicReference` — never silently leak.

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
| Constructs a cycle through a Closure | `EvalError::CyclicReference` — Closures expose their captured env via `closure_arena.with_env`; `walk_cells` descends into the env values; cycle caught at write time. |
| Constructs a cycle through a Stream | `EvalError::CyclicReference` for walkable variants (Pure, MPlus); for Native/External/Resolver variants, the runtime invariant "stream-state closures don't capture Cells" is enforced by code review of builtins. Either way, no silent leak. |
| Constructs a cycle through a future user-defined opaque sort | Typer rule rejects "MyOpaque[T]" when T may transitively contain Cell. v1 of cell_arena ships without this typer rule; in the meantime, Cells inside user-defined opaque sorts are caught at runtime by the construction-site builtin (or fail to compile if the typer rule lands first). |
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

5. **Walk completeness for future opaque sorts.** v1 covers all Value variants (Closure via captured-env exposure; walkable Stream variants; runtime-invariant for Native/External/Resolver streams). User-defined opaque sorts arrive later (proposal-driven); when they do, the typer needs a "may-contain-Cell" rule rejecting cell-bearing type parameters in opaque-sort positions. Until that typer rule lands, v1 enforces at construction time: any builtin that constructs an opaque-sort value with Cell-bearing payload errors. The principle: every program either runs cleanly or fails at write time with a clear error — no silent leaks.

6. **Type-driven walk skip** as a perf optimization: when the typer can prove a cell's value type contains no Cell, skip the runtime walk. Requires computing a "may-contain-Cell" flag per anthill type (transitive closure over field/element types). v1 does not include this; file as a perf follow-up if measurements warrant.

## Design variant: optional `GCCell` sort

Cell as designed is strict — `Cell[T]` requires T to be Cell-free, so cycles are inexpressible. This is right for the common case (state cells, configs, counters) but rejects programs that genuinely want graph-shaped mutable state (DAG nodes, observer chains, doubly-linked structures).

A natural extension: a sibling sort `GCCell[T]` with no typer restriction on T, backed by a tracing mark-sweep arena. Programs that need graph state opt in; programs that don't, don't pay GC cost.

### The split

```anthill
sort anthill.prelude.Cell      -- strict; T must be Cell-free
sort anthill.prelude.GCCell    -- permissive; any T, including GCCell-bearing
```

| | `Cell[T]` | `GCCell[T]` |
|---|---|---|
| Typer rule on T | `may_contain_cell(T)` rejected | None |
| Cycle handling | Impossible by construction | Tracing mark-sweep, periodic |
| Per-write cost | O(1) — refcount + write | O(1) — slot write |
| Reclamation | Synchronous on refcount → 0 | Pauses for collection |
| Determinism | Fully deterministic | GC pauses non-deterministic |
| Implementation cost | ~150 LoC | ~300 LoC (arena + mark-sweep + roots + walk_gccells trait) |

Two distinct Value variants, two arenas:
- `Value::Cell(CellHandle)` → cell_arena (refcount).
- `Value::GCCell(GCCellHandle)` → gc_cell_arena (mark-sweep).

The GC infrastructure stays *inside* the gc_cell_arena. The rest of the interpreter — Value, Frame, Substitution, builtins — doesn't see it. No `'gc` lifetime contamination. The collection pause is bounded to the gc_cell_arena's root-walk.

### Why hand-rolled mark-sweep, not `gc-arena`

Same reason the unified design rejected `gc-arena`: `Gc<'gc, ...>` slots inside the arena would require Value to derive `Collect`, propagating `'gc` back through Value and beyond. Manual mark-sweep keeps the GC strictly internal — slots hold plain `Value`s; the `walk_gccells` trait method walks reachable cells from a root set; the sweep pass frees unmarked slots. No lifetime invasion.

### Roots

The mark phase needs a root set: every `Value::GCCell` currently live in the executing program. Sources:
- The activation stack — every Frame's locals.
- The current eval pipeline's intermediate Values.
- Effect handler captured state.

Collection pauses eval, walks these, marks reachable from each, sweeps unmarked. Same general pattern as any mark-sweep collector for an interpreter.

### Walks reused across both sorts

The `walk_cells` / `walk_gccells` traits — auto-derived for entities, manual for arena variants — serve double duty:

- **Cell**: typer-time `may_contain_cell` predicate (the static analog of the walk; never runs at runtime).
- **GCCell**: runtime mark phase.

The trait machinery isn't wasted by the type-level approach for Cell. It lives in the runtime as the GC mark function for GCCell, and statically as the typer rule for Cell. Same metadata source (entity field types), two consumers.

### When does GC run?

- **Explicit**: `GCCell.collect() -> Int` operation, returns count of slots reclaimed. User triggers; deterministic.
- **Threshold-based**: when the gc_cell_arena's free_list is empty and would otherwise grow, run collection first. Implicit; bounded growth.
- **Time-based**: periodic from a host loop. Probably overkill for an interpreter; skip.

### Choosing between Cell and GCCell

The user picks at type-declaration time. Most state goes in `Cell`; if the typer rejects `Cell[T]` because T may contain Cell, the error message redirects to `GCCell` as the intended-graph-state alternative:

```
error: Cell[T] requires T to be Cell-free; T = `List[Cell[Int]]` contains
       Cell at element type. Consider using GCCell[T] if you intend
       graph-shaped state, or refactor T to avoid nested Cells (e.g.
       Cell[List[Int]] with the outer list reconstructed on update).
```

### Migration impact

Adding GCCell as a sibling sort doesn't affect existing code:
- Cell users keep working unchanged.
- GCCell is new opt-in.
- The Modify framework's typing-level rules (Modifiable[T = Cell], Modifiable[T = GCCell]) treat both.

### Status

This is a **design variant**, not currently committed-to. The strict-Cell design as written is sufficient for WI-203's WorkItemStore use case (Cell[wis(...)] is well-typed since wis fields are non-Cell). GCCell becomes load-bearing only if a real consumer surfaces graph-shaped mutable state.

If/when GCCell lands, the cell_arena and gc_cell_arena coexist as siblings; neither obviates the other. Both share the walk traits.

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
