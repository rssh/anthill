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
- **Cycles are inexpressible.** The typer's `may_contain_cell`-style rule (see §"Cycle handling — type-level prevention") rejects payload types that could close a loop, so the runtime never sees a cycle and `Cell.set` is unconditional O(1). The earlier Modify handler's runtime walk goes away.
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
1. Match `c` as `Value::Cell(h)` → set the slot's value to `new`. No cycle check at this layer — the typer's static rule (§"Cycle handling") ensures `new`'s type can't reach back to `c`'s cell type, so a cycle is unconstructible.
2. Return `Value::Unit`.

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

#### The rule — `acyclic_cell` as a discharged predicate

The constraint is **not** a hardcoded typer rule. It's an open predicate `acyclic_cell(T)` on the payload type, with `Cell.new(v: V)` (and `Cell[V]` annotations more generally) requiring it. The kernel discharges `acyclic_cell(V)` at every site, by:

1. **Fact lookup.** If any fact `acyclic_cell[T = V]` holds (via the standard SLD resolution), accept.
2. **Default static walk.** Else, run the algorithm below. If it accepts, accept.
3. **Reject** if neither holds.

This factors the design cleanly:
- Most code never thinks about it — `Cell[Int64]`, `Cell[wis(...)]`, `Cell[List[Int64]]` clear the default walk and "just work."
- Domain-specific sorts that maintain acyclicity through some other mechanism (an age-ordered runtime discipline, a DLL whose public API preserves the invariant, a region-scoped construction protocol) can declare their guarantee with a fact: `fact acyclic_cell[T = dll[E]]`. These types pass the check without going through the static walk.
- Future proof-system integration plugs in as another way to discharge the fact (e.g., a proved instance via SMT or kernel proofs) — same predicate, new discharge.

The default static walk is described next; it's what fires when no explicit `acyclic_cell` fact covers V.

#### Default discharge — the static walk

A runtime cycle through `Cell` requires a *type-graph cycle*: payload type T must transitively reach back to `Cell[T]` itself, or to some other `Cell[U]` whose payload reaches back to `Cell[T]`, etc. Plain nesting like `Cell[Cell[Int64]]` or `Cell[List[Cell[Int64]]]` cannot form a cycle — the inner `Cell[Int64]` holds Int64, and Int64 has no path back to any outer Cell. The default walk allows these and only rejects when the descent through the type graph closes a loop through the same Cell type already seen in the chain.

The check at a `Cell[T]` site is a depth-first walk over T's structure carrying a set of *Cell types currently in the descent chain* (call it `topCells`). When the walk hits another `Cell[U]`: if `Cell[U] ∈ topCells`, that's a cycle — reject. Otherwise recurse into U with `Cell[U]` added to `topCells`. Non-Cell type structure (entities, lists, maps, tuples, abstract-sort unfoldings) recurses without changing `topCells`; a separate `visiting` set handles non-cell recursive sorts so the walk terminates.

##### Algorithm

```
-- check at every site where a Cell[T] type is constructed (Cell.new(v),
-- annotations, fact heads, ...). Decision:
--   ACCEPT  → the program may construct values of this Cell type
--   REJECT  → typer error: cycle possible through this Cell

is_cell_well_typed(Cell[T]):
  return descend(T,
                 topCells = { Cell[T] },         -- Cell types in the current chain
                 visiting = { Cell[T] })         -- termination guard for sort recursion

descend(τ, topCells, visiting):
  if τ ∈ visiting:
    return ACCEPT                                -- recursion through non-Cell sort: terminate
  let visiting' = visiting ∪ { τ }

  match τ:
    Cell[U]:
      if Cell[U] ∈ topCells:
        return REJECT                            -- cycle through this Cell type
      return descend(U,
                     topCells ∪ { Cell[U] },
                     visiting')

    Int64 | Bool | String | Float | Symbol | Term | …:
      return ACCEPT                              -- primitives have no payload

    Entity Foo(f1: T1, …, fn: Tn):
      return ⋀ descend(Ti, topCells, visiting')

    Tuple t1 … tn:
      return ⋀ descend(ti, topCells, visiting')

    List[T] | Option[T] | … (single-param containers):
      return descend(T, topCells, visiting')

    Map[K, V]:
      return descend(K, topCells, visiting')
           ∧ descend(V, topCells, visiting')

    AbstractSort F[X = A, Y = B, …]:
      -- unfold F's body with type-args substituted, descend into the
      -- resulting fully-applied form. visiting' guards termination on
      -- sorts that recurse through their own fields without going
      -- through Cell.
      return descend(unfold(F, [X→A, Y→B, …]),
                     topCells, visiting')

    Closure | Stream | <user-defined opaque sort>:
      return REJECT                              -- conservative: opaque captures
                                                 -- aren't introspectable. A future
                                                 -- "no-Cell-captures" annotation
                                                 -- could relax this per-sort.

    -- Type variables (?T): two stances —
    --   (a) cautious: REJECT (treat as if T could bind to a top Cell)
    --   (b) deferred: ACCEPT here; re-run the check at the call site
    --       where ?T is bound to a concrete type.
    -- (b) matches anthill's existing call-site checking for parametric
    -- effects/types and is the intended stance.
```

##### Worked examples

| Type expression | Walk | Decision |
|---|---|---|
| `Cell[Int64]` | descend(Int64, {Cell[Int64]}) → primitive | ACCEPT |
| `Cell[Cell[Int64]]` | descend(Cell[Int64], {Cell[Cell[Int64]]}) → Cell[Int64] ∉ topCells → descend(Int64, {Cell[Cell[Int64]], Cell[Int64]}) → primitive | ACCEPT |
| `Cell[List[Cell[Int64]]]` | descend(List[Cell[Int64]], {Cell[List[Cell[Int64]]]}) → descend(Cell[Int64], …) → Cell[Int64] ∉ topCells → descend(Int64, …) | ACCEPT |
| `Cell[wis(backend: IFS, id_counter: Int64)]` | entity with non-cell fields | ACCEPT (WI-203's case) |
| `Cell[A]` where `sort A { entity wrap(value: Cell[A]) }` | descend(A, {Cell[A]}) → unfold wrap(value: Cell[A]) → descend(Cell[A], {Cell[A]}) → Cell[A] ∈ topCells | **REJECT** — cycle |
| `Cell[A]` where A = `sort A { entity x(t: Int64, more: List[A]) }` | descend(A, …) → unfold → descend(List[A]) → descend(A) → A ∈ visiting → terminate | ACCEPT — no Cell on the recursion path |
| `Cell[A]` where `sort A { entity wrap(b: B) }` and `sort B { entity wrap(a: Cell[A]) }` | descend(A) → unfold → descend(B) → unfold → descend(Cell[A]) → Cell[A] ∈ topCells | **REJECT** — cycle through B |
| `Cell[Closure]` | Closure variant → conservative reject | REJECT (until per-sort opt-in lands) |

##### Where the check fires

The kernel attaches an implicit `acyclic_cell(V)` discharge obligation to `Cell.new` and to any `Cell[V]` annotation site. Whether this surfaces in the language as an explicit `require acyclic_cell(V)` clause on the operation, as a sort-level constraint on `Cell` itself, or as a hidden kernel check is a surface-syntax decision that can land separately — the architecture and obligation set are the same either way. Specifically:

- `Cell.new(v)`: V is inferred from v's type. Discharge `acyclic_cell(V)` — fact lookup first, default walk as fallback.
- `Cell[T]` annotations (let-bindings, op param/return types, fact heads, generic instantiations): same discharge on the annotated form.
- `MySort[T = Cell[U]]`: discharge `acyclic_cell(U)` before considering MySort's instantiation.

##### Sketch — extending coverage via facts

```anthill
-- Default: kernel walks the type graph (the algorithm above). No fact
-- needed for ordinary cases like Cell[Int64], Cell[wis(...)],
-- Cell[List[Int64]], Cell[Cell[Int64]] — they clear the walk on their own.

-- A domain sort declares its invariant with a fact:
sort dll
  sort E = ?
  entity Node(prev: Cell[dll[E = E]], next: Cell[dll[E = E]], data: E)
  -- … operations push_front, push_back, delete, … that preserve
  -- acyclicity by construction in their bodies.
end

-- The author asserts the guarantee:
fact acyclic_cell[T = dll[E = ?]]
-- (or per-instantiation, depending on how strong the invariant is)

-- Now `Cell[dll[E = Int64]]` is well-typed via the fact, even though the
-- default walk would reject it (dll's type graph closes a Cell-loop
-- through Node.prev / Node.next).
```

The fact's discharge story (why it holds) lives outside the kernel — it might be a paper proof, an SMT discharge under proposal 030, a runtime age-ordered discipline, or just author trust. The kernel only checks the fact exists at the site; it doesn't verify *why* the author believes it.

##### Caching

Cache the decision keyed by `(Cell[T], topCells)` — same Cell type with same incoming chain decides identically. For most call sites `topCells` is a singleton, so the cache key collapses to the type expression itself; deeper sites add the chain.

##### Implementation hook

Same place the earlier first-cut sketch was going to land:
- After `scan_definitions` in `rustland/anthill-core/src/kb/`, a new pass walks each entity/sort declaration and pre-computes any `topCells`-free decisions.
- A predicate `kb.cell_well_typed(ty: TermId, top_cells: &HashSet<TermId>) -> bool` is the runtime entry point; the typer's `Cell.new` arm calls it with `top_cells` seeded from any enclosing `Cell[U]` annotations.

#### Discharge by data-flow on operation bodies (extension; future direction)

The static walk above rejects sorts whose type graph closes a Cell-loop (e.g., a doubly-linked list `dll(prev: Cell[dll], next: Cell[dll], data: E)` — both fields close a Cell-cycle through `dll` itself). Many such sorts are *operationally* acyclic: the public API only ever produces values whose runtime cell graph is acyclic, even though the type graph isn't. They want a third discharge mechanism — beyond fact-lookup and the static walk — that **proves the operation set preserves acyclicity**.

The proof obligation lifts to a **local syntactic check** on operation bodies.

##### The proof obligation per operation

Given a sort `V` with the precondition "every input `v: V` is acyclic" and the postcondition "every produced `v: V` is acyclic," each operation must show that its body, when executed on acyclic inputs, produces an acyclic output. The inputs being acyclic is the inductive hypothesis; the output being acyclic is what we have to show. (Empty-list / construct-from-primitives base cases are vacuous.)

##### The local rule per `Cell.set`

The body of an operation is a sequence of `Cell.new`, `Cell.get`, `Cell.set`, and ordinary expressions. `Cell.new` is unconditional (a fresh slot can't be in any cycle). `Cell.get` is observation-only. The interesting case is `Cell.set(c, v)`.

For each pointer field `f` in `v` (a field whose static type is a `Cell[…]` or `Option[Cell[…]]` etc.), classify `v.f` into one of three categories:

| Category | Definition | Why no cycle is introduced |
|---|---|---|
| **fresh** | `v.f` was just allocated (or is `none`) by a `Cell.new` in this op, and has not been linked into the prior heap | A fresh cell has no incoming references, so no path can pass *through* it back to `c`. |
| **unchanged** | `v.f = c.prior.f` (the same value the slot already had on this field) | No new edge — the f-graph is unchanged for this slot. |
| **downstream** | `v.f` is reachable from `c` by following `f`-pointers in the prior heap (i.e., `v.f` was already "below" `c` in the f-graph) | Re-pointing `c.f` to something reachable from `c.f` only shortens chains — never closes them. |

A `Cell.set(c, v)` discharges the obligation if **every pointer field of v** falls into one of these categories. An operation discharges acyclicity-preservation if every `Cell.set` in its body discharges, and every `Cell.new` is unconstrained.

Per-field independence matters: the f-graph and g-graph are separate, and writing both fields in one `set` only needs each to satisfy the rule. (push_front below illustrates: it writes a `prev` whose target is fresh, and a `next` whose target is unchanged — both clear, and neither field's graph cycles.)

##### Worked example — DLL push_front

```anthill
sort dll
  sort E = ?
  entity Node(
    prev: Option[Cell[dll[E = E]]],
    next: Option[Cell[dll[E = E]]],
    data: E,
  )
end

operation push_front(head: Option[Cell[dll[E]]], v: E) -> Option[Cell[dll[E]]] =
  let new_cell = Cell.new(Node(prev: none, next: head, data: v))   -- ❶
  let _ = match head with                                          -- ❷
          | some(head_cell) ->
              let h = Cell.get(head_cell)
              Cell.set(head_cell, Node(
                prev: some(new_cell),
                next: h.next,
                data: h.data))
          | none -> ()
        end
  some(new_cell)
end
```

Discharging:

- ❶ `Cell.new(...)` — unconditional. `new_cell` is **fresh**. The `next: head` *inside* the freshly-allocated value is fine because `Cell.new` doesn't impose any constraint on the cell's contents (the constraint is only on incoming references to the new cell, of which there are none).

- ❷ `Cell.set(head_cell, Node(prev: some(new_cell), next: h.next, data: h.data))` — head_cell is *not* fresh (it's a parameter). Check each pointer field:

  - **prev**: `some(new_cell)`. `new_cell` is **fresh** (just allocated in step ❶, hasn't been written into any other cell yet). ✓
  - **next**: `h.next` where `h = Cell.get(head_cell)`. `h.next` is `head_cell.prior.next` — **unchanged** from the prior value. ✓

  All fields cleared; the `set` discharges.

Acyclicity is preserved.

##### Worked example — DLL delete (subset/downstream)

```anthill
operation delete(node: Cell[dll[E]]) -> Unit =
  let n = Cell.get(node)
  let _ = match n.prev, n.next with
          | some(prev), some(next) ->
              -- splice node out:
              let p = Cell.get(prev)
              let nx = Cell.get(next)
              let _ = Cell.set(prev, Node(prev: p.prev, next: some(next), data: p.data))
              Cell.set(next, Node(prev: some(prev), next: nx.next, data: nx.data))
          | …handle head/tail…
        end
  ()
end
```

For `Cell.set(prev, Node(prev: p.prev, next: some(next), data: p.data))`:
- **prev**: `p.prev` = `prev.prior.prev` — **unchanged**. ✓
- **next**: `some(next)`. Is `next` reachable from `prev` via `next`-pointers in the prior heap? Yes: `prev.next` was `node`, `node.next` was `next`. So `next` is **downstream** of `prev` via the next-graph. ✓

For `Cell.set(next, Node(prev: some(prev), next: nx.next, data: nx.data))`:
- **prev**: `some(prev)`. `prev` is downstream of `next` via the prev-graph in the prior heap (`next.prev` was `node`, `node.prev` was `prev`). ✓
- **next**: `nx.next` — **unchanged**. ✓

Discharges.

##### Worked example — a cycle attempt is rejected

```anthill
operation cycle_back(head: Cell[dll[E]]) -> Unit =
  let last = walk_to_last(head)                  -- last: Cell[dll[E]], not fresh
  let l = Cell.get(last)
  Cell.set(last, Node(prev: l.prev, next: some(head), data: l.data))
end
```

For `Cell.set(last, Node(prev: l.prev, next: some(head), data: l.data))`:
- **prev**: unchanged. ✓
- **next**: `some(head)`. Is `head` downstream of `last` via the next-graph? In an acyclic next-graph terminating at `last`, *no* — `head` is upstream of `last`, not downstream. Not unchanged either (was `none` for the tail). Not fresh. **Reject.**

The check refuses the operation at typer time, even though no runtime walk is performed.

##### What the rule cannot handle

Operations that **swap edges** (re-parent / rotate) — common in self-balancing trees, graph rewriting — do neither fresh, unchanged, nor downstream:

```anthill
-- AVL rotate_left: redirect node's right pointer to a sibling that is
-- not downstream of node (it's a sibling subtree), then make the
-- sibling's left pointer point to node (definitely upstream).
```

Such ops need stronger reasoning: either the runtime age-ordered discipline (option A in the brainstorm), or a proper proof discharge through proposal 030's proof cache, or a domain-specific invariant ("this is a known-acyclic transformation" — paper proof). The data-flow check cleanly identifies which operations need richer discharge.

##### Where this lives

- **Predicate definition**: an anthill sort `acyclic_cell` whose logical content is "no cell in this V-rooted graph reaches itself via any pointer field." First-order definable using a `cell_reaches_via_f` relation per pointer field.
- **Discharge mechanism — fact lookup**: `fact acyclic_cell[T = V] :- ops_of(V) all preserve acyclicity` — the kernel's per-operation data-flow checker emits this when V's operations all clear the rule.
- **Discharge mechanism — proof cache**: per proposal 030, paper proofs / SMT proofs that an operation preserves acyclicity discharge the same fact. Same predicate, different evidence.
- **Discharge mechanism — runtime age-ordered**: a separate sort `OrderedCell[V]` whose runtime invariant ("Cell.set(c, v) requires every cell reachable from v to have allocation-age strictly less than c's") implies acyclicity at construction. `fact acyclic_cell[T = OrderedCell[V]]` is unconditional once the runtime check is in place.

The data-flow rule above is one way to populate `acyclic_cell` facts automatically. It's the cheapest discharge (no proof system, no runtime cost) and covers a useful slice (linked structures, tree builds, deletion). Beyond that slice, the other mechanisms take over.

(Filed as a follow-up to WI-207; the runtime side of WI-205 and the static walk of WI-207 don't depend on this extension landing.)

#### Why no runtime cycle check

Once the typer rule is in place, `Cell.set(c, v)` is `arena.write(handle, v)` — a single slot write, no walk, no detection. Cycles are inexpressible at the type level, so they cannot form at runtime. There is no `walk_cells`, no `detect_cycle`, no `WalkCells` trait — they would be enforcing an invariant the typer already enforced.

(Earlier drafts of this doc proposed a runtime arena walk on every `Cell.set`. That approach is superseded; the runtime walk machinery moves to the optional `GCCell` sibling sort below, where it's the mark phase of a tracing collector — a different consumer of the same metadata.)

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
2. **Add `cell_arena.rs`** — slot pool, refcount on clone/drop, alloc/with_value/write, mirrors map_arena.rs.
3. **Add `cells: CellArenaRef` field on `Interpreter`** (eval/mod.rs).
4. **Rewrite `cell_new`/`cell_get`/`cell_set` builtins** to allocate from / dispatch through the arena instead of the Modify handler.
5. **Typer rule** — `may_contain_cell` predicate populated as a load-time pass on the KB; check fires at every `Cell.new` call site and `Cell[T]` type annotation. (Replaces the runtime cycle walk from earlier drafts.)
6. **Tests** — recursion test (deep allocation, no aliasing); refcount test (slot reclaimed when handle dropped); typer-rejection tests for `Cell[Cell[Int64]]`, `Cell[List[Cell[X]]]`, etc.
7. **Diagnostics** — TermPrinter for Value::Cell (handle id, current value rendered).
8. **Update wi205_cell_test.rs** — same surface tests still pass under the new representation.

The Modify handler stays in place for non-Cell Modify users (Modify.get/set on plain entities; existing tests in `eval_m5_modify_test.rs`). Cell is a new dispatch path alongside, not a replacement of the Modify handler.

## Failure modes — what crashes vs what errors

A summary of how user-side mistakes manifest:

| What the developer does | Result |
|---|---|
| Tries to write a `Cell` value into another `Cell` (`Cell[Cell[Int64]]`, `Cell[List[Cell[T]]]`, `Cell[Closure]`, `Cell[Stream]`, …) | **Compile-time error** at the `Cell.new(v)` call or the `Cell[T]` annotation — the typer's `may_contain_cell` rule rejects it with a clear "Cell[T] requires T to be Cell-free" diagnostic. No runtime path. |
| Wants graph-shaped mutable state with internal cell references | Use the optional `GCCell[T]` sibling sort (when it lands; see "Design variant" below) — permissive on T, backed by tracing mark-sweep. |
| Writes infinite recursion (no Cell-specific concern) | `ActivationStack` grows in heap; no host-stack overflow. Eventually OOM → allocator panic → process abort. Same as any non-terminating program. |
| Builds and `Cell.set`s a 10 000-deep nested Tuple/Entity tree | `Cell.set` is O(1) — a single slot write. Tree depth is irrelevant; the value passes through by handle. |
| Allocates 10 000 Cells, drops the references | Each handle's `Drop` decrements the slot's refcount; 10 000 slots returned to free_list. No crash, no monotonic growth. |

The boundary between "controlled error" and "process abort" is set by:
- Cycle prevention: **compile-time only** — there is no runtime `CyclicReference` for `Cell` because cycles are inexpressible. Errors fire at typecheck, not at write time.
- Heap-bounded operations (everything Vec/HashMap-backed): abort only on actual OOM, same as any Rust program.
- The runtime `Cell.set` is unconditional and constant-time; no analysis runs on the value being written.

## Open questions

1. **Graph-shaped mutable state.** Some user code legitimately wants cyclic structure (doubly-linked nodes, observer chains). The strict typer rule rules these out for `Cell`; the answer is the optional `GCCell[T]` sibling sort (see "Design variant" below). v1 ships without `GCCell`; revisit when a real consumer surfaces the need.

2. **Interaction with `with_resource`/lexical scoping** (proposal 027 future direction). When that lands, cells allocated inside a `with_resource(...) { ... }` block die at scope exit regardless of refcount — this is a new code path on the arena (a "scope-bound free" mechanism). Out of scope for v1.

3. **Print form.** `Value::Cell(handle)` has no natural structural rendering — the arena holds the value, but printing through the handle would force a borrow on every print. Likely render as `Cell#<id>=<value>` (the slot index plus a snapshot of the held value at print time). Diagnostic-only; not part of the round-trip.

4. **Concurrency.** The arena uses `Rc<RefCell<...>>`, single-threaded. Same constraint as the rest of the evaluator. Multi-threaded anthill code is a separate (much later) story.

5. **`may_contain_cell` for future opaque sorts.** When user-defined opaque sorts arrive (proposal-driven), the typer rule must extend to reject cell-bearing type parameters in opaque-sort positions. The conservative default — opaque sorts treated as `may_contain_cell = true` — keeps v1 sound; refining it as opaque-sort declarations gain the means to advertise "I don't capture Cell" is a follow-up.

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

- **Explicit**: `GCCell.collect() -> Int64` operation, returns count of slots reclaimed. User triggers; deterministic.
- **Threshold-based**: when the gc_cell_arena's free_list is empty and would otherwise grow, run collection first. Implicit; bounded growth.
- **Time-based**: periodic from a host loop. Probably overkill for an interpreter; skip.

### Choosing between Cell and GCCell

The user picks at type-declaration time. Most state goes in `Cell`; if the typer rejects `Cell[T]` because T may contain Cell, the error message redirects to `GCCell` as the intended-graph-state alternative:

```
error: Cell[T] requires T to be Cell-free; T = `List[Cell[Int64]]` contains
       Cell at element type. Consider using GCCell[T] if you intend
       graph-shaped state, or refactor T to avoid nested Cells (e.g.
       Cell[List[Int64]] with the outer list reconstructed on update).
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

**Why not use Rust's `Rc<RefCell<Value>>` directly inside `Value::Cell`?** That would make every Value::Cell its own little piece of shared state, no central arena. Three downsides: (a) no slot reuse across arena lifetimes — each cell's allocation/free is a separate heap op; (b) no central registry for branch-snapshot accounting (every Cell would need its own undo wiring); (c) breaks consistency with the other arenas (Map/Substitution/Stream all use the slot-pool pattern). The arena pattern wins.

**Why not put Cell inside the existing map_arena / subst_arena?** They're typed for their domains (Map values, substitutions). A separate cell_arena keeps the typing tight; the structural similarity is a copy template, not a shared instance.

## Acceptance

When the cell_arena WI lands:

1. `Value::Cell(CellHandle)` exists; pattern-matches add a Cell arm.
2. `cell_arena.rs` provides `CellArena`, `CellArenaRef`, `CellHandle` mirroring map_arena.
3. `Interpreter::cells` field; arena lifecycle managed.
4. Cell.new/get/set builtins use arena, drop the Modify-handler delegation.
5. Recursion test: 1000 deep `Cell.new` calls each see their own value at unwind.
6. Refcount test: drop the only handle, verify slot reclaimed (free list grew).
7. Typer rule fires: a program with `let c: Cell[Cell[Int64]] = …` (or equivalent at a `Cell.new` call site whose argument has cell-bearing type) is rejected at load time with a clear `Cell[T] requires T to be Cell-free` diagnostic.
8. All existing wi205_cell_test.rs tests still pass.
9. `Print` of a `Value::Cell` doesn't panic.

The Cell sort's anthill-side declaration in stdlib stays unchanged — the migration is purely under the dispatch builtin layer plus the new typer pass.
