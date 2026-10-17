# 037 implementation — the Modify framework at run time

## Status: Draft (2026-10-17). The last step of WI-20261017-T34HP. The proposal is
[`../proposals/037-anthill-state-model.md`](../proposals/037-anthill-state-model.md), revised and
reviewed on 2026-10-17; this document owns HOW. Nothing here is implemented. What the user has not
decided is marked PROPOSED and collected in §3.

## 0. The sequence

Every edge is technical.

| step | ticket | what | after |
|---|---|---|---|
| 1 | WI-200, re-scoped (PROPOSED, D1) | retire `ModifyRuntime`, Cell's `provides ModifyRuntime`, the generic `Modify` handler, and the fixtures only it served (§2.1) | — |
| 2 | to be filed (D6) | the installation map; `Cell.new` reads it; a cell handle carries the implementation it is bound to (§2.2, §2.3) | — |
| 3 | WI-078 (h), re-scoped (D3) | installing for the duration of a call, and wrapping (§2.4) | 2 |
| 4 | to be filed (D6) | the store rows: `External` on `flush`, `Modify[kb]` on `persist`, `retract` and `update`, and on their callers (§2.5) | — |
| 5 | step 4's, or its own (D6, D8) | a mount key compared by `Eq` (§2.6) | — |
| 6 | 072's, on T34HP (no ticket of its own, by the user's decision) | `FileStorage`; constructor contracts; the file backends' `ensures` (§2.7) | 050.1 stage 1 (WI-20261015-809JN) |
| 7 | WI-20261015-X57XR (050.1 stage 3) | Cell's memory clauses (§2.8) | 050.1 stage 1 |
| 8 | WI-070 | undo in every implementation, for `Branch` (§2.9) | 2 |
| — | WI-20260926-7D48J | a rule-body application that modifies shared state refused at load (§2.10) | its own sequence |

Step 1 first is not an edge but a saving: the generic handler has a `Cell` arm, and step 2 changes
the type that arm reads. 037 §5.4 and the last item of §6.2 are claims about rule bodies that hold
only once WI-20260926-7D48J's boundary rule is enforced; nothing in this sequence makes them true.

## 1. Today: four write paths

Read on `main` at `4f6569ac`.

### 1.1 `Cell.*` — the arena, through the handle

- `Cell.new`, `get` and `set` are the host functions `cell_new`, `cell_get` and `cell_set`
  (`eval/builtins.rs:7146–7180`), named by `provides Cell language rust`
  (`rustland/anthill-stl/anthill/effects.anthill`).
- `cell_new` allocates in the interpreter's own arena (`Interpreter::alloc_cell`,
  `eval/mod.rs:1938`). `cell_get` and `cell_set` go through the handle, which carries the arena that
  minted it (`CellHandle { raw, arena }`, `eval/cell_arena.rs:113`).
- So a cell is already bound to one store when it is made, and every call on it goes there. What is
  missing is a choice at `new`, a second implementation, and undo (§2.3, §2.9).
- One place mints a handle, `CellArenaRef::alloc` (`cell_arena.rs:90`), reached through
  `alloc_cell` from `cell_new` and from anthill-todo's host, which seeds the bundle's
  `Cell[V = WIS]` (`rustland/anthill-todo/src/main.rs:5347`).
- A cell is opaque to every structural reader: `TermView::head` answers `Opaque`
  (`kb/term_view.rs:2962`), so no structural comparison holds of it, not even with itself, and
  `alloc_from_value` refuses it, so it never becomes a term or a fact (`kb/execute.rs:455`).
  `CellHandle`'s own `PartialEq` compares the slot and the arena.

### 1.2 `ModifyRuntime.*` — one global handler

- `ModifyRuntime.get` and `set` (`stdlib/anthill/prelude/effects.anthill:124–130`) are mapped to
  `modify_runtime_get` / `modify_runtime_set`. Each is an `effect_dispatcher!` that takes the handler
  registered for `anthill.prelude.Modify` out of the registry
  (`Interpreter::dispatch_effect_operation`, `EffectRegistry::take_for_invoke`, `eval/effects.rs:545`)
  and runs it.
- The handler, `default_modify_handler` (`eval/effects.rs:254`), has two arms. On a `Value::Cell` it
  does what `Cell.get` / `set` do. On anything else it keeps one slot per constructor symbol, with a
  cycle walk on `set`. A constructor with fields has been refused at run time since 2026-10-16
  (`EvalError::ResourceWithFields`), because one slot per constructor made `box(id: 1)` and
  `box(id: 2)` one place.
- `Cell` reaches it through `provides ModifyRuntime[T = Self, V = V]` (`cell.anthill:39`).
- What uses it is the m5 fixtures and the tests of §2.1. No stdlib body, example or tool calls it.

### 1.3 The store — a mirror found by its printed value

- **The values** are entities of three sorts declared in `anthill.persistence.filesystem`:
  `FileStore(root, convention)`, `IndexedFileStore(root, convention)` and
  `ItemPerFileStore(root, status_field, id_field, ref_field)`. Their fields are strings, plus a plain
  enum (`FileConvention`).
- **The mount.** Only anthill-todo mounts a store. `build_declared_store`
  (`rustland/anthill-todo/src/main.rs:1083`) reads the project's one `ExtentBinding`, or uses a
  default `IndexedFileStore`. It builds the backend object (`IndexedFileStore::new`,
  `ItemPerFileStore::new`), and `register_declared_store` (`main.rs:1319`) registers it under the
  key of the declared value (`KnowledgeBase::register_mirror`, `kb/extent.rs:900`). `FileStore` is
  never mounted in production, and `anthill-cli` mounts nothing, so a store operation run there
  fails "no store registered for key".
- **The key** is printed text (`Interpreter::store_canonical_key`, `eval/mod.rs:628`). It prints an
  entity's functor by its local name and sorts named arguments by their local labels. Its doc says it
  agrees with `views_structurally_equal`, which compares functors and labels by symbol, but the text
  is coarser: two entities of two packages that share a local name and their fields are one key.
  Code relies on that. Tests build store values from bare interned names
  (`persistence_builtins_test.rs:31–35`), and anthill-todo interns the labels again when it rebuilds
  the value with an absolute root (`main.rs:4222–4251`).
- **The registry** maps that text to the backend (`ExtentRegistry.mirrors:
  HashMap<String, Box<dyn Store>>`, `kb/extent.rs:640`). A stored row's `FactRef` carries the text
  too (`:83–160`).
- **The calls.** The `persistence_*` host functions (`eval/builtins.rs:6892–7200`) compute the key
  and take the backend out of the registry for the call. A key that is not mounted fails loudly
  (`builtins.rs:7130`, `:7191`; `kb/extent.rs:1270`, `:1301`, `:1340`).
- **The writes.**
  - `persist` → `persist_mirrored` (`kb/extent.rs:1231`): the backend buffers the row, then the KB
    asserts the resident fact (`:1282`).
  - `retract` and `update` go through the same seam (`retract_persistent`, `update_persistent`).
  - `flush` writes the files. It is the only `persistence::Store` method that touches the
    filesystem in any of the three backends. Everything else on disk is host-only (fsck's repairs,
    anthill-todo's migrations).
- **The rows** are `{Modify[store], Error}` on all four writers.
- **The one anthill caller** is anthill-todo's `FileBasedWorkitemStore`
  (`rustland/anthill-todo/anthill/store.anthill`). `retrieve` and `monotonicity` have no anthill
  caller.
- *Found in passing, not 037's:* `IndexedFileStore::index_by_id` has no caller outside
  `wi202_retrieve_test.rs`, though its comment (`indexed_file_store.rs:125`) says
  `persistence_persist` calls it. So `retrieve`'s lookup by id answers nothing in production.

### 1.4 The KB — the interpreter, and its layers

- **The root** is `kb()`, answered by `kb_ambient` (`eval/builtins.rs:3932`) as a field-less entity
  that stands for the interpreter's own knowledge base.
- **A layer** is `KB.loaded(sources)`, answered by `kb_loaded` (`builtins.rs:3961`). It takes a
  scoped snapshot (`KnowledgeBase::snapshot_scoped`, `kb/layer.rs:87`), loads the sources into the
  live KB, and returns `Value::Kb(handle)` (`eval/layer_arena.rs`). Dropping the value discards the
  layer: `restore_scoped` (`kb/layer.rs:103`) puts the scoped fields back and tombstones the layer's
  rules. This is the one rollback the runtime has.
- **`KB.assert` and `KB.add_guard` have no implementation in the interpreter.** They are body-less,
  not `@[host_implemented]`, and no `operation_map` names them (`reflect.anthill:736–744`). Only the
  generated-Rust host bridge implements them (`KbBridge`, `rustland/anthill-stl/src/reflect/bridge.rs:1117–1144`,
  through `assert_checked`).
- **What does write the knowledge base at run time** is a layer's load and the store's resident
  facts (§1.3).
- **FOUND, by reading, not measured: a store write under a live layer.** A layer is applied in
  place, so a `persist` made while one is live asserts its resident fact among the layer's rules,
  and the layer's discard takes it away. The backend's buffered row stays, because a scoped
  snapshot holds the mount tables but not the backends, which cannot be cloned (`kb/layer.rs:71`).
  A later `flush` then writes a fact the KB no longer holds. A `retract` under a live layer is the
  mirror case: the layer's discard brings the rule back, and the buffered retract stays. 037 makes
  this visible, since both the layer and the store write are writes of `kb`. D7 asks what to do.

### 1.5 Around the four: the registry, the bridge, load-time evaluation

- **The registry.** Every interpreter is built with an empty `EffectRegistry` and fresh arenas
  (`Interpreter::with_config`, `eval/mod.rs:516–547`). `register_standard_effect_handlers`
  (`eval/effects.rs:931`) installs six handlers: three `Console`, `Modify`, `Error` and `Clock`.
  The runner (`rustland/anthill-stl/src/runner.rs:53`, for `anthill-cli` and anthill-todo) and a
  generated bundle (`rustland/anthill-rust-gen/src/bundle.rs:319`) call it. A handler is taken out
  of its slot while it runs (`take_for_invoke`, `effects.rs:545`), so it cannot reach another.
- **The bridge.** `run_in_bridge_interp` (`kb/resolve.rs:12137`) lends the KB to a new interpreter
  for each rule-body call. It has builtins, no effect handlers and fresh arenas. Its callers are
  rule-body operand reduction (`bridge_op_to_eval`), the semantic-equality dispatch (also from a
  running interpreter, through `semantic_equal`), `@[simp]` macro expansion at load, and a const in
  a query pattern. A cell handle it returns outlives it in σ and is read by later bridged calls
  through the handle (`resolve.rs:12126–12131`). A layer may not outlive the call
  (`ScopedKbOutlivesCall`, `eval/mod.rs:2054`), but nothing like that exists for a cell.
- **Evaluating a `const`.** At load, a host `const_map` value source runs in an interpreter over an
  empty KB (`host_const_literal`, `builtins.rs:674–703`), and a computed `const` is not evaluated:
  it is refused where a literal is needed (`ConstSource::Computed`, `kb/const_value.rs:161`). A
  computed `const` is forced when it is read: in the running interpreter on a stack of its own
  (`eval_node_isolated`, `eval/eval.rs:1124`), or through the bridge for a query pattern
  (`evaluated_const_literal`, `kb/const_value.rs:177`). Each of these interpreters has its arenas,
  so 037 §5.3's default is present in all of them.
- **No undo exists for a cell.** `write` returns the prior value and both callers drop it. Neither
  `register_undo` nor a snapshot hook exists, and `HandlerAction::Fail` and `Choice` are refused
  (`UnsupportedHandlerAction`, WI-389).

## 2. What each becomes

### 2.1 Retire `ModifyRuntime` and the generic handler (step 1)

037 §3.5 and §4.1. Measured on `main` at `4f6569ac`.

**What goes.**

| where | what |
|---|---|
| `stdlib/anthill/prelude/effects.anthill` | `sort ModifyRuntime` (124–130) and its doc (109–123); the header paragraphs on it (16–19), on "runtime-handler semantics" (41–48) and on ambient resources written through it (50–62) |
| `stdlib/anthill/prelude/cell.anthill` | `ModifyRuntime` in the import (7); `provides ModifyRuntime[T = Self, V = V]` and its comment (35–39) |
| `rustland/anthill-stl/anthill/effects.anthill` | the binding block `provides ModifyRuntime language rust` (46–52); the header's two mentions (2, 8) |
| `eval/builtins.rs` | the `HOST_FNS` rows `modify_runtime_get` / `modify_runtime_set` (353–354); the two `effect_dispatcher!` (6729–6740); "Console/Modify/Clock" in `error_raise`'s comment |
| `eval/effects.rs` | `default_modify_handler`, `resource_key`, `detect_cycle`, `detect_cycle_term` (228–481); its entry in `register_standard_effect_handlers` (945), whose doc then says five, not six (919–930); the `ViewHead` import, used only there (19); "a `Modify` arena for stateful cells" in the module doc (8) |
| `eval/error.rs` | `CyclicReference` (130), `ResourceWithFields` (131–137), `ResourceUnset` (140–143): the handler is their only producer. Their arms in `bridge_disposition` (467–469) and `Display` (656–666) go with them |
| `tests/common/mod.rs` | `register_modify_handler` (1310–1321) |

What stays: `Modify`, the marker, which the typer keys by name (`check_override_refinement`,
`check_modify_targets`, `check_written_row_bindings`, `unrekeyed_modify_argument`, `is_modify_effect`,
the target-slot lowering in `kb/load.rs`); `Modifiable`; the TR8CF check; masking; `region_sorts`.
The registry keeps its other five handlers (D2).

**The typer has no `ModifyRuntime` code.** Every mention there is a comment that uses it as an
example, and each gets another: `kb/typing/coherence.rs:1777`, `carrier.rs:2961` and `:3583`,
`apply.rs:393`, `signature.rs:3242`, `:3248`, `:3368`, `:3503`, `:3516`, and `kb/resolve.rs:11895`,
where `bridge_fault_message`'s comment lists a write through `ModifyRuntime` as a route to its
hidden-row report (D4 is the spec's twin of this comment).

**The tests,** by what each one is about.

- *About the generic handler itself: they go.*
  - `eval_test.rs`: the seven `m5_modify_*` tests at 2840, 2926, 2972, 2999, 3048, 3073 and 3102.
    They write and read nullary resources (`counter`, `a`, `b`), and check a get before any set, a
    resource with fields, a self-reference and a host round trip.
  - `wi205_cell_test.rs:215` and `:303`: the handler's `Cell` arm. `Cell`'s own tests at 67
    (`cell_new_returns_distinct_handles`) and 38 (`cell_set_overwrites_value`) already cover what
    they show.
  - `wi1025_occurrence_referent_test.rs:249` and `:326`: `detect_cycle`'s occurrence arms.
  - One row replaces them all: the m5 fixtures' shape, an operation declaring `Modify[counter]` that
    writes through `ModifyRuntime.set(counter(), n)`, is refused at load because the name resolves
    to nothing (037 §3.5). Restore the sort and the row loads.
- *Using it only as a fixture: they keep their subject with another fixture.*
  - `eval_test.rs:3134`, `:3164`, `:3201` are about the registry: a taken handler, a `Throw`
    action, a `Fail` action. They register a custom handler under `anthill.prelude.Modify`, and
    move to `anthill.prelude.Time.Clock`, which a real operation still dispatches to.
  - `wi205_cell_test.rs:354` is about the bridge's report that the callee's row does not declare
    the effect it asked for. `wi_9wvt7_clock_handler_test.rs:505` pins the same branch with `Clock`,
    so the `ModifyRuntime` half goes, and the `Cell.set` twin, which answers 9, stays as the control.
  - `wi_0rp29_call_binding_test.rs:613` and `:625` are about the field-path re-key of a dispatched
    override's effect. `ModifyRuntime.set` was the spec operation and `Cell.set` its override. They
    need a spec and an override of their own, as `wi347_override_refinement_test.rs:1660` already has.
  - `wi4gbqv_ambient_resource_test.rs:67`, `:93`, `:117`, `:142`, `:403`, `:435` are about typing a
    nullary constructor as a `Modify` target. These rows load, and `ModifyRuntime.set` was only the
    callee that carried `Modify[target]`. A fixture operation does instead,
    `operation touch(target: CounterState) -> Unit effects Modify[target]`, whose body writes
    nothing: a row is an upper bound. The typing subject is unchanged. Pool sorts depend on it
    (`file_storage` is such a place, 037 §3.2).
  - `wi_brt4y_host_implemented_test.rs:389–390`: two rows of `MIGRATED`, which becomes 44.
  - `scaland/core/src/test/scala/anthill/codegen/scala/BootstrapTest.scala:3484`: `ModifyRuntime.scala`
    leaves the emitted list, which becomes nine sorts.
- *Installing the handler without reaching it: they lose the call.* Their programs use `Cell.*` or
  `MutableStack`, so the handler never runs. The files are `wi205_cell_test.rs` (19, 38, 67, 116,
  146, 178), `wi_0rp29_call_binding_test.rs` (842, 881), `wi_jn09w_holder_gate_test.rs`,
  `wi_41yye_enclosing_place_type_test.rs`, `wi507_carrier_only_dispatch_test.rs`,
  `wi508_nullary_carrier_dispatch_test.rs`, `wi_s7yf5_self_receiver_row_test.rs`,
  `wi364_mutable_stack_test.rs` and `wi_2nmxa_denoted_provision_binding_test.rs`.

`tree-sitter-anthill/` has no reference, and `examples/` only prose
(`examples/guardians/docs/design/measured.md:1288`, a measurement record, left as written).

### 2.2 The installation map (step 2)

037 §5.2. A module `eval/installation.rs`:

```rust
/// The implementations in force: one entry per base sort that has one installed. A
/// missing entry is the sort's default, which is always available (037 §5.3).
#[derive(Clone, Default)]
pub struct Installations(Rc<[(Symbol, Implementation)]>);

#[derive(Clone)]
pub enum Implementation {
    Cell(Rc<dyn CellImplementation>),
}
```

- **Keyed by the base sort's canonical symbol** (`anthill.prelude.Cell`), never by an
  instantiation: one implementation serves every `V`.
- **Persistent.** `with(sort, implementation)` returns a new version and leaves the old one as it
  was. There are few base sorts, so a version is a small slice copied when an entry changes.
- **One field on `Interpreter`**, `installations`. The embedder sets it before a run, which is the
  whole-run default of 037 §5.2 item 1; a scope replaces it for its duration (§2.4).
- **Read only where a resource is made or mounted.** A call on an existing resource never reads it
  (037 §5.1). In step 2 its one reader is `cell_new`.
- **A variant per family of base sorts, not `Rc<dyn Any>`.** Each base sort has its own operations
  (037 §4.1), so each family's implementation is its own trait, and the enum makes "an
  implementation of something else installed for `Cell`" unrepresentable.
- **The store family gets no variant yet.** A store is bound when the embedder mounts it, and the
  embedder chooses the backend object then (§1.3). That is the whole-run choice of 037 §5.2 item 1,
  made in host code. A variant comes with the first mount that anthill code makes.
- **`KB` gets none either.** The root is bound to the interpreter and a layer to the layer arena
  (§1.4); an entry comes with a second implementation of `KB`.

### 2.3 `Cell` through the implementation it is bound to (step 2)

`Cell`'s three operations already reach one store per cell: `cell_get` and `cell_set` read and write
through the handle, and the handle carries the arena that minted it (`CellHandle { raw, arena }`,
`eval/cell_arena.rs:113`; WI-20260922-BRT4Y, WI-20260923-9R5HN). Two things are missing: nothing
chooses the store at `new`, which always allocates in the interpreter's own arena
(`Interpreter::alloc_cell`, `eval/mod.rs:1938`), and the arena is a concrete type, so no second
implementation can exist.

```rust
/// An implementation of the base sort `Cell` (037 §4.2): it mints the identity, stores the
/// initial value, and answers the reads.
pub trait CellImplementation {
    fn alloc(&self, initial: Value) -> u32;
    fn read(&self, raw: u32) -> Value;
    /// Store `new`, returning the prior value for the caller to drop outside any borrow.
    fn write(&self, raw: u32, new: Value) -> Value;
    fn retain(&self, raw: u32);
    /// Drop one reference; the value of a slot this frees, for the caller to drop.
    fn release(&self, raw: u32) -> Option<Value>;
}

pub struct CellHandle {
    raw: u32,
    implementation: Rc<dyn CellImplementation>,
}
```

- **The arena is the default implementation.** Its five methods are today's `alloc_raw`, `read`
  (the swap-out clone), `write`, `retain_raw` and `release_and_take`.
- **A handle's identity is its implementation and its slot.** `PartialEq` compares the allocation
  (`Rc::ptr_eq`, which ignores a `dyn` pointer's vtable) and `raw`, as it compares the arena today;
  `Hash` stays `raw`.
- **`cell_new`** takes the installed `Cell` entry, else the interpreter's arena, and allocates there.
  **`cell_get` and `cell_set`** go through the handle as they do today. The handle is the single
  door the user directed (WI-20260908-9WVT7, note F10): every write to a cell reaches the
  implementation it is bound to.
- **Unchanged:** a handle minted in one interpreter and read from another reads its own
  implementation (`a_handle_reads_the_arena_that_minted_it`); reclamation by reference count;
  `cell_arena_live_count`, which counts the default's slots.

The sites, all small, since one place mints a handle (§1.1):

| site | change |
|---|---|
| `eval/cell_arena.rs` | the handle's field becomes `implementation`; `Clone`, `Drop`, `PartialEq`, `Hash`, `Debug` (175–212) call through it; the arena implements the trait. `with_value` (131) has no caller outside its unit test and goes |
| `eval/mod.rs` | `alloc_cell` (1938) takes the installed entry; `read_cell` / `write_cell` (1943–1951) keep their shape; `cell_arena()` (1955) has no caller and goes; `cell_arena_live_count` (1834) counts the default's slots |
| `eval/builtins.rs` | `cell_new` (7146) reaches the map through `alloc_cell`; `cell_get` / `cell_set` unchanged |
| `rustland/anthill-todo/src/main.rs:5347` | the seeded `Cell[V = WIS]` goes through `alloc_cell` as before, so a host that installs an implementation first binds the seed to it |
| every other `Value::Cell` reader | unchanged: none of them looks inside the handle (`TermView::head` → `Opaque`, `alloc_from_value`'s refusal, `value_functor`, `runtime_carrier_sort`, `type_name`, `deep_clone`'s refusal) |

### 2.4 Installing for a call, and wrapping (step 3)

- **A host entry first.** `Interpreter::with_installed(sort, implementation, f)` keeps the current
  version, sets the new one, runs `f`, and restores the kept version whatever `f` returned, a raise
  included. Scopes nest as the host's calls do. Its users are an embedder, a test fixture and a
  time-travel debugger, all host code, which is what 037 §4.3 allows an implementation to be today.
- **Wrapping.** An implementation installed over a version can take the entry it replaces
  (`installations.get(cell_sort)`) and forward to it, which is how audit and logging are expressed
  (037 §5.2 item 3). Nothing is taken out of a slot while it runs, so the wrapped implementation
  stays reachable. A wrapper sees only the cells bound to it.
- **An installing operation in anthill waits** (PROPOSED, D3). It is a higher-order operation whose
  frame sets the version on entry and restores it on exit or unwind, as `Error.reify`'s frame does
  (027.4; `Interpreter::enter_reify_boundary`, `eval/eval.rs:4174`). It needs an anthill value that
  is an implementation, which exists only once 037 §4.3's design does; its name and signature are
  037 §10's open question.
- **037 §5.2 item 2 costs nothing.** The version is an interpreter field read at `new`, so a closure
  made inside a scope and called after it allocates under the version in force where it runs.

### 2.5 The store rows (step 4)

037 §3.2, §6.2 and §8, as the user decided after the review.

- **`stdlib/anthill/persistence/store.anthill`.**
  - `persist`, `retract` and `update` declare `{Modify[store], Modify[kb], Error}`, and `flush`
    declares `{Modify[store], External, Error}`. `retrieve` and `monotonicity` are unchanged.
  - The file imports the accessor `kb`, which it does not today. A zero-argument operation in a
    `Modify` target is read as the resource it denotes (`parse_test.rs:193–200`).
- **anthill-todo's `store.anthill`.**
  - The four direct callers in `FileBasedWorkitemStore`:
    - `persist_buffer` (501) and `retract_row` (514) gain `Modify[kb]`;
    - `flush_backend` (585) gains `External`;
    - `replace` (636), which updates and flushes, gains both.
  - The operations above them gain what they reach:
    - `retract_rows`, `forget_buffer` and `forget_satellites_buffer` gain `Modify[kb]`;
    - `persist_through` and every operation that calls it (`commit`, `commit_feedback`,
      `tag_item`, `stamp_format`, `link_entry`) gain both;
    - so do `forget` and `untag_item`, which flush.
  - The spec `WorkItemStore`'s eight mutators (68–175) gain both, since an implementation's row may
    not exceed its spec's (WI-347).
- **anthill-todo's `main.anthill`.**
  - Every `cmd_*` and `do_*` that reaches a mutator gains both; the census found about thirty.
  - `dispatch`, `undated_gate`, `Main.main` and the export chain already declare `External`, and
    gain `Modify[kb]`.
  - `ingest_comments` (4367) gains `External`.
- **Nothing else changes.**
  - `check_branch_external_exclusion` (`kb/typing/sorts.rs:1103`; WI-701) refuses an operation whose
    declared row holds both `Branch` and `External`, and the ordinary undeclared-effect check
    carries `External` up from `flush`. So a caller under `Branch` is refused without new code.
  - `anthill-stl/build.rs:121` generates `store.rs` from the real file. Its `&mut self` comes from
    `Modify[<first parameter>]` (`codegen/rust.rs:1931–1938`), and neither `Modify[kb]` nor
    `External` changes the generated trait (`rust.rs:2067–2083`).
- **The tests that change** are the ones whose typed fixtures call these operations:
  - `wi219_modify_transitivity_test.rs:87`, whose `commit` fixture declares `{Modify[s], Error}`
    over the stdlib's `persist`;
  - `wi204_smoke_test.rs:66`, `wi204_let_ctor_env_test.rs:55` and `:105`, whose drivers declare
    that row over `WorkItemStore.commit`;
  - anthill-todo's binary suite, which loads the bundle.

  `wi219_modify_transitivity_test.rs:62` loads the real `store.anthill` and passes once the rows
  agree. `wi1magr_member_signature_test.rs:455` counts one refusal, which should not move.

### 2.6 Mount keys compared by `Eq` (step 5)

037 §3.4: a mount key's type provides total `Eq`, and identity follows `Eq`, not the printed text.
§1.3 shows the text is coarser than equality, so the step changes an answer.

- **The key names symbols.** An entity is keyed by its qualified functor, and its named arguments by
  their label symbols in declared order. String equality of the key is then structural equality.
  For the three backends structural equality is their derived `Eq`, since their fields are strings
  and a plain enum. Two entities that share a local name across packages become two keys, and the
  doc comment at `eval/mod.rs:625` becomes true.
- **A key that is not totally `Eq` is refused at mount**, naming the field: a type with a `NonEq`
  witness (WI-644), such as a `Float` field.
- **A key sort with an `Eq` of its own is refused at mount**, loudly, until one exists. None does,
  and keying such a sort structurally would be the silent wrong answer.
- **The hosts build store values from resolved symbols.** The tests' bare interned names
  (`persistence_builtins_test.rs:31–35`) and anthill-todo's re-interned labels (`main.rs:4235`) go.
- **The tests that change** are the keying suites: `persistence_builtins_test.rs`
  (`store_canonical_key_is_stable`, :375, asserts the key's text), `wi667_*`, `wi666_*`, `wi830_*`,
  `wi913_*`, `wi919_*`, `wi920_*`, and anthill-todo's `wi830_declared_store_test.rs`.

### 2.7 The pool and constructor contracts (step 6)

- **The pool.** In `anthill.persistence.filesystem` (`stdlib/anthill/persistence/filesystem.anthill`):
  `sort FileStorage { provides Modifiable[T = Self]; entity file_storage }` (037 §3.2).
- **072's grammar,** in both parsers: an `EntityClause*` after the field list —
  `entity_declaration` (`tree-sitter-anthill/grammar.js:742`) and `entityDecl`
  (`scaland/core/src/main/scala/anthill/parse/AnthillParser.scala:2668`) — with corpus rows.
- **072's loader:** the clauses stored with the entity, as an operation's are, and `<entity>.result`
  declared per entity (proposal 041's binder).
- **072's typer:**
  - a construction call's `requires`, through the call-site contract machinery of WI-539;
  - the implicit `ensures` added to Γ after a construction call, beside `assume_call_ensures`
    (`kb/typing/effects.rs:1691`), which reads `lookup_operation_info(…).ensures` and so sees no
    entity today;
  - the ground check of a fact's terms;
  - the explicit `ensures` assumed at the three places of 072 §3.
- **The backends' constructors** declare `ensures memory_maybe_connected(result, file_storage)`. The
  relation is declared in `anthill.memory` (050.1 §8 F), which stage 1 (WI-20261015-809JN) creates,
  so this step follows it.

### 2.8 Cell's memory clauses (step 7)

From the review of 037 (§3.2). In `stdlib/anthill/prelude/cell.anthill`:

```anthill
operation new(v: V) -> Self
  effects Modify[result]
  ensures memory_maybe_connected(result, v) @[host_implemented]
operation get(c: Self) -> V
  ensures memory_maybe_connected(result, c) @[host_implemented]
operation set(c: Self, value: V) -> Unit
  effects Modify[c]
  ensures memory_maybe_connected(c, value) @[host_implemented]
```

A host operation's clauses are trusted (050.1 §4), so nothing checks these against `cell_new`; they
join 050.1 stage 3's census of the stdlib's clauses, which is where they belong.

### 2.9 Undo, for `Branch` (step 8)

037 §6.2 makes the undo of an abandoned alternative the duty of the implementation each resource is
bound to. None exists (§1.5). This step is WI-070's, and states only what each implementation owes
it.

- **One log on the interpreter** (D5). While a branch is open, each write records how to undo
  itself, in the order the writes happen. The `Branch` frame marks the log on entry, replays
  newest-first down to the mark when an alternative is abandoned, and drops the entries when the
  alternative commits. That is `cell-runtime.md` §"Branch interaction", whose marks nest as a stack
  over the depth-first path.
- **The entry is undone by the implementation the resource is bound to.** For a cell,
  `cell_set` has the prior value in hand, since `write` returns it. It records the handle and that
  value, and replay hands them back to the handle's implementation, through a method that defaults
  to `write`. A time-travel implementation can then tell an undo from a write.
- **What each base sort owes:**

  | resource | written by | undone by |
  |---|---|---|
  | a cell | `Cell.set` | restoring the prior value through the handle |
  | a cell | `Cell.new` | nothing beyond dropping its handles: an abandoned alternative's frames go, and the slot is reclaimed by reference count. `cell-runtime.md` §"Allocation undo" frees the slot eagerly instead; either works |
  | the KB's resident facts | `Store.persist`, `retract`, `update` | retracting what was asserted and reviving what was retracted |
  | a store's buffer | the same three | taking the buffered row or retract back out of the backend, a method each `persistence::Store` backend gains |
  | the disk | `Store.flush` | nothing: `External`, refused under `Branch` (054; WI-701, delivered) |
  | a layer | `KB.loaded` | its own discard (`restore_scoped`), a scope already |

- **The installation map needs nothing yet.** While installing is a host entry (D3), the version
  changes only between host calls, so every alternative of a branch runs under one version. Once
  the installing operation exists in anthill, its frame holds the version, and a branch's snapshot
  of the activation stack carries it (037 §5.2). The field alone would not do: an alternative
  resumed after a scope's frame was left would read the version that frame set.
- **SLD backtracking is not served by this log.** It needs no undo once WI-20260926-7D48J refuses a
  rule-body call that modifies shared state (§2.10).

### 2.10 Rule bodies

- **The pure-call rule holds by construction today.** A bridged call runs in a new interpreter with
  fresh arenas and an empty registry (§1.5), so its private cells are its own (037 §5.4). After
  step 2 that interpreter starts with an empty installation map, which means the defaults, and the
  rule holds unchanged. Nothing is built for it.
- **The inheritance for a call that modifies shared state is not built.** Under
  WI-20260926-7D48J's rule no such call runs.
- **That rule is not enforced yet**, and no step here enforces it.
  - `mkVia(lambda () -> Cell.new(3), ?c)` returns a cell handle into σ, where it outlives the
    interpreter that made it (§1.5).
  - `useVia(?c, lambda (x) -> Cell.set(x, 9), ?u)` then writes it, and a backtrack does not undo the
    write.
  - 7D48J refuses both at load where they are typed (`Modify[result]` counts) and declines them at
    run time otherwise. After that, no cell leaves a bridged call.
  - 037 §5.4 and the last item of §6.2 rest on it.

### 2.11 Comments that cite the withdrawn 037

Made with step 1, which deletes several of the sites. A citation of Rule 8 is current wherever it
means "a `Modify` fires only on a place of a modifiable type" — 037 kept the rule and its number —
and is left alone (`kb/region.rs:148`, `kb/typing/signature.rs:3665`, `eval/builtins.rs:5738`,
`reflect.anthill:478` and `:661`, `store.anthill:39`).

| site | says | becomes |
|---|---|---|
| `stdlib/anthill/prelude/effects.anthill:79` | Rule 8 as "bidirectional Modify↔handler correspondence: only types with a registered handler can be modified" | Rule 8 as 037 states it: a base sort through its `Modifiable` claim, a secondary sort through containment, and a base sort has a default implementation (BRT4Y) |
| `stdlib/anthill/prelude/cell.anthill:2`, `:12–13` | 037 §"Cell[V]"; identity "opaque-handle scheme per WI-205" | 037 §2 (a base sort) and §3.2 (a new resource per `new`); the scheme menu is withdrawn (037 §9) |
| `stdlib/anthill/prelude/mutable_stack.anthill:12` | "rides the existing Cell arena + Modify handler (proposal 037 §"Cell[V]")" | rides `Cell`'s operations, so each write reaches the implementation the backing cell is bound to (037 §5.1) |
| `eval/cell_arena.rs:2`, `:12` | 037 §`Cell[V]`; "the opaque-handle scheme from proposal 037 §"Resource type plug-in"" | the default implementation of `Cell` (037 §4.2) |
| `eval/value.rs:208` | 037 §`Cell[V]`; "Cycles are inexpressible: the typer's `may_contain_cell` rule rejects `Cell[T]` whenever T transitively contains Cell" | 037 §2; the cycle sentence goes: no `may_contain_cell` or `acyclic_cell` rule exists in the code (`effects.rs:253` names the second), and `Cell[V = List[T = Cell[V = Int64]]]` loads (050.1 §2) |
| `eval/builtins.rs:7154` | 037 §"Read operations" | 037 Rule 3 |
| `eval/builtins.rs:7166–7167` | 037 §"With time-travel" | 037 §6.4 |
| `kb/typing/projection.rs:583` | "proposal 037's effect-row convention" | 037 §6.3 |
| `anthill-stl/src/prelude/mod.rs:26–28` | "`fact Modifiable[T = X]` … which types admit `Modify[T]`" | `provides Modifiable[T = X]`, which admits a `Modify` over a place of that type (a raw fact is not read since WI-20260917-S8JYF; a type target is refused since 39AD2) |
| `eval/effects.rs:252` | 037 §`Cell[V]` | deleted with `default_modify_handler` |
| `docs/design/cell-runtime.md:475` | 037 §"Cell[V]" "branch-local snapshot" | 037 §6.2 — fixed with this document |

## 3. Decisions

All PROPOSED; none is decided yet.

- **D1 — WI-200 is re-scoped to step 1.** Its description is the generic handler's functor map
  ("two `wis(backend_a, …)` and `wis(backend_b, …)` share a single cell"), and 037 §3.5 says that
  goal has no counterpart: nothing writes a `Box`. Step 1 deletes the map, so it is the change
  WI-200's history leads to. The other way is to close WI-200 as superseded and file step 1 anew.
- **D2 — the effect registry keeps `Console`, `Clock` and `Error`; only the base modifiable sorts
  leave it.** After step 1 the registry serves no base sort, and 037 covers `Modify` only (its
  treatment of `Console` under `Branch` is open). 037 §8's "the flat registry is replaced by the
  installation map" then reads "for the base sorts", and the registry's `take_for_invoke`, which
  keeps a handler from reaching another, stays for the three effects until WI-078 decides their
  scoping. 037 §8's bullet would say so.
- **D3 — installing is a host entry first** (§2.4). The anthill-level operation needs an anthill
  value that is an implementation (037 §4.3), and its name and signature are 037 §10's question.
  WI-078 (h) is re-scoped to the host entry and the wrapping; the anthill operation is its later
  half.
- **D4 — kernel-language §5.3's bridge paragraph loses its `ModifyRuntime` example**
  (`docs/kernel-language.md:2127`): "as a write through `ModifyRuntime` to a cell the operation keeps
  to itself does, the typer dropping that `Modify` from the row". After step 1 a write to a local
  cell asks no handler, so the example names nothing. The rule before it stays, as the diagnostic of
  a typer that dropped an effect it should not have. A spec change, so its wording is agreed at
  step 1.
- **D5 — undo goes through one log on the interpreter** (§2.9), as `cell-runtime.md` §"Branch
  interaction" designs it: a write made while a branch is open records how to undo it, in the order
  the writes happen, and an abandoned alternative replays its part of the log newest first. Each
  entry is undone by the implementation the resource is bound to. The other way, each
  implementation keeping its own log and the `Branch` frame asking every implementation that took a
  write, loses the order between two implementations.
- **D6 — tickets.** Steps 2, 4 and 5 have none. Proposed: one ticket for step 2, with step 3 as
  WI-078 (h) after it (D3); one for step 4; step 5 folded into step 4's ticket, or its own (D8).
  Step 6 is 072's implementation, which rides T34HP by the user's decision. T34HP is the design
  ticket and is done when this document is, so either it stays open until 072 lands, or 072's
  implementation gets a ticket when T34HP is delivered. None is filed before the user agrees.
- **D7 — a store write under a live layer** (§1.4; found by reading, not measured). The first move
  is the failing test: `persist` while a `KB.loaded` layer is live, the layer dropped, then `flush`.
  It should show a file holding a fact the KB no longer has. Then one of:
  - (a) refuse a store write while a layer is live, loudly. Small, and it closes the gap now.
  - (b) discard, with the layer, the store writes made since its snapshot. That is the backends' undo
    of §2.9, the work `Branch` needs anyway.
  - (c) write the resident fact below the layer. Not possible while a layer is applied in place.

  Proposed: (a) now, and (b) when step 8 gives the backends an undo.
- **D8 — step 5 now, or later.** The collision it removes needs two store sorts with one local name,
  which no shipped project has. But the key's doc comment claims an equality it does not have, and
  037 §3.4 states the rule. Proposed: with step 4, in its ticket. The refusals of a key that is not
  totally `Eq`, and of a key sort with an `Eq` of its own, are what make the rule hold.
- **D9 — `KB.assert` and `KB.add_guard` in the interpreter** (§1.4). 037 Rule 8 says a base sort
  has a default implementation that BRT4Y holds to its declarations, and the interpreter has none
  for these two. They are not `@[host_implemented]`, so BRT4Y does not ask. Only the generated-Rust
  host bridge implements them. Either:
  - (a) host functions over `assert_checked` and `add_guard_labeled`, mapped in `reflect.anthill`'s
    binding block and tagged `@[host_implemented]`, so the check holds them;
  - (b) 037's table says the interpreter implements only `kb()` and `loaded`, and the KB's writes
    stay host-only.

  Proposed: (a), with step 4, which writes the KB's rows anyway. It also gives step 8 a KB write to
  undo that is not a store's.

## 4. Acceptance, per step

Each row drives the capability: it runs the program and reads the value, and says which rows fail
when the step is backed out.

**Step 1.**

1. The m5 shape is refused at load, naming `ModifyRuntime` as a name that resolves to nothing.
   With the sort restored it loads, so the row fails when the step is backed out.
2. The rows given new fixtures keep their verdicts, and pass with or without the step by design:
   - the registry rows: a taken handler is `UnhandledEffect` naming `Clock`, a `Throw` is `Raised`,
     a `Fail` is `UnsupportedHandlerAction` carrying its reason;
   - the 0RP29 pair: it loads with `Modify[h]` and is refused without it, naming `Modify[T = h]`;
   - the 4GBQV typing rows.
3. `register_standard_effect_handlers` registers five handlers, and a program that prints and reads
   the clock still runs (control).
4. The gate, and `sbt testFull` for the Scala bootstrap list.

**Step 2.** Over `operation localCell(n: Int64) -> Int64 = (let c = Cell.new(n); let _ =
Cell.set(c, n + 6); Cell.get(c))`, and a host wrapper over the default that counts the calls it
forwards:

1. Installed for the whole run, `interp.call(localCell, [3])` answers 9 and the wrapper counts one
   `alloc` and one `write`: an installed implementation sees the private cells of pure code (037
   §5.3). Not installed, the call answers 9 and the wrapper counts nothing. Backed out, the counts
   stay zero; the answer is 9 either way by design.
2. The binding is made at `new`. A cell made while the wrapper is in force and written after the
   wrapper is gone is counted; a cell made before it is installed and written while it is in force
   is not (037 §5.1, the map read only where a resource is made).
3. A rule body calling `localCell(3, ?r)` answers `?r = 9`, and the wrapper counts nothing: a pure
   bridged call runs with the defaults (037 §5.4).
4. `a_handle_reads_the_arena_that_minted_it` and the arena's reclamation tests pass unchanged
   (controls).

**Step 3.**

1. Two nested `with_installed` scopes: an allocation inside the inner one is counted by the inner
   wrapper; after the inner one returns, the next allocation by the outer; after a raise inside the
   inner one, caught outside it, the next allocation by the outer again.
2. A wrapper that forwards to the entry it replaced: a value written through it is read back
   through it, and the arena it wraps holds the slot.

**Step 4.** Over a `FileStore` mounted on a temporary directory:

1. An operation that calls `flush(s, nil())` and declares `{Modify[s], Error}` is refused at load,
   naming `External`. Declaring `{Modify[s], External, Error}`, it loads and runs, and the file is
   on disk.
2. An operation that calls `persist(s, f, m)` and declares `{Modify[s], Error}` is refused at load,
   naming `Modify[kb]`. Declared, it loads and runs, and `facts_of(kb(), …)` holds the fact
   afterwards: the knowledge base did change.
3. An operation whose row holds `Branch` and that reaches `flush` is refused at load (054).
4. anthill-todo's suite passes, and `store_anthill_typechecks` loads the real file (controls).

Backed out to the old rows, rows 1–3 load, so they fail.

**Step 5.**

1. Two store entities that share a local name in two packages, each mounted, are two stores: a
   `persist` through one is not in the other's buffer. Today the second registration replaces the
   first (`ExtentRegistry::register_mirror`, `kb/extent.rs:774`), so the row fails.
2. A store entity with a `Float` field is refused at mount, naming the field.
3. The keying suites pass with store values built from resolved symbols.

**Step 6.** 072's acceptance, rows 1–5. Row 5 is this step's: with 050.1 stage 1, a write through a
`FileStore` that an operation without a memory clause returns stays in the row, charged
`Modify[file_storage]`.

**Step 7.** The review's program: `operation bad(p: Cell[V = Int64]) -> Unit = (let c = Cell.new(p);
let q = Cell.get(c); Cell.set(q, 5))` declares nothing and is refused, the write charged to `p`. Declaring
`effects Modify[p]`, it loads, and a caller reads 5 from `p`. `localCell(3)` still loads with an
empty row (control).

**Step 8.** WI-070's own acceptance (`pick(c)` reads `c`'s old value, 037 §6.2), plus, for the
implementations other than the arena: a `persist` in an abandoned alternative leaves neither a
buffered row nor a resident fact; a `retract` in one leaves the row in both; a `Branch` region
reaching `flush` is refused at load (054, WI-701).
