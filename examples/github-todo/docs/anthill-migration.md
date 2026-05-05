# Migrating `anthill-todo` to anthill (WI-009)

**Status:** Design draft
**Tracks:** WI-009 (port todo-app to anthill)
**Implements:** Proposal 026 (`anthill run`), proposal 028 (entry-point discovery via `anthill.cli.Main`), proposal 007 (pluggable persistence), the `rust+anthill` realization profile (WI-164).

## 1. Goal

Replace the 1625-line Rust monolith at `rustland/anthill-todo/src/main.rs` with a thin Rust shim (~150 lines) plus a set of `.anthill` source files bundled at build time. The shipped binary remains `anthill-todo` with the same CLI surface and the same on-disk artefact (`<project>/anthill-todo/{domain,rules,workitems,project}.anthill`).

The migration is the first concrete consumer of the `rust+anthill` realization profile (`stdlib/anthill/realization/rust_anthill.anthill`): one static binary embeds the interpreter, the stdlib, and this program's own `.anthill` files.

## 2. Architecture

```
                ┌─────────────────────────────────────────────────────┐
                │  Rust shim (rustland/anthill-todo/src/main.rs)      │
                │  • parse embedded stdlib + bundled todo .anthill    │
                │  • register builtins (eval::builtins)               │
                │  • register effect handlers (Console, Modify)       │
                │  • register persistence builtins                    │
                │  • register `anthill.prelude.Time.now` builtin      │
                │  • construct FileStore, BulkStore::pull → load      │
                │  • interp.call("anthill.todo.main", [argv...])      │
                │  • return Int as exit code                          │
                └─────────────────────────────────────────────────────┘
                                   │
                                   ▼
                ┌─────────────────────────────────────────────────────┐
                │  anthill program (rustland/anthill-todo/anthill/)   │
                │                                                     │
                │  main.anthill          dispatch + parse_argv        │
                │  cli_specs.anthill     16 OperationSpec facts       │
                │  cmd_query.anthill     list, show, status, graph,   │
                │                          next, skill (read-only)    │
                │  cmd_mutate.anthill    add, claim, deliver, verify, │
                │                          feedback                   │
                │  cmd_edit.anthill      update, add-dependency,      │
                │                          remove-dependency, delete  │
                │  bootstrap.anthill     FileStore + route() rules    │
                └─────────────────────────────────────────────────────┘
```

The user data files (`anthill-todo/workitems.anthill` etc.) are **not** bundled — they are the operand the shim reads from disk via `BulkStore::pull` at startup.

## 3. Why this shape

### 3.1 No project-local "edit source text" effect

The current Rust does surgical text editing on `workitems.anthill`: `find_fact_block`, `update_status_in_source`, `update_depends_in_source`, etc. We deliberately avoid porting that approach. Instead we use the persistence layer (proposal 007):

- **Read**: `BulkStore::pull` at startup loads every `.anthill` file under the project's scan dir into the KB. After this, every command reads from the KB only.
- **Mutate**: anthill code calls `KB.assert(kb, new_fact, sort)` (already wired in `eval::builtins::kb_execute` family) and `KB.retract(kb, fact_id)` for in-memory mutation.
- **Write back**: `Store::persist(store, fact, meta)` + `Store::flush(store)` (proposal 007 §4) writes durable changes.

This is exactly the bulk-pull / persist-flush flow proposal 007 §11 describes for `bulk` stores. WorkItem mutation collapses to: query → build new term → assert + retract old → persist + flush.

### 3.2 What's host-side, what's anthill-side

Host (Rust shim):
- Embedded stdlib + todo source bundling (`include_str!`).
- Interpreter setup, builtin/effect registration.
- `FileStore` instance creation (knows the filesystem path; anthill code receives an opaque `Value::Entity`).
- `init` subcommand — runs *before* KB construction (creates the directory the KB will live in).
- `--skill` subcommand — emits a const string; runs before KB construction.
- `Time.now` builtin (clock effect).

Anthill (the bundled program):
- argv parsing via `anthill.cli.parse.parse_argv` over the `OperationSpec` registry.
- All other subcommands as `operation cmd_<name>(args, agent, store) -> Int`.
- KB queries via `anthill.reflect.KB.execute`.
- KB mutations via `anthill.reflect.KB.assert` / `KB.retract`.
- Persistence via `anthill.persistence.{persist, flush}`.
- Output formatting via `anthill.prelude.Console.{println, eprintln}`.

## 4. Subcommand catalogue (16)

| Subcommand        | KB shape               | Persistence       |
|-------------------|------------------------|-------------------|
| `init`            | shim, pre-KB           | direct fs writes  |
| `--skill`         | shim, pre-KB           | none              |
| `list`            | KB.execute             | none              |
| `status`          | KB.execute             | none              |
| `show <id>`       | KB.execute             | none              |
| `graph`           | KB.execute             | none              |
| `next`            | KB.execute (via `claimable` rule) | none   |
| `add <desc> …`    | KB.assert (new fact)   | persist + flush   |
| `feedback <id> …` | KB.assert (new fact)   | persist + flush   |
| `claim <id>`      | retract + assert       | persist + flush   |
| `deliver <id>`    | retract + assert       | persist + flush   |
| `verify <id>`     | retract + assert       | persist + flush   |
| `update <id> …`   | retract + assert       | persist + flush   |
| `add-dependency`  | retract + assert       | persist + flush   |
| `remove-dependency` | retract + assert     | persist + flush   |
| `delete <id>`     | retract                | retract + flush   |

Every mutation follows the same shape — `retract` (if updating) + `assert` (the new term) + `persist` (durable buffer) + `flush` (write to disk). No subcommand-specific persistence path.

## 5. Prerequisites

This migration cannot land directly. Two pieces have to be in place first:

### 5.1 `FileStore::retract` must modify files (WI-X-RETRACT)

`rustland/anthill-core/src/persistence/file_store.rs:118` currently records retractions in a `pending_retracts` Vec but **never modifies files** — explicitly noted as deferred ("Stage 0: record the retraction but don't modify files. File modification on retract is deferred to a future stage").

Without this, mutating subcommands break: `claim WI-001` would `retract` the old WorkItem(status: Open) and `persist` the new WorkItem(status: Claimed). The retract is a no-op on disk; the persist appends. Result: two WorkItem facts on disk with the same id, diverging from KB state.

**Required behaviour**:
- Retract is buffered (current behaviour) but `flush` rewrites affected files.
- For each file containing at least one retracted-or-newly-asserted fact, the flush walks the KB's *current* facts assigned to that file (per `route(fact)`), prints them via `print_fact`, and writes the file fresh.
- Inter-fact text outside any `fact …(…)` block (header comments, blank lines) is preserved by recording byte ranges before re-rendering.
- Comments *inside* a fact block are not preserved — facts are rendered from KB state. This is the same fidelity proposal 007 §4 implies.

**Persist-buffering interaction**: today `persist` records `(path, text)` pairs. With retract working, persist+flush must be idempotent over the KB's current state — calling `persist(fact); flush()` and then `flush()` again should not duplicate the fact on disk. The cleanest way is to make flush *fully driven by current KB state* and treat `persist` calls as a hint for which files are dirty (which file routes for each affected fact).

### 5.2 Persistence builtins must be wired (WI-X-PERSIST-BUILTINS)

`rustland/anthill-core/src/eval/builtins.rs:24–82` registers prelude/Console/Modify and `anthill.reflect.KB.execute`. It does **not** register the four persistence operations from proposal 007 §4 (`persist`, `retract`, `flush`, `pull`). They are declared in `stdlib/anthill/persistence/` but unreachable from interpreted code today.

**Required**:
- `Interpreter` gains a `Store` registry mapping `Value::Entity` (the `FileStore(...)` term) to a `Box<dyn Store>` instance.
- `register_if_present(interp, "anthill.persistence.persist", …)` and friends look up the registry, dispatch to the trait method.
- The shim populates the registry before calling `main`.

Acceptance for the wiring WI: an integration test where an anthill program asserts a fact, calls `persist` + `flush`, the on-disk file contains the fact, and a fresh process pulls it back.

## 6. Cache invalidation on KB mutation: bridging retract and the proof cache

Two caches in the codebase:

1. `SearchStream::query_cache` (`rustland/anthill-core/src/kb/resolve.rs:270`) — per-`resolve` call, rebuilt each call. Not a concern for retract.
2. **The proof cache** from proposal 030 phase α — `ProofRecord.state_hash` is computed by `state_hash(kb, visited_rules)` (`rustland/anthill-smt-gen/src/cache/key.rs:79`) and stored alongside each cached witness (`rustland/anthill-cli/src/prove.rs:70`). When a cite or `prove --check` accesses a `ProofRecord`, the kernel **recomputes** its state_hash against the current KB and compares; mismatch ⇒ stale, re-discharge required.

The proof cache's invalidation is correct today: any retract (or rule edit) changes some visited rule/functor's content, which changes the recomputed `state_hash`, which marks the record stale. WI-175 doesn't break this — it's just another path that mutates the KB, and the existing recomputation already covers it.

The **performance** picture changes once retract becomes routine. Today `prove --check` is invoked rarely and recomputes `state_hash` per record by walking visited rules + their referenced functors over the whole KB — O(visited × kb_size). Once WI-009 lands, every `claim` / `deliver` / `verify` / `update` invocation of `anthill-todo` mutates the KB, and the next `prove --check` recomputes hashes for every recorded ProofRecord even though most are unaffected.

**Filed as WI-177** (no longer forward-looking; not blocking WI-009): add a monotonic `kb.epoch: u64` bumped on every `assert_rule` / `assert_fact` / `retract`, plus optional per-functor `kb.functor_epoch(sym)`. ProofRecords cache `(epoch, state_hash)`; on access, if `kb.epoch() == cached_epoch` skip recomputation, else recompute and compare. The no-mutation steady state collapses to O(1) per record.

Per-functor epochs are the natural finer grain — a `ProofRecord` records the set of functors its `visited_rules` referenced (already collected by `walk_visited` in `cache/key.rs`), and the cache hit condition becomes "every recorded functor's epoch matches its cached value." Mutation of an unrelated functor doesn't invalidate.

WI-177 is independent of WI-009: shipping WI-009 without WI-177 yields a correct but slower `prove --check` after each todo mutation. WI-177 can land before, after, or alongside.

## 7. Bundle layout

```
rustland/anthill-todo/
  Cargo.toml
  anthill/                          # NEW — bundled into binary via include_str!
    main.anthill                    # sort Main requires anthill.cli.Main; operation main
    bootstrap.anthill               # FileStore decl + route(WorkItem(?)) etc.
    cli_specs.anthill               # 16 OperationSpec facts, one per subcommand
    cmd_query.anthill               # read-only commands
    cmd_mutate.anthill              # add, feedback, claim, deliver, verify
    cmd_edit.anthill                # update, add-dep, remove-dep, delete
    skill_md.anthill                # SKILL_MD as a String constant
  src/
    main.rs                         # NEW thin shim, ~150 lines
    stdlib_embedded.rs              # unchanged
```

Old contents (`src/main.rs` 1625 lines, mostly text-editing helpers) is deleted at cutover. The unit tests for `has_transitive_dep` move to anthill-side rule tests (the cycle-detection rule already exists in `rules.anthill` as `dep_satisfied` / `all_deps_satisfied`).

## 8. CLI dispatch detail

`anthill.cli.parse.parse_argv` (WI-159) handles the heavy lifting:

```anthill
operation main(args: List[T = String]) -> Int =
  let store = bootstrap_store(args) in
  match parse_argv(specs, args)
    case parse_err(no_subcommand()) -> print_help(specs)  -- exit 0
    case parse_err(e) -> render_err(e)                    -- exit 2
    case parse_ok(parsed) ->
      match parsed
        case ParsedArgs("list",   bs) -> cmd_list(bs)
        case ParsedArgs("show",   bs) -> cmd_show(bs)
        ...
        case ParsedArgs("claim",  bs) -> cmd_claim(bs, store)
        case ParsedArgs("delete", bs) -> cmd_delete(bs, store)
```

`-d <dir>` and `--agent <name>` are global flags. WI-159's spec shape attaches params to one OperationSpec, so they're declared on every spec (tolerable v1 duplication; the spec module in stdlib could later grow a `globals` field).

## 9. Cutover plan

WI-009 ships in one PR (acceptance is a single tool, `cargo-test`), but the implementation order inside the PR is:

1. Land the bundle's read-only paths (`list`, `status`, `show`, `graph`, `next`, `skill`) behind the new shim. Existing CLI integration tests that hit these subcommands must still pass.
2. Wire add / feedback (append-only persist; doesn't need WI-X-RETRACT).
3. Wire claim / deliver / verify / update / add-dep / remove-dep / delete (depend on WI-X-RETRACT being merged).
4. Delete the old `src/main.rs` body. Keep `src/stdlib_embedded.rs`.

If WI-X-RETRACT slips, steps 1–2 still ship as a partial migration; step 3 is gated on the prerequisite landing.

## 10. Out of scope for WI-009

- Switching the bootstrap convention from `Flat` (one `workitems.anthill`) to Stage 0's per-fact files (`workitems/WI-001.anthill`) — proposal 007 §6 mentions this but it's a separate decision, not required for the port.
- KB epoch / cache invalidation primitive (§6 above).
- The `Store::route` rule machinery driving resolver dispatch (proposal 007 §5; landed for queryable backends per 007 §11 Q4 status, but the file-store path stays bulk-pull).
- Any change to the user-facing CLI surface or output formatting — the migration must produce byte-identical output for `list` / `show` / `status` / `graph` against the existing fixtures, otherwise downstream callers (the `/todo` skill) break.
