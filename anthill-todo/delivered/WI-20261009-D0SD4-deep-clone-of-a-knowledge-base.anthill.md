## Attributes

- id: WI-20261009-D0SD4-deep-clone-of-a-knowledge-base
- created: 2026-10-09T05:20:09Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-09T06:50:27Z

- acceptance: cargo-test

- tags: test-infra

## Description

DEEP CLONE OF A KNOWLEDGE BASE, AND A SEND WRAPPER FOR THE TEST BASE — what WI-059 (the stdlib loaded once per test binary) needs first, and not what its item 3 says it is.

WHAT. (1) In `anthill-core`, safe code: an independent copy of a `KnowledgeBase` that shares NO `Rc` with the one it was made from — a new allocation for every body tree, every `Value` payload, every discrimination-tree node and every cache row. (2) In `anthill-core/tests/common` ONLY: a wrapper type holding such a copy, with the one `unsafe impl Send` this change adds, so a `static` can hold the stdlib's KB and hand each test a copy of its own. Nothing here changes the load recipe; that is WI-059.

WHY NOT `Rc -> Arc` (WI-059 item 3, docs/design/test-infrastructure.md §5.2). Measured 2026-10-09 by asking the compiler, a field at a time, which of `KnowledgeBase`'s 116 fields are `Clone + Send`: 5 are not `Clone` (`TermStore`, `SymbolTable`, `SourceRegistry`, `HostFnRegistry`, `ExtentRegistry`) and 25 hold something that is not `Send`. Two of the reasons no `Arc` removes: `Value` carries the interpreter's five arenas (`Rc<RefCell<CellArena | MapArena | StreamArena | ClosureArena | SubstArena>>`) and the layer arena, so `Send` for a `Value` is a lock on each; and every expression node (`NodeKind::Expr`, `kb/node_occurrence.rs`) has four `RefCell` slots the typer writes IN PLACE — `classification`, `op_dicts`, `inferred_type`, `lowered_receiver` — and an `Arc` of a type holding a `RefCell` is not `Send`. Decided 2026-10-09 (user): the deep copy and the wrapper; real `Send` is not taken. The count §5.2 gives is also low: 2 030 `Rc` uses in 72 files of `anthill-core/src`, 85 in the other crates.

WHY THE COPY MUST BE DEEP, the wrapper aside. §5.2 says the `Rc`s are shared-immutable, so a clone that shares them is correct. For body trees that is false: a second `load_all` re-types every operation body already in the KB (the free-op sweep, `kb/typing/sorts.rs`), and the typer's stamps are written through `&self` into nodes two shallow copies would share — so one test's load would stamp the bodies another test reads.

HOW, suggested. A fallible entry, not `impl Clone`: a KB with a mounted store backend, or a `Value` that holds a live arena handle, cannot be copied, and says so. Written as a struct literal over every field with no `..`, so a new field does not compile until it is placed. A field with no `Rc` in it goes through one helper bounded `Clone + Send` — the compiler's own proof that it holds none — and only the others get a hand-written copier, each an exhaustive match for the same reason. Body trees keep their internal sharing (a memo by node address) and the `Weak` of `lowered_receiver` is re-pointed at the copy. `kb/layer.rs` already clones about 100 of the fields for its snapshot, and its `classify_every_field_for_layering` is the precedent for the no-`..` check. `HostFnImpl::Dynamic` is an `Arc<dyn Fn>` with no `Send + Sync` bound: bound it, or refuse a base that holds one.

THE WRAPPER'S CLAIM, to be stated at the `unsafe`: it is built BY the deep copy, it is only ever read under a `Mutex` to make another deep copy, and so no `Rc` it holds is reachable from any other thread. Whatever breaks the deep copy's "shares nothing" breaks this, silently — which is why the copy is compiler-checked where it can be.

NOT VERIFIED, found on the way, ask before filing: the layer snapshot (`snapshot_scoped`) clones `op_records` and `const_bodies` by `Rc`, so the stamps a layer's load writes on a BASE body are not rolled back at the discard. Whether `KB.loaded` can leave a base call site dispatching to something the discarded layer declared has not been tested.

CONTROL. (a) Independence: stamp a node of the copy, add a clause and a sort to the copy, and read the original unchanged — and the other way round; fails when a copier shares an `Rc`. (b) Sharing: every `Rc` the copy holds has the strong count its own structure accounts for, read after the original is dropped. (c) Equivalence: the copy of a loaded stdlib answers what the original answers, and a user file loaded into the copy gives the diagnostics and the KB it gives loaded into the original. (d) The refusals: a mounted backend, an arena handle. Say at each row which back-out fails it.

MEASURE. The copy's cost beside one stdlib load and one second-call load (`docs/measurements/test-infrastructure/bench_load.rs`), both builds — it is the per-test floor once the frontier-driven passes (§4 A3) land.

DONE WHEN: the copy and the wrapper are in, the controls are in with their back-outs measured, the gate is green, and §5.2 says what was found and what was built.

## Changes

### 2026-10-09T06:50:25Z — feedback — user

DELIVERED 2026-10-09 — the deep copy, the wrapper, the controls and the measurement.

THE COPY. `KnowledgeBase::deep_clone` (`kb/deep_clone.rs`), safe code: a struct literal over all 116 fields with no `..`; a field with no `Rc` passes `plain` (bounded `Clone + Send`), the others a copier that is an exhaustive match. A node or payload reached twice is copied once (a memo by address), and the receiver twin's `Weak` is re-pointed at the copy. The interners are NOT `Clone`: `TermStore`, `SymbolTable` and `SourceRegistry` each have a `duplicate` of their own. REFUSED (`DeepCloneError`, the least of several reasons, asked before anything is copied where it can be): a closure host function; a mounted backend or a record of one; an interpreter-arena handle; an applied layer; a live import audit; a KB mid-load or mid-search; a receiver twin the KB does not own; a body nested past a megabyte of stack. The ten memo caches whose rows hold an `Rc` start empty.

THE WRAPPER. `common::SendableKb` (`tests/common/mod.rs`): a deep copy in, a deep copy out, never lent, and the one `unsafe impl Send` of the change with its argument at the site.

NOT AS THE TICKET SAID. (1) The discrimination tree is not copied: its children are `Arc` now (`kb/discrim.rs`), so a copy SHARES it and each side path-copies what it writes — /code-review's finding; it was three quarters of the first cut's cost. (2) Control (b) is not a strong-count audit: the original is DROPPED and every occurrence and payload it held must be freed, which a copy sharing one by any path prevents.

CONTROLS. `kb/deep_clone.rs`: five rows, fifteen back-outs measured one at a time, each failing the row its table names. `wi_d0sd4_deep_clone_test`: three rows — a file loads into a copy as into the original and gets the same refusal; copies of one `static` base taken on eight threads at once; a mounted source is refused — two back-outs measured. NO ROW covers `ProvidesIndex::deep_clone_with` and the requirement entries inside a call's classification; a mirror store, the asking file, `pending_citation_routes` and `ReceiverTwinNotOwned` are refusals nothing drives. Each is said at its site.

MEASURED (docs/design/test-infrastructure.md §5.1; raw: docs/measurements/test-infrastructure/clone-cost-2026-10-09.txt), the gate's build, one thread: a copy 7.3 ms beside a full load of 302-313 ms and a second-call load of 180-184 ms; the `Arc` did not move either load.

/code-review ran (15 findings, all taken; what was changed in answer was checked by the rows and the gate, not by a second review). Gate: 8 831 passed, 0 failed, 14 ignored. After it, one comment in `kb/layer.rs` was corrected (`Rc`-COW -> copy-on-write); nothing else.

STILL NOT TESTED, ask before filing: whether `KB.loaded` can leave a base call site carrying a discarded layer's typer stamp — the layer snapshot clones `op_records` by `Rc`.

