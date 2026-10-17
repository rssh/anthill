## Attributes

- id: WI-20261017-KE2GP-037-step-4-the-store-rows-say
- created: 2026-10-17T12:35:57Z

- status: Open
- status_agent: claude
- status_at: 2026-10-17T12:35:57Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-037

## Description

037 STEP 4: THE STORE ROWS SAY WHAT A STORE WRITE CHANGES. Plan: docs/design/037-implementation.md §2.5; acceptance §4, step 4. Proposal 037 §3.2, §6.2 and §8, as the user decided after 037's review (2026-10-17). WHY: Store.persist asserts the fact into the interpreter's KB as well as buffering it, and retract and update take it out (KnowledgeBase::persist_mirrored, retract_persistent, update_persistent), so a store write changes what kb answers, and no row says so. flush is the only store operation that writes the disk in all three file backends, and it declares no External, so 054's refusal of Branch with External does not reach it. THE CHANGE: (1) In stdlib/anthill/persistence/store.anthill, persist, retract and update declare {Modify[store], Modify[kb], Error}, and flush declares {Modify[store], External, Error}. The file imports the accessor kb. (2) anthill-todo's store.anthill and main.anthill carry the rows up, as the plan lists: FileBasedWorkitemStore's four direct callers and the operations above them; the WorkItemStore spec's eight mutators; every cmd_* and do_* that reaches one. dispatch, undated_gate and Main.main gain Modify[kb], and ingest_comments gains External. (3) The typed test fixtures over these operations move with them (plan §2.5's list). Whether step 5 (mount keys compared by Eq) joins this ticket is the plan's decision D8.

## Changes

### 2026-10-17T12:38:37Z — feedback — claude

ADDED BY THE USER'S DECISION (2026-10-17; docs/design/037-implementation.md D7, §1.4): A STORE WRITE WHILE A KB.loaded LAYER IS LIVE. Found by reading, not measured. A layer is applied in place, so a persist made while one is live asserts its resident fact among the layer's rules. Dropping the layer (restore_scoped, kb/layer.rs:103) takes the fact away, but the backend keeps its buffered row: a scoped snapshot holds the mount tables, not the backends, which cannot be cloned (kb/layer.rs:71). A later flush then writes a fact the KB no longer holds. retract is the mirror case. This ticket does three things: (1) a failing test that measures it (persist under a live layer, drop the layer, flush; and the retract twin); (2) a loud refusal of persist, retract and update while a layer is live, naming the layer; (3) nothing more, until step 8 (WI-070) gives the backends an undo. Then dropping a layer undoes the store writes made since its snapshot, and the refusal goes. Acceptance: plan §4, step 4, row 5.

### 2026-10-17T12:39:22Z — feedback — claude

STEP 5 JOINS THIS TICKET (user, 2026-10-17; docs/design/037-implementation.md D8, §2.6; acceptance §4, step 5). MOUNT KEYS COMPARED BY Eq (proposal 037 §3.4). Today the key is printed text (Interpreter::store_canonical_key, eval/mod.rs:628). It prints the functor by its LOCAL name and sorts named arguments by local label, so two store entities that share a local name in two packages are one key, and the second registration replaces the first (ExtentRegistry::register_mirror, kb/extent.rs:774). Its doc comment claims agreement with views_structurally_equal, which compares by symbol. THE CHANGE: (1) key by the qualified functor, and by label symbols in declared order, so string equality is structural equality, which for the three file backends (strings and a plain enum) is their derived Eq; (2) refuse at mount a key whose type is not totally Eq (a NonEq witness, e.g. a Float field), naming the field; (3) refuse at mount a key sort with an Eq of its own, until one exists; (4) hosts build store values from resolved symbols: persistence_builtins_test.rs:31-35's bare interned names and anthill-todo's re-interned labels (main.rs:4235) go. The keying suites move: persistence_builtins_test (store_canonical_key_is_stable asserts the key's text), wi666, wi667, wi830_*, wi913, wi919, wi920, and anthill-todo's wi830_declared_store_test.

