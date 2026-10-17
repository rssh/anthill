## Attributes

- id: WI-20261017-J4WGC-037-step-6-the-file-backends
- created: 2026-10-17T12:46:50Z

- status: Open
- status_agent: claude
- status_at: 2026-10-17T12:46:50Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261017-WPBXQ-072-constructor-contracts, WI-20261015-809JN-proposal-050-1-stage-1-a-write

- tags: proposal-037

## Description

037 STEP 6: THE FILE BACKENDS' POOL — FileStorage, AND THE CONSTRUCTORS THAT NAME IT. Plan: docs/design/037-implementation.md §2.7; acceptance §4, step 6. Proposal 037 §3.2 and §3.3: a value that names state outside the process is connected to a pool. The three file backends (FileStore, IndexedFileStore, ItemPerFileStore) share one, since any two of them can name one directory. THE CHANGE: (1) in anthill.persistence.filesystem (stdlib/anthill/persistence/filesystem.anthill), sort FileStorage { provides Modifiable[T = Self]; entity file_storage }; (2) each backend's entity declares ensures memory_maybe_connected(result, file_storage), the constructor contract 072 adds (WI-20261017-WPBXQ). The relation lives in anthill.memory, which 050.1 stage 1 creates (WI-20261015-809JN), and stage 1 is what reads memory clauses at calls. ACCEPTANCE: 072's row 5, which drives it: with 050.1 stage 1, a write through a FileStore that an operation without a memory clause returns stays in the row, charged Modify[file_storage], and is refused where the row does not declare it. Without the backends' clause, 050.1's fresh default drops that write.

