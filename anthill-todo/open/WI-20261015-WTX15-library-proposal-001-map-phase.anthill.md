## Attributes

- id: WI-20261015-WTX15-library-proposal-001-map-phase
- created: 2026-10-15T13:50:32Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T13:50:32Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261015-H6323-library-proposal-001-map

- tags: library-001-map

## Description

Library proposal 001-map, phase 4: MutableMap — the in-place map, provides MapReadable and MutableCollection (docs/proposals/library/001-map.md §Mutable variant, §Rust runtime backing, Phase 4).

EXPECTED: stdlib/anthill/prelude/mutable_map.anthill with new() -> Self effects Modify[result]; set(m, key, value) -> Bool (true if the key was new), delete(m, key) -> Bool (true if it was present), clear(m), all effects Modify[m]; setMany / deleteMany returning their membership-change counts (001-map §Batched access, Open Q 9–10). It provides MapReadable (its E from the carrier) and MutableCollection with Element = Pair[K, V]. The runtime reuses the existing MapArena / MapHandle — reference equality, a fresh handle per new — with the mutating operations editing the slot's MapBody in place rather than copying it.
ROWS: the full lifecycle new → set → get → delete → clear under effect tracking (an operation that sets a map it takes owes Modify[m]; one that builds and drops its own does not; new's Modify[result] where the map is returned); set / delete answer their witnesses; setMany / deleteMany their counts; a walk through Iterable.
The memory clauses (proposal 050.1: set's ensures memory_maybe_connected(m, value), a read's result sharing with m) come with 050.1 stage 3's stdlib census.

