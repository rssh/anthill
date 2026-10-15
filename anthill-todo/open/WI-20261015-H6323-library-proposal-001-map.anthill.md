## Attributes

- id: WI-20261015-H6323-library-proposal-001-map
- created: 2026-10-15T13:49:47Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T13:49:47Z

- acceptance: cargo-test, scaland-sbt-test

- tags: library-001-map

## Description

Library proposal 001-map, phases 1–2: declare MapReadable, the read-only map interface, and have today's Map provide it — the read half of the split into MapReadable / PersistentMap / MutableMap (docs/proposals/library/001-map.md).

WHY NOW: 001-map (Draft 2026-05-28) never had a work item. Its sibling 002 (Iterable / PersistentCollection / MutableCollection) was carried through, and 002's phase 4 (WI-364) took MutableStack as the first mutable carrier, so the map split stayed a draft. The stdlib's Map is the persistent half today (put -> Self, remove -> Self), with no mutable map.

EXPECTED (001-map §Read-only abstraction, §Why MapReadable has its own effect, §Batched access, Phase 1–2):
- stdlib/anthill/prelude/map_readable.anthill: sort MapReadable over a carrier M, K, V and its access effect E (`{}` for an in-memory carrier) with get, contains, keys, values, entries, size, getMany, and the contains law; reads return Stream[T, E] where 001-map says so.
- Map provides MapReadable (a provision, not a requires; 001-map Open Q 2), and every read goes through it.
- Value equality for the persistent map over its imbl body, as §Rust runtime backing says — first measured: what Map's eq answers today for two maps built apart with equal contents.
ROWS: a read through MapReadable on a Map value answers as Map's own read; getMany drops absent keys in input order; two maps built apart with equal contents are equal.

