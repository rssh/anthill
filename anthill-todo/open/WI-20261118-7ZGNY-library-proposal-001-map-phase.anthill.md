## Attributes

- id: WI-20261118-7ZGNY-library-proposal-001-map-phase
- created: 2026-11-18T04:15:38Z

- status: Open
- status_agent: user
- status_at: 2026-11-18T04:15:38Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261015-H6323-library-proposal-001-map

- tags: library-001-map

## Description

Library proposal 001-map, phase 2b: SortedMap, the persistent map keyed through an ordering, and the default-map rule (docs/proposals/library/001-map.md §Key discipline, Phase 2b, Open Q 11, 12, 14).

WHY: since phase 2a (WI-20261117-PWK0X) Map keys through Hash[T = K], so a key type that provides Ord and no Hash (a sort that writes its own eq and an ordering, and no hash) has no map. The user decided (2026-11-17) that such a key gets the sorted map by default.

EXPECTED:
- stdlib/anthill/prelude/sorted_map.anthill: SortedMap[K, V, O], persistent, requires O: Ord[T = K] as a named slot (SortedSet's precedent, library/007), so two orderings are two types. Ord, not WeakOrd (Open Q 12): the map provides MapReadable, whose reads answer by Eq. A balanced tree, O(log N) per operation; its operations and laws are PersistentMap's (empty, with, without); keys and entries in the ordering's order; provides MapReadable and PersistentCollection.
- The default map: a key type that provides Hash gets the hash map, one that provides Ord and no Hash the sorted map, one with neither is refused where the map is made. Its spelling and the value's type (Open Q 14: Map as the selecting name once phase 3 frees it, or a provision of MapReadable's constructor chosen by K's instances; the implementation's type or the interface's) are decided with the user before the default is implemented.
ROWS: SortedMap's reads and laws answer as the hash map's; keys and entries come in the ordering's order; a map under one ordering is refused where one under another is asked; a key with its own eq and an Ord and no hash is one key at two values its eq equates, found in O(log N) (an operation count, as phase 2a's rows count comparisons); the default at String is the hash map, at that key the sorted map, and a key with neither is refused.
NOT HERE: a mutable sorted map (Open Q 11, added when a caller needs one); a checked Hash law (Open Q 13).

