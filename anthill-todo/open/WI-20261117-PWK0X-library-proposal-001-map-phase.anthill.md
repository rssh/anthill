## Attributes

- id: WI-20261117-PWK0X-library-proposal-001-map-phase
- created: 2026-11-17T21:38:23Z

- status: Open
- status_agent: claude
- status_at: 2026-11-17T21:38:23Z

- acceptance: cargo-test, scaland-sbt-test

- tags: library-001-map

## Description

Library proposal 001-map, phase 2a: a Hash spec, and a map keyed through it, so a key whose sort writes its own eq is found in O(1) and no map compares a key with every stored one (docs/proposals/library/001-map.md §Key discipline, Phase 2a).

WHY: since c36e2ff0 a map keeps K's Eq instance and reads a tuple key at K's labels, but a key whose sort writes its own eq (a Pt whose eq reads x alone; Set, TotalFloat, Type, EffectExpression) is keyed by its structure, so pt(1, 2) and pt(1, 9), one key by Pt's eq, are two keys of the map. Keying it through eq alone compares it with every stored key, O(N) per operation, which the user rejected (2026-11-17).

EXPECTED:
- sort anthill.prelude.Hash: sort T = ?; provides Eq[T = T]; operation hash(x: T) -> Int64; the dormant law rule hash_eq: eq(hash(?a), hash(?b)) = true :- eq(?a, ?b).
- Hash provided by every scalar Eq is (a host hash), by a tuple from its components' instances at the labels its type names, by a composite eq_derive derives Eq for (a hash member mirroring its derived eq member), and conditionally beside each written conditional Eq (Pair, SortedSet). A sort that writes its own eq writes hash beside it (Set, TotalFloat, Type, EffectExpression in the stdlib); one that does not provides no Hash.
- Map requires Hash[T = K] and Map.empty() requires Hash[T = K]; the map keeps that instance. The host keys a value by its structure (a tuple at K's labels) where its instance is derived, and otherwise buckets it by its hash and compares with eq within the bucket.
- The fixtures that require Eq[T = K] to build a map require Hash[T = K].
ROWS: a Pt with its own eq and hash is one key at pt(1, 2) and pt(1, 9) (get finds it, put replaces it); a sort with its own eq and no hash is refused as a key, naming Hash[T = ...]; a tuple key wider than its type is one key; the Map laws' guard agrees with the map; Set as a key; building N entries stays O(N log N) (a measured timing or an operation count).
NOT HERE: SortedMap and the default-map rule (a hashable key gets the hash map, an ordered unhashable one the sorted map; 001-map Open Q 14) are phase 2b.

