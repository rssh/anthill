## Attributes

- id: WI-20261121-59S43-a-lambda-writing-its
- created: 2026-11-21T08:43:12Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T08:43:12Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A LAMBDA WRITING ITS PARAMETERS AT THE SLOT'S OWN SPECIFIC TYPE IS REFUSED AT ITS DEPENDENT BINDER: over `sort State { sort P = ?; requires DataProvider[P = P]; entity state(provider: P) }` and `MemStore` providing `DataProvider[P = MemStore, K = Int64]`, with `operation takes(f: (s: State[P = MemStore], j: s.provider.K) -> Int64, w: State[P = MemStore], j: w.provider.K) -> Int64 = f(w, j)`, the call `takes(lambda (s2: State[P = MemStore], k: s2.provider.K) -> check(s2, k), state(provider: mem(n: 1)), 41)` is refused "type mismatch in <binder>.k (binder-annotation): expected s2.provider.K, got Int64" — the lambda's types written exactly as the slot's — measured on f7ed45c6 with the debug CLI, 2026-11-21, and the same before WI-20261121-204T6 (that ticket's test names it, NOT HERE); the forward form (`(k: s2.provider.K, s2: State[P = MemStore])` against a slot naming the key first) likewise. The slot's component for `k` is read to `Int64` (its `s` grounds `K`), the binder's annotation `s2.provider.K` stays the neutral, and the binder check compares the two. WHAT: measure where the slot's component is read and where the binder's annotation is, and read them alike — the annotation off `s2` at the slot's `State[P = MemStore]`, or the component left the neutral `s2.provider.K` in the lambda's names (`in_lambda_binders`). ACCEPTANCE: the call runs to 42; a key of another state's type (`String` where `K = Int64`) is refused at the call; the lambda against the generic `f: (s: State, j: s.provider.K)` stays as it is (runs); full workspace green via rustland/scripts/test.sh.

