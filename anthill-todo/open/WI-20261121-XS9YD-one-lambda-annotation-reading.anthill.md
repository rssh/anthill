## Attributes

- id: WI-20261121-XS9YD-one-lambda-annotation-reading
- created: 2026-11-21T08:43:24Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T08:43:24Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

ONE LAMBDA ANNOTATION READING A SIBLING BOTH OFF ITSELF AND THROUGH A FIELD IS REFUSED: over `sort WrapH { sort L = ?; entity wraph(f: Box[T = List[T = ?]], l: L) }` (`sort Box { sort T = ?; entity box(v: T) }`), `sort Pair2 { sort A = ?; sort B = ?; entity pair2(a: A, b: B) }` and `sort State { sort P = ?; entity state(provider: P) }`, `let g = lambda (a: WrapH[L = State], k: Pair2[A = a.L, B = a.f.T]) -> 42` is refused "type mismatch in <binder>.k (binder-annotation)" — measured on f7ed45c6, pinned as refused (not crashed) by WI-20261121-204T6's `one_annotation_reading_a_sibling_both_ways_is_refused_not_crashed`; before that change it stopped a build with debug assertions. `a`'s closing mints a rigid for `State`'s `P` (a slot nested in a written binding), so `a.L` is read off `a` as written — the slot left open — and the lambda's own tuple reads `k`'s annotation so, in a record of its own (`read_list_in_order`); the binder check reads it with `a` closed, and the two readings differ (`State` against `State[P = ?P]`, and the field's nested slot opened twice). Split over two binders (`b: a.L`, `k: a.f.T`) each reading is the binder check's and the lambda loads. WHAT: measure whether one annotation's two readings of `a` can be split as two binders' are — the member reading at `a` as written, the field reading at `a` closed in the body's record — or the member reading's open slot named from the closed `a`'s rigid with its `requires` bound kept. ACCEPTANCE: the lambda loads; applied where its arguments allow (`k`'s `A` component given a `State`), it runs; the 204T6 row turns into a load; full workspace green via rustland/scripts/test.sh.

