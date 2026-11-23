## Attributes

- id: WI-20261121-XS9YD-one-lambda-annotation-reading
- created: 2026-11-21T08:43:24Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-23T18:53:30Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

ONE LAMBDA ANNOTATION READING A SIBLING BOTH OFF ITSELF AND THROUGH A FIELD IS REFUSED: over `sort WrapH { sort L = ?; entity wraph(f: Box[T = List[T = ?]], l: L) }` (`sort Box { sort T = ?; entity box(v: T) }`), `sort Pair2 { sort A = ?; sort B = ?; entity pair2(a: A, b: B) }` and `sort State { sort P = ?; entity state(provider: P) }`, `let g = lambda (a: WrapH[L = State], k: Pair2[A = a.L, B = a.f.T]) -> 42` is refused "type mismatch in <binder>.k (binder-annotation)" — measured on f7ed45c6, pinned as refused (not crashed) by WI-20261121-204T6's `one_annotation_reading_a_sibling_both_ways_is_refused_not_crashed`; before that change it stopped a build with debug assertions. `a`'s closing mints a rigid for `State`'s `P` (a slot nested in a written binding), so `a.L` is read off `a` as written — the slot left open — and the lambda's own tuple reads `k`'s annotation so, in a record of its own (`read_list_in_order`); the binder check reads it with `a` closed, and the two readings differ (`State` against `State[P = ?P]`, and the field's nested slot opened twice). Split over two binders (`b: a.L`, `k: a.f.T`) each reading is the binder check's and the lambda loads. WHAT: measure whether one annotation's two readings of `a` can be split as two binders' are — the member reading at `a` as written, the field reading at `a` closed in the body's record — or the member reading's open slot named from the closed `a`'s rigid with its `requires` bound kept. ACCEPTANCE: the lambda loads; applied where its arguments allow (`k`'s `A` component given a `State`), it runs; the 204T6 row turns into a load; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-23T18:53:28Z — feedback — user

DELIVERED 2026-11-23 in aa0e972bd, closed with the user. Measured first on 338cce4e8 with the debug CLI: the description's lambda was refused 'expected Pair2[A = State, B = List[T = ?T]], got Pair2[A = State[P = ?P], B = List[T = ?T]]', the two ?T two unknowns: the lambda's own tuple read the whole annotation with a as written in a record of its own, the binder check read it with a closed in the body's, and the field's nested slot (List's T) opened once in each. The A halves were never the difference (with f: Box[T = List[T = Int64]] it loaded). WHICH OF THE TWO (the description's question): the split, as two binders read it. (a) read_list_in_order reads only a MEMBER off a sibling whose closing minted a rigid (a.L) off the sibling as written, its own reading (read_minted_siblings_as_written, a lookup through Discharge.reading), and the rest of the annotation with the sibling closed, in the body's record; no record of its own any more (TypingEnv::with_own_path_openings gone). (b) Found by /code-review: the own tuple took the body's reading, so b: a.L was State and any State passed, where operation h(a: WrapH[L = State], b: a.L) refuses one of another P (the two-binder form alike since 204T6). The own tuple now keeps each projection off a binder of the list the lambda's own, read at the application's arguments (SiblingReading::Own, ArrowBinders); the binders are typed at the body's readings. ACCEPTANCE: the lambda loads in either order; applied with k's A the State a0 holds and B = [] it runs; a State of another P is refused there, 'expected Pair2[A = State[P = Int64], ...], got Pair2[A = State[P = String], ...]'; the 204T6 row is a load (moved to wi_xs9yd_one_annotation_both_ways_test). Two 204T6 rows move to what an operation answers: the chain's h(pair(l: u), w, ju) refused at b as well as k; lambda (h: Hold2[X = List], k: h.f.T) takes [1] and refuses ['s']. That is part of WI-20261121-ZPZDY's acceptance; its g(h0, h0.f.v) over Hold stays refused (an application reads without the caller's record of h0.f). Rows: wi_xs9yd_one_annotation_both_ways_test (7). Back-outs over a temporary binary of the 14 lambda-annotation files (315): all 6, own tuple at the body's reading 5, raw annotation as written 1, no member read as written 1; three controls pass backed out. /code-review xhigh: 5 findings, all fixed. Gate 12643 / 0 / 26, all 36 binaries; families green, no verdict moved; scaland testFull 811 + 51 (2 skipped), tree unchanged.

