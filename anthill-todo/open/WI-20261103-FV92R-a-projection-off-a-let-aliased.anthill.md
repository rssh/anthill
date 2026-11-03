## Attributes

- id: WI-20261103-FV92R-a-projection-off-a-let-aliased
- created: 2026-11-03T09:49:40Z

- status: Open
- status_agent: user
- status_at: 2026-11-03T09:49:40Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A PROJECTION OFF A LET-ALIASED COMPOUND RECEIVER, NESTED IN A WRITTEN TYPE, STAYS KEYED TO THE ALIAS: over `sort State { sort P = ?; requires DataProvider[P = P]; entity state(provider: P) }` (`DataProvider { sort P = ?; sort K = ? }`), in `operation fwd(st: State, j: st.provider.K) -> Int64 = let t = st …` with `check(s: State, k: s.provider.K) -> Int64`, `let p: (k: t.provider.K, n: Int64) = (k: j, n: 1)` is refused "type mismatch in p.annotation (let-binding): expected (k: t.provider.K, n: Int64), got (k: st.provider.K, n: Int64)", `let o: Option[T = t.provider.K] = some(j)` likewise, and a lambda binder `p: (k: t.provider.K, n: Int64)` applied to `(k: j, n: 1)` is refused at `check(st, p.k)` "expected st.provider.K, got t.provider.K" — on HEAD 9c60680a and with WI-20261103-SG16K, measured 2026-11-03. At the top of the annotation the alias is read: `let k: t.provider.K = get(t, j)` (WI-0RP29's `a_let_annotation_through_an_alias_names_its_target`) and `lambda (k: t.provider.K)` (SG16K's `a_compound_receiver_through_an_alias_is_the_path_it_names`) are `st.provider.K` and run; that is `canonicalize_projection_receivers`, whose doc names this boundary — it rewrites a top-level projection only, "a loud over-rejection, never a wrong accept". A NESTED projection off a single-name alias is read too (`List[T = y.E]` under `let y = x` is `List[T = x.E]`); a nested one off a compound alias path is read by neither. WHAT: in `read_written_annotation`, the one reader of a body's annotation (a `let`, a lambda, a pattern binder), read a let-aliased receiver as the path it names wherever the projection stands in the written type; measure first whether the discharge's own alias reading or the canonicalization is the place. ACCEPTANCE: the three programs above run to 42 at `go()` (`let st: State[P = MemStore] = state(provider: mem(n: 1))`, `fwd(st, 41)`); a nested `t.provider.K` handed to `check(u, …)` for another `u: State` stays refused; the top-level rows stay green; full workspace green via rustland/scripts/test.sh.

