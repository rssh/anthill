## Attributes

- id: WI-20260930-74H6J-a-spec-operation-call-over-a
- created: 2026-09-30T09:10:29Z

- status: Open
- status_agent: user
- status_at: 2026-09-30T09:10:29Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SPEC-OPERATION CALL OVER A CARRIER WHOSE EFFECT ROW IS THE CALLER'S ROW PARAMETER DROPS THAT ROW, SO A PURE CALLER LOADS. `sort Cnt { sort T = ?; effects EC = ?; entity cnt(items: List[T]); provides Stream[T = T, E = {EC}]; operation splitFirst(c: Cnt) -> Option[Pair[A = c.T, B = Cnt[T = c.T, EC = c.EC]]] effects EC = … }` and `operation first[R](x: Cnt[T = Int64, EC = R]) -> Int64 = match Stream.splitFirst(x) case some(_) -> 1 case none() -> 0`: LOADS, although the call incurs `R` — `Stream.splitFirst`'s `effects s.E` over `E = {EC}`, and the override's `effects EC` alike. The qualified `Cnt.splitFirst(x)` is refused "undeclared effect: ?R", and so is the same `Stream.splitFirst(x)` over a value-in-type element (`T = Buf[T = Int64, N = 3]`); the `N = Bool` element loads like `Int64`; declaring `effects R` loads every spelling. An effect-soundness hole: a caller of `first` at `EC = {Modify[c]}` never sees the `Modify`. MEASURED identically on the build after WI-20260929-0RP29 and on the release build before it. MECHANISM NOT LOCATED: the value-in-type twin takes the WI-606 fallback (its `s.E` does not ground) and threads the override's effects; the term twin's `s.E` grounds on the spec path, and the row is lost after it — the dispatch arm's effect threading or the WI-365 row close are the suspects. FOUND BY WI-20260929-0RP29's /code-review (gap sweep). ACCEPTANCE: the pure `first` refused naming the undeclared row, as the qualified call and the value-in-type twin are, and the `effects R` spelling still loads; full workspace green via rustland/scripts/test.sh.

