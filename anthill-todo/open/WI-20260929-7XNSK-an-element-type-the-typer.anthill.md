## Attributes

- id: WI-20260929-7XNSK-an-element-type-the-typer
- created: 2026-09-29T20:15:47Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T20:15:47Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN ELEMENT TYPE THE TYPER COULD NOT INFER DISPATCHES AS A WILDCARD, SO WHICH PROVIDER A CALL REACHES DEPENDS ON ARGUMENT ORDER. `sort Store2 { sort State = ?; operation peek2(s: State, t: State) -> Int64 }`, providers `CA` at `Buf[T = Int64, N = Bool]` (answers `s.v + 10`) and `CB` at `Buf[T = String, N = Bool]` (answers `s.v + 20`), `mkb[E](xs: List[T = E]) -> Buf[T = E, N = Bool] = buf(v: 1)` and `use(y: Buf[T = Int64, N = Bool])`: `Store2.peek2(mkb([]), y)` is refused "ambiguous dispatch … (CA, CB)" while `Store2.peek2(y, mkb([]))` runs CA (11); with CB alone, `peek2(mkb([]), y)` RUNS CB (21) although `y` pins `T = Int64`. MEASURED identically before and after WI-20260929-WBHTM; since WBHTM the value-in-type spelling (`N = 3`) reaches it too, where it used to be refused as "missing requires". MECHANISM: `[]`'s element type is the inert `TypeExtractor.TypeVar` marker (typing/constructor.rs ~407), σ binds the spec parameter from the FIRST argument and only checks the second against that binding, so the goal keeps the marker; `types_lesseq` treats `type_var` as compatible with anything (subtype.rs ~90), so `match_candidate_against_goal` accepts every provider on that element. FOUND by WI-20260929-WBHTM's /code-review (V5). ACCEPTANCE: the goal carries what a later argument pins (or the call is refused as under-determined), so the verdict does not depend on argument order — `peek2(mkb([]), y)` reaches CA with both providers and is refused with CB alone, in the typed and the value-in-type spelling; full workspace green via rustland/scripts/test.sh.

