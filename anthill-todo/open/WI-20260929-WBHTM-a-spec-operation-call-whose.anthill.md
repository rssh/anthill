## Attributes

- id: WI-20260929-WBHTM-a-spec-operation-call-whose
- created: 2026-09-29T16:04:04Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T16:04:04Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SPEC-OPERATION CALL WHOSE ARGUMENT'S STATIC TYPE CARRIES A VALUE-IN-TYPE PANICS A DEBUG BUILD, AND IN RELEASE A DEFERRED ONE DISPATCHES TO THE WRONG PROVIDER (WI-348 "Phase C"). `operation use(s: Buf[T = Int64, N = 3]) -> Int64 = Store.peek(s)`: the spec parameter's per-call binding is the `Value::Node` type, and `sort_goal_from_subst` (typing/carrier.rs ~47) and the defer-match (typing/call_class.rs ~901) `debug_assert!(false, "WI-348 … Phase C")`, then drop it. MEASURED independent of any value-in-type provision: it fires with a GROUND provision and with none. In release: at the dispatch site the call is refused at load with a misleading "missing requires" (so the correct `N = 3` call is refused too); at the DEFER-MATCH site (`User requires Store[State = Other]`, `go(s: Buf[T = Int64, N = 4]) = Store.peek(s)`, providers `Carrier` at `Buf[T = Int64]` and `OtherImpl` at `Other`) the dropped pair leaves `entry_matches_subst` nothing to refute, the call defers, and it RUNS `OtherImpl.peek` on a `Buf` (exit 99) — the code's own note "Conservatively drop (sound — resolved at runtime)" is false. FOUND by WI-20260924-F3FYJ's review (V4). FIX: carry a Node binding through `SortGoal` and the defer-match (or lower it with `node_occurrence::value_to_term` where a term is needed), refusing rather than dropping what cannot be matched. ACCEPTANCE: both calls typecheck and dispatch correctly with no debug panic; the defer-match case refused (or dispatched to the right provider) in both builds; full workspace green via rustland/scripts/test.sh.

