## Attributes

- id: WI-20261023-HH0HT-a-call-written-under-an-arrow
- created: 2026-10-23T17:58:48Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-30T23:46:54Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

A CALL WRITTEN UNDER AN ARROW-TYPE TERM IN A RULE BODY IS EVALUATED BUT NOT TYPED, so neither of WI-20261013-R1W5A's load checks (the call typed as an operation body is, an effectful call refused by its row) reaches it. MEASURED 2026-10-23 (01424c91), over `operation plus1(n: Int64) -> Int64 = n + 1`: `rule pureUnder(?t) :- ?t <=> Int64 -> plus1(1)` answers `?t = arrow(Int64, 2)` — the call ran; `rule illTypedUnder(?t) :- ?t <=> Int64 -> plus1("a")` LOADS and faults at run time ("type mismatch: expected Int64, got Node and Int64"), leaving `arrow(Int64, plus1("a"))`, where `?t <=> plus1("a")` is refused at load ("type mismatch in plus1.n (op-arg): expected Int64, got String"). Over `operation stamp() -> String effects {Clock} = now()`, `rule underArrow(?t) :- ?t <=> Int64 -> stamp()` loads and is declined at run time (undecided, "it performs `anthill.prelude.Time.Clock`, and a rule body performs no effect"), where `?t <=> stamp()` and `?t <=> [stamp()]` are refused at load. TO DECIDE: whether a call in an arrow-type term is a value-slot call (068 §1.1 — typed and refused as the clause's other calls are) or the arrow term is a type whose calls are not evaluated. ACCEPTANCE (cargo-test, driven): the decided reading for `pureUnder`, `illTypedUnder` and `underArrow`, each row with its back-out; the `arrow-type term` rows of WI-618 (`?t <=> (Int64) -> Int64` loads) unchanged.

## Changes

### 2026-10-30T23:46:53Z — feedback — claude

Delivered in 4b9afb18, the value-slot reading (user, 2026-10-30). An arrow in a rule's own term is a type written as a term, and what it holds is data, as a tuple's components are: the rule-body walk gives its components value positions (child_body_positions), the clause typing walks them (type_written_as_term no longer names the arrow), and a call there is typed and refused as its twin outside the arrow is, with the twin's text — ?t <=> Int64 -> plus1("a"), ?t <=> Int64 -> stamp(), in data, in a parameter, in a row, in a branch; a variable such a call reads is typed by its parameter; a dot there is dispatched, arrow(3, Int64). Under = an arrow is a value of Type (check_apply_iter, in the rule's own term only, and only for a name the program does not declare): (Int64 -> Int64) = (Int64 -> Int64) holds, where it was refused "unknown functor". Under a compound expression the operation-body reading is kept (lambda t -> (t -> t) refused as before). Kept, as decided: a keyword-less typo ?y <=> ((x) -> plus1(x)) gives a second error. Fixed inline, found on the way (user, 2026-10-30): PartialEq.eq, neq and struct_eq (===) in a value slot are their Bool value, run by run_builtin_for_value — (Int64, PartialEq.eq(1, 1)) binds (Int64, true), was (Int64, eq(1, 1)) in a definite answer; flag(PartialEq.eq(1, 1)) meets fact flag(true), where not(...) over it held; a goal-only builtin written as data (nonvar(5)) stays the term. The K4JGC row that pinned the term is rewritten (an_equality_passed_to_a_relation_is_its_value). kernel-language §5.3 and the rule-body evaluation section, one sentence each; 068-implementation note. 11 rows with back-out ledgers in wi_hh0ht_call_under_an_arrow_test and wi_hh0ht_equality_is_its_value_test; full workspace 11,252 passed, 0 failed; families unchanged; scaland testFull 792 passed.

