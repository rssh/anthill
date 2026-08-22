## Attributes

- id: WI-20260822-ZJZS7-a-host-backed-operation-does
- created: 2026-08-22T07:53:44Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T07:53:44Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A HOST-BACKED OPERATION DOES NOT REDUCE IN A RULE BODY — it reduces in an operation body,
and the same call one context over is silently inert. This is what stops `Bool.and` /
`Bool.or` / `Bool.not` from being CONDITIONS in a goal, which WI-20260822-J38JE item 1
says every Bool-valued expression is.

MEASURED (rustland, current tree):
  operation f() -> Bool = Bool.and(true, true)  ;  rule p(1) :- f()   -> 1   REDUCES
  operation f() -> Bool = Bool.and(true, false) ;  rule p(1) :- f()   -> 0
  operation f() -> Bool = Bool.not(true)        ;  rule p(1) :- f()   -> 0
  rule p(1) :- Bool.and(true, true) = true                            -> 0   DOES NOT
  rule p(1) :- Int64.gt(2, 1) = true                (control)         -> 1
  rule p(1) :- Int64.gt(2, 1)                       (control)         -> 1

THE SPLIT IS WHAT THE RULE BODY CAN REDUCE. A rule body reduces (a) a resolver BUILTIN —
`Int64.gt` has a `BuiltinTag`, which is why both controls answer — and (b) a BODIED
operation, through `bare_bodied_bool_relation` / `reduce_op_value` and the SLD→eval
bridge. `Bool.and` is neither: `prelude/bool.anthill` declares `and`/`or`/`not` body-less
("backed by a host builtin"), and its Boolean-algebra `<=>` laws are UNTAGGED, so by
WI-881/884/888 they are inert and cannot stand in for the reduction either.

THIS IS THE SAME SHAPE AS WI-20260822-NDG34 (a `const` does not fold in a rule body,
folds in an operation body) and the two may share a fix: both are "the eval bridge is
reachable from an operation body and not from a rule body" for a construct that carries
no anthill body.

WHAT THIS TICKET MUST DECIDE:
 1. WHERE the reduction hooks in. `bare_bodied_bool_relation` and
    `functional_relation_arity` (kb/resolve.rs) both gate on `op_body_node(f).is_some()`
    — "has a runnable body" — precisely because the view is DERIVED from the body. A
    host-backed op has no body to derive from but DOES have a host fn the interpreter can
    call. Decide whether the gate widens to "reducible" (body OR host fn) or whether a
    separate host-call route is added beside it, and say what happens to the rule-LESS
    clause (design §3.3 precedence) under the wider gate.
 2. EFFECTS AND PURITY. Both gates refuse an effectful op because "an effectful body is
    not a logical relation". A host fn's effect row is declared the same way, so the same
    clause should apply — confirm it does, and that a host fn with no declared effects is
    genuinely pure (the generativity hazard proposal 039 gates `const` bodies for).
 3. WHETHER §6.6's `and` REFUSAL THEN NARROWS. WI-1046 refuses `a & b` in a goal
    unconditionally, and its measurement was `l(?x) & r(?x)` — operands that are GOALS,
    so not Bool values, which stays refused. Once `Bool.and` reduces, `Bool.and(?b, ?b)`
    with `?b: Bool` is an ordinary condition and must answer. Decide the predicate that
    separates them (operand TYPE, presumably) and keep WI-1046's message for the case it
    was written for. J38JE's `pand` row is the driver.

ACCEPTANCE: drive every row of the table above and assert the ANSWER COUNT, in both
polarities — `Bool.and(true, false)` in a goal answers 0 and `Bool.and(true, true)`
answers 1, `Bool.not(false)` answers 1, and the operation-body rows keep answering what
they already answer. CONTROLS THAT MUST STAY GREEN: `Int64.gt` in both positions (a
resolver builtin, untouched); a BODIED Bool op's bare goal (WI-583/WI-580, untouched); an
effectful op still declines the route; and WI-1046's refusal still fires with its §6.6
message on `l(?x) & r(?x)`. Say at each site which rows fail on a back-out.
cargo-test green via rustland/scripts/test.sh.

