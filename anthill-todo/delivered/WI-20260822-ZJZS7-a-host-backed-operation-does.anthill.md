## Attributes

- id: WI-20260822-ZJZS7-a-host-backed-operation-does
- created: 2026-08-22T07:53:44Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-27T06:02:38Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260826-VPEWK-a-rule-body-operand-does-not

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

## Changes

### 2026-08-27T04:52:14Z — feedback — claude

MOSTLY DELIVERED ALREADY, RESIDUE IS ONE ROW AND IS NOW OWNED BY WI-20260826-VPEWK. Do NOT claim and re-analyse this from the description above -- its diagnosis has been overtaken. Commit 36f16461 (J38JE, 2026-08-22 09:01) names this ticket in its own message and at kb/resolve.rs:8060, and closed three of the four parts:

 * ITEM 1, at the GOAL position. bare_bodied_bool_relation now asks op_reducible_in_rule_body = op_body_node(f).is_some() || is_interpreter_mapped_op(f) (resolve.rs:8089) -- the wider gate, not a separate route. So the description claim "A HOST-BACKED OPERATION DOES NOT REDUCE IN A RULE BODY" is FALSE as of that commit: :- Bool.not(false) answers 1, :- Bool.or(false, true) answers 1, and the rule-LESS clause (design section 3.3 precedence) is untouched, which was the second half of the question item 1 asked.
 * ITEM 2, effects and purity. The effect-free clause was kept, not widened, and is documented at bare_bodied_bool_relation (resolve.rs:8117): an effectful host fn is no more a logical relation than an effectful body, and the eval bridge empty effect registry would suspend on one anyway. Stream.isEmpty is the named effectful Bool op that is still refused the relational view.
 * ITEM 3 IS MOOT, NOT ANSWERED. This ticket asked which predicate would NARROW section 6.6 and refusal so Bool.and(?b, ?b) could pass while l(?x) & r(?x) stayed refused. It was never narrowed -- 36f16461 added push_and (a BuiltinTag spliced into the same frame, no choice point) plus rule and(?a, ?b) :- push_and(?a, ?b), gave & a real CONJUNCTION reading, and DELETED WI-1046 refusal outright; its two refusal rows now assert answers. l(?x) & r(?x) answers 1. So the operand-TYPE predicate this ticket proposed is not needed and was not written: the conjunction reading subsumes the value one wherever both apply and also resolves the UNGROUND case, which no value reading can.

WHAT SURVIVES IS EXACTLY ONE ROW OF THE TABLE ABOVE: `rule p(1) :- Bool.and(true, true) = true` still answers 0. Re-measured 2026-08-27 -- it is pinned at anthill-core/tests/include/wi_j38je_boolean_goal_test.rs:512 carrying THIS ticket id in its assertion message, and that module is green (11 passed). Every other row now answers what the ACCEPTANCE section asks for.

AND THE RESIDUE IS RE-DIAGNOSED. This description says the cause is that a rule body reduces only a BODIED operation and a resolver BUILTIN -- true when written, false since 36f16461. The real cause is a POSITION split, not a rule-body-wide one: the GOAL side asks the widened op_reducible_in_rule_body while the OPERAND side still asks reduce_op_value(dispatch_body_less: false), i.e. a body and nothing else (resolve.rs:7400). J38JE fixed one position and the other kept the old question. WI-20260826-VPEWK carries that diagnosis with the exact separator (is_interpreter_mapped_op is TRUE for Bool.and, FALSE for Set.insert) and the symbolic-algebra control (Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 1) must stay at 1) that this ticket does not have. The two ZJZS7 negatives recorded at resolve.rs:8173 have been folded into VPEWK as well.

STATUS PLAN, per user decision 2026-08-27: this stays OPEN and now DEPENDS ON VPEWK, so it drops off claimable (rules.anthill:70 -- claimable is Open + all_deps_satisfied) and cannot be picked up in the meantime. Closing it today would misstate it in every available status: Rejected is false (the premise was never refuted, the row is real and still red), Stale is false (the precedent, WI-229, is wholesale supersession, whereas three of four parts here SHIPPED), and Delivered is not yet true. When VPEWK lands, that last row answers, this ticket ACCEPTANCE is met in full, and it closes as Delivered naming both commits.

### 2026-08-27T06:02:37Z — feedback — claude

CLOSING AS DELIVERED. Every row of the MEASURED table in the description now answers, across TWO commits, and the last one landed with WI-20260826-VPEWK.

  operation f() -> Bool = Bool.and(true, true)  ; rule p(1) :- f()   1   (always did)
  operation f() -> Bool = Bool.and(true, false) ; rule p(1) :- f()   0   (always did)
  operation f() -> Bool = Bool.not(true)        ; rule p(1) :- f()   0   (always did)
  rule p(1) :- Bool.and(true, true) = true                           1   <- WAS 0, the last row
  rule p(1) :- Int64.gt(2, 1) = true                (control)        1   (untouched)
  rule p(1) :- Int64.gt(2, 1)                       (control)        1   (untouched)

WHO DELIVERED WHAT.
 * 36f16461 (J38JE, 2026-08-22) -- item 1 at the GOAL position (`op_reducible_in_rule_body`), and item 3, which turned out MOOT rather than answered: `push_and` gave `&` a real conjunction reading and DELETED WI-1046 refusal outright instead of narrowing it, so the operand-TYPE predicate this ticket proposed was never needed.
 * WI-20260826-VPEWK (today) -- the OPERAND row, and item 2.

TWO CORRECTIONS TO THIS TICKET OWN TEXT, both measured while delivering VPEWK.
 * THE DIAGNOSIS WAS WRONG. "A rule body reduces a BODIED operation and a resolver BUILTIN, and nothing else" was true when written and stopped being true at 36f16461. But the deeper claim -- that the goal position works for host ops -- was never true either: `:- Bool.and(true, true)` answers 1 through the CONNECTIVE reading (position-directed to `anthill.kernel.and`, resolved by `push_and`), not a host call, and it answers 1 with VPEWK entire change backed out. For a NON-connective host op like `String.contains`, BOTH positions were broken. J38JE widened the goal-side ENTRY gate but the relational view it admits routes to `eq(f(args), true)` -- into the operand path -- so that widening was INERT for every host op except the three connectives, which never take the route. The commit message rows crediting it (":- Bool.not(false) nothing -> 1") were the connective reading.
 * ITEM 2 DID NOT HOLD FOR FREE, which is exactly what this ticket asked to have CONFIRMED ("A host fn effect row is declared the same way, so the same clause should apply -- confirm it does"). It did not. The goal-side reason is "an effectful body is not a logical relation, and the eval bridge empty effect registry would suspend on one anyway" -- the second half is what makes it self-enforcing for a BODIED op, which RAISES its effect while the bridge runs the body. A HOST function raises nothing; it is opaque Rust that simply runs. MEASURED: a fixture mapping two operations to the SAME host function, one pure and one `effects {Error}`, answered 1 for BOTH. VPEWK added the effect clause; the pure one answers 1 and the effectful one residualizes. So this ticket item 2 was the right question and the answer was NO.

ONE ACCEPTANCE CLAUSE IS NOW UNSATISFIABLE and is superseded rather than met: "WI-1046 refusal still fires with its 6.6 message on `l(?x) & r(?x)`". That refusal was deleted by 36f16461 and the row answers 1. The rest of the acceptance -- both polarities on the Bool rows, `Int64.gt` in both positions, a BODIED Bool op bare goal, an effectful op declining the route -- is met and driven at `wi_vpewk_host_op_operand_test` and `wi_j38je_boolean_goal_test`.

THE PINNED ROW THAT CARRIED THIS TICKET ID HAS FLIPPED. `wi_j38je_boolean_goal_test.rs` asserted `answers(j38jeh.pand(1)) == 0` with the message "a HOST-BACKED op does not reduce in a rule body: WI-20260822-ZJZS7"; it now asserts 1 and names VPEWK. The stale bullet above it -- which claimed host ops are inert in a rule body AND that this is why `a & b` is refused, both falsified by the commit that landed in J38JE own ticket -- is corrected in place rather than deleted, so the history stays readable.

