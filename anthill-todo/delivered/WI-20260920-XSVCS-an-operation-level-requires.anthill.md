## Attributes

- id: WI-20260920-XSVCS-an-operation-level-requires
- created: 2026-09-20T20:31:56Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-21T10:45:22Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN OPERATION-LEVEL `requires` FORWARDED THROUGH A GENERIC CALLER IS NOT CHECKED, AND THE PROGRAM DIES `Internal` AT RUN TIME.

MEASURED, this session, driven end to end:

  sort TT
    sort T = ?
    operation valueOf() -> Type          -- body-less
  end
  sort Boom
    entity boom(why: String)
    provides TT[T = Boom]
    operation valueOf() -> Type = Boom
  end
  operation tyOf[B](x: B) -> Type requires TT[T = B] = TT.valueOf()
  operation mid[U](y: U) -> Type = tyOf(y)          -- NO requires, loads clean
  operation direct() -> Type = tyOf(boom("x"))      -- => Boom
  operation viaMid() -> Type = mid(boom("x"))       -- => Err(Internal(...))

Load: 0 errors. `direct()` answers `Boom`. `viaMid()` answers
EvalError::Internal("DeferToRequirement: requirement param `__req_tt` not bound in caller
frame (running `tyOf`, requires-chain owner `tyOf`; frame binds [])").

WHY THAT IS THE BAD KIND OF FAILURE. An `Internal` is not a `Raised` payload, so no
handler sees it and the caller cannot catch it; in a debug build it is an ABORT from a
program the typer accepted. WI-20260917-NR6FJ states exactly this consequence for its own
route and put the refusal at the CALL, at load, 'where the typer has both'. This is the
SAME defect class one route over: NR6FJ refuses a call whose callee `requires` names a
CONCRETE carrier providing no such spec; this is a call whose callee `requires` names a
type parameter OF THE CALLER, which the caller can neither construct nor forward because
it declared no such clause.

WHERE IT IS, AND THE MEASURED REASON IT IS SILENT. `build_op_scoped_dicts`
(kb/typing.rs): when `build_dep_projection` yields `None` the slot is left unfilled and
the call proceeds. Only two outcomes escape: an `Ambiguous` tie is raised, and a
`NoMatch` at a PINNED carrier is PARKED (WI-1102). Everything else is a deliberate silent
absence, and the site says why: '29 stdlib bodies that have a chain and never read it'.
That reason is real — a body MAY declare a requirement it never reads, and refusing those
would break the stdlib.

SO THE TICKET IS THE DISCRIMINATION, not the refusal. What separates 'declared and never
read' from 'declared, READ, and unfilled'? Candidates, none measured yet:
 (a) ask whether the callee's body actually reads the slot — the information exists (the
     callee's typed body carries its DeferToRequirement classifications) but may not be
     available yet when this call is typed, which is the ordering WI-1102's park exists
     to dodge; the same park could carry this;
 (b) refuse only when the carrier is a type parameter OF THE CALLER (a rigid), leaving
     every other unsuppliable dep alone — narrow, and exactly the shape driven above;
 (c) make the eval-time fault a located, CATCHABLE error rather than `Internal`, and
     accept that this class is caught late.

WHAT IS ALREADY DECIDED AND MUST NOT BE RE-LITIGATED. WI-20260919-N31XX closed this for
`anthill.reflect.TypeValue` ONLY, and for a reason specific to it: `type_value()` is
NULLARY, so the dispatching dictionary is the only carrier of its answer and an unfilled
slot is never the benign 'declared and never read' case. That leg is narrow on purpose and
its acceptance row asserts BOTH halves — the TypeValue shape refused, the plain-spec shape
still loading — precisely so this ticket's scope stays visible. Whatever lands here should
SUBSUME that leg or say at its site why it does not.

FIRST STEP: census. How many call sites in stdlib, anthill-stl, examples and the test
corpus forward an unsuppliable op-level dep? Of those, how many name a caller rigid, and
how many of THOSE have a callee that reads the slot? The answer decides between (a) and
(b), and it is the same shape of measurement WI-20260919-BQHGD ran for 065 §6.

ACCEPTANCE: the `viaMid` program above refused at LOAD, at the call, with a message
naming the caller and the clause to add; a control where the caller DOES declare the
clause that loads AND answers `Boom`; the 29 declared-never-read stdlib bodies still
loading, asserted rather than assumed; and N31XX's plain-spec control row updated to
whatever this decides. Full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-09-21T10:45:17Z — feedback — user

DELIVERED. The gate is (b) — the carrier is a type parameter OF THE CALLER — carried on (a)'s machinery: WI-1102's park, decided against `op_body_reads_op_requirement_slot` once every body is typed. The census chose it.

THE CENSUS (the ticket's FIRST STEP), instrumented at `build_op_scoped_dicts`' `projected.is_none()` site and drained in `report_unsuppliable_requirements` where the read predicate is safe to ask. Full workspace run, rows deduped: 57 distinct unfilled op slots.
  31  body READS the slot and the program stays green — all concrete carriers, supplied by routes this ticket does not touch. This is the population that rules out "refuse every unfilled slot whose body reads it".
  18  body never reads it — the declared-and-never-read class `build_op_scoped_dicts`' header measures at 29 stdlib bodies.
   4  carrier is a caller RIGID. Every one of them is this defect.
The 4: `test.n31xx.twobad` (065's own forward, still refused by 065's arm), `test.n31xx.othersp` (the same shape over a plain spec — the control this ticket was told to update), `test.xsvcs.fwd` (the ticket's program), and `test.wi416.Coll.contains`.

THE FOURTH ROW WAS NOT A TEST, and it is the reason the census was worth running. `anthill-cli/tests/fixtures/check/wi416-cross-sort-member.anthill` calls `List.contains(items, x)` on `Coll`'s own `T`; `List.contains` declares `requires Eq[T]` and its body reads it (`eq(head, x)`). It has loaded clean since WI-416 and would have died `Internal` had anything ever called it. Its own test asserts "typecheck OR a clean diagnostic, never crash", so it stays green on the diagnostic — and the shape is now a row in `wi_xsvcs_op_requires_forward_test`, carrier repaired by the clause the refusal prints.

WHY THE CARRIER AND NOT THE READ. Reaching the site means `build_dep_projection` found no forward, so the caller's composed chain covers nothing. A caller rigid is then unfillable from anywhere: not ground, so no provider can be constructed (that is WI-1102's case, which the same `match` takes first); not open, so it is not the WI-415/418 gap a later, more pinned call site still resolves. The caller's frame is the only possible supplier and it declared no slot.

STILL PARKED. "Nothing can fill it" and "the callee needs it filled" are different questions and only the body answers the second — `a_slot_the_callee_never_reads_still_loads_and_answers` is that half, driven to an ANSWER rather than to a load.

065 IS NOT SUBSUMED, and says so at its site. `type_value_forward_unsuppliable`'s arm stays ABOVE this one and RAISES: `type_value()` is nullary, so no body holding the evidence can fail to read it and there is nothing to wait for; it also reaches deps this does not (a `TypeValue` whose carrier is not a caller rigid) and sites this does not (`park` is `None` for a builtin callee and for a non-operation caller). The shape they share keeps 065's message. N31XX's plain-spec control row flips from "loads" to "refused" and now asserts the OTHER arm's message plus `!contains("proposal 065")`, so the two arms stay distinguishable from the test side.

THE MESSAGE names the caller, the parameter and the clause, rendered in the CALLER's spelling (`TT[T = U]`, not the callee's formal `TT[T = tyOf.B]`) and pointing at the declaration that can carry it — the OPERATION for a bracket param, the SORT for a sort param. Both tests read the clause back OUT of the refusal and paste it verbatim, so the rows measure the message and not just the check.

BACK-OUTS RUN, not read — each mutation applied on its own over the whole `wi_tests` binary (4828 rows):
  rule off (`caller_rigid_carrier` -> None)  4 red, exactly the census's four, nothing else in the binary moves.
  READ gate off                              5 red. Only one is this ticket's; the other four — wi1102's own `control_a_body_that_never_reads_the_slot_still_runs`, wi1119, wi201, wi855 — are the gate's PRE-EXISTING population. I had written "1 red" from reading and it was wrong; the measured number is the better statement, because it says "declared and never read must keep loading" is not a rule invented here to excuse this change.
  sort-parameter half off                    1 red, the WI-416 row, whose carrier is a sort param and not a bracket.

/code-review (high) raised two, both fixed inline:
  * the printed clause could contain a binding it cannot name — a two-parameter spec with one element a body skolem would print `<term#18340>`, advice that does not parse. Now every binding must be a caller parameter or a GROUND type or no refusal is parked at all (a refusal withheld, never a wrong value). 0 corpus rows; stated as unmeasured in the test file's doc rather than left to be discovered.
  * `impl_parent_of_op` where the SORT was meant — WI-956's own consolidation. Now `impl_parent_sort_of_op`.

SPEC: §5.2 gains the rule as the abstract half of WI-1102's exclusion; §8.4's 065 paragraph gains the cross-reference and the reason its arm survives.

ACCEPTANCE: `rustland/scripts/test.sh` full workspace green. scaland `sbt testFull` (after `sbt shutdown`) 578 passed / 0 failed plus 34 passed / 1 skipped — real counts, not the stale-server zero CLAUDE.md warns about.

NOT DONE, deliberately: the ticket's option (c), turning the eval-time `DeferToRequirement` fault into a located catchable error. The load refusal closes the rigid class; the concrete-carrier and open classes can still reach that raise, and re-shaping `EvalError::Internal` is a separate change with its own blast radius.

