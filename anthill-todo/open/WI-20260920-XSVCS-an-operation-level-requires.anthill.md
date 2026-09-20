## Attributes

- id: WI-20260920-XSVCS-an-operation-level-requires
- created: 2026-09-20T20:31:56Z

- status: Open
- status_agent: claude
- status_at: 2026-09-20T20:31:56Z

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

