## Attributes

- id: WI-20260829-6RBPD-diagnostics-an-op-return-type
- created: 2026-08-29T10:18:57Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T10:18:57Z

- acceptance: cargo-test, scaland-sbt-test

## Description

DIAGNOSTICS: an OP-RETURN type mismatch carries NO SPAN, so the commonest type error in the language points at no line. Found by the WI-20260829-ARQ5X capability matrix.

MEASURED, four errors through the same loader, the first two unlocated and the last two located:

  operation c() -> Int64 = "x"
    -> type mismatch in c.return (op-return): expected Int64, got String            NO SPAN
  operation c() -> Set[T = Int64] = {1}
    -> type mismatch in c.return (op-return): expected Set[T = Int64], got Int64    NO SPAN
  operation d(v: Int64) -> Int64 = v
  operation c() -> Int64 = d("x")
    -> 5:28: type mismatch in d.v (op-arg): expected Int64, got String              LOCATED
  operation c() -> Int64 = (1).nosuch
    -> 4:28: type mismatch in ...Int64.nosuch: ... no such member (dot dispatch)     LOCATED

So the location machinery works and this one path does not use it. `operation c() -> Int64 = "x"` is about as ordinary as a type error gets -- a body that does not match its declared return -- and in a file of any size the author is told only the operation's name.

WHY IT IS WORTH ITS OWN ITEM rather than a line in the matrix. Every OTHER verdict in `typer_capability_matrix_test` asserts a refusal is LOCATED, because an unlocated diagnostic is the difference between a usable error and a hunt; this one path cannot meet that bar, so the matrix records it with `Verdict::RefusesUnlocated` citing this ticket, and that cell FAILS when a span appears -- which is the signal to flip it to `RefusesLocated` and close this.

WHERE TO LOOK: the op-boundary return check in `check_operation_bodies` (typing.rs) builds `TypeErrorContext::OperationReturn { op_name, surface }` and the `types_compatible` failure it raises. The body occurrence is in hand at that point (`result.node`), so its span is available -- compare with the op-arg path, which threads one. Whether the right span is the whole body or the specific sub-term that disagrees is the design question: the whole body is trivially available and already better than nothing; the disagreeing sub-term is what the op-arg path manages and is what an author actually wants.

CONTROL FOR WHOEVER FIXES IT: the two located rows above must stay located and keep their current spans -- this is a change to one raise site, not to the span plumbing.

