## Attributes

- id: WI-20260829-6RBPD-diagnostics-an-op-return-type
- created: 2026-08-29T10:18:57Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-21T00:33:39Z

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

## Changes

### 2026-11-21T00:19:55Z — feedback — user

MEASURED FIRST on 274a51b0 with the debug CLI (2026-11-20): 'operation c1() -> Int64 = "x"', '-> Set[T = Int64] = {1}', a let chain ending in a wrong value ('let k = n + 1' then '"tail"'), a body that is a wrong call, and two sorts each with 'operation f() -> Int64 = "a"' all printed 'path: type mismatch in <op>.return (op-return): ...' with no line:col; the two f's were one sentence. An if or match branch was already located (if.rule / match.rule at the branch), the op-arg and dot controls too. The let annotation's mismatch, the renderer's third channel (WI-801), was unlocated as well ('let r: String = 1' -> 'type mismatch in r.annotation (let-binding)', no span). FIX: the op-boundary conformance_error is given the span of the body's RESULT POSITION (op_bodies::result_position: the body as written, past its lets); the let annotation's is given the written value's span, read off the let occurrence. Both read the body as WRITTEN, not the typed tree: a @[simp] rule fired there keeps its RHS's span, the rule's file, while the error is stamped with the body's; found by /code-review and MEASURED, the typed value's span printed sb.anthill:4:25 for a mistake at 5:21. Now: '4:29' at "x", the 1 inside {1}, the let tail, the call, '13:30' / '16:30' for the two f's, the let value. ROWS: typer_capability_matrix_test: the braced-expression cell flipped to RefusesLocated; an_op_return_mismatch_carries_no_span became an_op_return_mismatch_is_at_the_bodys_value (five rows each asserting the exact line:col of the body's value, the op-arg and dot controls pinned to their positions); a_rewritten_value_is_reported_where_the_body_writes_it (two files); the judge split out of check_src (judge) so the self-tests hand it an unlocated message instead of relying on one the loader still raises. The 2VPHT docs that named the let annotation as the measured unlocated case are corrected. BACK-OUTS over the whole anthill-core (11356), one optimized build, a run-time switch each: control 0; op-return span None 2 (the row and the braced cell); op-return at the whole body 1 (the row, at the first let-tail case); let span None 1 (the row, at its case); the typed let span fails the two-file row (selected run). Families green on both carriers. /code-review high: 3 findings, 2 fixed (the typed span; a comment saying op-arg errors stand at the argument, they stand at the call), 1 skipped: abstracting_return_error and branch_leaf_abstracting_return_error (WI-401/457 sealing-return refusals at the same boundary) still build span: None; the branch-leaf walk owes each leaf its own span.

