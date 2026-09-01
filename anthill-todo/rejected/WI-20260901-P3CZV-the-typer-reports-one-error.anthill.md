## Attributes

- id: WI-20260901-P3CZV-the-typer-reports-one-error
- created: 2026-09-01T17:04:03Z

- status: Rejected
- status_agent: user
- status_at: 2026-09-01T18:48:55Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BROKEN SUBEXPRESSION SWALLOWS EVERY DIAGNOSTIC ITS ANCESTORS WOULD HAVE RAISED — including
the two that do not depend on it. Cascade suppression is right for a type-DEPENDENT ancestor
diagnostic and wrong for a type-INDEPENDENT one.

THIS REPLACES THE TICKET'S ORIGINAL TEXT, which said "the typer reports ONE error per
operation body, innermost first". THAT IS FALSE, and it was filed on two fixtures that
happened to agree with it. Errors accumulate freely — the user asked "is it the first error
that is reported?", and driving it says no:

  two(aaa_no(1), bbb_no(1))                        -> 2 errors, both siblings
  two broken operations in one file                -> 2 errors, both
  two(aaa_no(1), two(bbb_no(1), ccc_no(1)))        -> 3 errors, all
  a broken op body + a broken rule body            -> 2 errors, both
  aaa_no(two(1, 2))       (outer broken only)      -> 1 error, the outer
  aaa_no(bbb_no(1))       (both broken, nested)    -> 1 error, THE INNER ONLY

Only the ANCESTOR relation suppresses. Siblings, separate declarations and separate
positions are all unaffected.

THE SPLIT, and it is what makes this a defect rather than a design. Three ancestor
diagnostics, measured against the same broken child, with a control that proves each is
reachable when the child is clean:

  parent's own fault      fixture                                    reported
  ----------------------  -----------------------------------------  --------------------
  arity (2 params, 1 arg) `two(aaa_no(1))`                           child only
  op-return P vs Int64    `go() -> P = two(aaa_no(1), 2)`            child only
  op-return P vs Int64    `go() -> P = two(1, 2)`   [CONTROL]        THE OP-RETURN ERROR

  (`H` = `sort P entity p(x: Int64) end` plus `operation two(a: Int64, b: Int64) -> Int64 = a`.)

The control is the point: the ancestor diagnostic EXISTS and fires; a broken descendant is
what withholds it.

  * SUPPRESSING THE OP-RETURN MISMATCH IS CORRECT. The body has no type once the child
    failed, so "expected P, got …" would be invented.
  * SUPPRESSING `unknown functor` AND THE ARITY MISMATCH IS NOT. Neither reads the child's
    type: `aaa_no` is undeclared whatever its argument turns out to be, and `two(x)` is the
    wrong arity syntactically. Both are withheld anyway.

THE COST, and how it was found. WI-20260901-92VA4 narrowed the accessor gate so that a
hand-written `field_access(q, x)` is refused instead of silently lowered as `q.x`. The
refusal an author actually sees is "x: expected resolved name, got unresolved" — because `x`
is a descendant whose own name resolves to nothing, and the functor's INDEPENDENT
`unknown functor` refusal is swallowed. `field_access(q, q)` gets the good message, and that
is the shape `wi92va4_written_accessor_test` has to drive the refusal through. So the
diagnostic 92VA4 improved is reachable only when the argument slot happens to be clean.

THE RULE BODY DOES NOT BEHAVE THIS WAY: `check_rule_body_goals` reports EVERY undefined goal,
deduped by (functor, span). Two positions, two policies.

NOT DIAGNOSED BEYOND THE SHAPE. The suppression is structural — a child that fails to type
returns no type, and the ancestor's check is skipped or its result dropped — but the SITE was
not traced, and a grep for `cascade` / `suppress` / `already errored` in `typing.rs` finds no
such mechanism by name, so do not assume there is a flag to flip. `TypeHead::Error` (9 sites)
is a LEAD and nothing more. Trace it before choosing a shape.

THE SHAPE THAT IS PROBABLY RIGHT, stated so it can be argued with rather than discovered:
raise the type-INDEPENDENT checks (unknown functor, arity) BEFORE descending into arguments,
so they cannot be suppressed, and leave every type-dependent ancestor diagnostic suppressed
exactly as it is now. That adds errors only in programs that already fail to load.

CARE REQUIRED: this changes how many errors a program reports. Census the tests that assert
`errs.len()` or index `errs[0]` before choosing — a fix that reports MORE is a corpus-wide
change even when every added error is correct.

ACCEPTANCE: drive `foo_access(q, x)` and assert the FUNCTOR is named, with
`foo_access(q, q)` beside it as the row that already worked; keep the op-return control
green (a type-dependent ancestor diagnostic must STILL be suppressed, and a test that does
not check this would let a fix regress into noise); say which tests fail when the change is
backed out and which pass either way. cargo-test green via rustland/scripts/test.sh.

## Reason

Premise measured and found not to warrant work (user, 2026-09-01): the suppression returns one of several INDEPENDENT true errors rather than hiding a real one, it converges, the case that fires most is the one that should, and the motivating spelling has zero corpus sites. See the closing note for the fixtures and the one observation kept for a future ticket.

## Changes

### 2026-09-01T18:38:16Z — feedback — user

TICKET TEXT REPLACED 2026-09-01 (claude), on the user's question 'is it the first error that is reported?'. The answer is NO, and the original text's mechanism — 'ONE error per operation body, innermost first' — was wrong. It was filed from two fixtures (`aaa_no(bbb_no(q))` and `foo_access(q, x)`) that both happened to be ANCESTOR/DESCENDANT pairs, so a policy that only suppresses ancestors looked like a policy that reports one error. Two fixtures agreeing is not a mechanism; a third shape (siblings) inverted it immediately.

WHAT THE ID STILL SAYS is 'the-typer-reports-one-error', which is now the false claim. The slug is not editable; this note is the correction a reader reaches from it. The description above carries the six accumulation fixtures and the three ancestor-diagnostic rows with their control.

### 2026-09-01T18:48:54Z — feedback — user

CLOSED 2026-09-01 (user decision) — the premise was measured and does not warrant work. An
analogous ticket gets opened if a direct problem shows up.

WHAT THE TICKET FIRST CLAIMED, AND WHY IT WAS WRONG: "the typer reports ONE error per
operation body, innermost first". False. Errors accumulate — two sibling faults report both,
two broken operations report both, three faults on distinct branches report three, a broken
op body plus a broken rule body report both. It was filed from two fixtures that were both
ancestor/descendant pairs, so a policy suppressing only ANCESTORS looked like a policy
reporting only one error.

WHAT IS ACTUALLY TRUE: a broken DESCENDANT withholds the diagnostics its ANCESTORS would
have raised. Measured against one broken child, with a control proving each ancestor
diagnostic fires when the child is clean:
  arity (2 params, 1 arg)   `two(aaa_no(1))`                    -> child only
  op-return P vs Int64      `go() -> P = two(aaa_no(1), 2)`     -> child only
  op-return P vs Int64      `go() -> P = two(1, 2)`  [CONTROL]  -> the op-return error

WHY IT IS NOT WORTH FIXING, which is the user's own test applied to the evidence. The
question is whether the sequence HIDES a real error, or merely returns one of several real
ones. It is the second:
  * Nothing spurious is shown. In `field_access(q, x)` both faults are independent and both
    are true — `x` names nothing in ANY reading, and the functor is unresolved whatever `x`
    turns out to be. Neither is a consequence of the other.
  * Nothing is lost. Fix the child, recompile, the ancestor's error appears. It converges,
    and every message on the way is correct.
  * No case was found where the SHOWN error is spurious and caused by the parent. The shape
    would need an expectation to flow down and manufacture a child error; under an unresolved
    functor no expectation flows down at all. Looked for, not found, and not claimed.
  * The suppression that fires most is the one that SHOULD: an op-return mismatch has nothing
    true to say once the body has no type.
COST AGAINST THAT: reporting more errors is a corpus-wide change to every test asserting
`errs.len()` or indexing `errs[0]`.

AND THE MOTIVATING EXAMPLE HAS NO USERS. The confusing message needs a hand-written
`field_access(q, x)`; `q.x` is unaffected and answers 7
(`wi92va4_written_accessor_test::the_dot_form_still_lowers`). Corpus census: ZERO
hand-written short-spelling `field_access(` / `dot_apply(` calls in any `.anthill` file.

THE ONE OBSERVATION WORTH KEEPING, and it is a DIFFERENT ticket if it ever bites. The
"unknown functor" census cannot distinguish a forgotten import from a name that exists
nowhere, for a NAMESPACE-LEVEL operation. Driven: `lib.h` declares `operation helper(...)`,
`pr.f` calls `helper(n)` without importing it, and the message is byte-identical to the one
`zzz_nothing(xs)` gets — "no rule, fact, operation, entity, const or builtin is declared
under that name", while `lib.h.helper` is declared one import away. WI-565's `BareMemberCall`
already solves exactly this for sort MEMBERS (`length` -> "is a member of sorts IndexedSeq,
List, String; call it qualified"), and free-standing operations are the shape it does not
cover. The census wording predates this ticket — WI-1034 wrote it for rule-body goals and
WI-20260901-92VA4 propagated it to the operation body — so it is not a regression, but it is
where a future "the message did not help me" report should be pointed first.

