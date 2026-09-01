## Attributes

- id: WI-20260901-P3CZV-the-typer-reports-one-error
- created: 2026-09-01T17:04:03Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T17:04:03Z

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

## Changes

### 2026-09-01T18:38:16Z — feedback — user

TICKET TEXT REPLACED 2026-09-01 (claude), on the user's question 'is it the first error that is reported?'. The answer is NO, and the original text's mechanism — 'ONE error per operation body, innermost first' — was wrong. It was filed from two fixtures (`aaa_no(bbb_no(q))` and `foo_access(q, x)`) that both happened to be ANCESTOR/DESCENDANT pairs, so a policy that only suppresses ancestors looked like a policy that reports one error. Two fixtures agreeing is not a mechanism; a third shape (siblings) inverted it immediately.

WHAT THE ID STILL SAYS is 'the-typer-reports-one-error', which is now the false claim. The slug is not editable; this note is the correction a reader reaches from it. The description above carries the six accumulation fixtures and the three ancestor-diagnostic rows with their control.

