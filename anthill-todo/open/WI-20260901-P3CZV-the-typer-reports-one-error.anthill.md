## Attributes

- id: WI-20260901-P3CZV-the-typer-reports-one-error
- created: 2026-09-01T17:04:03Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T17:04:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE TYPER REPORTS ONE ERROR PER OPERATION BODY, INNERMOST FIRST, so the error an author is
shown is often not the one that explains the program. Split out of WI-20260901-92VA4, whose
narrowing made the commonest instance visible.

MEASURED, three fixtures, all in an operation body over `sort P entity p(x: Int64) end`:
  operation get(q: P) -> Int64 = foo_access(q, q)
      -> "type mismatch in foo_access.apply: … got unknown functor — …" (the useful one)
  operation get(q: P) -> Int64 = foo_access(q, x)
      -> "type mismatch in x.name: expected resolved name, got unresolved"
         The functor `foo_access` is undeclared TOO, and is never mentioned.
  operation get(q: P) -> Int64 = aaa_no(bbb_no(q))
      -> ONE error, for `bbb_no` only. Two independent undeclared functors, one report.

So it is not a functor-versus-argument precedence: it is one error per body, innermost
first, and every other fault in that body is invisible until the first is fixed.

WHY IT MATTERS MORE AFTER WI-20260901-92VA4. A hand-written `field_access(q, x)` used to be
silently lowered as `q.x`; it is now correctly refused — but the refusal an author sees is
"x: expected resolved name, got unresolved", which blames the field name and never says that
`field_access` is the undeclared name. `field_access(q, q)` gets the good message, and that
is the shape `wi92va4_written_accessor_test` has to drive the refusal through. The
diagnostic 92VA4 improved is therefore reachable only when the argument slot happens to be
clean.

THE RULE BODY DOES NOT BEHAVE THIS WAY, which is what makes it a defect rather than a
design: `check_rule_body_goals` reports EVERY undefined goal, deduped by (functor, span),
and `undefined_rule_body_goal_message` names each one. Two positions, two policies.

NOT DIAGNOSED — this ticket names the SYMPTOM and the fixtures, not the mechanism. First
step is to find where the operation-body type check stops: whether it is a `?` on the first
`TypeError`, a single-error return type, or a dedup. Do NOT assume it is the argument-before-
functor ordering; the third fixture above rules that out.

CARE REQUIRED: this changes how many errors a program reports, so a large number of existing
tests assert `errs.len()` or index `errs[0]`. Census those before choosing a shape — a fix
that reports more is a corpus-wide change, and one that merely REORDERS may be enough for
the case above and much cheaper.

ACCEPTANCE: an operation body with two independent faults reports both, or reports the one
that explains the program and says at the site why the other is withheld; drive the
`foo_access(q, x)` fixture and assert the FUNCTOR is named; say which tests fail when the
change is backed out, and which pass either way. cargo-test green via
rustland/scripts/test.sh.

