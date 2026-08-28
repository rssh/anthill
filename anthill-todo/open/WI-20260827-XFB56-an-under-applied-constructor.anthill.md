## Attributes

- id: WI-20260827-XFB56-an-under-applied-constructor
- created: 2026-08-27T23:09:29Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T23:09:29Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN UNDER-APPLIED CONSTRUCTOR IN AN OPERATION BODY BUILDS A VALUE NOTHING MATCHES, because the evaluator does the positional→named desugar but NOT the loader's ABSENT-FIELD FILL. The operation answers nothing, definitely, so NAF over it concludes -- the same unsoundness shape as WI-20260827-T2470 and a DIFFERENT axis.

MEASURED 2026-08-27 on the tree with T2470's fix in. Every row answers (0, 0):

  sort Two
    entity two(a: Int64, b: Int64)
  end
  sort OptF
    entity of(a: Int64, b: Option[T = Int64])
  end
  sort C
    operation f()  -> Two  = two(1)      -- POSITIONAL, under-applied
    operation g()  -> Two  = two(a: 1)   -- NAMED, under-applied
    operation h()  -> OptF = of(1)
    operation i2() -> OptF = of(a: 1)
  end
  rule r1(1) :- C.f()  = two(a: 1, b: 2)   -> no solutions
  rule r2(1) :- C.g()  = two(a: 1, b: 2)   -> no solutions
  rule r3(1) :- C.f()  = two(a: 1)         -> no solutions
  rule r4(1) :- C.g()  = two(a: 1)         -> no solutions
  rule r5(1) :- C.h()  = of(a: 1)          -> no solutions
  rule r6(1) :- C.i2() = of(a: 1)          -> no solutions

IT IS NOT THE POSITIONAL AXIS, AND r2/r4/r6 ARE THE CONTROL THAT SAYS SO. Those three write the constructor with NAMED arguments, so `pos` is empty and T2470's desugar block (`if !pos.is_empty()`) cannot run at all -- yet they answer nothing exactly like their positional twins. The defect is orthogonal to the spelling and PRE-DATES T2470.

THE MECHANISM, stated as a hypothesis and NOT traced. docs/design/entity-term-mapping.md's Rule 3 ("Fill absent named fields", `kb/load.rs`) says every unprovided named field of a registered entity is filled so that all facts and patterns of one functor index UNIFORMLY -- a fresh var in a pattern position, and since WI-716 `none()` for an absent OPTIONAL field in a value position. So a rule body's `two(a: 1)` becomes `two(a: 1, b: ?)`, named_arity 2. `finish_constructor` (`eval/eval.rs`) and `anf_flatten` (`kb/resolve.rs`) do only the positional→named half, so the evaluated twin stays named_arity 1, and `unify_concrete`'s `na != nb` fail-fast (`kb/resolve.rs`) decides the equation FALSE before comparing anything. Verify before fixing.

WHICH HALF FILLS WHAT IS THE FIRST QUESTION AND IT IS NOT OBVIOUS. An operation body is a VALUE position, so WI-716 says an absent OPTIONAL field is `none()` there and not a wildcard -- `of(a: 1)` should build `of(a: 1, b: none())`, which is a different value from `of(a: 1, b: ?)`. An absent REQUIRED field is a fresh var under Rule 3 wherever it appears, but a fresh var in an evaluated VALUE is a different thing from one in a pattern, and whether an operation body may build a value with an unbound field at all is the question this ticket has to answer before it can copy the loader's rule. Do not assume the loader's branch transplants.

HOW IT WAS FOUND: /code-review on WI-20260827-T2470's delivery, which named it as "Rule 6 claims a parity it does not have" -- that ticket added `finish_constructor`/`anf_flatten` to the doc's rule list as new PRODUCERS of the canonical form, and they implement Rule 1's desugar but not Rule 3's fill. The reviewer flagged that it may be unreachable if the typer refuses an under-applied constructor; it does not -- the program above LOADS CLEAN.

ACCEPTANCE: the six rows above driven as a test, with the chosen semantics asserted and r2/r4/r6 kept as the control that the fix is not on the positional axis; the OPTIONAL vs REQUIRED absent field decided explicitly and separately, with WI-716's value-vs-pattern rule read at its own site rather than assumed to transplant; a census of which producers now fill and which do not, stated against docs/design/entity-term-mapping.md's rule list; Rule 6's text in that doc corrected to say which halves it implements once it implements them; full workspace green via rustland/scripts/test.sh.

REFERENCE: `finish_constructor` (rustland/anthill-core/src/eval/eval.rs), `anf_flatten` (rustland/anthill-core/src/kb/resolve.rs), Rule 1/3/6 in docs/design/entity-term-mapping.md, the absent-field fill in rustland/anthill-core/src/kb/load.rs, `unify_concrete` (rustland/anthill-core/src/kb/resolve.rs), WI-716 for the value-vs-pattern split.

