## Attributes

- id: WI-20260822-WZX6B-the-test-suite-counts-resolve
- created: 2026-08-22T09:01:50Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T09:01:50Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE TEST SUITE COUNTS `resolve(…).len()`, WHICH COUNTS FLOUNDERED ANSWERS AS ANSWERS.
40 sites do it; `is_definite` is mentioned in 17 of 497 test files.

THE API IS NOT AT FAULT AND DOES NOT DROP DELAYS. `Solution { subst, residual }` carries
the undischarged goals on the answer itself, `is_definite()` is `residual.is_empty()`,
and its own doc already states the rule: "a floundered solution must never be counted as
a definite answer … the codified form of the convention every honest consumer was
hand-rolling". `proof_verify` enforces it (WI-519). What is missing is not a mechanism
but its USE: `.len()` is the shortest thing to write and it is wrong wherever a goal can
suspend.

HOW IT BITES, measured while delivering WI-20260822-J38JE:
  rule cmp(?x) :- ?x = 42          asked as cmp(?r)   total=1  definite=0
  rule paren(?r) :- …, ?r = (?a & ?b)                 total=1  definite=0
  rule eqlit(1)  :- ft(?a), ?a = true                 total=1  definite=1   (ground: real)
`=` is `PartialEq.eq`, a semantic equality TEST that never binds (§8.3), so ANY fixture
of the form `?r = <expr>` with `?r` free suspends. The first row was a CONTROL in
`wi_j38je_boolean_goal_test` asserting "a constant `eq` operand is a value" — it had been
green for a suspension, and only went red once that file's helper was changed to count
definite solutions. A control that cannot fail is the defect this repo already has a
principle about; this is a way to write one by accident, and it is the DEFAULT way.

WHAT THIS TICKET MUST DECIDE:
 1. THE CENSUS AND ITS VERDICT PER SITE. 40 `.len()` sites is the population, and they
    are not all wrong: a test that drives a GROUND goal can never flounder, so `.len()`
    and the definite count agree and the site measures what it claims. The work is to
    separate those from the ones where a variable can stay free. Do it by MEASURING —
    run each with a definite-only counter and diff the counts — not by reading, because
    the sites that agree today are exactly the ones that will silently start disagreeing
    when the goal they drive gains a suspending operand.
 2. WHETHER THE DEFAULT SHOULD BE HARDER TO GET WRONG. Options: a shared
    `common::definite_answers(kb, pattern)` helper that the fixtures use (cheap, opt-in,
    leaves the trap in place for new code); or a `resolve_definite` on the KB that
    returns only definite solutions and makes the floundered ones an explicit ask
    (changes the API's shape, so the ergonomics move rather than the convention). Say
    which, and say what a test that WANTS to assert a flounder writes instead.
 3. WHETHER A FLOUNDER SHOULD BE LOUDER THAN A RETURN VALUE. WI-737 already treats an
    ungrounded residual as something to surface; decide whether a resolve whose only
    answers are floundered should be visible without the caller asking — at least in
    tests, where "green" is the whole signal.

ACCEPTANCE: the census is RUN, not read — every one of the 40 sites reported with its
`.len()` count and its definite count side by side, and every DISAGREEING site either
fixed or documented at its own site as deliberately counting suspensions. Say which tests
fail when the change is backed out. CONTROLS THAT MUST STAY GREEN: the suites that
legitimately assert a residual (`wi583_bool_op_goal_test::wi583_unbound_arg_in_bool_goal_-
suspends` asserts `!is_definite` and must keep passing), and `proof_verify`'s
definite-only contract (WI-519). cargo-test green via rustland/scripts/test.sh.

