## Attributes

- id: WI-20260822-WZX6B-the-test-suite-counts-resolve
- created: 2026-08-22T09:01:50Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-22T09:38:53Z

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

## Changes

### 2026-08-22T09:09:35Z — feedback — claude

CENSUS CORRECTED BEFORE STARTING: the population is 113, not 40. My first number came from a
loose one-line regex (`resolve(&[.*].*)\.len()`) which both over-matched on greedy `.*` and
MISSED every multi-line form — and the multi-line form is the common one (107 of 113 bind
the result to a variable, or return `kb.resolve(..).len()` from a per-file helper whose
`.len()` sits on the next line). Classified over all 209 `.resolve(` sites in
`anthill-core/tests`:
    .len()              113
    iter/first/index     56
    is_definite          21
    bound to a variable  12
    other                 7

PRODUCTION IS CLEAN, which narrows this ticket to what its title says. Every non-test
consumer already hand-rolls the check: `region.rs` (`.any(|s| s.residual.is_empty())`),
`cpp-gen/src/lib.rs` (`.filter(|s| s.residual.is_empty())`, with a comment saying a
floundered solution binds nothing), `stl/src/reflect/builtins.rs`
(`sols.len() == 1 && sols[0].residual.is_empty()`). The three `mod.rs` sites that looked
like production are inside `#[cfg(test)] mod tests`. So no wrong ANSWER ships from this;
what ships is a suite that cannot see one.

METHOD — MEASURE FIRST, EDIT SECOND. Rewriting 113 call sites and then running would
report a compile-and-pass, not a census. Instead `KnowledgeBase::resolve` is temporarily
made to `retain(|s| s.is_definite())`: one edit, and every test whose count depends on a
floundered answer FAILS AND NAMES ITSELF. That is the exact disagreeing population, and
it separates the two kinds of site the acceptance asks about without reading any of them
— a site whose goal is ground cannot flounder and stays green.

### 2026-08-22T09:38:52Z — feedback — claude

DELIVERED (2026-08-22). THE CENSUS WAS RUN, NOT READ, AND IT SAYS 5 OF 113 — the rest
agree because their goals are GROUND and cannot flounder.

THE INSTRUMENT, so this is re-runnable in three lines: make `KnowledgeBase::resolve`
(kb/resolve.rs) `retain(|s| s.is_definite())` on its result and run the full suite. Every
test whose count depends on a floundered answer then FAILS AND NAMES ITSELF. That is the
exact disagreeing population, obtained without editing or reading 113 call sites — and it
answers the acceptance's "fixed or documented" split by itself, because a site whose goal
is ground stays green.

FIRST PASS: 26 failures of 5476. Twenty-one are suites whose SUBJECT is the residual —
the instrument deletes what they test, and each already says so in its own assertion
message ("should residualize", "expected exactly one (residual) solution", "must DELAY
and residualize honestly", "yields a residual solution by default"). Five claimed a
DECISION while counting a suspension:

  wi939::list_contains_as_a_rule_body_goal
  wi939::set_contains_answers_over_the_symbolic_algebra
  wi939::set_equality_still_decides_by_membership      <- "DECIDES"
  wi884::bool_is_audited_and_ite_is_not_one_of_its_operations   <- a CONTROL
  wi818::sld_head_law_still_proves_once                <- "PROVES"

ONE IDIOM PRODUCED FOUR OF THE FIVE: `rule p(?m) :- <the real goal>, ?m = 1`, queried as
`p(?r)`. `=` is `PartialEq.eq`, a semantic equality TEST that NEVER BINDS (§8.3), so the
trailing conjunct suspends and the whole answer is `total = 1, definite = 0`. The count
being asserted was the suspension, not the goal's verdict.

THE CLAIMS WERE TRUE; THE FIXTURES WERE NOT. Measured before repairing anything — moving
the constant into the HEAD (`rule p(1) :- <goal>`, where head unification binds) makes
every one of them decide:
    List.contains([7], 7)                     total=1 definite=1     (9: 0)
    Set.contains({1,2}, 2)                    total=1 definite=1     (9: 0)
    Set.eq({1,2}, {2,1})                      total=1 definite=1     ({1} vs {9}: 0)
    holds(10)  (wi884's control)              total=1 definite=1
So four fixtures are repaired rather than reinterpreted, and wi884's counter now filters
to definite — it is the CONTROL whose own message reads "the control must answer, or
nothing below proves anything", and it had been answering with a suspension.

wi818 IS THE FIFTH AND IS DIFFERENT: it counts DERIVATIONS, not proofs. Its subject is
multiplicity — one derivation from the law + body pair, never two — and each derivation
contributes a solution whether or not it decides, so `.len()` is the right instrument
there and a definite-only count would measure something else. Left counting, and DOCUMENTED
at its site with a second assertion pinning that the solutions are NOT definite, so the
first cannot be misread as a proof. The obvious repair is unavailable and that is recorded
too: the arity+1 relational form (`head(cons(7, nil), ?r)`), which would bind through
`unify`, answers NOTHING for three of its four ops.

THE ERGONOMIC HALF. `common::query_unary` ALREADY RETURNED DEFINITENESS — every pair is
`(Value, is_definite)` — and callers were dropping the flag. Added
`common::definite_unary`, which keeps only the definite answers, with the measurement in
its doc; `query_unary` stays for the suites whose subject is a residual. One site was
already doing it by hand (`wi939`'s `cr3lit` row, `.filter(|(_, definite)| *definite)`)
and a blanket rename broke it — restored, and it is the evidence that the convention was
known and merely unergonomic.

THE REMAINING ~90 `.len()` SITES ARE NOT EDITED, deliberately: they were measured to
AGREE, because their goals are ground and cannot flounder. Editing them would be churn
with no measurement behind it. They will start disagreeing if a goal they drive gains a
suspending operand, and the guard against that is this ticket's instrument, which is
cheap enough to re-run.

VERIFIED: with the four fixtures repaired, the instrument re-run leaves 22 failures and
every one of them is a deliberate residual/derivation suite (wi884 now passes WITH the
instrument active, which is the proof its fix is real, not a re-baseline). Instrument
removed; clean suite 35 binaries, 5476 tests, 0 failures.

ALSO CORRECTED: the population is 113, not the 40 this ticket was filed with. See the
earlier feedback entry — the first number came from a one-line regex that missed every
multi-line form, and the multi-line form is 107 of the 113.

