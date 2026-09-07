## Attributes

- id: WI-20260907-0QV5A-a-match-arm-guard-is-never
- created: 2026-09-07T07:26:00Z

- status: Open
- status_agent: user
- status_at: 2026-09-07T07:26:00Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `match` ARM GUARD IS NEVER EVALUATED, so a guarded arm matches on its PATTERN alone.

MEASURED, with no type value anywhere in the fixture (found while pinning WI-20260824-Q0093's `matching` family, whose runtime half this makes undrivable):

  operation pick(n: Int64) -> String =
    match n
      case x | eq(x, 1) -> "one"
      case _ -> "other"

`pick(7)` answers "one". `Interpreter`'s `AwaitState::MatchDispatch` (eval.rs) clones `branch.guard` into its await state and then selects the first branch whose `match_pattern` succeeds; the guard is never read, never evaluated, and never reported. A guarded arm is therefore indistinguishable from an unguarded one at run time, on a program that loads clean — the silent-wrong-answer shape, not a missing diagnostic.

THE TWO LAYERS DISAGREE, which is what makes this more than an unimplemented feature. The TYPER already treats a guarded arm as conditional: WI-537's `match_arm_gamma_facts` deliberately contributes NO negation from a guarded earlier arm ("`case 0 | g -> …` matches only when g holds, so a later arm cannot conclude s ≠ 0" — `wi537_local_interpretation_test::match_guarded_earlier_arm_contributes_no_negation`), and the guard's own Γ is assumed for its arm. So the type-level reading of a guard is "this arm is conditional" while eval's is "this arm always matches", and the spec (§4.8, "A guard after `|` is checked only for that arm") states the first. WI-20260824-Q0093 also added a `Bool` DESTINATION check on the guard (`typing.rs::boolean_position_error`), so the slot is now type-checked as a condition it is not used as.

SCOPE. Evaluate each candidate arm's guard after its pattern matches and before its body is entered, and fall through to the next arm when the guard is false. This needs a suspend/resume state of its own — a guard is an arbitrary expression that may call operations, so the dispatch loop cannot stay synchronous — plus decisions this ticket owns:

  * arm FALLTHROUGH: a false guard must resume the scan at the NEXT branch with the pattern bindings discarded, and reaching the end must raise the same `raise_match_failed` an unmatched scrutinee does (WI-610), not silently take the last arm;
  * the guard's BINDINGS are its arm's pattern bindings (they are what a guard reads), and they must not leak into a later arm's environment;
  * EFFECTS: the guard's row is already merged into the match's effects by the typer (WI-537), so a guard that raises must behave as that row says rather than escaping the match;
  * a guard whose value is not `Bool` is a load error since Q0093, so eval may treat a non-`Bool` guard result as an internal error rather than a user-facing one.

DRIVING TESTS, not "it loads": each guard asserted in BOTH directions (the guarded arm taken when the guard holds, the next arm taken when it does not, over the SAME program), a later arm reached by a false guard on an EARLIER arm whose pattern matched, a guard that calls an operation (so the suspend/resume path is exercised rather than a constant folded in place), and the exhaustiveness end — every arm guarded and every guard false — reported as a match failure. State which rows fail when the change is backed out.

WHERE THE PIN IS TODAY: `wi_q0093_type_value_occurrence_matrix_test::a_match_arm_guards_type_value_is_classified_and_validated_at_load` asserts the CURRENT behaviour (`pick(7) == "one"`) with a comment saying that when this ticket lands the assertion fails and must be replaced by driving the guard family at eval. That row is the acceptance signal to flip, not a test to delete quietly.

