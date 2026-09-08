## Attributes

- id: WI-20260907-0QV5A-a-match-arm-guard-is-never
- created: 2026-09-07T07:26:00Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-08T05:05:10Z

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

## Changes

### 2026-09-08T05:04:58Z — feedback — user

DELIVERED. A guard is evaluated after its arm's pattern matches and before its body is
entered; a false one falls through to the NEXT arm with the arm's bindings discarded;
running out of arms raises the same `Error[MatchFailed]` an unmatched scrutinee gets.

THE MECHANISM. `AwaitState::MatchGuard` (`eval/frame.rs`) is its own suspend state — a
guard is an arbitrary expression that may call an operation, so the arm scan cannot stay
synchronous once it reaches one. `eval/eval.rs::scan_match_arms` is the ONE scan both
states enter: `MatchDispatch` when the scrutinee arrives, `MatchGuard` when a guard
answered `false` and the scan resumes at the arms AFTER the declining one, carrying the
already-computed scrutinee so nothing is re-evaluated. The arm's pattern bindings go on
the GUARD'S CHILD FRAME ONLY — that is what makes the fallthrough discard them for free
(delivery pops that frame) and what keeps them out of a later arm's environment. The tail
is split only on the guarded path, so an ordinary `match` allocates nothing it did not
before.

A non-`Bool` guard is `EvalError::TypeMismatch { expected: "Bool" }`, the same shape the
`if` condition gets, not an `Internal`: Q0093's `boolean_position_error` refuses one at
LOAD for a source match, but `term_to_occurrence` rebuilds an `Expr::Match` from a reflect
`Term` and never passed that check. NOT DRIVABLE from surface source, and said at its site
rather than credited.

FOUR NEIGHBOURS THE CHANGE DESYNCED, repaired here because each was a SECOND answer to "is
this arm taken?" that was RIGHT while eval's answer was "always". Each has one row and one
back-out:

  * `body_specialize::folded_call_match` — the SLD case split enumerated a guarded arm as
    an unconditional alternative. Backed out, `Ops.rank(?h) = 1` answers 1 DEFINITE
    solution binding `?h` to `warm`, on a program where evaluating `Ops.rank(warm())`
    RAISES. It declines the whole unfold now, as `select_arm` beside it already did. The
    `cool` query suspends too — completeness lost, soundness kept, which is the trade that
    function's own doc states.
  * `typing::collect_covered_entities` — exhaustiveness counted a guarded arm as covering,
    so the check promised an arm for a value that now raises. A guarded arm covers nothing
    now, the same reading a written `: T` annotation already gets. Backed out, the guarded
    `enum` program loads clean.
  * `persistence/print.rs` — the renderer dropped the guard, so `match n { x => "one"; _
    => "other"; }` was the render of BOTH the guarded program and the guard-free one.
  * `anthill-cpp-gen::lower_match_branches_node` — emitted the tag check alone, so the
    generated C++ took an arm the interpreter declines. REFUSED now: the chain's last
    branch is its catch-all, so a guarded final arm has no fallthrough to lower to, and
    the exhaustiveness check cannot supply the coverage (it only diagnoses ENUM
    scrutinees). Backed out, it emits
    `(std::holds_alternative<warm>(h) ? [&]() { auto a = std::get<warm>(h).heat; return a; }() : 0)`
    with `never()` nowhere in it.

GUARD-AWARE ALREADY, checked rather than assumed: `select_arm` (declines), WI-537's
`match_arm_gamma_facts` (no negation from a guarded earlier arm), `flow_derive` (merges
the guard's effect row), `simp_rewrite` (rewrites it structurally),
`load::const_node_is_pure` (walks it), smt-gen's cache key (hashes it through
`for_each_child`).

`/code-review` (high) FOUND TWO, both in cpp-gen, both fixed and 1:1 measured:
  * the refusal was a BARE `CppCodegenError`, which WI-891 makes FATAL — one guarded arm
    anywhere in a KB would have emitted no C++ for any other operation or sort. It is
    `ctx.capability_gap(...)` now, degrading the ONE method to a build-breaking
    `static_assert` while the sibling operation still emits. Every refusal beside it
    already used that channel.
  * `node_references_name` walked an arm's scrutinee and body but not its GUARD, so
    `check_recursive_lambda_node` was blind to a binder referenced only from a guard —
    the one guard-blind reader my own census missed. Drivable because that check runs
    before lowering, so the two refusals differ by message.

TESTS. `wi_0qv5a_match_arm_guard_test.rs`, 11 rows. On the CORE back-out (the scan enters
a matched arm without consulting its guard) 7 fail and 1 passes by design — the unguarded
control, which is what says the scan was rewritten without moving ordinary matching. Its
three neighbour rows fail one-for-one on their own back-outs (all three at once: 8 pass /
3 fail). `anthill-cpp-gen/tests/wi_0qv5a_guarded_arm_refusal_test.rs` carries the cpp-gen
pair — the refusal and the review's two findings — each 1:1 on its own back-out.

THE PIN IS FLIPPED, NOT DELETED, as the ticket asked.
`wi_q0093_type_value_occurrence_matrix_test::a_match_arm_guards_type_value_is_classified_-
and_validated_at_load` asserted `pick(7) == "one"` with a note saying the assertion would
fail when this landed. It did; the eval half now DRIVES the guard family — a type value
written in a guard reaches `is_modifiable` at run time and the answer picks the arm, in
both directions over one program. Both of its type values are written APPLIED on purpose:
a BARE one would be classified by umbrella A's own `bare_name_denotes_type` and would move
the row out of the "survives the first back-out" group its file header lists it in. That
file's own back-out was RE-RUN and is unchanged at 15 fail / 9 pass.

SPEC. `docs/kernel-language.md` §4.8 states the runtime rule — the guard runs, a false one
falls through, exhaustion raises, a guarded arm covers nothing, the guard's effect row is
the match's — and names the three readers realigned with it.

ACCEPTANCE.
  * cargo-test: full workspace green.
  * scaland-sbt-test: 541 total / 539 passed / 2 failed — `BootstrapTest`, on
    `field.anthill`'s `requires Ring` import. VERIFIED PRE-EXISTING: a HEAD worktree gives
    the identical 541/2/539, and nothing outside `docs/` and `rustland/` is touched.
    Scaland has no `match` IR and no evaluator (its "guard" hits are effect-row guards),
    so there is nothing to port.

`cargo fmt --all -- --check` reports diffs in ~40 files, none in any line this change
touches — the pre-existing drift `rustfmt.toml` documents (`anthill-core/tests/` is 118
unformatted files and deliberately not a CI gate). The two NEW test files were formatted
individually and verified through the real `cargo fmt --check`.

