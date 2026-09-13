## Attributes

- id: WI-20260913-2858G-a-host-function-that-calls
- created: 2026-09-13T19:40:02Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-13T22:56:04Z

- acceptance: cargo-test, scaland-sbt-test

- tags: eval

## Description

A HOST FUNCTION THAT CALLS BACK INTO THE INTERPRETER FROM INSIDE AN ANTHILL BODY FAULTS `Internal("deliver: parent frame had no awaiting state")` — a nested `Interpreter::call` runs on the LIVE activation stack, and its success path delivers PAST ITS OWN FLOOR into the caller's frames.

MEASURED (WI-20260830-7MK73, pinned by `attempt_from_the_host_dies_inside_the_evaluator_today` in rustland/anthill-core/tests/guardians_test.rs). `guardians.attempt` — `let p = h.render_task(…)` then `chk.check(h.generate(llm, p), spec)` — called from a host with fake carriers dies with that error. Every host binding on its path re-enters: `guardians_generate` calls `interp.call("guardians.Llm.complete")`, `guardians_check` calls `KB.loaded` and `guardians.gate`. The SAME bindings, called from the host TOP LEVEL with no anthill frame beneath (the carrier chain `render_task` → `generate` → `check` driven one call at a time), answer correctly — which is why `one_round_of_the_generation_loop_answers_the_same_verdict` drives the carriers and not `attempt`.

THE MECHANISM, READ FROM THE CODE, NOT YET ISOLATED BY A MINIMAL REPRO:
 * `Interpreter::call` → `invoke_op_with_requirements` pushes the callee's frame onto `self.stack` and runs the trampoline there; a builtin invoked mid-`step` has live parent frames beneath it.
 * `deliver` (eval/eval.rs) answers `StepOutcome::Done` ONLY WHEN THE STACK IS EMPTY. On a nested run it pops the callee's last frame, finds the CALLER's frame on top — mid-`step`, awaiting nothing — and `awaiting.take()` is `None`: the exact error.
 * `run_inner` already computes a `floor` (proposal 027.4) — but uses it only to bound the reify-boundary scan and, in `run`, to truncate on the ERROR path. The success path ignores it.
 * `eval_node_isolated` states the hazard and avoids it: "a nested `run()` on the shared stack would wrongly drain those parents; swapping in a fresh stack confines `run()` to just this body." The `call` route has no such confinement.

TWO REPAIRS, AND THEY ARE NOT EQUIVALENT:
 (a) `deliver` answers `Done` when the pop reaches the run's floor rather than an empty stack — keeps one stack, so an outer `Error.reify` boundary stays visible exactly as 027.4's floor comment intends ("a builtin's `interp.call` pushes onto the live stack").
 (b) `call` swaps in a fresh stack when the live one is non-empty, as `eval_node_isolated` does — confines the run, but a raise escaping the nested call then crosses a Rust boundary rather than the activation stack, so what an outer `reify` catches may change.
Deciding between them is part of the work; 027.4's floor comment reads as intending (a).

WHAT THE ACCEPTANCE MUST NOT MISTAKE FOR THE FIX: making `attempt` pass. The guardians row is the motivating case, not the measurement — `attempt` may reveal a second defect once this one is gone.

ACCEPTANCE: a minimal repro in wi_tests — an anthill operation whose body calls a host function that calls `interp.call` on another anthill operation and uses the result — fails today with this error and answers the right value after the fix, with a CONTROL that the same host function called from the host top level answers both before and after; a nested call that RAISES inside an outer `Error.reify` boundary is caught by that boundary (or the ticket records why not); `attempt_from_the_host_dies_inside_the_evaluator_today` is then RED and is replaced by driving `guardians.attempt` in `one_round_of_the_generation_loop_answers_the_same_verdict`, or re-pinned on whatever `attempt` does next; full workspace green via rustland/scripts/test.sh.

