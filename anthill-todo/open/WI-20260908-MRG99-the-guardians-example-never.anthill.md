## Attributes

- id: WI-20260908-MRG99-the-guardians-example-never
- created: 2026-09-08T07:54:37Z

- status: Open
- status_agent: user
- status_at: 2026-09-08T07:54:37Z

- acceptance: cargo-test

## Description

THE GUARDIANS EXAMPLE NEVER RUNS A GENERATED AGENT, so every claim it makes is a LOAD-TIME claim. The pipeline generates and CHECKS; nothing executes an accepted `Triage`. Against CLAUDE.md's own rule -- "a test for a capability must DRIVE the capability: resolve the goal, call the operation, assert the value; 'it loads clean' is not evidence that anything works" -- the example's headline is untested at the level a reader assumes it is tested.

WHAT IS AND IS NOT DRIVEN TODAY. The 59 rows in `guardians_test.rs` drive REFUSALS well: each seal has a fixture that reds when the seal is backed out, measured. What none of them drive is the accepted path. `fixtures/agent/good.anthill` is asserted to LOAD; it is never called. `run_triage` (lib/spec.anthill) has a real body -- it mints a `Text[Trusted]` and calls `t.run(box, llm, wording)` -- and the only thing touching it is two wrapper sources that are themselves load-checked. So a body dispatching to the wrong operation, or a `Text.trusted` returning a malformed value, keeps the suite green.

WHAT IT WOULD TAKE, and this is the bulk of the work. Twenty-one operations in `lib/` are declared with no body; the harness registers five host names (`guardians_fake_complete`, `guardians_live_complete`, `guardians_render_task`, `guardians_generate`, `guardians_check`). An end-to-end run needs bindings for at least `Email.fetch`, `Email.send`, `categories_of` and `choose_recipient` -- fetch reading the deployment's `InMailbox` rows, send recording what it was handed so the test can assert on it. `one_round_of_the_generation_loop_answers_the_same_verdict` and `checker_interp` are the existing execution harness to build on.

WHAT IT WOULD CATCH THAT LOADING DOES NOT. Three things are known to be invisible today. (1) `fixtures/mailbox.anthill` stores unreduced OPERATION applications -- `untrusted(raw: "...")` -- where a `Text` value is declared, because `entity text` is `internal` and a fact is a term that is never evaluated; a real `Email.fetch` binding reading those rows would hand an agent a call term instead of a text. Nothing catches it: a nested entity field inside a fact is not type-checked (`check_entity_facts` visits only facts whose HEAD FUNCTOR is the constructor). (2) `ensures mentions_all(result)` is REFINED against the spec and never PROVED of a body (measured.md C13, WI-20260830-2FP2K) -- running the accepted agent over the fixture mailbox is what would show whether its report actually mentions every message. (3) `run_triage`'s hand-off of vouched text, which is the premise the whole trust design rests on.

NOT A SECURITY GAP, and the ticket should not be sold as one. Everything MCKTE closes is a load-time refusal and is measured as such; this is about the ACCEPTED half, where the example currently says "this program was permitted" and never says "and it works".

SUGGESTED SHAPE: one execution row that drives `run_triage` over `fixtures/agent/good.anthill`'s carrier against the fixture mailbox, asserting the `Report`'s `items` cover all five message ids and that `Email.send` was not called. Its CONTROL is `conceal.anthill`, the accepted agent that drops the injected message: driven, its report should MISS m5 -- which is what would turn C13 from a pinned gap into a measured one.

ACCEPTANCE: an accepted `Triage` is loaded and RUN end to end, and the test asserts on the resulting `Report` rather than on the absence of load errors. Existing rows stay green.

Split out of WI-20260829-MCKTE, whose scope is the refusals.

