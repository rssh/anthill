## Attributes

- id: WI-20260908-H2GDZ-render-task-drops-tools-and
- created: 2026-09-08T14:43:35Z

- status: Open
- status_agent: user
- status_at: 2026-09-08T14:43:35Z

- acceptance: cargo-test

- tags: guardians

## Description

`render_task` DROPS `tools` AND `feedback`, SO THE REPAIR LOOP CANNOT CONVERGE. Split from WI-20260830-THZ8R part D, whose frame no longer applies and whose "blocked" finding is wrong.

MEASURED. `guardians_render_task` is registered at arity 4 (`rustland/anthill-core/tests/guardians_test.rs:384`) and reads `args[1]` alone:

    let spec = spec_name(interp.kb(), &args[1])?;
    let body = format!("Write an anthill implementation of {spec}.");

`tools` (`args[2]`) and `feedback` (`args[3]`) are ACCEPTED AND DROPPED, against a declaration that promises a prompt built from the trusted declarations.

WHAT IT COSTS, AND IT IS NOT TIDINESS. `guardians.attempt` is ONE ROUND of a repair loop whose next round feeds `Rejected`'s diagnostics back as `feedback` — `lib/harness.anthill` says so at `attempt`'s own declaration. With `feedback` dropped, every round renders the IDENTICAL prompt, so a rejected candidate is regenerated from exactly the inputs that produced it. The loop cannot converge, and no row notices, because every harness test asserts on a SINGLE round.

THE DEAD PARAMETERS ARE THE SMALLER HALF, and a reader of the signature cannot see them. The comment above the binding does record that the prompt is a stand-in ("this stands in with a fixed instruction and is the example's clearest remaining gap"); what it does not say is that two of the four parameters are accepted and thrown away.

NOT BLOCKED — CORRECTING THZ8R PART D, which stated "WHAT IS ACTUALLY BLOCKED, and it is one thing: `anthill.reflect` exposes no declaration-printer ... Until there is, a faithful `render_task` cannot be written in anthill OR in a host binding without reaching around reflect." MEASURED, THE PIECES ARE ALL THERE: `KB.operations(kb, sort) -> List[T = OperationInfo]` (stdlib/anthill/reflect/reflect.anthill:512), `OperationInfo(name, params, return_type, effects, requires, ensures, ...)` (:797), `term_to_string(t: Term) -> String` (:276 — already imported by `examples/guardians/lib/gate.anthill`) and `qualified_name(s: Symbol) -> String` (:211). The literal claim is true and weaker than it reads: no operation returns a declaration as SOURCE TEXT, and nothing here needs source text. A prompt needs a readable signature, and those four render one.

AND THE HALF THAT MATTERS NEEDS NONE OF IT. `feedback` arrives as `List[T = String]` and the body drops it; splicing it into the prompt is a string join. `tools` is the same shape. Only the "render the declarations back out of the knowledge base" ambition touches the reflect surface above, and that is an IMPROVEMENT ON A FIXED INSTRUCTION, not a precondition for one. So this is three sizes and the ticket must not be read as the largest:

  (a) splice `feedback` and `tools` into the fixed instruction — THE CONVERGENCE FIX, and a string join;
  (b) render the spec's signatures from `KB.operations` — the faithful prompt the declaration promises;
  (c) narrow the signature to the parameters the body uses — the honest fallback.

(c) IS A FALLBACK AND NOT A FIX, and the distinction is the whole point: dropping the parameters removes the dead-parameter defect and LEAVES THE LOOP BROKEN. Do not take it while (a) is a string join.

WHAT WOULD MEASURE IT, because "the prompt changed" is not the claim. A row that drives TWO ROUNDS: reject the first candidate, feed its diagnostics back as `feedback`, and assert the SECOND round's prompt DIFFERS from the first — with the control that an empty `feedback` leaves the two identical. Every harness row today asserts on one round, which is exactly why this is invisible; a one-round assertion passes both with and without the fix. `one_round_of_the_generation_loop_answers_the_same_verdict` and `checker_interp` are the harness to build on.

ADJACENT, NOT THE SAME. WI-20260908-MRG99 (the example never RUNS a generated agent) is the other half of the accepted path going untested, but it is different work on a different surface: that one needs host bindings for `Email.fetch`/`Email.send`/`categories_of`/`choose_recipient`; this one needs the prompt to depend on its inputs. Neither blocks the other.

WHY IT IS ITS OWN TICKET. THZ8R is framed as "divergences between `examples/guardians` and the ICTERI-2026 article"; the article is finished and its next version may diverge deliberately, so that frame is retired. Of its four parts, B shipped (`TrustLevel` is `Untrusted`/`Trusted`), C is dead and would revert MCKTE's `Source` seal if implemented, and A was a one-line change made inline (`is_minted` now uses `exists`). This part is the only one that was never about the article at all.

ACCEPTANCE: `render_task`'s output DEPENDS on `feedback` and on `tools`; a two-round row asserts the second prompt differs from the first, with a control pinning that an empty `feedback` leaves them identical; no parameter is accepted and dropped; the guardians suite green with every fixture still accepted or refused FOR ITS OWN REASON and diagnostic substrings unchanged.

