## Attributes

- id: WI-20260828-0ZG83-a-binding-block-naming
- created: 2026-08-28T04:27:03Z

- status: Open
- status_agent: claude
- status_at: 2026-08-28T04:27:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BINDING BLOCK NAMING EMBEDDER-REGISTERED HOST FUNCTIONS PANICS EVERY QUERY OVER THAT PROGRAM, because building an interpreter validates the WHOLE binding-block set eagerly -- so a mapping the goal never touches aborts a goal that has nothing to do with it. `examples/guardians` is no longer CLI-queryable, and the panic is a PANIC and not a diagnostic.

MEASURED 2026-08-28 on the tree at 3c112e16, with a CONTROL that isolates the one variable. Same query file, same goal, same binary; the ONLY difference is whether `examples/guardians/lib` is also on the load path.

  -- ctl.anthill
  namespace ctl
    import anthill.reflect.{term_as_int, as_term}
    import anthill.prelude.{Option, Int64}
    import anthill.prelude.Option.{some}
    rule read(1) :- term_as_int(as_term(7)) = some(7)
  end

  CONTROL  anthill query -p ctl/ 'ctl.read(1)'
             -> true, 1 solution
  TEST     anthill query -p ctl/ -p examples/guardians/lib 'ctl.read(1)'
             -> thread 'main' panicked at anthill-core/src/kb/resolve.rs:7815:17:
                bridge_op_to_eval: internal evaluator error bridging
                `anthill.reflect.as_term`: internal evaluator error: broken binding
                block: operation_map names host function "guardians_render_task" for
                guardians.FileHarness.render_task, which the rust runtime does not
                provide.

THE GOAL NEVER MENTIONS GUARDIANS. It bridges `anthill.reflect.as_term`, and the abort is charged to a mapping in a different namespace for an operation the query does not call. The message already anticipates the confusion in its own last sentence -- "this error may surface at a call that has nothing to do with guardians.FileHarness.render_task" -- which is an accurate warning and not a fix.

WHY IT STARTED, and it is a consequence rather than a defect of the ticket that caused it. Before WI-880 the `anthill.reflect` surface was registered by hardcoded qualified name, so bridging an accessor built nothing and validated nothing. WI-880 (b6805994) moved all 26 onto `operation_map` -- which is what made a rule able to read a term at all -- and an `operation_map` is registered by BUILDING AN INTERPRETER, which validates every block in the KB before running anything. So the eager check has always been there; WI-880 is what put a bridge on the common path. Proposal 008 §2b recorded the effect the day it landed; nothing has owned it since.

THE POPULATION IS EXACTLY ONE PROGRAM, censused rather than assumed. Every `operation_map` host-function name outside `rustland/anthill-stl/anthill/` is one of five, all in two files:
  examples/guardians/lib/harness.anthill  render_task -> "guardians_render_task",
                                          generate    -> "guardians_generate",
                                          check       -> "guardians_check"
  examples/guardians/lib/llm.anthill      complete    -> "guardians_live_complete",
                                          complete    -> "guardians_fake_complete"
The only other match in the tree is `ordered_compare` in `wi1122_embedder_host_fn_test.rs`, which is a real `HOST_FNS` key and not an embedder name. So this is not a class with many members today -- it is one example -- but the SHAPE is the supported extension point, not a mistake: all five are registered through WI-1122's `KnowledgeBase::register_host_fn` by `rustland/anthill-core/tests/guardians_test.rs`, which is also the block's declared `artifact`. `examples/guardians/README.md` documents that arrangement, and WI-1122 requires `register_host_fn` BEFORE load. The suite is green because the harness registers them; the CLI has no way to.

WHY IT MATTERS BEYOND ONE EXAMPLE. Guardians is the worked example for proposals 064/two-flows and 008's intended first consumer (`examples/guardians/lib/safety.anthill`, a tier-1 rule over reflection facts). 008's whole point is that a rule can now read a term -- and the one program it wants to read terms IN is the one program where doing so aborts. An embedder shipping a library with a binding block hits this the moment any consumer runs a query, which is the general form.

QUESTIONS THIS TICKET MUST DECIDE, stated as the fork rather than as a chosen fix:
 (a) LAZY vs EAGER. Validate the mapping actually being bridged instead of the whole set. This makes the guardians query work and keeps a genuinely broken mapping loud AT ITS OWN CALL. Against it: the eager check exists so a broken block is reported once and early rather than at some unrelated later call, which is a real property to give up -- and WI-1122's own test asserts the refusal happens at INTERPRETER BUILD (`wi1122_embedder_host_fn_test.rs` around the "WHERE IT IS REFUSED" note), so that test states the current contract and would have to move with it.
 (b) A DECLARED-UNRUNNABLE ESCAPE. Let a block say its host functions come from an embedder, so this runtime reports rather than aborts. Costs a spelling and a spec sentence.
 (c) THE CLI LEARNS TO REGISTER. Out of reach for host functions whose bodies live in a Rust test file, so this cannot be the whole answer, but it may be part of one for a real embedder.
Whichever is chosen, PANICKING IS WRONG INDEPENDENTLY OF THE FORK: `bridge_op_to_eval` has an error channel and the query surface prints diagnostics, so a malformed program should be an error, not a crash with a backtrace hint. That much is repairable without settling (a)/(b)/(c) -- it is the repo's loud-error principle, and a panic is louder than loud in the wrong direction.

ACCEPTANCE: `anthill query` over a KB containing `examples/guardians/lib` answers a goal that bridges a host op -- the CONTROL/TEST pair above driven as a test, with the control (guardians absent) asserted too so a fix that breaks bridging outright cannot pass; no panic remains on any path a malformed or unrunnable binding block can reach, with a diagnostic naming the block instead; whichever of (a)/(b)/(c) is taken is written at the site and in kernel-language.md, and if (a), `wi1122_embedder_host_fn_test`'s "refused at interpreter build" assertion is updated rather than deleted, since it is the current contract; full workspace green via rustland/scripts/test.sh.

REFERENCE: `bridge_op_to_eval` and the raise site at `rustland/anthill-core/src/kb/resolve.rs:7815`; `register_operation_mappings` (`rustland/anthill-core/src/eval/builtins.rs`); WI-1122's `register_host_fn` and `wi1122_embedder_host_fn_test.rs`; WI-880 (b6805994) for the change that put a bridge on the common path; `docs/proposals/library/008-term-view-and-operations.md` §2b, which recorded this and is blocked by it; `examples/guardians/README.md` on the intended host-binding arrangement.

