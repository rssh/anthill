## Attributes

- id: WI-20260822-7FSX1-a-program-can-declare
- created: 2026-08-22T10:27:55Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T10:27:55Z

- acceptance: cargo-test

## Description

A PROGRAM CAN DECLARE `operation_map` KEYS, LOAD COMPLETELY CLEAN, AND BE UNRUNNABLE -- with the failure surfacing much later, at a call site having nothing to do with the mapping. There is no diagnostic between "loaded: N facts, M rules" and the first interpreter build.

MEASURED, and it is what made this ticket. examples/guardians declared four `operation_map` keys (`guardians_live_summarize`, `guardians_live_observe`, `guardians_generate`, `guardians_check`) that nothing registered. `anthill load examples/guardians` printed only the three refusals the example intends. SIX integration tests passed over that KB. All of them asserted load outcomes, and none built an interpreter -- so nothing noticed that NO INTERPRETER COULD BE BUILT AT ALL:

  Internal("broken binding block: operation_map names host function
  \"guardians_generate\" for guardians.Generator.generate, which the rust runtime
  does not provide. No interpreter can be built for this program until the binding
  is fixed -- this error may surface at a call that has nothing to do with
  guardians.Generator.generate.")

The runtime message is GOOD -- it names the key, the operation, and warns that the symptom will appear elsewhere. The gap is entirely that nothing asks the question until an interpreter is built, and an interpreter is built lazily: `anthill run`, `common::interp_for`, and every short-lived interpreter `run_in_bridge_interp` constructs per `[simp]` fire or bridged `eq` dispatch. So `anthill load` and `anthill query` can both answer normally over a program that can never execute.

NOT A LOADER DEFECT, AND THAT IS THE POINT. WI-1122's own doc states the constraint: `is_interpreter_mapped_op` "promises at typing time that this process's interpreter has an implementation for a rust mapping, and it answers off the mapping's LANGUAGE -- it cannot check that the key resolves to anything." It cannot, because the embedder table is per-process and registration is legal right up until load seals it. So the loader is honest; what is missing is anyone asking AFTER registration is sealed and BEFORE the first call.

WHAT IS KNOWABLE, AND WHEN. At the moment `set_host_op_mappings` seals the registry the answer is fully determined: the set of declared `lang == "rust"` keys is known from the KB, and the set of provided keys is HOST_FNS plus the embedder table. The difference is computable exactly, once, with no interpreter. `register_operation_mappings` already computes it -- it just does so per interpreter, as a fatal error, at whatever moment the first one happens to be built.

PROPOSED: report the difference as a DIAGNOSTIC at the seam, listing every unbound key with its operation, rather than waiting for a build to die on the first one it meets. Two surfaces worth considering, and the choice is the design question this ticket owes:
  * `anthill check` gains it -- fits the existing command, requires the CLI to register whatever the embedder would.
  * a `KnowledgeBase` method the embedder calls after registration -- honest about being per-process, usable from a test.
An `anthill load` warning is the third option and probably wrong: load runs before the embedder has necessarily finished, and a warning that fires spuriously in the normal embedding case is worse than none.

WHY IT MATTERS BEYOND CONVENIENCE. This is the repo's own rule -- "prefer a loud error over a silent skip ... Silent skips hide bugs and read as 'handled' when they aren't" -- at a seam that currently reads as handled. The specific damage is that a test suite of load-only assertions is GREEN over an unrunnable program, which is the exact shape CLAUDE.md warns about: "a test for a capability must DRIVE the capability ... 'It loads clean' is not evidence that anything works." A diagnostic here converts that class of mistake from six passing tests into one line.

ACCEPTANCE: a program declaring a `lang == "rust"` `operation_map` key that no HOST_FNS entry and no registered embedder function provides is reported -- with the key, the operation's qualified name, and every such key rather than the first -- without an interpreter being constructed. CONTROL: a program whose keys are all bound reports nothing, and the existing fatal error at `register_operation_mappings` is unchanged for callers that skip the check. Arity mismatch (WI-876) is already checked there and should be reported by the same pass if it is cheap to do so.

