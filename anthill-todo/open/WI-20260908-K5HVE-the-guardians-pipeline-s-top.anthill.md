## Attributes

- id: WI-20260908-K5HVE-the-guardians-pipeline-s-top
- created: 2026-09-08T14:05:45Z

- status: Open
- status_agent: user
- status_at: 2026-09-08T14:05:45Z

- acceptance: cargo-test

- tags: guardians

## Description

THE GUARDIANS PIPELINE'S TOP-LEVEL INTERFACE: one entry point, and a carrier only where a set of implementations exists. SUPERSEDES WI-20260830-A0MBV, whose question ("should `Checker.check` take no `self`?") is answered YES while both premises it argued from turn out false.

THE RULE THIS APPLIES: a carrier is earned by a set of potential implementations THE TYPE SYSTEM CAN TELL APART. Variation that lives only in the host is what `operation_map` is for — a test deployment and an operational one name different `artifact`s in their binding block, same carrier. A spec is an EXTENSION POINT; a namespace operation is not.

THE INVENTORY, MEASURED. Four `sort C = ?` specs in `examples/guardians/lib/`:
 * `Triage` — unbounded, every candidate a model generates. EARNED, and it is where the one check that NEEDS a spec is measured: row widening against the spec's declared row (`rejected/wide_row.anthill`, `wide_row_modify.anthill`).
 * `Llm` — `LiveLlm` (`E = {External}`, mint costs `Permission[Llm]`) and `FakeLlm` (`E = {}`). Different mints, different rows, and 054's `Branch x External` bar rides on the difference. EARNED, and it is the pipeline's ONLY fake/live axis.
 * `Harness` — one carrier, `entity file_harness`, NULLARY. A second is genuinely conceivable and `harness.anthill` names one itself (a SEARCHING generator: "try, check, backtrack", under the `Branch` paragraph), so the SPEC stands. The threaded INSTANCE does not.
 * `Checker` — one carrier, `entity load_checker`, NULLARY. No second is conceivable: it loads a candidate into a discardable layer and runs the gate. No network, no external service, no strategy to vary — the real one is what you want under test.

MEASURED: `provides Checker` DOES NO MEASUREMENT WORK. Deleting `provides Checker[C = MintingChecker]` from `rejected/minting_checker.anthill` leaves the refusal byte-identical (`type mismatch in check.effects (op-effects) ... denied effect: Permission[T = Llm]`). Controls: the lib alone loads (3154 facts, 218 rules); `checker.anthill` with its `provides` stripped loads (3163 facts). All seven checker fixtures are decided by per-operation body-vs-own-declaration checks, so the second spec, the second carrier, the second `provides ... language rust` block and the `chk: Checker` parameter threaded through `attempt`/`open_round` buy narrative, not measurement.

MEASURED: THE RECEIVER IS DEAD AT THE HOST. `guardians_check` is registered at arity 3 (`guardians_test.rs:419`) and reads `args[1]` and `args[2]`; `args[0]` is never touched. `guardians_generate` is `|interp, _args|` — it ignores EVERY argument including the `llm` it was handed, so the one operation that should inherit the fake/live axis does not route through it. (That last one is a defect in its own right and is in scope here only because the fix moves the same code.)

MEASURED: A CARRIER-FREE OPERATION REACHES ITS HOST. `provides <namespace> language rust ... operation_map { ... } end` loads and lands a real `OperationMapping(carrier: "<namespace QN>", operation: ..., host_fn: ..., lang: "rust")`. Spec §10.2 (kernel-language.md:1891) says the same for `anthill.reflect`'s twenty namespace-level accessors.

THE EXAMPLE ALREADY AGREES, IN THREE PLACES, WHICH IS THE STRONGEST FORM OF THE ARGUMENT. `Email.fetch(box: Mailbox)` is a plain sort operation — no `self`, no `sort C = ?`, no carrier, body-less, deployment-bound. So are `categories_of` and `choose_recipient` at namespace level. `email.anthill` and `harness.anthill` disagree about how to declare a single-implementation component, and `harness.anthill` picked the expensive spelling.

THE SHAPE.
 (1) `sort guardians.Harness` KEEPS `sort C = ?` with `render_task` and `generate`, and STOPS BEING THREADED. Selection moves to `requires Harness[C]` at the top — `anthill-todo`'s own pattern, whose `store.anthill` states it: "Selection is already done, by `sort Main`'s `requires WorkItemStore[State]` and the host's requirement dictionary." No store value crosses that API and no harness value should cross this one.
 (2) `check` LEAVES THE SPEC ENTIRELY, and two spellings that look equivalent are measured NOT to be. A selfless `operation check(...)` written INSIDE `sort Harness` is still a spec member: the loader's own error says a carrier's own `chk` would back it ("no default on `probe.H`, no own `chk` on `probe.FileH`"), and §5.3/WI-1091 answers a licensed call from the dictionary the `requires` clause names — which is exactly the licence that selects the harness, so `requires Harness[C = X]` would answer the check from `X`. Writing it in `namespace guardians.Harness` is no better: proposal 059 makes that a SECONDARY ENTRY, measured identical to the sort body ("111 both ways", WI-1008), and R3 refuses a body-less operation there outright. It goes at an address NO SORT OCCUPIES, where 059's own "ordinary namespace" clause applies — one gate, unprovidable, host-bindable.
 (3) `Checker` and `LoadChecker` COLLAPSE.
 (4) ONE ENTRY POINT, AND `open_round` IS NOT IT. It is one round, not the loop (the repair loop is the caller's — `Rejected`'s diagnostics are next round's `feedback`); it mints `LiveLlm` from `endpoint`/`model` strings internally, which locks the deployer out of the `Llm` extension point this ticket establishes; and nothing drives it (calling `attempt` from a host dies `OperationBodyMissing`, so the suite drives carriers). Its own comment says what it IS: "the POSITIVE CONTROL for every `Permission` refusal in this example". It stays, in the implementation half. What is missing is the deployer's call — take the `Llm` they supply, own the loop, return the verdict — which also moves `Permission[Llm]` to the deployment boundary, the move `run_triage` already made for `Permission[Vouch]`.
 (5) THE PACKAGE SPLIT is documentary, and must stay so. Candidate fixtures must keep NAMING implementation vocabulary — `forged_llm` names `fake_llm`, `frontier_checker` names `LiveLlm.open_frontier`, `harness_launder` names `file_harness` — or four refusals degrade from "denied by authority" to "no such name", which is the trap this example's own methodology warns about. Anthill namespaces do not seal (only `internal` does), so a `guardians.impl` namespace organises the reader's view without changing what a candidate can name. Write that down, or someone later "tightens" it into a seal and guts the measurements.

WHY A0MBV DOES NOT CARRY THIS. Its stated cost EXPIRED: it argued that dropping `self` would leave nothing measuring `Permission[Reveal]`, and WI-20260829-MCKTE deleted `Permission[Reveal]`, `LlmOutput` and `steering_checker` outright. Its security argument does not hold either: a candidate provides `Triage` into a DISCARDABLE LAYER and never selects the base pipeline's carriers, so a hostile `provides Checker` is not in the threat model and "who guards the guard" does not apply to a sort only the deployment writes. What survives is an INTERFACE argument, and the change is larger than A0MBV's description — which is this project's own test for when a follow-up gets its own ticket.

THE FINDING NEITHER TICKET STARTED FROM, recorded because the restructure does not fix it and should not be read as fixing it: `-Permission[Llm]` on `check` CONSTRAINS NOTHING TODAY. `LoadChecker.check` is host-bound, so the row bounds its DECLARED row while its body sits outside the row's reach — the same boundary `harness.anthill` already admits for the `Source` seal ("THE SEAL IS AGAINST ANTHILL, NOT AGAINST THE HOST"). The denial's entire measured content is that a candidate declaring the row and violating it is refused, demonstrated on seven counterfactual programs the pipeline never asks a model to write. Making the denial bind the real checker means writing `check` in anthill, which needs WI-20260908-9WVT7 (047's `Error` layer) and is that ticket's dependent, not this one's.

ACCEPTANCE: the deployer's surface is ONE call and constructs nothing they did not author; `Harness` keeps its spec and loses its threaded instance; `check` is declared at an address no sort occupies and reaches its host through a namespace binding block; `Checker`/`LoadChecker` are gone. The seven ex-checker fixtures keep the refusals they measure today — measured, none needs `provides` — with a decision RECORDED for where they live once they stop naming a spec the pipeline never generates. Every existing row in `guardians_test.rs` stays green, and the count is stated before and after.

