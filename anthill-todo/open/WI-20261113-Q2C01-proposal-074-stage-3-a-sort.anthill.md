## Attributes

- id: WI-20261113-Q2C01-proposal-074-stage-3-a-sort
- created: 2026-11-13T23:01:26Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T23:01:26Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 3 — A SORT WITH OPERATIONS AND NO PARAMETER HAS A DICTIONARY (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§2, the third row of "Which sorts have a dictionary", with no parameter). - `use(c: Ticker)` takes `Dictionary.instance[Ticker]()`, and `Ticker.now()` in its body reads that dictionary. - `use() requires Ticker = Ticker.now()` reads the dictionary its caller passes. Today it loads and dies at run time, `OperationBodyMissing("Ticker.now")`. - `go() = Ticker.now()` takes the dictionary as any dictionary at one type is chosen: the one provider, a default provision, or a named one where several answer. Today: "no provider can be selected here". - Refused at load: `use(sc())`, a provider's value where the dictionary is expected (it answers 1 today); and a call of the spec's operation with two of its dictionaries in scope, two parameters or a parameter and a clause. - A provider named: `Dictionary.instance[Ticker, Ticker = SysTicker]()` over a `SysTicker` without constructors; naming one with constructors is refused (058 §3.5). - The operations keep their effects: `now() -> String effects Time.Clock`, run under `anthill run` and under a frozen clock. - First, a census: every sort in this row in the stdlib, the examples and the fixtures, and every parameter typed at one. Those are the programs whose meaning moves. - A module has the dictionary of its own bodies: `Dictionary.instance[Time]()`; `Time.now()`, every example's `Program` and lf1's controllers run as today. - What is new to build (from review): a supply channel for a requirement with no carrier, which has none today (`use() requires Ticker = Ticker.now()` loads and dies); the refusal of a call two dictionaries answer; and the row's change of admissibility, `use(sc())` answering 1 today, which the census measures as KSSA4's did. The class is read by `spec_over_parameter` and `spec_has_carrier_param` at 28 call sites in 11 files (counted 2026-11-13), each of which the declaration-only reading of stage 1 and this row reach. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

