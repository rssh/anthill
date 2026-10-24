## Attributes

- id: WI-20261024-TC54R-a-call-s-bracket-in-a-rule
- created: 2026-10-24T18:42:02Z

- status: Open
- status_agent: claude
- status_at: 2026-10-24T18:42:02Z

- acceptance: cargo-test

- depends_on: WI-20261013-RYDNV-068-c1d-one-classification-per

- tags: proposal-068

## Description

A CALL'S BRACKET IN A RULE BODY IS READ, AS IN AN OPERATION BODY: lift the rule-body half of WI-839's refusal (`CallTypeArgsNotSupportedHere`, `NoChannel`: "a rule-body goal … has no channel for it") for a goal and a value slot, and WI-20261023-CX743's refusal of a parameter default that writes a bracket when a rule-body call takes it (`bracketed_call`, typing/param_defaults.rs). It waits on WI-20261013-RYDNV (068 C1d): the typer reads a rule-body call's bracket into its σ, and the rule body's requirement weave reads the argument values instead, so a type parameter only the bracket fixes reaches run time unbound. MEASURED 2026-10-24 with CX743's refusal backed out: `rule r(?t) :- ?t <=> typeOf(1)` over `typeOf[T](x: T, t: Type = TypeValue.type_value[T = T]()) -> Type requires TypeValue[T = T]` loads and answers a free `?t`, where the operation-body twin `typeOf(1)` answers `Int64`. ROWS (each driven by value, with a control that fails with the weave reading argument values): that rule answers `Int64`; a written `?t <=> TypeValue.type_value[T = Int64]()` in a rule body answers `Int64`; RYDNV's 2026-10-21 SHED7 row, `vs <=> Builder.fromList[C = C]([?p, ?q, ?r])` (`Sat[C = Bag[T = Bit]].model` 2 models); and, if WI-20261015-D2KZ5 settles on the bracket, `Error.reify[T1 = Other](lambda () -> twoWays(7), ?r)` at a rule-body goal answers `err(other(n: 7))`. Spec: kernel-language §5.4's bracket paragraph and §5.3, which today name the rule body among the positions with no channel.

