## Attributes

- id: WI-20261102-G2NHE-a-key-written-in-an-operation
- created: 2026-11-02T21:32:19Z

- status: Open
- status_agent: user
- status_at: 2026-11-02T21:32:19Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A KEY WRITTEN IN AN OPERATION'S `ensures`, IN A `fact`'S BRACKET OR IN A RULE BODY IS NEVER JUDGED FOR A LAWFUL `Eq`: `operation k() -> Int64 ensures Holder[C = Map[K = Float, V = Int64]] = 1`, `fact Holder[C = Map[K = Float, V = Int64]]` and `rule usesmap(?x) :- known(Map[K = Float, V = Int64]), known(?x)` each load clean (measured 2026-11-02), where the same `Map[K = Float, V = Int64]` as a parameter type, in a sort's `requires`/`provides` and since WI-20260929-TJ3G4 in an operation's `requires` is refused. MECHANISM: the three are lowered as TERMS by `Loader::convert_term`, not by a type lowering, so no `ParameterizedSite` is recorded for them; TJ3G4 recorded the brackets written as type arguments in an operation's `requires` alone (`contract_bracket_arg`, `SiteOrigin::OperationRequires`), and `check_use_site_requires_eq`'s non-scope (4) names these three. The WI-710 argument-fit check (`check_sort_type_args`) already runs at every such nested bracket, and the WI-835 doc says the two must not disagree about which instantiations they see. DECIDE FIRST which of these is a USE of the type: a `fact`'s bracket is an instance claim, whose sibling `provides Holder[C = Map[K = Float, V = Int64]]` is refused at the type it binds; an `ensures` spec application is WI-402's existential return, and a bracket in a rule body is a type held as a value. ACCEPTANCE: each position that is a use refuses the unlawful key at its bracket and loads a lawful one, as an operation's `requires` does (wi_tj3g4_valued_key_positions_test); the written-row check judges a row there once; full workspace green via rustland/scripts/test.sh.

