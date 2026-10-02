## Attributes

- id: WI-20260930-AMYV4-an-effect-guard-naming-nothing
- created: 2026-09-30T16:24:39Z

- status: Open
- status_agent: user
- status_at: 2026-09-30T16:24:39Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN EFFECT GUARD NAMING NOTHING LOADS CLEAN, AND NEGATION AS FAILURE THEN READS IT AS REFUTED, SO THE EFFECT IS DROPPED WHEREVER THE GUARD GROUNDS. `operation dz(d: Int64) -> Int64 effects {Error[DivisionByZero] :- nosuchpred(d, 0)} = 1` loads with no diagnostic, and so does a PURE caller `operation pure0() -> Int64 = dz(0)`; the same holds for `eq(d, 0)` written WITHOUT `import anthill.prelude.PartialEq.{eq}`. With the import, pure0 is refused 'undeclared effect: Error[T = DivisionByZero]' (eq(0, 0) holds) and dz(1) is admitted (refuted) — the right answers. A nameless guard also loads clean in an ARROW type's row (`f: (d: Int64) -> Int64 @ {Error[DivisionByZero] :- nosuchpred(d, 0)}`) and in a PROVISION's effect binding (`provides Sp[T = Car, E = {Error[DivisionByZero] :- nosuchpred(1, 0)}]`). MECHANISM: the loader name-checks a rule body (WI-1034, LoadError::UndefinedRuleBodyGoal) and a contract clause (WI-20260822-59CDQ, load.rs check_contract_clause_goals, LoadError::UndefinedContractGoal) but no effect guard. At the call, typing/effects.rs guarded_atom_refuted -> gamma.rs refute_guard -> negate_goal swaps eq/neq only for the RESOLVED PartialEq functors and wraps anything else in `not(..)`; prove_from_gamma proves `not(nosuchpred(0, 0))` by NAF over a predicate with no clauses — ground, so it does not flounder — and the effect drops. A parameter argument flounders and keeps it, so whether the effect exists depends on the call site. MEASURED identically on the pre-WI-20260929-0RP29 binary; FOUND by that ticket's third /code-review (a test program missing the eq import passed its control for the wrong reason). FIX: name-check every guard's conjuncts at load as check_contract_clause_goals checks a clause (kb.undefined_query_goal_functors on a term; the undefined_functor head test on an occurrence), over every row a guard can be written in — an operation's declared row, a type's row, a provision's or sort's effect binding — with a message that says what a nameless guard does (the effect vanishes wherever the guard grounds) and the repair (undefined_name_repair). ACCEPTANCE: the three programs above refused at the guard, naming the functor; the imported-eq twin unchanged (pure0 refused, dz(1) admitted); full workspace green via rustland/scripts/test.sh.

