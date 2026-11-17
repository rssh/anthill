## Attributes

- id: WI-20261117-22S8N-a-law-is-not-usable-by-a-guard
- created: 2026-11-17T15:48:28Z

- status: Open
- status_agent: user
- status_at: 2026-11-17T15:48:28Z

- acceptance: cargo-test

## Description

A LAW IS NOT USABLE BY A GUARD PROOF OF ITS OWN LOAD: within one load the operation bodies, and with them every guard's and precondition's proof, are typed before the rule sweep types the laws and weaves their requirement reads (sorts.rs: check_operation_bodies, then type_rule_bodies, install_typed_head_domain_goals, install_rule_provider_dictionaries). So a guarded law over a type variable (WI-20261117-V0RPW's form: rule euclid_div: add[A](mul(?b: A, …), …) = ?a :- EuclideanDomain[T = A], Additive[T = A], neq(?b, zero)) is not yet resolved when a proof of the same load meets it, and the lemma is not used — sound, a lost precision. MEASURED under ANTHILL_TEST_FRESH_LOAD=1 (stdlib and program one load): wi_v0rpw's positive rows (euclid_div at an Int64 / BigInt divisor of 2, Field's law at F5) owe Boom where the product order (stdlib sealed first) uses the lemma; those rows are pinned to the product order by name. A program's own law used by a guard of the same load meets the same. TO DECIDE: type guarded laws (their rule-body typing and requirement weave) before operation bodies in a load, or re-run a load's guard proofs that met an untyped law after the rule sweep. CBRD2 hit the same order for a relation's rule run by a proof (rule cmp in wi_5g28a). ACCEPTANCE: wi_v0rpw's rows unpinned and green under all three recipes; a program law used by a guard in the same load is used; full workspace green via rustland/scripts/test.sh.

