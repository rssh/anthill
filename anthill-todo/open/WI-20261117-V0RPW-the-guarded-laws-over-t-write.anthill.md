## Attributes

- id: WI-20261117-V0RPW-the-guarded-laws-over-t-write
- created: 2026-11-17T06:16:05Z

- status: Open
- status_agent: user
- status_at: 2026-11-17T06:16:05Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE GUARDED LAWS OVER T WRITE THE ZERO AS THE INT64 LITERAL 0: `euclid_div: add(mul(?b, div(?a, ?b)), rem(?a, ?b)) = ?a :- neq(?b, 0)` (stdlib/anthill/prelude/division.anthill, EuclideanDomain) and Field's three inverse laws `mul(div(?a, ?b), ?b) = ?a :- neq(?b, 0)`, `div(?a, ?b) = mul(?a, recip(?b)) :- neq(?b, 0)`, `mul(recip(?a), ?a) = 1 :- neq(?a, 0)` (field.anthill) — the shape WI-20261109-5VM2G removed from the effect guards. A guarded `=` law is a premise a proof from Gamma takes (KnowledgeBase::is_guarded_eq_law, kernel-language §5.3), so at T = BigInt or Float the guard `neq(?b, 0)` compares a BigInt or a Float with an Int64, holds of every divisor, zero included, and the proof may use `mul(div(?a, 0n), 0n) = ?a` or `mul(recip(0.0), 0.0) = 1` (found by /code-review on 5VM2G; NOT measured yet — measure first which proofs reach these laws: a guard, a precondition, a contract, `anthill prove`). The `1` of the third law is an Int64 literal at T too. TO DECIDE with the user: how a law over T writes the carrier's zero and one (`zero`/`one` of Additive/Multiplicative at T, and how the resolver reads them in a law's guard, where 5VM2G showed a bare nullary name is a datum), and whether a law's guard comparisons are typed as a contract's are (§5.4, CBRD2). ACCEPTANCE: a row driving a proof that reaches each law at BigInt and at Float with a zero divisor, the law not applied; the same proof with a non-zero divisor still uses it; full workspace green via rustland/scripts/test.sh.

