## Attributes

- id: WI-20261117-V0RPW-the-guarded-laws-over-t-write
- created: 2026-11-17T06:16:05Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-17T16:37:26Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE GUARDED LAWS OVER T WRITE THE ZERO AS THE INT64 LITERAL 0: `euclid_div: add(mul(?b, div(?a, ?b)), rem(?a, ?b)) = ?a :- neq(?b, 0)` (stdlib/anthill/prelude/division.anthill, EuclideanDomain) and Field's three inverse laws `mul(div(?a, ?b), ?b) = ?a :- neq(?b, 0)`, `div(?a, ?b) = mul(?a, recip(?b)) :- neq(?b, 0)`, `mul(recip(?a), ?a) = 1 :- neq(?a, 0)` (field.anthill) — the shape WI-20261109-5VM2G removed from the effect guards. A guarded `=` law is a premise a proof from Gamma takes (KnowledgeBase::is_guarded_eq_law, kernel-language §5.3), so at T = BigInt or Float the guard `neq(?b, 0)` compares a BigInt or a Float with an Int64, holds of every divisor, zero included, and the proof may use `mul(div(?a, 0n), 0n) = ?a` or `mul(recip(0.0), 0.0) = 1` (found by /code-review on 5VM2G; NOT measured yet — measure first which proofs reach these laws: a guard, a precondition, a contract, `anthill prove`). The `1` of the third law is an Int64 literal at T too. TO DECIDE with the user: how a law over T writes the carrier's zero and one (`zero`/`one` of Additive/Multiplicative at T, and how the resolver reads them in a law's guard, where 5VM2G showed a bare nullary name is a datum), and whether a law's guard comparisons are typed as a contract's are (§5.4, CBRD2). ACCEPTANCE: a row driving a proof that reaches each law at BigInt and at Float with a zero divisor, the law not applied; the same proof with a non-zero divisor still uses it; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-17T06:32:59Z — feedback — user

MEASURED and DECIDED with the user 2026-11-17 (main daafd6db). Guard probes: effects { Boom :- neq(b * (a / b) + EuclideanDomain.rem(a, b), a) } drops Boom at risky(x, 0n) (euclid_div used, neq(0n, 0) holding: BigInt vs Int64 compare apart; Int64 risky(x, 0) keeps it); effects { Boom :- neq((a / b) * b, a) } drops Boom at risky(x, 0.0) and risky(x, 49.0) (Float; (1.0 / 49.0) * 49.0 = 0.9999999999999999), and at risky(x, 2) over Int64 (integer division: (7 / 2) * 2 = 6) and risky(x, 2n) over BigInt — a guarded = law of a spec sort is a clause of the global eq connective over the generic mul/div and answers at every carrier, whether or not it provides the sort. Ground calls evaluate and are right. DECISIONS: (1) Float provides Divisible[T = Float], not Field (Float is not a field; its inverse laws are false under IEEE). (2) A guarded law of spec sort S over T is a premise only at a carrier that provides S: the law's variables are typed at T, a proof binds T to the operands' carrier C, checks the provision S[T = C], and reads S's requirements there, so the guard is written neq(?b, zero) with zero Additive's (EuclideanDomain reaches it through Numeric[T], Field through Ring[T]) and read as C's zero; undecided where no ground carrier fixes T. Measured on the way: zero at T is typed in an operation body and a contract (eq(b, zero()) loads in a sort requiring Numeric[T]) but refused in a rule body and a law's guard ('ambiguous dispatch of Additive.zero: 5 instances provide Additive') — rule-body typing does not read a nullary spec member through the sort's requirement.

### 2026-11-17T16:37:23Z — feedback — user

Delivered (c91946d32, merged with origin/main). Float provides Divisible, not Field. A law is written over its type variable — euclid_div: add[A](mul(?b: A, div(?a, ?b)), rem(?a, ?b)) = ?a :- EuclideanDomain[T = A], Additive[T = A], neq(?b, zero), and Field's three likewise — and a proof using it instantiates it at the type of what ?b matched, passing each guard as the typer's instance there; where nothing provides it, the lemma is not used. zero is Additive[T].zero by scoping: a call with no carrier argument reads the one instance of its spec a one-variable clause holds. Acceptance: euclid_div used at an Int64 / BigInt divisor of 2 and not at 0 / 0n; Field's laws used at the field F5 and at no Int64, BigInt or Float divisor (each measured unsound before). Rows: wi_v0rpw_law_over_type_variable_test (5; back-out table in its header). Limit filed as WI-20261117-22S8N (a law serves the proofs of a later load; the rows measuring it used are pinned to the product's order). Gate on the merged tree 12250 / 0 / 17; before the merge two-step 11158 / 0 / 9, fresh green after the pin, families green, scaland 859 / 0.

