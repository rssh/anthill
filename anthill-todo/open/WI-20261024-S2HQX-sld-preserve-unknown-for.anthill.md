## Attributes

- id: WI-20261024-S2HQX-sld-preserve-unknown-for
- created: 2026-10-24T12:47:17Z

- status: Open
- status_agent: user
- status_at: 2026-10-24T12:47:17Z

- acceptance: cargo-test, scaland-sbt-test

## Description

SLD: preserve UNKNOWN for unproved universal goals and through negation-as-failure.


User decision 2026-10-24: return UNKNOWN when a goal about an eigenvariable cannot be established and closed-world failure is unjustified. Insufficient knowledge is neither inconsistency nor FAILURE, DELAY, or ERROR. First attempt proofs from general rules and scoped assumptions; merely containing a rigid is not sufficient to classify a goal as unknown.

Reuse the existing BuiltinResult::Unknown, UnknownCause, Solution::undecided and drain_verdict mechanisms in rustland/anthill-core/src/kb/resolve.rs. Audit clause-candidate exhaustion, step_naf, and the distinct representations Var::Rigid, opaque Term::Ref skolems, and open-world parameter references. Establish executable baseline reproducers; the discussed hazard has not yet been measured on every current path.

Negation semantics: a proof of P makes not(P) fail; complete failure permits not(P) to succeed only with a valid closed-world interpretation; UNKNOWN remains UNKNOWN; pending work remains pending and errors remain observable. Filtering unknown residuals must never turn the result into complete-empty failure. Preserve valid concrete closed-world queries and decisive proofs/refutations independent of the symbolic value.

### Concrete regression tests

Logical notation below does not request new surface syntax. Use existing syntax or resolver APIs. Isolate each KB. Assert actual answer classification and residual cause, not just loading or absence of definite answers.

1. With sole fact p(0), forall X. not(p(X)) must not yield definite success: the symbolic p(c) and its negation are UNKNOWN. No matching clause for the fresh witness does not prove the universal negation.
2. Under the same program and universal-proof context, positive p(c) is UNKNOWN. Controls: concrete p(0) succeeds, concrete p(1) fails under the existing closed-world policy, and not(p(1)) succeeds.
3. With general clause p(Z), forall X. p(X) succeeds and forall X. not(p(X)) fails. This rejects a blanket rigid-presence guard.
4. Under local assumption p(c), p(c) succeeds and not(p(c)) fails. Exercise the actual forall_impl assumption stack and the Gamma bridge where applicable. Nested NAF must inherit the correct assumptions, which must disappear at scope exit.
5. With sole fact p(0) and helper r(Z) :- p(Z), not(r(c)) remains UNKNOWN: hidden symbolic dependencies must propagate through clause bodies.
6. With sole fact p(0), not(not(p(c))) remains UNKNOWN with its reason preserved through nested drains.
7. UNKNOWN conjoined with definitely-false is false; UNKNOWN disjoined with definitely-true has a definite proof. Exercise both evaluation orders so unknown neither prematurely stops search nor suppresses a decisive sibling.
8. Distinguish a flexible argument awaiting binding (DELAY), an unproved eigenvariable goal (UNKNOWN), and an ill-typed operation (ERROR). With sole clause p(Z,Z), p(c,c) still succeeds.
9. Run unknown cases through definite_only and NAF/guard consumers. An empty filtered answer stream must retain the metadata that prevents spurious NAF success.
10. Repeat representative cases through real supported entry points for Var::Rigid, opaque contract skolems, and open-world references. Include a witness nested inside a constructor and reached through an alias, avoiding top-level-only detection.

Measure the baseline and back-out results. Identify which tests detect the fix and which pass either way as preservation controls. Run Rust tests through rustland/scripts/test.sh and include the set in the full workspace workflow; exercise Scala parity as required by acceptance. No constructive-negation or arithmetic-prover expansion is required. Discuss any canonical-spec changes first.

Related: WI-20261024-YHYZ3-sld-forall-enforce-opening covers opening/closing scopes and preventing witness escape. This ticket covers the interpretation of missing proofs and UNKNOWN propagation; coordinate scope metadata and assumption handling without treating either fix as a substitute for the other.

References: docs/local/references/lambda-prolog/implementation-ho-0911.5203v1-QI.pdf section 2.2, printed pp. 15-16 (goal grammar and fresh-constant treatment of forall), and section 4.2, printed pp. 42-44 (scope and quantifier order); docs/local/references/lambda-prolog/ptlp-2025-12-30.pdf sections 5.11-5.12 (local assumptions and eigenvariables). These justify universal proof/scoping; UNKNOWN/NAF integration is the Anthill decision here, not a claim about lambda-Prolog's result API.
