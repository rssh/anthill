## Attributes

- id: WI-20261024-YHYZ3-sld-forall-enforce-opening
- created: 2026-10-24T12:21:53Z

- status: Open
- status_agent: user
- status_at: 2026-10-24T12:21:53Z

- acceptance: cargo-test, scaland-sbt-test

## Description

SLD forall: enforce opening/closing eigenvariable scopes and scope-safe substitutions, following lambda-Prolog.

User requested 2026-10-24. Keep fresh Var::Rigid witnesses for universal goals, but implement the scope/dependency discipline that makes them sound. A rigid never changes; a flexible variable created outside its scope must not acquire that rigid, directly or through aliases/compound terms. Flexible variables created inside may refer to it. Closing a scope must preserve valid outer substitutions without allowing local eigenvariables or hypotheses to escape; failure and backtracking must restore scope state. Nested scopes and delayed goals must retain their correct proof context.

Current inspection: rustland/anthill-core/src/kb/resolve.rs::step_forall_impl opens binders to fresh rigids, substitutes antecedents/consequents, and appends an assumption-pop marker. No corresponding universe-level discipline was identified in this path. This is an audit finding, not yet a reproduced unsound answer: first construct an executable baseline reproducer. Use explicit scope/dependency representation (universe levels or an equivalent sound design), rather than relying on rigid identity or deleting escaped answer bindings afterward. Review binder opening before substitution and scope ownership of pending goals as part of the implementation.

References: docs/local/references/lambda-prolog/implementation-ho-0911.5203v1-QI.pdf (Xiaochu Qi, An Implementation of the Language Lambda Prolog Organized around Higher-Order Pattern Unification), section 2.2 printed pp. 15-16: goal grammar and forall/implication operational rules; section 4.2 printed pp. 42-44: quantifier-order counterexample, universe labels and propagation of dependencies through substitution; section 6.2: universe counter, entry/exit and choice-point restoration. docs/local/references/lambda-prolog/ptlp-2025-12-30.pdf sections 5.11-5.12: local assumptions and eigenvariables as scoped constants.

Acceptance: drive actual resolution. With the clause p(Z,Z), forall x exists y p(y,x) succeeds, while exists y forall x p(y,x) has no successful proof. Test indirect escape through aliases and nested terms, nested forall with distinct rigids, valid binding of fresh clause variables to a local rigid, scope restoration after failure/backtracking, and removal of local assumptions before surrounding goals resume (including delayed goals). Preserve valid outer-variable solutions independent of local witnesses. Record which regression tests fail with the change backed out and which are positive controls; use rustland/scripts/test.sh and include the cases in the full workspace workflow. If existing syntax cannot express a case, exercise the resolver API rather than substituting a load-only test. Higher-order abstraction, where supported, must be judged by free dependency rather than rejecting all historical occurrences of a witness.

Scope: implement resolver scope discipline; do not change the canonical language specification without prior discussion. Lambda-Prolog permits forall x G for any admissible goal G, not only implications; its implication antecedent is restricted to program-clause formulas. General expression evaluation, negation-as-failure, and bounded enumeration must not silently acquire new logical semantics as part of this fix.

### Concrete scope-discipline regression suite

The following is logical test notation, not a request for new Anthill syntax. `exists` introduces a fresh flexible variable at that point; `forall` opens a fresh eigenvariable; `=` means structural unification (not dispatched semantic equality); `&` is ordered conjunction; `|` is disjunction; `=>` introduces scoped assumptions. `box` is an uninterpreted constructor, `a` a global constant, and `false` a goal with no proofs. Use existing surface forms where they express the case faithfully, otherwise construct resolver goals through the API. No negation-as-failure is needed to assert failure: collect answers and assert that there are none. Each case runs in an isolated KB. In cases using `p`, its sole clause is `p(Z,Z)`; `q` has no global clauses.

#### Negative cases: forbidden dependencies must never yield an answer

1. **Direct escape / quantifier order.** Query `exists Y. forall X. p(Y,X)`. Expect zero answers. Without the scope check, the clause's fresh variable and the older `Y` both bind to the local rigid, producing an unsound success. Inspect the answer count, not merely whether the returned substitution was cleaned up.

2. **Escape through a constructor.** Query `exists Y. forall X. Y = box(X)`. Expect zero answers. A check of only the binding's top-level carrier misses the rigid nested in `box`.

3. **Escape through a younger alias.** Query `exists Y. forall X. exists Z. (Y = Z & Z = X)`. Expect zero answers. The initially harmless alias must constrain the younger variable's future bindings. Also run the variant with the first equality reversed, `Z = Y`, to catch orientation-dependent alias handling. Drive these unifications in the stated order through the API if needed.

4. **Dependency propagation through a compound binding.** Query `exists Y. forall X. exists Z. (Y = box(Z) & Z = X)`. Expect zero answers. When `Y` acquires a term containing the younger flexible `Z`, the restriction must propagate to `Z`; checking only for rigids already present at binding time is insufficient.

5. **Nested scope boundary.** Query `forall X. exists Y. forall Z. Y = Z`. Expect zero answers. `Y` may reference the outer witness but cannot reference the inner witness. A single global flag saying a variable was created under some forall is insufficient.

6. **Sibling scopes are distinct.** Query `exists Y. ((forall X. Y = X) & (forall Z. Y = Z))`. Expect zero answers already at the first binding. In a companion low-level freshness test, retain the two opened witnesses for inspection and assert distinct identities even when the sibling scopes use the same universe depth; depth is permission metadata, not witness identity.

7. **Assumptions expire on successful exit.** Query `(forall X. (q(X) => q(X))) & (exists Y. q(Y))`. Expect zero answers. The inner proof succeeds, but its assumption must not answer the continuation. This catches failure to close the assumption scope even when variable-escape checks are correct.

8. **Assumptions expire on failed branches.** Query `(forall X. (q(a) => false)) | q(a)`. Expect zero answers. Backtracking out of the first branch must remove `q(a)` before the second branch runs. Using a global constant isolates assumption leakage from eigenvariable leakage.

#### Positive controls: scope enforcement must preserve legal proofs

9. **Inner existential may depend on its enclosing universal.** Query `forall X. exists Y. p(Y,X)`. Expect one proof. The clause variable and `Y` may bind to the witness. Pair with case 1; rejecting every flex-to-rigid binding is not a valid fix.

10. **Outer witness remains accessible inside nested scopes.** Query `forall X. exists Y. (Y = X & (forall Z. Y = X))`. Expect one proof. Pair with case 5; the inner scope must retain access to older witnesses and existing legal substitutions.

11. **Valid outer answers survive closing.** Query `exists Y. forall X. (Y = a & p(X,X))`. Expect exactly the answer `Y = a`. Closing must not discard every binding made while the scope was active. No local witness may occur free in the observable answer.

12. **Failed alternatives restore substitutions and scope.** Query `exists Y. ((forall X. (Y = a & false)) | Y = box(a))`. Expect exactly `Y = box(a)`. A binding or scope state retained from the failed branch incorrectly suppresses the valid alternative. Also run `(forall X. false) | (forall Z. exists W. p(W,Z))`: expect one proof from the second branch.

#### Scheduling and scope restoration probes

13. **A pending outer goal cannot borrow an inner assumption.** Construct a resolver-level test with an outer `q(a)` goal deliberately in the suspended/pending state, followed by `forall X. (q(a) => true)`. Resume the pending goal after the quantified goal. Expect no successful answer: it must run with its original outer hypothesis context. Assert that the suspension/resumption path actually ran. This catches rotation that executes a goal under the wrong assumptions; do not replace it with an ordinary sequential duplicate of case 7.

14. **An unfinished inner goal cannot be discharged by closing its scope.** Suspend an inner consequent under `forall X. (q(X) => G(X))`, where `G` is a test-controlled resumable goal. Verify that no definite answer is emitted while `G` is pending, that resuming it sees the same witness and the local `q(X)` assumption, and that both cease to be available to the outer continuation after completion. The harness must explicitly control the suspension rather than rely on an operation that might evaluate eagerly.

15. **Universe restoration is observable at the resolver boundary.** Where levels are used, assert the current level before entry, inside nested entry, after normal exit, after failure, and after backtracking. Create new flexible variables at each stage and check their permitted dependencies. If the implementation uses scope identities instead, assert the equivalent ancestry/visibility properties. Pair state assertions with the actual-resolution cases above; internal counters alone are not acceptance evidence.

For every case, record the baseline result and the result with the scope implementation backed out. Cases 1-8 and 13-15 target particular missing pieces; not every case is expected to fail on the current implementation (existing assumption cleanup may already pass its controls). Cases 9-12 are preservation controls and may pass both before and after. At least one demonstrated unsound success must become zero answers, and tests must assert semantic results rather than only absence of a rigid in the final substitution. Run the applicable suite for each implementation covered by this ticket's acceptance tools. Higher-order free-dependency/abstraction tests should be added if that resolver path is supported; this first-order suite does not establish higher-order unification correctness.

