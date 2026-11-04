## Attributes

- id: WI-20261104-PF4CH-a-projection-off-a-callee-s
- created: 2026-11-04T06:52:19Z

- status: Open
- status_agent: user
- status_at: 2026-11-04T06:52:19Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A PROJECTION OFF A CALLEE'S TYPE PARAMETER IS NOT RE-KEYED TO THE CALLER'S OWN PARAMETER. `g[P](x: P, k: P.Key) -> P.Val requires Storage[C = P] = Storage.get(x, k)` called from `h[Q](y: Q, k: Q.Key) -> Q.Val requires Storage[C = Q] = g(y, k)` is refused "type mismatch in h.return (op-return): expected Q.Val, got P.Val"; the row twin — `g[P](x: P) -> Int64 effects {P.E} requires Strm[C = P] = Strm.step(x)` called from `h[Q](y: Q) -> Int64 effects {Q.E} requires Strm[C = Q] = g(y)` — is refused "expected declared: [Q.E], got undeclared effect: P.E", and under `effects {}` the refusal names the callee's `P.E`, which the caller does not have. MEASURED on 0eaa2e86 (found by WI-20261103-JGW88's /code-review). MECHANISM: a call grounds a type-parameter `RigidProjection` only at a CONCRETE fill (`ground_rigid_projection_if_concrete`, from `resolve_type_deep_value`); where the call fills `P` with the caller's rigid `Q`, the projection's subject — an identity slot the σ walk does not rewrite (WI-400) — stays the callee's `P`. Rewriting the subject `P := Q` is a substitution, not the binding of `P.K ≡ Q.K` WI-400 forbids. EXPECTED: both load, and run through `h` at a concrete carrier; `h` under `effects {}` is refused naming `Q.E` (or the instance's row); a call filling `P` with another parameter's carrier stays apart. ACCEPTANCE: rows for the type and the row, on an operation's clause and a sort's; back-outs measured; full gate green.

