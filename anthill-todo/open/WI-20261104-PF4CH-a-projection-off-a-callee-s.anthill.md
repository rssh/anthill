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

## Changes

### 2026-11-12T05:12:38Z — feedback — claude

ROW ADDED 2026-11-12, from WI-20261104-KBZ4F (c7ad2ef0): the same forwarding through a function value. `forward[Q](y: Q) -> Q.Val requires Storage[C = Q] = app(g, y)` over `g[P](x: P) -> P.Val requires Storage[C = P]` and `app[A, B](f: (x: A) -> B, a: A) -> B = f(a)` is refused "type mismatch in forward.return (op-return): expected Q.Val, got Storage[C = ?Q].Val", as `g(y)` is refused "expected Q.Val, got P.Val". Since KBZ4F the value writes its projection as the member of the requirement's instance, `Storage[C = P].Val`, read at the carrier once it is concrete; at the caller's rigid `Q` it stays the instance member, which is `Q.Val` under the caller's `requires Storage[C = Q]`. EXPECTED with this ticket: both spellings load. KBZ4F's control row `forwarding_through_a_type_parameter_is_refused_as_the_direct_call_is` (wi_kbz4f_operation_value_reads_projection_test) asserts the refusal today and is rewritten to the acceptance then.

