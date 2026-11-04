## Attributes

- id: WI-20261104-KBZ4F-an-operation-as-a-function
- created: 2026-11-04T06:52:22Z

- status: Open
- status_agent: user
- status_at: 2026-11-04T06:52:22Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN OPERATION AS A FUNCTION VALUE CARRIES ITS PROJECTION UNGROUNDED. `g[P](x: P) -> P.Val requires Storage[C = P] = Storage.get(x)` (`MemStore provides Storage[C = MemStore, Val = Int64]`) passed to `app[A, B](f: (x: A) -> B, a: A) -> B = f(a)` as `app(g, memStore)` in `main() -> Int64` is refused "type mismatch in main.return (op-return): expected Int64, got P.Val"; the row twin — `g[P](x: P) -> Int64 effects {P.E} requires Strm[C = P] = Strm.step(x)` passed to `app[A, R](f: (x: A) -> Int64 @ {R}, a: A) -> Int64 effects {R} = f(a)` as `app(g, mem)` in `main() -> Int64 effects {Error}` (`Mem provides Strm[C = Mem, E = {Error}]`) — is refused "undeclared effect: P.E". The direct calls `g(memStore)` and `g(mem)` load (the row since WI-20261103-JGW88). MEASURED on 0eaa2e86 (found by JGW88's /code-review). MECHANISM, not traced past the first step: the eta'd arrow (`operation_as_function_value`) is built from the signature as declared, and once its ∀ is instantiated at the carrier nothing reads the projection off the carrier's provision, where a direct call does (`resolve_type_deep_value`). EXPECTED: both run to 7; at a carrier whose provision leaves the member unwritten the call is refused as a direct call is (`UnreadProjection`). ACCEPTANCE: rows, both kinds; back-outs measured; full gate green.

