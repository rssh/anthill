## Attributes

- id: WI-20261104-KBZ4F-an-operation-as-a-function
- created: 2026-11-04T06:52:22Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-11T22:34:16Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN OPERATION AS A FUNCTION VALUE CARRIES ITS PROJECTION UNGROUNDED. `g[P](x: P) -> P.Val requires Storage[C = P] = Storage.get(x)` (`MemStore provides Storage[C = MemStore, Val = Int64]`) passed to `app[A, B](f: (x: A) -> B, a: A) -> B = f(a)` as `app(g, memStore)` in `main() -> Int64` is refused "type mismatch in main.return (op-return): expected Int64, got P.Val"; the row twin — `g[P](x: P) -> Int64 effects {P.E} requires Strm[C = P] = Strm.step(x)` passed to `app[A, R](f: (x: A) -> Int64 @ {R}, a: A) -> Int64 effects {R} = f(a)` as `app(g, mem)` in `main() -> Int64 effects {Error}` (`Mem provides Strm[C = Mem, E = {Error}]`) — is refused "undeclared effect: P.E". The direct calls `g(memStore)` and `g(mem)` load (the row since WI-20261103-JGW88). MEASURED on 0eaa2e86 (found by JGW88's /code-review). MECHANISM, not traced past the first step: the eta'd arrow (`operation_as_function_value`) is built from the signature as declared, and once its ∀ is instantiated at the carrier nothing reads the projection off the carrier's provision, where a direct call does (`resolve_type_deep_value`). EXPECTED: both run to 7; at a carrier whose provision leaves the member unwritten the call is refused as a direct call is (`UnreadProjection`). ACCEPTANCE: rows, both kinds; back-outs measured; full gate green.

## Changes

### 2026-11-11T22:34:07Z — feedback — claude

DELIVERED 2026-11-11. The eta lift (operation_as_function_value) writes a projection off a parameter it quantifies — an operation's bracket parameter or a parameter of its declaring sort — as the member of the instance of the requirement that lends it: P.Val under requires Storage[C = P] is Storage[C = P].Val (projection_as_instance_member). The reference's instantiation reaches the instance's variable; every σ walk reads the member once its carrier is fixed (instance_member_at, through the requirement-goal completion a sort parameter's projection uses), and a row label reading to a row is that row's labels (decompose_effect_row_raw). app(g, memStore) and app(h, mem) run to 7. Found beside it, same root: at a slot that fixes the carrier where the value is written, applyStr(g) over (x: MemStore) -> String loaded and returned MemStore's Int64 (now refused), and applyErr(h) over @ {Error} was refused naming P.E (now runs); the sort's own clause gives the same verdicts there. At a carrier whose provision leaves the row unwritten, app(h, lz) is refused naming the requirement, as h(lz) is. Rows: wi_kbz4f_operation_value_reads_projection_test (9). LEFT, each measured on the parent with no projection: (a) a value made where the carrier is not yet fixed holds no dictionary when two sorts provide the spec — app(g2, memStore) over g2[P](x: P) -> Int64 requires Storage[C = P] loads and stops at run time ('__req_storage' not bound); (b) a let annotation does not instantiate a type-parameterized operation (let h: (x: Int64) -> Int64 = idp is refused); (c) the sort's own clause at a carrier a later argument fixes (app(Sp.t, memStore)) is refused as an unsatisfiable requirement (WI-420); (d) forwarding through a caller's own type parameter (forward[Q](y: Q) -> Q.Val = app(g, y)) is refused, as g(y) is.

