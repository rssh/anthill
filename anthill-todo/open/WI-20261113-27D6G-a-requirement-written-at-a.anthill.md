## Attributes

- id: WI-20261113-27D6G-a-requirement-written-at-a
- created: 2026-11-13T08:46:17Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T08:46:17Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A REQUIREMENT WRITTEN AT A PROJECTION OF A DEFAULTED MEMBER IS NOT THE ONE THE CALL READS — over `sort Sz { sort T = ?  sort U = ? default Int64  operation sz(x: T) -> U }`, `sort Box { sort A = ?  sort B = ? default Int64  entity box(a: A) }` and `sort Leaf { entity leaf  provides Sz[T = Leaf, U = Int64]  operation sz(x: Leaf) -> Int64 = 3 }`, `operation f2(b: Box, x: b.A) -> b.B requires Sz[T = b.A, U = b.B] = Sz.sz(x)` is refused at load, "no impl matches — unresolved: `Sz[T = b.A, U = Int64]`": the call's goal reads `b.B` through `B`'s default as `Int64`, the clause keeps `b.B`, and the cover does not see them as one. The requirement a parameter typed at a spec over a parameter stands for (proposal 073 §2) is refused the same way: `operation f(s: Sz, x: s.T) -> s.U = Sz.sz(x)`, "unresolved: `Sz[T = s.T, U = Int64]`", the instance's entry being `Sz[T = s.T, U = s.U]`. Measured 2026-11-13: the written clause on 86a8c7dd, both on WI-20261105-P0QGF part 2's tree. NOT A REPAIR, measured: writing the instance's entry from the parameter's own bindings with the default filled (`Sz[T = s.T, U = Int64]`) answers 3 there and breaks the other side — `Hold.ask[C = h.C]()` over `h: Hold[C = Buf[…]]` is then refused "unresolved: `Hold[C = h.C]`", the bracket's `h.C` not read through `h`'s type (`wi_2kv4y_unfixed_carrier_test::the_advised_bracket_reads_the_instance_in_scope`). WHAT: one reading of a projection off a parameter on both sides of the cover — the requirement, and the call's goal from its arguments, its result and its bracket — so a member the parameter's type writes or defaults is one type in each. CONTROL: both programs above answer 3; the `Hold.ask[C = h.C]()` row keeps 100; a written `requires Desc[T = b.V]` with `b.V` open keeps answering (`wi_p0qgf_spec_instance_values_test::a_spec_body_at_a_written_projection_requirement`). Found with P0QGF part 2's /code-review (filed with the user).

