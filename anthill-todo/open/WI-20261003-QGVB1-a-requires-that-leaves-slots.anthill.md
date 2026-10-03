## Attributes

- id: WI-20261003-QGVB1-a-requires-that-leaves-slots
- created: 2026-10-03T08:59:23Z

- status: Open
- status_agent: user
- status_at: 2026-10-03T08:59:23Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A `requires` THAT LEAVES SLOTS UNWRITTEN IS CHECKED AS IF THEY WERE WRITTEN: A PROVISION OF THE REQUIRING SPEC IS REFUSED, AND A MEMBER RESTATING A PROJECTION THROUGH IT IS REFUSED TOO. (a) `sort Storage { sort C = ?; sort Key = ?; sort Val = ?; operation get(s: C, k: Key) -> Val }`, `sort MemStore { entity memStore; provides Storage[C = MemStore, Key = String, Val = Int64]; operation get(s: MemStore, k: String) -> Int64 = 0 }`, `sort Sp { sort P = ?; requires Storage[C = P]; operation size(s: Sp) -> Int64 }`, `sort Car { entity car(n: Int64); provides Sp[P = MemStore]; operation size(c: Car) -> Int64 = c.n }`: refused "'Car' provides 'Sp', which requires 'Storage', but nothing provides `Storage[C = MemStore, Key = Storage.Key, Val = Storage.Val]`" — the unwritten `Key`/`Val` are read as the rigid projections `Storage.Key`/`Storage.Val`, which MemStore's `Key = String, Val = Int64` does not match. Written `Key = ?, Val = ?` it is refused the same way ("… `Storage[C = MemStore, Key = ?, Val = ?]`"); written `Key = String, Val = Int64` it loads and `Sp.size(car(n: 42))` runs. A partial application's unwritten slot, and a written `?`, are a fresh variable — any type (kernel-language.md §8.1, Expansion during unification: `Stream[T = Int64]` ≡ `Stream[T = Int64, E = ?]`). (b) With that requirement in place, `operation op(s: Sp, x: P.Key) -> Int64` behind the member `operation op(c: Car, x: MemStore.Key) -> Int64 = 42` — the spec's own text at `P = MemStore` — is refused "parameter 2 (`x: MemStore.Key`) takes less than the spec's": the member side reduces `MemStore.Key` to `String` through MemStore's provision of Storage, the spec side leaves `P.Key` at `P = MemStore` an unreduced projection, so a member written as the spec writes it is narrower than itself. §8.7 reads a projection through the provision that LENDS the member, which the receiver's declaration names (`requires Storage[C = P]`: MemStore's provision), on both sides. Both MEASURED identically on the trees before and after WI-20260929-0RP29's ninth and tenth passes; FOUND by the tenth pass (probe S1/final/c4b_panic_rigid_projection_of_spec_parameter; that pass's row `a_rigid_type_projection_under_a_rebuilt_binding_does_not_panic` pins this program's verdict only as 'no panic, the earlier verdict' and must flip to the running one). FIX: (a) the provision check builds the requirement's goal with its unwritten and `?` slots open (fresh variables), as a call and the declaration rule read an unwritten slot; (b) the declaration rule's spec side eliminates a projection off a spec parameter through the lending provision, as the member side does. ACCEPTANCE: (a) and its `?` spelling load and run; (b) loads and `Sp.op(car(n: 1), "k")` runs to 42; a provision whose carrier provides no Storage at all, and one whose Storage binds a Key the requirement writes otherwise, still refused; the tenth pass's row flipped to the running verdict; full workspace green via rustland/scripts/test.sh.

