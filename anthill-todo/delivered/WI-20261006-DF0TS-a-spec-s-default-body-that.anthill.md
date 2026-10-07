## Attributes

- id: WI-20261006-DF0TS-a-spec-s-default-body-that
- created: 2026-10-06T06:39:57Z

- status: Delivered
- status_agent: codex
- status_at: 2026-10-07T12:20:30Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SPEC'S DEFAULT BODY THAT FORWARDS ITS OWN INSTANCE LOADS AND DIES — `__req_self` is not bound in the frame the body runs in. `sort Coll { sort C = ?; operation size(c: C) -> Int64; operation viaHelper(c: C) -> Int64 = Helper.twice(c); operation viaBuild(c: C) -> Int64 = Holder.read(hold(c)) }`, `sort Helper { sort X = ?; requires Coll[C = X]; operation twice(x: X) -> Int64 = Coll.size(x) + Coll.size(x) }`, `sort Holder { sort X = ?; requires Coll[C = X]; entity hold(x: X); operation read(h: Self) -> Int64 = match h case hold(x) -> Coll.size(x) }`, `sort L { entity l(n: Int64); provides Coll[C = L]; operation size(c: L) -> Int64 = c.n }`. `operation go() -> Int64 = Coll.viaHelper(l(n: 3))` loads clean and dies `Internal("var_ref(__req_self) unbound in requirement position (running `Coll.viaHelper`; frame binds [])")`; `operation go2() -> Int64 = Coll.viaBuild(l(n: 3))` dies the same way, running `Coll.viaBuild`. EXPECTED: 6 and 3. `Helper.twice(c)` owes `Coll[C = X]` at the body's own carrier, and the typer supplies it with the instance the body runs at — the dictionary a default body is dispatched through, `__req_self`. Entered as `Coll.viaHelper(l(…))` from an operation outside the spec, the body's frame binds nothing, so the forward reads a slot nobody filled. MEASURED on the tree that delivers WI-20261005-KSSA4 and on its parent commit 02cdda6e alike: not introduced by that ticket, found while measuring it. Its row `wi_kssa4_spec_typed_value_test …a_specs_default_body_builds_over_its_own_instance` builds the value in a default body and does not call through it, which is why it runs. NOT MEASURED: the same bodies reached through a caller that holds `Coll` in its own `requires`, and a default body inherited by a provider that overrides nothing else. ACCEPTANCE: both programs answer, 6 and 3 — or, if a default body cannot be handed its own instance on that entry, are refused at load naming the requirement; the KSSA4 row is extended to call through the value it builds; full workspace green via rustland/scripts/test.sh. REFERENCE: kernel-language §5.2 (a spec's default body at its own carrier), §8.7; `dep_is_owner_self_instance` in rustland/anthill-core/src/kb/typing/.

## Changes

### 2026-10-07T12:20:29Z — feedback — codex

Implemented DF0TS in call classification. Leaf instances now supply the self dictionary when entering their own spec default, using the same concrete ApplyWithin path as conditional instances. The existing resolve_op_target equality guard still excludes redirects to a different sorts member. A receiver-precise enclosing requirement can now forward its dictionary to a default; the original sole-clause gate remains for receiver-less calls. Added seven executing regression/control tests: direct helper returns 6, direct construction/read returns 3, requirement-backed caller returns 9, provider inheriting every operation returns 21, two distinct carrier requirements return 31, and explicit caller-selected witness returns 300; host entry remains a passing control. Extended KSSA4 own-instance test to call Holder.read on the value it builds (returns 3). Focused set: eight passed. Back-out measurement on the final set: six regressions fail with __req_self unbound, while host entry and extended KSSA4 control pass. Final Rust workspace via rustland/scripts/test.sh: 8750 passed, 0 failed, 14 ignored. Scala sbt testFull: 600 passed, 0 failed. Standard library, examples, and existing redirect/receiver-less controls green. Manual code review and git diff --check passed; /code-review skill unavailable and not run. No canonical specification changes. Open unblocked queue after claim: 163.

