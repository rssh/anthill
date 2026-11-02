## Attributes

- id: WI-20261102-6GAS1-a-cross-sort-call-of-a-spec
- created: 2026-11-02T07:07:09Z

- status: Open
- status_agent: claude
- status_at: 2026-11-02T07:07:09Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A CROSS-SORT CALL OF A SPEC OPERATION WHOSE SUPPLIED MEMBER'S SORT DECLARES `requires` FAILS IN AN OPERATION BODY: run as a program it dies with an internal evaluator error, and reached from a rule with an argument that is not yet a value it panics the CLI. Found on WI-20260925-SHED7, probing the resolver's fold.

MEASURED on 5476eece, the same on f0d38c95. WI-1037's program (`wi1037_requires_impl_rule_body_test.rs`, `program`): `Desc { sort T = ?; operation describe(x: T) -> Int64 }`, `Tag`, `Leaf provides Tag[G = Leaf]` answering 7, `LeafDesc { sort L = ?; requires Tag[G = L]; operation describeLeaf(x: L) -> Int64 = Tag.tagval(x) }`, `namespace Leaf provides Desc[T = Leaf, describe = LeafDesc.describeLeaf] end`, and at namespace level `operation probe() -> Int64 = Desc.describe(leaf())`.

- `probe()` run as a program (`anthill run`, a `Main` printing it): "error: internal evaluator error: deferred dispatch frame-push: dispatch of `Desc.describe` landed on `LeafDesc.describeLeaf`, whose parent `LeafDesc` is neither the spec nor the provider of the dictionary (0 slot(s) — 0 for spec `Desc`'s requires chain then 0 for provider `Leaf`'s), so its 1 requirement slot(s) cannot be filled". From a rule (`rule answer(?r) :- probe(?r)`) the same call answers 7, WI-1037's OP row, because the resolver's fold bridges the inner call itself with its requirements resolved (`reduce_op_value`, the NeedsDict arm). WI-1037's comment there names the cause: eval reaches a nested `ConcreteApplyWithin` through `start_apply_same_sort`, which installs the classification's `dispatch_dict` and nothing else, and that is `None` for a cross-sort call from a caller with no enclosing sort.
- With `describe(x: T, xs: List[T = Int64])`, `describeLeaf` matching on `xs` (`case cons(h, r) -> Tag.tagval(x) + h`) and `probe() = Desc.describe(leaf(), [1, 2])`: `rule answer(?r) :- probe(?r)` PANICS, "panicked at anthill-core/src/kb/resolve.rs:12845:9: bridged_value: internal evaluator error bridging `probe`: internal evaluator error: deferred dispatch frame-push: …" (the same). With `Desc.describe(leaf(), one())`, `one() -> List[T = Int64] = [1, 2]`, the same panic: the fold's inner bridge declines an argument that is still a call (WI-20261016-5CDN5) or is handed the operation body's literal unevaluated (the sibling ticket on the fold's literal), and the enclosing bridge runs `probe` through eval's path above. The rule-body call `rule direct(?r) :- Desc.describe(leaf(), [1, 2], ?r)` answers 8.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): `probe()` run through the interpreter answers 7, and 8 with the list argument and with `one()`; `answer` answers 7 and 8 with no panic; WI-1037's rows unchanged.

## Changes

### 2026-11-02T07:07:30Z — feedback — claude

The sibling ticket on the fold's literal, named in the description, is WI-20261102-989Z0 (tagged proposal-068).

