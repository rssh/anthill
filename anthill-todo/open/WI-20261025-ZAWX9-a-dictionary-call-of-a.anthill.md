## Attributes

- id: WI-20261025-ZAWX9-a-dictionary-call-of-a
- created: 2026-10-25T05:53:14Z

- status: Open
- status_agent: user
- status_at: 2026-10-25T05:53:14Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A DICTIONARY CALL OF A DEFAULTED SPEC OPERATION IGNORES ITS PROVISION'S BINDING — `resolve_op_target` reaches an instance binding only for a body-less spec op, so through a `requires` dictionary a defaulted op runs the spec's DEFAULT where the same call written by name runs the binding, or dies on an own member the interpreter cannot run. WI-1010's defect ("the default ran and the written binding meant nothing"), fixed for the call by name and never for the call through a dictionary. Found by /code-review of an inline fix under WI-885 (2026-10-25), which was reverted because it made the second shape below SILENT.

MEASURED on 724492e6 (`anthill run`), one fixture, two spellings of one call. `sort Desc { sort T = ?  operation name() -> Int64 = 1 }`; `sort Leaf { entity leaf  provides Desc[T = Leaf] }`; `operation otherName() -> Int64 = 7`; `namespace Leaf { provides Desc[T = Leaf, name = otherName] }`; `probe() = Desc.name[T = Leaf]()` (by name) and `probeDict() = viaDict[A = Leaf]()` over `viaDict[A]() -> Int64 requires Desc[T = A] = Desc.name[T = A]()` (through the dictionary).
  (1) BINDING ONLY: by name 7, through the dictionary 1 — a SILENT wrong answer, today.
  (2) the same plus a clause-defined own member (`operation name() -> Int64` and `rule name(3) :- true` in `Leaf`): by name 7, through the dictionary `OperationBodyMissing {Leaf.name}`.
  (3) an op that TAKES the carrier — `describe(x: T)`, wi1010's `an_unrunnable_own_member_is_not_a_supplier` fixture, called `viaDict(leaf())` over `requires Desc[T = A]`: by name 7, through the dictionary `OperationBodyMissing {Leaf.describe}` (measured on the WI-885 build, which did not touch this path). Shape (1) with a receiver answers by value at eval's step 3 and does not show the defect, which is why every wi1010 row passes.

MECHANISM, as read. The call by name is resolved by the typer through `carrier_override_suppliers` (kb/typing/call_class.rs): every supplier from the three routes (own member, instance binding, witness), narrowed to what the interpreter can run (`op_is_interpretable`), then arbitrated; the default fills a gap. The call through a dictionary is resolved at eval by `resolve_op_target` (`dispatch_via_sort_ops_table`, and the reflect `Dictionary.resolveOp` / `Dictionary.ops` faces): the raw `sort_ops_lookup` own member WHATEVER it is, else `instance_fact_op_binding` — but that fallback goes through `lookup_spec_op_dispatch`, which answers only for a BODY-LESS spec op, so for a defaulted op it is unreachable and the spec op itself (its default) is returned. Two readers of one question with different rules.

WHAT. For a spec op with a default body, the dictionary picks what the call by name picks: the same supplier set, the same interpretability filter, the default only where no route supplies one, and a loud answer where the by-name route refuses. The inline attempt (filter the own member by `op_is_interpretable` when the spec op has a body) is NOT it: with the binding still unreachable it turned (2) from a fault into a silent 1. Points a fix has to settle, found by that review:
  * CALLERS PASS MIXED SYMBOLS — the spec op (eval's dictionary dispatch, `resolveOp`) and an already-concrete member (`build.rs` `threads_instance`'s `impl_op`, eval's WI-415 route, `Dictionary.ops`' table entries) — so "defaulted" must be read off the dispatched SPEC op, not off the argument; and `Dictionary.ops` and `Dictionary.resolveOp` must keep agreeing (`dict_ops`' doc promises it).
  * THE HOT PATH. `resolve_op_target` runs per dictionary call at eval; the supplier set walks the spec's provision bucket and `op_is_interpretable`'s body leg builds an `OpInfoRecord`. Measure, or answer once at load (the sort-ops table) instead of per call.
  * THE TYPER READS IT TOO (`defaulted_call_target`, `threads_instance`): what it classifies such a call as moves with it — a row must drive that, not only eval.
  * WI-1042's shape — a carrier providing two specs with one short name, where `sort_ops_lookup` returns one arbitrarily — changes answer on the dictionary route; say which.
  * WI-1012 refuses a tie at load for the call by name; the dictionary route's answer to a tie (or the reason none can reach it) has to be stated.

ACCEPTANCE: shapes (1)–(3) answer the same by name and through a `requires` dictionary (7 each, the binding), each driven on BOTH routes, with a receiver-less op among them; a control that a runnable own member answers on both, and that a carrier no route supplies runs the default on both; `Dictionary.ops` and `Dictionary.resolveOp` agree on the fixture; the change backed out reds the rows that measure it; the cost on the dictionary path measured; full workspace green via rustland/scripts/test.sh.

REFERENCE: WI-1010 (the by-name half, `carrier_override_suppliers`), WI-876 (the interpretability filter and the `sub` ↔ `Numeric.sub` collision it excludes), WI-842 (`spec_op_suppliers_for_carrier`, one owner of the three routes), WI-431 (instance bindings), WI-1012 (supplier ties), WI-1042, WI-885 (where it was found; its delivery note records the review).

