## Attributes

- id: WI-20261105-0BD56-a-dispatch-through-a-run-time
- created: 2026-11-05T17:31:03Z

- status: Open
- status_agent: claude
- status_at: 2026-11-05T17:31:03Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-073

## Description

A DISPATCH THROUGH A RUN-TIME DICTIONARY THAT LANDS ON A MEMBER OF A THIRD SORT READING ITS OWN requires DIES Internal (found by /code-review on WI-20261013-DEY66, 2026-11-05; the typer-classified route is WI-20261102-6GAS1's, delivered in ab6d7288). MEASURED on ab6d7288, the same on fd640523, over WI-1037's program (wi1037_requires_impl_rule_body_test.rs, program: Desc { sort T = ?; operation describe(x: T) -> Int64 }, Leaf provides Tag[G = Leaf] answering 7, LeafDesc { sort L = ?; requires Tag[G = L]; operation describeLeaf(x: L) -> Int64 = Tag.tagval(x) }, namespace Leaf provides Desc[T = Leaf, describe = LeafDesc.describeLeaf] end): operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x) and useGen() -> Int64 = gen(leaf()) — interp.call of useGen returns Internal("deferred dispatch frame-push: dispatch of Desc.describe landed on LeafDesc.describeLeaf, whose parent LeafDesc is neither the spec nor the provider of the dictionary (0 slot(s) …), so its 1 requirement slot(s) cannot be filled"), and rule viaGen(?r) :- ?r <=> gen(leaf()) PANICS the CLI (bridged_value's internal-error assert). gen's Desc slot is the dictionary for Desc at Leaf, laid out for (Desc, Leaf), and carries nothing for LeafDesc; the frame push (eval's expand_dispatching_dict) has no stamp to correct, unlike the typer route 6GAS1 fixed (typing::build::third_sort_member_dict). DECISION NEEDED: where the third sort's chain comes from — the provision's dictionary layout (Leaf's provision of Desc owes LeafDesc's requires at L = Leaf, as a provision condition would), or the arguments at entry (enter_operation filling the member sort's slots from the values, as fill_missing_op_scoped_slots fills the op half; the comment at requirements_for_value_directed_impl records that a value loses a conditional provision's sub-dictionaries). ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): useGen() answers 7 through the interpreter, viaGen 7 with no panic; a provider of Desc at a second sort with its own LeafDesc-style member answers its own value; 6GAS1's rows (wi_dey66_per_consumer_reductions_test's a_dispatch_to_a_third_sorts_member_*) and WI-1037's unchanged.

## Changes

### 2026-11-05T17:31:27Z — feedback — claude

DECIDED WITH THE USER (2026-11-05), correcting the description: there is NO run-time route. The dictionary gen's slot holds is the one the TYPER builds at load, at the call gen(leaf()) in useGen (gen's own requires Desc[T = A] at A = Leaf); the run only carries it. That dictionary is laid out for (Desc, Leaf) and omits what the provision's member needs: Leaf's provision of Desc maps describe to LeafDesc.describeLeaf, whose sort requires Tag[G = L], i.e. Tag[G = Leaf] at the provision's binding. THE RULE: a dictionary built for a provision whose member lives in a third sort carries that sort's requirements, resolved at the provision's binding; where nothing supplies them, it is a LOAD error (no value-filled frame at entry — the description's second option is rejected). So the acceptance's rows stand (useGen 7, viaGen 7 with no panic), and a row is added: with no provider of Tag at Leaf, the program is refused at load, naming the requirement.

### 2026-11-06T06:26:31Z — feedback — claude

PLACED UNDER PROPOSAL 073 WITH THE USER 2026-11-06 (docs/proposals/073-abstract-values-are-instances.md). Re-run on 3395af90 over the description's program with `operation probe() -> Int64 = Desc.describe(leaf())` and `operation useGen() -> Int64 = gen(leaf())`, read through `rule rProbe(?r) :- unify(?r, probe())` and `rule rUse(?r) :- unify(?r, useGen())`: `rProbe` answers 7 (the call typed at `Leaf`, 6GAS1's route); `rUse` panics the CLI with the frame-push Internal error quoted above. The rule decided 2026-11-05 is 073 §5.4's function-value rule applied to a provision's member: `describe = LeafDesc.describeLeaf` reads as `describe = lambda (x: Leaf) -> LeafDesc.describeLeaf(x)`, the call in it typed at `L = Leaf` and passing `Leaf`'s `Tag`, built at load; with no `Tag` at `Leaf` the program is refused at load. It is a fifth case of 073 stage 2 (every call passes what its callee reads), one that stage 2's trace of the slot fill did not see: the program dies at the frame push, before any slot is filled. Tagged proposal-073; WI-20261105-89J6K depends on this ticket.

