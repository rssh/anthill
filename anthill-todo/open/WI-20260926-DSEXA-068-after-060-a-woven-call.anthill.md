## Attributes

- id: WI-20260926-DSEXA-068-after-060-a-woven-call
- created: 2026-09-26T09:54:11Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T09:54:11Z

- acceptance: cargo-test

- depends_on: WI-20260926-K4JGC-an-operation-call-in-a-rule, WI-20260926-7D48J-one-typing-of-a-rule-clause

- tags: proposal-068

## Description

068 AFTER 060: A WOVEN CALL WAITING FOR ITS DICTIONARY IS SUSPENDED ON IT; THE PER-CONSUMER REDUCTIONS RETIRE; THE WI-580 UNFOLD THREADS DICTIONARIES. Step D1 of the 068/060 sequence — the part of proposal 068 that needs 060's requirement channel.

 1. DICTIONARY BLOCKERS (068 §2.1). A call woven by P7VP4 as `apply_within(fn, args, requirements = [?d])` is SUSPENDED with `?d` among its blockers (WI-20260926-CYNPE's mechanism): typing created `?d` and the goal that may bind it, so the blocker is read off the call, not discovered. A dictionary that turns CONCRETE with no supplier for the member makes the call UNREDUCED — parked, never retried, a NAMED residual cause (WI-20260923-KCNA0's acceptance at run time).
 2. RETIRE THE PER-CONSUMER REDUCTIONS (068 §8 step 3): `reduce_op_value`'s call-by-name fold, `body_specialize`'s reducer and `unify_values`' evaluate-on-reach become WI-20260926-K4JGC's walker. Goal arguments are evaluated before the head match, so `unify_match_values` stays structural.
 3. THE UNFOLD (068 §8 step 4): `unfold_eq_operand` reads OTHER through WI-20260926-K4JGC's strategy and threads dictionaries as clause conditions (as P7VP4 does for rule-body calls) instead of declining every operation with `requires`; WI-20260827-XBHX3's gate goes. XBHX3's rows: `C.bpick(?c) = box(v: C.tag(red()))` answers `?c = red` definite; `C.pick(?c) = C.mk(red())` (custom `Eq`, WI-20260827-P1TPE) is never a wrong refutation; `append(?a, [3]) = append(?b, [4])` terminates.
 4. kernel-language §5.3 ("what the gate still declines") and §8.1's rule-body typing sentence.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): a woven call whose dictionary is bound only by a LATER goal answers once it is bound, and conditionally if never; KCNA0's rows name their cause; XBHX3's three rows as above; no consumer reduces an operand by its own path (the retired functions are gone, not bypassed). CONTROLS: P7VP4's and SHED7's rows unchanged; classic-mini unchanged (tiny-sat 2, alphabet-words 27/12/100, map-colouring 6).

## Changes

### 2026-09-30T04:03:44Z — feedback — user

FROM WI-20260926-K4JGC (user, 2026-09-30): P7VP4's load-time refusal to weave an UNPINNED body-less spec op in a value slot (inferred_demand) was KEPT, although 068-implementation §1.3 says it 'goes with K4JGC'. Removing it gives a call like Set.insert(...) a find_dictionary(…, out: ?d) condition that DontFires at a ground carrier no provider supplies — a DEFINITE failure, where 068 §2 says such a call is UNREDUCED (undecided, never false). K4JGC dispatches the call at run time by its ground carrier instead (reduce_op_value's dispatch_body_less, now on for every evaluated call), which gives the right value where a provider exists (wi_p7vp4_rule_body_requirements_test::a_body_less_operand_stays_the_term_the_rule_wrote: ?s = num(v: 9)). Retiring the refusal belongs here, with dictionary blockers: a find_dictionary that finds NO provider at a ground carrier must answer UNREDUCED, not fail.

### 2026-10-08T07:06:30Z — feedback — claude

FROM WI-20260925-P7VP4 (2026-10-08, 81ea3c9e): item 3's shape at an operation with its own `requires`, pinned. `rule lit(?c) :- ?c = Util.sign(1, 5)` over `sign[A](x: A, y: A) requires WeakOrd[T = A]` loads and answers one UNDECIDED row with `?c` free (relation_floundered when an operation reads it), where `?c <=> Util.sign(1, 5)` answers -1. Row: wi_p7vp4_rule_body_requirements_test::an_operations_own_requires_is_inferred_in_a_value_slot_and_refused_as_an_eq_operand (its `lit` half), which turns when the unfold threads dictionaries. The same operand at rule variables is a load error today and is recorded on WI-20260926-7D48J.

