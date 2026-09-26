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

