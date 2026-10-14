## Attributes

- id: WI-20261013-GFS6A-068-d1a-a-woven-call-is
- created: 2026-10-13T08:03:25Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-14T15:07:45Z

- acceptance: cargo-test

- tags: proposal-068

## Description

068 D1a — A WOVEN CALL IS SUSPENDED ON ITS DICTIONARY (068 §2.1; item 1 of WI-20260926-DSEXA). A call woven as `apply_within(fn, args, requirements = [?d])` waits with `?d` among its blockers (WI-20260926-CYNPE's mechanism), read off the call; a dictionary that turns concrete with no supplier for the member leaves the call UNREDUCED — parked, a named residual cause (WI-20260923-KCNA0's acceptance at run time), never a definite failure. NEEDS NOTHING OF 7D48J: the weave is WI-20260925-P7VP4's as delivered, and both programs below are measured on it.

FROM WI-20261003-4DYR6, measured 2026-10-13 on 34b21d28 with that change. (1) Over `sort Sp { sort T = ?; operation size(s: Sp) -> Int64; operation dflt(s: Sp) -> Int64 = 7 }`, `sort Car { entity car(n: Int64); provides Sp[T = Int64]; operation size(c: Car) -> Int64 = 42; operation dflt(c: Car) -> Int64 = 43 }`, `rule sized(?s, ?x) :- Sp.size(?s, ?x)`, `rule dflted(?s, ?x) :- Sp.dflt(?s, ?x)`: the goals `sized(car(n: 1), ?x)` and `dflted(car(n: 1), ?x)` each give one conditional row, residual `find_dictionary(Sp, size, car(n: 1), out: ?_), size(car(n: 1), ?_)` (and the same for `dflt`) — the carrier is ground and provides `Sp`, and the dictionary is never fetched. `Sp.dflt(car(n: 1), ?x)`, written with its receiver, answers 43. The same before 4DYR6. (2) The same sorts without `sort T = ?` (`provides Sp`): `sized(car(n: 1), ?x)` answers 42, and `dflted(car(n: 1), ?x)` answers 7 — a woven DEFAULTED call runs the default where the dictionary's sort declares the member; `Sp.dflt(car(n: 1), ?x)` answers 43. With `dflt` the only operation of `Sp` (no body-less one beside it) the call is not woven and `dflted(car(n: 1), ?x)` answers 43.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; driven, back-outs at their sites): a woven call whose dictionary is bound only by a LATER goal answers once it is bound, and conditionally if never; (1) answers 42 and 43; (2) answers 43; KCNA0's rows name their cause. CONTROLS: P7VP4's and SHED7's rows unchanged; classic-mini unchanged (tiny-sat 2, alphabet-words 27/12/100, map-colouring 6).

## Changes

### 2026-10-14T15:07:42Z — feedback — claude

DELIVERED in 4d22dbc2. (1) answers 42 and 43, (2) answers 43; a woven call whose dictionary a later goal binds answers once it is bound (Sp.dflt(?s, ?x), ?s <=> car(n: 1) is 43, and in a value slot), and is a conditional row with no undecided cause if never; KCNA0's q1, q2 and fwd are each one undecided row whose cause is Unreduced, where a debug build aborted. ?d was already among the call's blockers (CYNPE's coarse ones walk an ApplyWithin's requirements); the read before the call was wrong at four places: a self-represented spec's elements now come off the carrier's provision (witness and anchor goals alike, a written bracket element still selecting); a goal a receiver made no longer takes the refinement leaf; an unbound carrier at an abstract bound waits; an inferred read at a ground carrier with no provider is UNREDUCED, and at the bridge an operation's own pinned requirement no provider answers is a recorded absence whose read is UNREDUCED. PRVA2's four rows over a woven call at carriers no provision binds moved from an empty answer to UNREDUCED, by the user's 2026-09-30 note on DSEXA. Rows: wi_gfs6a_woven_call_waits_on_its_dictionary_test (17), back-outs at its header. LEFT FOR THE USER: a read the author WROTE (require[X]) at a carrier with no provider still FAILS while the inferred one is UNREDUCED (measured: written(van(n: 1), ?x) no solutions, inferred(van(n: 1), ?x) undecided), though kernel-language 8.1 says the inferred condition reads as though require[X] stood before the call; and 8.1 has no sentence yet for the undecided answer. NOT DONE: the woven call itself waits on ?d while its read is the parked, unreduced goal — the answer names the cause through the read.

### 2026-10-14T16:11:46Z — feedback — claude

CORRECTION (38c9e23b, decided with the user 2026-10-14): a missing provider is no undecided answer. A requirement read at a carrier known to provide no instance FAILS, written or inferred, as before this ticket; KCNA0's q1, q2 and fwd fail by a complete search (the call has no value, Stuck::Absent), not an undecided row. The UNREDUCED reading of the note above is withdrawn. Also delivered in 38c9e23b: a selection an operation makes reaches the rule it cites when the operation runs from a rule (desc = viaRule[A = Int64, WeakOrd = Descending](1, 5): 4, was -1), and a carrier type that pins no carrier builds no goal (viaSp(s: Sp): 43). A provider passed through a generic rule that calls another generic rule is 060's S7, on WI-20260911-5G28A.

