## Attributes

- id: WI-20261013-GFS6A-068-d1a-a-woven-call-is
- created: 2026-10-13T08:03:25Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:03:25Z

- acceptance: cargo-test

- tags: proposal-068

## Description

068 D1a — A WOVEN CALL IS SUSPENDED ON ITS DICTIONARY (068 §2.1; item 1 of WI-20260926-DSEXA). A call woven as `apply_within(fn, args, requirements = [?d])` waits with `?d` among its blockers (WI-20260926-CYNPE's mechanism), read off the call; a dictionary that turns concrete with no supplier for the member leaves the call UNREDUCED — parked, a named residual cause (WI-20260923-KCNA0's acceptance at run time), never a definite failure. NEEDS NOTHING OF 7D48J: the weave is WI-20260925-P7VP4's as delivered, and both programs below are measured on it.

FROM WI-20261003-4DYR6, measured 2026-10-13 on 34b21d28 with that change. (1) Over `sort Sp { sort T = ?; operation size(s: Sp) -> Int64; operation dflt(s: Sp) -> Int64 = 7 }`, `sort Car { entity car(n: Int64); provides Sp[T = Int64]; operation size(c: Car) -> Int64 = 42; operation dflt(c: Car) -> Int64 = 43 }`, `rule sized(?s, ?x) :- Sp.size(?s, ?x)`, `rule dflted(?s, ?x) :- Sp.dflt(?s, ?x)`: the goals `sized(car(n: 1), ?x)` and `dflted(car(n: 1), ?x)` each give one conditional row, residual `find_dictionary(Sp, size, car(n: 1), out: ?_), size(car(n: 1), ?_)` (and the same for `dflt`) — the carrier is ground and provides `Sp`, and the dictionary is never fetched. `Sp.dflt(car(n: 1), ?x)`, written with its receiver, answers 43. The same before 4DYR6. (2) The same sorts without `sort T = ?` (`provides Sp`): `sized(car(n: 1), ?x)` answers 42, and `dflted(car(n: 1), ?x)` answers 7 — a woven DEFAULTED call runs the default where the dictionary's sort declares the member; `Sp.dflt(car(n: 1), ?x)` answers 43. With `dflt` the only operation of `Sp` (no body-less one beside it) the call is not woven and `dflted(car(n: 1), ?x)` answers 43.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; driven, back-outs at their sites): a woven call whose dictionary is bound only by a LATER goal answers once it is bound, and conditionally if never; (1) answers 42 and 43; (2) answers 43; KCNA0's rows name their cause. CONTROLS: P7VP4's and SHED7's rows unchanged; classic-mini unchanged (tiny-sat 2, alphabet-words 27/12/100, map-colouring 6).

