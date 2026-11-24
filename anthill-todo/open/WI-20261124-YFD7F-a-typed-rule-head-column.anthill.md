## Attributes

- id: WI-20261124-YFD7F-a-typed-rule-head-column
- created: 2026-11-24T10:02:24Z

- status: Open
- status_agent: user
- status_at: 2026-11-24T10:02:24Z

- acceptance: cargo-test

## Description

A typed rule-head column checks its whole value again at every call: a recursive rule over a typed List costs more than O(n^2)
WHO NEEDS IT. Every rule whose head types a column with a recursive sort (List, a tree) and recurses on a part of it: membership, lookup and walk rules over a cons spine, which is how anthill-traces' specifications hold their entities (WI-20261122-96QKW measured such a membership rule). Found while drafting proposal 076 (docs/proposals/076-goal-scope-in-the-search.md §7); the user asked whether the sort domain generates where it should check.

WHAT IS THERE TODAY (read from the code on 2026-11-24). install_typed_head_domain_goals (kb/typing/rules.rs) gives a clause with a head bound ?x: T two goals: __domain_guard(?x, T) IN FRONT of the written body (WI-742's conformance check, which waits on an unbound or partly bound ?x), and domain(?x, T), the fill, APPENDED after it (WI-743: a generator ahead of the body enumerates a recursive type forever). At the resolver, domain(?x, T) is apply_domain, and with ?x ground lower_apply_domain (kb/resolve.rs) turns it into the provider's fill(?x) goal, proved by the domain's clauses one constructor at a time, so a ground value is CHECKED, not generated, by walking all of it. Both goals run at EVERY call of the rule, including the rule's own recursive call on a part of a value the clause has already checked: in mem(?x, ?t) below, ?t is the tail: Self of a List[T = Int64]. And because the fill comes after the body, it is still pending when the recursive call opens the next level, so each level leaves one more fill in the resolvent, which proposal 076 measured as quadratic on its own.

MEASURED 2026-11-24 (debug build at or near 5e721bf5e; anthill query --max-depth 100000; wall time, peak RSS). Membership of the LAST element of a ground list [1, ..., n]:
  rule mem(?x: Int64, ?l: List[T = Int64]) :- (?l <=> cons(head: ?x, tail: ?)) | (?l <=> cons(head: ?, tail: ?t), mem(?x, ?t))
  n                        100              200              400
  ?l: List[T = Int64]      0.75 s / 241 MB  2.46 s / 1.1 GB  20.0 s / 7.6 GB
  ?l untyped               0.51 s / 85 MB   0.55 s / 99 MB   0.73 s / 145 MB
Time grows about eightfold per doubling. The split between the guard, the fill and the pending resolvent is not measured: no step counts were taken.

WHAT IS ASKED. A typed column whose value is already known to conform is not checked again, so the typed mem costs within a small factor of the untyped one. The approach is open; to choose before implementing:
  (a) Discharge statically: where the typer knows the argument conforms (a part of a checked value, a typed variable, a typed column of the caller), the call does not run the callee's guard and fill: the clause gets a checked entry and an unchecked body.
  (b) Remember per search the ground values that passed the fill at a type, keyed by the hash-consed term, so a tail already walked as part of its list is not walked again.
  (c) With ?x ground at the call, run the fill at the guard's place and not after the body, so no fill is pending across the recursive call. That removes the growing resolvent but still walks each tail once per level, O(n^2).
Note why the fill is not redundant beside the guard on a ground value: the guard's closed reading cannot tell [[]] from [] against List[T = Int64], and the fill refuses the first (install_typed_head_domain_goals' doc). Whatever is chosen keeps that refusal.

WHAT IS NOT ASKED. Changing what a typed column admits or refuses, or when a column with an unbound value generates. The 2^k of ground goals with several proofs (WI-20261122-P6G1P, WI-20261122-VT9S7, proposal 076): separate, though each replayed branch re-runs its checks.

DONE WHEN. A test: the typed mem above on a ground list of 400 runs in steps within a small factor of the untyped one (count steps, not time), and at 100 and 200 the steps grow linearly with n; the control is the same test before the change, where they do not. The refusals still hold: [[]] against List[T = Int64] is refused, a value of the wrong type is refused before the body runs (WI-742's rows), and WI-743's word(?w: List[T = Letter]) :- ?w <=> [?, ?, ?] still answers 27 and stops.

## Changes

### 2026-11-24T10:35:11Z — feedback — user

APPROACH PROPOSED, agreed with the user 2026-11-24 (not implemented; the typer's part below is not yet checked against the code).

(a) THROUGH THE DICTIONARY CHANNEL, not through two versions of a clause. The user: 'during call we pass dictionaries, so we can look on untyped as on translated typed'. Every call is elaborated and carries its dictionaries, so there is no untyped caller: an untyped rule is a typed one whose column types are variables, and the caller always has a place to say what it knows about each argument. The hidden parameter of a typed column gets TWO STATES, one value of two variants:
  - check with d: the caller does not know the argument conforms. The callee tests a bound value and generates for an unbound one, as today.
  - trusted, d for generation only: the typer has the column's type for the argument at that occurrence. The callee tests nothing, and uses d only when the value is not ground.
'Trusted' with no dictionary is not representable, so generation (WI-743's word(?w) answering 27) cannot be lost. A dictionary says the TYPE has a domain; it is not evidence that this VALUE is in it, which is why the second state is needed and the dictionary alone is not enough.
In mem: ?l is typed by the head, ?t is the tail of a List[T = Int64], so the recursive call passes 'trusted' and the list is walked once, at the first call. A type mentioning a variable (apply_domain(?d, ?x, B)) reads nothing from the value when the call site instantiates B's variables and passes ?d; the citation route becomes the only route. What is still walked, once: a value from outside any elaboration (a CLI or execute query argument, a host-decoded value).

TWO CAUTIONS. A type is per occurrence (WI-20261124-C6VN0: two branches of | may each type a variable), so a use in one branch does not make the other trusted. And 'trusted' rests on TYPE PRESERVATION: every binding of a variable the typer has at T is a T. Whether the typer establishes that for rule bodies is TO BE CHECKED FIRST; the approach depends on it.

FALLBACK WHERE NO TYPER ELABORATES (scaland; a value from outside): option (b), a per-search memo of ground values that passed the fill at a type, keyed by hash-consed term and type. The fill's own walk of a list visits every tail, so one walk records them all and each later call on a tail is one lookup. Not covered: values that are not hash-consed terms (occurrences, entities).

WITH EITHER: 'nothing to generate' decided in O(1) by a ground bit set when a term is hash-consed; walking the value to learn it is ground is O(n) a level again.

Option (c) (the fill at the guard's place when the value is ground at the call) removes the pending fill by itself. MEASURED 2026-11-24 (proposal 076, MEASURED): the pending fill is what makes a typed recursion's memory quadratic. cnt(?n: Int64) 208 / 537 MB at n = 1000 / 2000 against 107 MB untyped at 2000; the control chain(?n: Int64) 498 MB / 1.63 GB against 123 / 145 MB untyped. Proposal 076 Stage A (a linked continuation) makes a pending fill O(1) to carry without it.

STILL NOT MEASURED: how the typed cost splits between the guard, the fill and the pending resolvent. It decides whether the memo alone brings typed mem within the small factor DONE WHEN asks for, or the guard needs it too. Take step counts before choosing between (b) alone and (a).

