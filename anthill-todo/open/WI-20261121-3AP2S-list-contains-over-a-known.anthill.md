## Attributes

- id: WI-20261121-3AP2S-list-contains-over-a-known
- created: 2026-11-21T11:00:19Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T11:00:19Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`List.contains` OVER A KNOWN LIST DOES NOT ENUMERATE THE ELEMENTS A PARTIAL PATTERN MATCHES: `contains([Item(1, 10), Item(2, 20), Item(3, 10)], Item(id: ?id, tag: 10)) = true` stays conditional where it could answer `?id = 1` and `?id = 3`. This is the generator case WI-580 deferred, and the reason it was deferred does not hold here.

FOUND while modelling a shop's state as a value (the setting of WI-20261115-32WQJ). Every lookup by partial key, such as `has_order(s, Order(id: ?o, status: CREATED))`, needs the elements of a list in the state that match a pattern. `contains` cannot give them, so the model hand-writes `member(?x, cons(head: ?x, tail: ?))` / `member(?x, cons(head: ?, tail: ?t)) :- member(?x, ?t)`, the unification twins WI-580 retired from `list.anthill`. The stdlib writes the same recursion twice for itself: `reflect/typing.anthill` `list_contains`, `realization/realization.anthill` `effect_map_entry`.

WHY WI-580 STOPPED SHORT. Its increment 2 made the relational view of `contains` "a sound checker, not a generator" (design §5): a ground call decides through the bridge with the declared `eq`, and an unground one is a WI-519 residual. The case-split was deferred because it "only fires over an UNGROUND LIST, which is inherently NON-TERMINATING", "until a bodied Bool op has a TERMINATING relational consumer (§10 Q4)". A known list with a partial element is that consumer: the `match` on the list reduces at every step, so the recursion follows the list and ends at `nil`.

MEASURED on 53a0d453b (debug CLI of 2026-11-13). The code paths named below read the same on 0971ebd1a.
  1 `contains([Item(1,10), Item(2,20), Item(3,10)], Item(id: ?id, tag: 10)) = true`: 1 conditional, residual `eq(contains([…], Item(id: ?_, tag: 10)), true)`
  2 the same as a bare goal `contains(items(), Item(id: ?id, tag: 10))` (routed by `bare_bodied_bool_relation`): conditional, the same residual
  3 `pick(?b) = 2` over `operation pick(b: Bool) -> Int64 = if b then 1 else 2`: conditional, residual `eq(pick(?_), 2)`
  4 `eq(1, ?id) = true` and `eq(Item(1, 10), Item(id: ?id, tag: 10)) = true`: conditional. Correct for a written goal (§8.3: `=` never binds); listed because it is the shape the body's condition takes.
  5 control, the hand-written `member(Item(id: ?id, tag: 10), items())`: `?id = 1`, `?id = 3`, definite
  6 control, `(some ?y in [Item(1,10), Item(2,20), Item(3,10)]: ?y <=> Item(id: ?id, tag: 10))`: `?id = 1`, `?id = 3`, definite

THE CAUSE (read at 0971ebd1a). Two places, both in the WI-580 unfold:
- `kb/body_specialize.rs::folded_call_match` case-splits only a residual that is a `match` on a flexible scrutinee. Over a known list the `match` reduces, and what is left is the `cons` arm's `if eq(head, x) then true else contains(tail, x)`: an `if`, so it returns `None` and the goal delays. Row 3 is the same gap without `eq`.
- `kb/resolve.rs::anf_flatten` declines an `if` ("`if`/`let`/`lambda`/… — the caller then declines the whole unfold"), and the body's `eq(head, x)` is hoisted as a call run at its member, which never binds (§8.3). So even a split `if` would delay on its condition.

PROPOSED.
- Split an `if` whose condition is undecided, as the `match` on `true` / `false` it is: two disjoint alternatives, the condition `= true` with the then-residual and `= false` with the else-residual. Design §3.3 already describes this flattening; WI-580 increment 1 listed it as remaining, and increment 2 dropped it as not needed for the checker. Row 3 then answers `?b = false`.
- In that split, a condition `eq(a, b)` at a carrier compared by `===` (a scalar whose equality is identity, or a composite every field of which compares by structure, §8.3) narrows. Its `true` alternative is `unify(a, b)`; its `false` alternative keeps `neq(a, b)` as a test, which delays until both sides are ground. At a carrier with an `eq` of its own the condition stays a call, as today, so WI-580's soundness fix is untouched. This is the line WI-20260827-P1TPE draws for the unfold.
- Unchanged: a `=` written in a rule body still never binds (that question is WI-20260822-F0HHB's). The narrowing is the unfold's reading of an `eq` the body calls, and only where it gives the answer `===` gives.

DESIGN QUESTION TO SETTLE FIRST: is the narrowed `eq` an exception to §8.3's "`=` never binds a logical variable", or a property of the derived relational view only? Either way, kernel-language §8.3 and design §3.3 / §5 are updated to say which.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site):
- rows 1 and 2 answer `?id = 1` and `?id = 3`, both definite;
- row 3 answers `?b = false`, definite;
- duplicates collapse as the `eq` body says: `contains([Item(1,10), Item(1,10)], Item(id: ?id, tag: 10)) = true` answers `?id = 1` once;
- a carrier whose `eq` reads `k` and ignores `tag`: `contains([ae(k: 1, tag: 9)], ae(k: ?k, tag: 5)) = true` stays conditional, never a wrong definite; `wi580_member_uses_declared_eq_not_unification` and `wi580_member_over_rule_defined_eq_decides` are unchanged;
- an unground list, `contains(?l, Item(1, 10)) = true`, stays a residual and terminates; `wi580_member_relational_unground_residualizes_not_wrong` is unchanged;
- back-out: with the `if` split removed, rows 1-3 return to conditional.

