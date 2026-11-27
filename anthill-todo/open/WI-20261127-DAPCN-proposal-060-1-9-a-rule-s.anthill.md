## Attributes

- id: WI-20261127-DAPCN-proposal-060-1-9-a-rule-s
- created: 2026-11-27T18:23:40Z

- status: Open
- status_agent: user
- status_at: 2026-11-27T18:23:40Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing, proposal-060.1

## Description

PROPOSAL 060.1 §9 — A RULE'S TYPES ARE KNOWN AT LOAD, AS AN OPERATION'S ARE (docs/proposals/060.1-written-rule-requirements.md §9, draft written with the user 2026-11-27, commit a5e2953df). Its stages S1–S5, S1 first.

WHAT §9 SAYS: (1) an introducer needs no guard — `rule tag[T](x: Wrap[T = T]) :- holder(h: x)` (refused today by WI-582); (2) a rule's type parameter is rigid in its body and fixed at each citation by bracket, arguments or expected type, a citation that fixes it by none refused at load, a query too ("uncited, the value decides", §8.9/§8.10, withdrawn); (3) the type variable of a slot a head leaves unfilled is created as an operation's is — the projection off the column at the top level (WI-1059), a fresh rigid when nested (WI-1061), a written `?t` quantified (WI-1FKR2), `?` the omitted slot — so `res: List[T = x.T]` becomes writable in a rule head; (4) a relation whose column type has an open slot is parametrized (`sort Holder[T] { entity holder(h: Wrap[T = T]) }`), each fact at its type at load, written or inferred alike, and a goal over it at the rule's `T` SELECTS its facts by type through the discrimination tree — the loader writes the fact's type into its stored head as a hidden argument, walked FIRST, and the goal writes its citation's type (leading positional or a new step after `Arity`, an interned-id key or a walk of the type: measured and decided here, at the tree); (5) nothing reads a type off a value; (6) only what is required is passed — a typed column's `SortDomain` is implicit (its citation passes `SortDomain[T = T]`, the column's own built through the sort's conditional provision), every other requirement written, a goal at a `T` no column covers refused at load without its guard (`rule some[T]() :- SortDomain[T = T], holder(h: ?w)`).

CARRIED FROM WI-20260911-5G28A (rejected as superseded by this ticket, 2026-11-27): (a) S6, demo2 end to end — `wi_5g28a_rule_dictionary_test.rs` §3, `countAt[X = Colour, Score = ByHeat]()` and `topAt[X]()`'s `Wrap[T = X].top.head.x` (060-implementation §7.3's table: `1`, and `wrap(red())` / `wrap(blue())` by provider), re-measured first; (b) the 0RRQP row of 2026-10-21 — `operation at[A](e: List[T = Wrap[T = A]]) -> Int64 effects {Error} = tag3(e).takeN(5).length()` over `rule tag3(?w: List[T = Wrap[T = ?t]], ?x: Wrap[T = ?t]) :- holder(h: ?x)` answers 2 at `A = Colour` (a solution at `Int64` read under `Colour`): refused at the citation, naming `requires SortDomain[T = A]` — flips the stated limit `wi_0rrqp_clause_typed_through_constructor_test::a_bound_at_the_callers_parameter_is_checked_through_its_domain_only`.

ALSO FLIPS (measured 2026-11-27, §9's measurements): `rule tag[T](x: Wrap[T = T]) :- holder(h: x)` loads and `tag[T = Int64]` answers `wrap(1)` alone; `rule tagV(?x: Wrap[T = ?t]) :- holder(h: ?x)` cited with nothing fixing `?t` is refused at load; `noDict[X]() = Wrap[T = X].el.takeN(9).length()` (no `requires SortDomain[T = X]`) is refused at load where it now loads and raises `relation_floundered`.

RELATED: WI-20261116-HBMRB (its decision taken in §9: a sort's `T` in its rule is the citation's, read through what the citation hands in); proposal 077 §5.2 (open conditions — superseded if §9 is approved); WI-20261124-YFD7F (a value the typer has at a rigid is trusted — its slot extended to an operation body's citation, 077 §9 / §9 item 5). Open questions of §9 decided before building: data at several types in one citation (2), a query's spelling (4).

ACCEPTANCE: S1 (measure, nothing built) reported first — every citation that leaves a rule's type variable to a value refused at load, every run-time read of a type off a value in a rule, the rows each moves counted — and the plan revised with the user on it; kernel-language text agreed with the user before S5 lands; every stage's rows DRIVE the capability, with back-outs measured at their site; full workspace via rustland/scripts/test.sh, families, scaland.

