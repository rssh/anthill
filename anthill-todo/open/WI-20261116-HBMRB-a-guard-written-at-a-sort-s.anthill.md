## Attributes

- id: WI-20261116-HBMRB-a-guard-written-at-a-sort-s
- created: 2026-11-16T10:12:58Z

- status: Open
- status_agent: claude
- status_at: 2026-11-16T10:12:58Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261127-DAPCN-proposal-060-1-9-a-rule-s

## Description

A GUARD WRITTEN AT A SORT'S OWN PARAMETER IN A SORT'S RULE IS NEVER READ: it is kept as the goal `Marker(T: T)`, and the rule answers no solutions. PROGRAM: sort Marker { sort T = ?  operation tag(x: T) -> Int64 } with IntMarker providing Marker[T = Int64]; sort Holder { sort T = ?  requires Marker[T = T]  rule g1(?x: T) :- Marker[T] }, rule t1() :- Holder[T = Int64].g1(1); sort Free { sort T = ?  rule f1(?x: T) :- Marker[T] }, rule tf() :- Free[T = Int64].f1(1). MEASURED on 7c63d768: both load clean, and t1() and tf() answer no solutions. `anthill query --mode functor` shows g1's body as `__domain_guard(?#1, ?#0), Marker(T: T), ...`: the sort application stays a goal over the relation Marker, its T the sort parameter's name rather than the clause's variable for it (?#0). A guard at a rule's own type parameter (rule keep[A](?x: A, ?t) :- Marker[A], ...) becomes a read, find_dictionary(Marker[T = ?#1], Marker, ?#1, out: ?#0, carrier_type: true). WANTED, to decide with the user: the guard is read as one at a declared type parameter is (a requirement the citation passes, so Free[T = Int64].f1(1) holds, and in Holder it is the sort's own requirement), or it is refused at load naming the sort's parameter; never a goal that fails in silence. ACCEPTANCE: rows driving t1 and tf to the decided verdict; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-27T18:27:20Z — feedback — user

DECISION TAKEN IN PROPOSAL 060.1 §9 (draft, user, 2026-11-27; WI-20261127-DAPCN): a sort's parameter in its rule is the citation's, as any type parameter is, read through what the citation hands in — this ticket's first alternative (the guard read as one at a declared type parameter, a requirement the citation passes), not a refusal. Buildable now under either design. A SECOND INSTANCE, measured 2026-11-27 (release CLI on c9d251abc): in sort Wrap[T] { entity wrap(v: T)  rule isT(?x) :- anthill.kernel.domain(?x, T) }, Wrap[T = Bool].isT(true) cited from an operation body answers NOTHING — at a concrete instance, no rigid involved — where the typed rule el(?x: T) :- true cited the same way answers 1; through op[X](v: X) at X = Bool, v = true, 0; open (Wrap[T = X].isT.takeN(9)) it raises relation_floundered(domain(Var, T)): the written goal's T is the parameter's NAME, as Marker(T: T) is here. Add it to the rows: isT(true) answers 1 at Wrap[T = Bool], 0 for a non-Bool.

