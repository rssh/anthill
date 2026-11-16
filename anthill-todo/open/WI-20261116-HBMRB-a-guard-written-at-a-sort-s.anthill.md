## Attributes

- id: WI-20261116-HBMRB-a-guard-written-at-a-sort-s
- created: 2026-11-16T10:12:58Z

- status: Open
- status_agent: claude
- status_at: 2026-11-16T10:12:58Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A GUARD WRITTEN AT A SORT'S OWN PARAMETER IN A SORT'S RULE IS NEVER READ: it is kept as the goal `Marker(T: T)`, and the rule answers no solutions. PROGRAM: sort Marker { sort T = ?  operation tag(x: T) -> Int64 } with IntMarker providing Marker[T = Int64]; sort Holder { sort T = ?  requires Marker[T = T]  rule g1(?x: T) :- Marker[T] }, rule t1() :- Holder[T = Int64].g1(1); sort Free { sort T = ?  rule f1(?x: T) :- Marker[T] }, rule tf() :- Free[T = Int64].f1(1). MEASURED on 7c63d768: both load clean, and t1() and tf() answer no solutions. `anthill query --mode functor` shows g1's body as `__domain_guard(?#1, ?#0), Marker(T: T), ...`: the sort application stays a goal over the relation Marker, its T the sort parameter's name rather than the clause's variable for it (?#0). A guard at a rule's own type parameter (rule keep[A](?x: A, ?t) :- Marker[A], ...) becomes a read, find_dictionary(Marker[T = ?#1], Marker, ?#1, out: ?#0, carrier_type: true). WANTED, to decide with the user: the guard is read as one at a declared type parameter is (a requirement the citation passes, so Free[T = Int64].f1(1) holds, and in Holder it is the sort's own requirement), or it is refused at load naming the sort's parameter; never a goal that fails in silence. ACCEPTANCE: rows driving t1 and tf to the decided verdict; full workspace green via rustland/scripts/test.sh.

