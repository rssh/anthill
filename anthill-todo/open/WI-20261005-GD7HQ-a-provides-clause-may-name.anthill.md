## Attributes

- id: WI-20261005-GD7HQ-a-provides-clause-may-name
- created: 2026-10-05T06:41:15Z

- status: Open
- status_agent: user
- status_at: 2026-10-05T06:41:15Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A `provides` CLAUSE MAY NAME SOMETHING THAT IS NOT A SORT, AND THE PROVISION IS FILED: `operation g(x: Int64) -> Int64 = x` + `sort Carrier { provides g }` loads clean, and so do `provides g[3]`, `provides K` (`const K: Int64 = 3`), `provides helper` (the carrier's own operation) and `provides pr` (`rule pr(?x) :- true`, a rule-introduced predicate). Each files a `SortProvidesInfo` row whose `spec` is that name — MEASURED: 410 rows against 409 for the same carrier with no clause, the new row's spec rendering `g` / `K`, exactly as the control `provides Spec0` adds `Spec0`. The same name in a `requires` clause is refused where it is written: "`requires g`: 'g' is a declaration of kind Operation, and a `requires` names a SPEC" (`LoadError::RequiresNamesNonSort`, WI-993, raised in `scan_definitions` pass 2). The `provides` side asks ONE thing of the name it resolved (`load_provides_clause`, kb/load.rs: `provided_spec_symbol`, then `sort_has_constructors`), and asks it without having established that the name is a sort: an operation, a const and a predicate have no constructors and pass. For two other kinds the same test refuses, with a reason that is false of them: `provides anthill.prelude` (a namespace) is told the namespace "declares constructors, which makes it a DATA sort" (`sort_has_constructors` scans direct children by qualified-name prefix, and a namespace's free-standing entities match), and `provides foo` (`foo` a constructor of `sort Foo`) is told that `Foo.foo` "declares constructors". FOUND while delivering WI-20260929-AAQT5 (its spec-head probes), PRE-EXISTING, not caused by it. FIX: refuse a `provides` clause whose spec — read through a type alias as the clause reads it — does not play `Sort`, where it is written and naming its kind, as `requires` does, BEFORE the data-sort test, so that test is asked of sorts only; file no provision for it; `provides foo` and `provides anthill.prelude` stay refused, in words that are true of a constructor and of a namespace. Measure the corpus first, as WI-1106 did for the data-sort refusal beside it: instrument the clause over every test binary and see what is written today. NOT in scope: `Item::ProvidesBlock` (`provides Int64 language rust`), whose `spec` field names the CARRIER (the WI-1110 note in `scan_definitions`). ACCEPTANCE: each of the five spellings above is refused where it is written and files no `SortProvidesInfo` row (driven — a row count or a rule over the relation, not "it is refused" alone); `provides anthill.prelude` and `provides foo` are refused for what they are; the control `provides Spec0` still files and its spec operation still dispatches through it; full workspace green via rustland/scripts/test.sh; scaland — run the same clauses through its loader (its `requires` rule is `parentScopeOf`, WI-988) and bring it in line if it differs.

