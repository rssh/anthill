## Attributes

- id: WI-20261008-HZVQA-the-parameters-an-alias-fixes
- created: 2026-10-08T09:06:40Z

- status: Open
- status_agent: claude
- status_at: 2026-10-08T09:06:40Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE PARAMETERS AN ALIAS FIXES DO NOT RIDE A COMPANION CALL THROUGH IT — over `sort Box[V]` with `operation wrap(x: V) -> V` and `sort CA = Box[V = Int64]`, `CA.wrap("s")` passes the argument check with `V` free and is refused only where its String result meets an Int64, while `Box[V = Int64].wrap("s")` is refused at `wrap.x: expected Int64, got String`. The let-bound `let t = CA; t.wrap("s")` does as the written `CA.wrap("s")` does. Measured 2026-10-08 on fd1cf282.

WHY. A member path is read through an alias to the sort it stands for (`read_path_through_aliases`, kb/load.rs: `CA.wrap` is `Box.wrap`), and the alias's bindings are not carried to the call. WI-20260824-PAPX0 made the let-bound spelling mirror that, so the two agree.

WHAT. Decide with the user whether a call through an alias is at the alias's bindings. My reading is yes: a type position reads `CA` as `Box[V = Int64]`. If so, carry them on the written route and in `denoted_sort_dot` (kb/typing/type_receiver.rs) in one change. The row `an_alias_denotes_what_it_stands_for` (wi_papx0_dot_receiver_split_test) compares the two spellings and fails if one moves alone.

CONTROL. `CA.wrap(5)` answers; `CA.wrap("s")` is refused at the argument, written and let-bound; an alias that owns members is still read as written. Say which rows fail with the change backed out.

DONE WHEN: both spellings refuse `CA.wrap("s")` at `wrap.x`; the gate is green.

