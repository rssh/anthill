## Attributes

- id: WI-20261011-DAW83-an-error-inside-a-rewrite-s
- created: 2026-10-11T05:28:00Z

- status: Open
- status_agent: claude
- status_at: 2026-10-11T05:28:00Z

- acceptance: cargo-test

- tags: typing

## Description

AN ERROR INSIDE A REWRITE'S TEXT IS REPORTED IN THE FILE OF THE BODY THAT FIRED IT — the rule's byte offset, rendered against another file. Measured 2026-10-10 on 5273d5a2 and on 5ba58df5; found while delivering WI-20261008-JMMHQ.

THE PROGRAM. `a_lib.anthill` holds `namespace rules` with `operation same(n: Int64) -> Int64`, `rule same(?n) <=> plus(?n, "x") @[simp]` on line 12 and `operation plus(a: Int64, b: Int64) -> Int64 = a + b`. `c_use.anthill` is four lines: `namespace test2`, `import rules.{same}`, `operation go() -> Int64 = same(1)`, `end`. `anthill load a_lib.anthill c_use.anthill` reports `c_use.anthill:5:1: type mismatch in plus.b (op-arg): expected Int64, got String` — a line past the end of a file that holds no `plus`. With rule and call in one file the location is the rule's. The refusal of an `internal` member reached from a rule's text (kernel-language.md §8.6; for a rule written outside the sort it is the designed outcome since JMMHQ) renders the same way: `b_use.anthill:9:1: 'peek' is internal to 'lib.Box' and cannot be referenced from scope 'rules'`, for a rule on line 11 of `a_lib.anthill`.

MECHANISM. A spliced right-hand side keeps each node's own span (`reparent_spliced`, WI-20260903-FCZ3N), so a `TypeError` raised under it carries the rule's byte range, and a `TypeError`'s span is a bare range. The file is stamped per body: every error of an operation body is tagged with `op.body_node.span.source` (`type_check_sorts_collect`'s parallel `sources`, WI-745), a rule body's with its atom's. `macro_rejection_error` states this hazard for its own channel and asserts it away (`rejection.span.source == redex.span.source`); nothing does for an ordinary error under spliced text.

WHAT. An error is rendered in the file its span indexes into. Either a `TypeError`'s span becomes a `SourceSpan`, or the frame that types a spliced subtree retags what comes back from it with the template's source — the occurrence holds it (`occ.span.source`). Decide with it whether the report also names the call that fired the rewrite: the author of `c_use.anthill` is shown a line of another file and none of their own.

RELATED. WI-1041 holds the LATENT mislocations of the same pairing (the empty-span sentinel, the truncating `sources.resize`). This one is driven by the two-file program above.

CONTROL. The two-file program as a row asserting file and line: fails on the tree before. Its one-file twin passes either way.

