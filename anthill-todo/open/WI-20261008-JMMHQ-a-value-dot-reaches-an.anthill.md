## Attributes

- id: WI-20261008-JMMHQ-a-value-dot-reaches-an
- created: 2026-10-08T09:06:39Z

- status: Open
- status_agent: claude
- status_at: 2026-10-08T09:06:39Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A VALUE DOT REACHES AN `internal` OPERATION FROM OUTSIDE ITS SORT — with `internal operation peek(b: Box[V]) -> V` in `lib.Box`, another namespace's `Box.peek(b)` is refused ("'Box.peek' is internal to 'lib.Box' and cannot be referenced from scope …") and `let b = Box.mk(4); b.peek()` answers 4. Measured 2026-10-08 on fd1cf282; it predates that commit.

WHERE. The typer's dot frame (`TypeBuildFrame::DotApply`, kb/typing/build.rs) resolves the receiver's own member with `find_operation_in_scope` and asks nothing about visibility; the parent-sort rung below it does the same. `denoted_sort_dot` beside them asks (`internal_visible_from`, `TypeError::ForbiddenInternalMember`).

WHAT. Ask the same question at those rungs. About ten lines; filed and not done inline because it tightens every value dot and wants its own gate run.

CONTROL. Refused from another namespace; reached from inside the declaring sort. The first row fails with the check backed out.

