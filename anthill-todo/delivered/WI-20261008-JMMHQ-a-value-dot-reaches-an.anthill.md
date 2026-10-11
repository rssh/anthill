## Attributes

- id: WI-20261008-JMMHQ-a-value-dot-reaches-an
- created: 2026-10-08T09:06:39Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-11T05:24:07Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A VALUE DOT REACHES AN `internal` OPERATION FROM OUTSIDE ITS SORT — with `internal operation peek(b: Box[V]) -> V` in `lib.Box`, another namespace's `Box.peek(b)` is refused ("'Box.peek' is internal to 'lib.Box' and cannot be referenced from scope …") and `let b = Box.mk(4); b.peek()` answers 4. Measured 2026-10-08 on fd1cf282; it predates that commit.

WHERE. The typer's dot frame (`TypeBuildFrame::DotApply`, kb/typing/build.rs) resolves the receiver's own member with `find_operation_in_scope` and asks nothing about visibility; the parent-sort rung below it does the same. `denoted_sort_dot` beside them asks (`internal_visible_from`, `TypeError::ForbiddenInternalMember`).

WHAT. Ask the same question at those rungs. About ten lines; filed and not done inline because it tightens every value dot and wants its own gate run.

CONTROL. Refused from another namespace; reached from inside the declaring sort. The first row fails with the check backed out.

## Changes

### 2026-10-11T05:24:06Z — feedback — claude

DELIVERED 2026-10-11. THE RULE AS BUILT. A member reached by a dot on a value is hidden as its written name is: `b.peek()` written outside `Box` is refused ("'peek' is internal to 'lib.Box' and cannot be referenced from scope 'test.go'") where `Box.peek(b)` is, and reached inside `Box` — in a nested sort, a second entry of the sort, a rule body. The leak was on every rung of the dot that finds an operation, not on the two this ticket names: the receiver's own member, the parent sort's (`r.shout()` on `r: Colour.red`), a provided spec's operation, a required spec's, and the spec of a `requires` clause on a type parameter all loaded from outside.

DECIDED WITH THE USER 2026-10-10, two questions put with their programs. (1) One name, two members: REFUSED, not passed over. With an `internal operation v` beside a public field `v`, `b.v` outside the sort is refused naming the operation; with `Leaf`'s own `label` `internal` and backing the public `Desc.label`, `l.label()` is refused and `Desc.label(l)` answers 7. The same on a receiver typed at a spec that carries the member. (2) The text of a rewrite is asked from the scope its RULE is written in: `rule open(?b) <=> ?b.peek() @[simp]` written in `Box` answers from every call it rewrites, as `peek(?b)` in the same rule does, and the same rule written in another namespace is refused at a call it rewrites, naming the rule's scope. The field twin `?b.v` over an `internal` constructor was refused on HEAD from every outside caller and now answers. The arguments of the rewritten call stay the caller's text.

WHERE. `hidden_dot_member` (typing/type_ctor.rs) is the one question; the dot frame (typing/build.rs) asks it of the operation the ladder settled on, and of the receiver's own member before the dispatch decision — on a spec-typed receiver that decision hands the call to the public spec operation the member backs, which would have passed a hidden member over. The denoted-sort dot asks through it too. The rule's scope rides the spliced node: `OccurrenceOrigin::Synthesized.written_in`, stamped by `reparent_spliced`, carried by `rebuilt_expr` and by `deep_clone`, read by `NodeOccurrence::text_scope` (which walks from a node a pass built to the text it was built from) and by `typing::written_scope` — the reader of every visibility question in the typer: the member check, the field check, the `FieldOf` reduction's site. `visibility_scope` is gone; `hidden_field_owner` takes the scope resolved.

A WRONG TURN. The first cut asked from `env.referencing_scope()`. A fence row found it refused the rule written inside the sort; the full workspace was green through it (9080 passed, the one failure that row).

CONTROLS. `wi_jmmhq_value_dot_internal_test`, 26 rows, one source per row; its header lists, per piece backed out, the rows that fail and the six that pass under every back-out. NOT DRIVEN and said there: the denoted-sort dot's read of the rule's scope — a rule's text cannot write a type as a receiver (`(Box).m()` names nothing in it).

REVIEW. `/code-review` at xhigh, 13 findings. Fixed: the hidden member passed over on a spec-typed receiver (the second check, with its row); a spec sentence that claimed a refusal at the rule's declaration; the duplicated refusal in the denoted-sort dot; a return value and a doc comment left stale in `hidden_field_owner`; the header's table. Left, each stated: a refusal inside a rewrite's text is rendered in the CALLER's file (below); at the parent-sort rung a supplier tie on a hidden member is reported before the hidden member; a node minted at a redex that is another rule's text takes that rule's scope (no reaching program).

FOUND ON THE WAY, on HEAD, NOT FIXED, no ticket filed (put to the user 2026-10-10). (a) The loader's assertion on parameter places fires where a refusal is due: two bodied `operation label` in one sort with different parameter names; `operation Desc.label` beside a sort whose `label` is `internal`; and `entity Desc.mk`, `sort Desc.Inner` over `internal` members fail other assertions. An early return in `load_operation` was written and backed out — it covered one spelling and its sibling still panicked. (b) An error inside a rewrite's text carries the rule's byte offset and is rendered against the file of the body that fired it: a rule on line 11 of `a_lib.anthill` fired from `b_use.anthill` reports `b_use.anthill:9:1`, for an ordinary type mismatch as for this refusal. (c) `rule open(?b) <=> peek(?b) @[simp]` on a body-less operation of a parametric sort does not fire: the program loads and the call fails `OperationBodyMissing`, where the non-parametric twin runs.

GATE, on 5273d5a2 with this change. `rustland/scripts/test.sh`, full: 36 binaries, 9088 passed, 0 failed, 14 ignored. `sbt -batch testFull`: 634 passed. scaland has no typer and nothing mirrors this; no scaland file changed. Spec: §8.6, two paragraphs.

