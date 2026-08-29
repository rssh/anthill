## Attributes

- id: WI-20260829-WBXGX-a-collection-literal-s-element
- created: 2026-08-29T13:41:36Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T13:41:36Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A COLLECTION LITERAL'S ELEMENT TYPE IS ITS FIRST ELEMENT'S, AND EVERY LATER ELEMENT IS UNCHECKED. `[1, "a"]` types as `List[T = Int64]` and loads wherever a `List[T = Int64]` is expected. No diagnostic, on any route.

MEASURED, in an ARGUMENT position (the route WI-20260826-7JDWY does NOT cover — there the literal IS checked, which is what makes this a second, separate hole):

  takes_list([1, "a"])          LOADS
  takes_list([1, "a", true])    LOADS
  takes_list(["a", 1])          REFUSES  expected List[T = Int64], got List[T = String]
  takes_list(["a"])             REFUSES  expected List[T = Int64], got List[T = String]
  takes_set({1, "a"})           LOADS
  takes_set([1, "a"])           REFUSES  expected Set[T = Int64], got List[T = Int64]

Read the first two against the third: the SAME two elements in the other order refuse. So the element type is not being JOINED or unified across the elements — it is taken from element ONE and the rest ride free. The `Set` rows show the same, so it is the literal's typing and not a `List` fact. The last row shows the literal's own SHAPE is still checked, which is why this reads as "loads clean" rather than "nothing is checked".

WHY IT IS NOT WI-20260826-7JDWY. That one is about the RETURN-HINT route: `operation c() -> List[T = Int64] = ["x"]` loads because `TypeBuildFrame::ListLit` takes `element_hint` as the element type UNCONDITIONALLY, overwriting instead of checking. This one is on the route that ticket's own table uses as the CONTROL — the argument route, where a hint is not pushed and elements are supposed to be inferred bottom-up. `takes_list(["x"])` refusing is that control working; `takes_list([1, "x"])` loading is this defect. Fixing 7JDWY by not overwriting the hint would not touch it.

WHERE TO LOOK. Whatever builds a `ListLiteral` / `SetLiteral`'s type from its elements in the bottom-up (no-hint) direction: it appears to take element 0's type as `T` and stop, rather than unifying element `i`'s against the accumulated `T` and refusing at the first that does not. The refusal wanted is per ELEMENT and located at that element's span, naming the accumulated type and the element's own — `[1, "a"]`: "list element 2 has type String; the literal's elements are Int64".

THE DECISION THAT COMES WITH IT: whether a mixed literal should unify to a common SUPERTYPE where one exists rather than refuse. Anthill has no join today, so refusing at the first mismatch is the answer unless one is added; say so wherever the fix lands.

PINNED: `typer_capability_matrix_test`'s literal rows record this as `SilentlyAccepted` naming this WI, so the cells fail the day it is refused. That is the signal to flip them to `RefusesLocated` and close this.

