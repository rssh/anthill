## Attributes

- id: WI-20260829-WBXGX-a-collection-literal-s-element
- created: 2026-08-29T13:41:36Z

- status: Delivered
- status_agent: user
- status_at: 2026-09-07T14:22:47Z

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

## Changes

### 2026-09-07T14:22:41Z — feedback — claude

DELIVERED. A collection literal whose position declares NO element type now takes the JOIN of its elements' types, and the first element with no join is refused at its own span: `4:43: type mismatch in list.element 2 (collection-element-join): expected Int64, got String`. Every row the ticket measured is closed, including the `Set` twin, and the two orders have stopped disagreeing.

THE PRESCRIBED REPAIR IS NOT THE ONE THAT LANDED, AND ITS REASON WAS FALSE. The ticket asked for "unifying element i's against the accumulated T and refusing at the first that does not", justified by "Anthill has no join today, so refusing at the first mismatch is the answer unless one is added". It has one: `join_types`, which `compute_branch_join_type` already gives `if` and `match` arms — the neighbouring construct that asks this exact question of several expressions at once. Borrowing it means the literal did not acquire a second opinion about when two types have no common supertype, and `control_the_branch_join_answers_the_same_clash_the_same_way` is the row that pins the two together.

AND THE PRESCRIBED REPAIR KEEPS AN ORDER-DEPENDENCE — the very tell the ticket used to IDENTIFY the defect. BUILT AND RUN, not predicted: with a subtype test against element one in place, `takeColours([r, c])` with `r: Colour.red, c: Colour` is refused `expected red, got Colour` while `takeColours([c, r])` loads. Same two values, two verdicts by order. Under the join both load and drive.

THE WIDENING DIRECTION IS INERT ON THIS CORPUS, and that is stated rather than claimed. Instrumented over the whole workspace suite BEFORE the change: exactly 4 literals reach the element-vs-element comparison at all, and every one of them CLASHES — none widens. So the join's ability to return a common supertype is exercised only by this ticket's own rows, and there is no corpus program whose TYPE this widens. What the order-independence row witnesses is order-independence, not a widened type reaching a consumer; it says so at its site.

THE DIAGNOSTIC KEEPS THE TWO SOURCES APART. `expected Int64, got String` means something different depending on where the `Int64` came from — a DECLARATION (the author writes the fix at the element) or a JOIN of siblings (the fix may equally be an earlier element, or the declaration that is missing). `TypeErrorContext::CollectionElement` gained an `ElementTypeSource`, and `kind_tag` renders `collection-element` against `collection-element-join`. `control_a_declared_element_type_still_takes_the_other_route` is the row that stops the two collapsing.

THREE BACK-OUTS, because there are three claims — each a run of the whole `wi_tests` binary, all re-run on the post-review tree.
 A. IS ANYTHING COMBINED AT ALL? Join -> `Some(acc)` (element one's type, nothing checked): 7 fail / 4242 pass — the four arms here, `typer_capability_matrix_test::the_row_remainders` (whose two cells recorded this hole as `SilentlyAccepted`), `wi_7jdwy_…::control_an_unhinted_literal_still_types_from_its_elements` (whose residual `load_clean` was PINNING this item and is the assertion that failed the day it closed), and `wi_7jdwy_…::a_rival_collection_declares_no_element_type`.
 B. IS IT A JOIN, OR A SUBTYPE TEST AGAINST ELEMENT ONE? Join -> the ticket's own prescription: 1 fails / 4248 pass, exactly `the_element_type_is_a_join_so_it_does_not_depend_on_order` and nothing else in the binary. That single row IS the difference between the two designs.
 C. DOES THE VALUE CARRIER JOIN TOO? `seq_literal_value_type` -> `first()`: 1 fails / 4248 pass. Its own axis because it is its own function, and a back-out of A leaves it untouched.
 The order-independence row PASSES under back-out A, which is stated rather than hidden: element one's type is a subtype of the declared `Colour`, so both orders loaded before this ticket too. A row that separates B cannot also separate A.

WHAT `/code-review` (high) FOUND — six, all acted on, and three were corrections to claims I had written.
 (1) `ElementTypeSource` had been inserted BETWEEN WI-RKMD4's forty-line doc and the `HeadPosition` it documented, so that whole argument was rendering as rustdoc for a two-variant enum about literal provenance, and `HeadPosition` had none. Moved beside the context variant that reads it.
 (2) The retired containment claim ("can only turn a refusal into an acceptance, never the reverse") survived VERBATIM in `variant_slot_arg_hint`'s header, sixty lines above the body comment retiring it — which defeats the point of retiring it, since the header is where a reader looks for the gate's soundness argument. The retirement is now where the claim stood.
 (3) THE VALUE CARRIER WAS STILL READING ELEMENT ONE. `value_type_term` answered `List[T = Int64]` for a runtime `ListLiteral(1, "a")` — this ticket's defect in the one place a value can be inspected at runtime, and my "one owner" note beside it read as more than had been delivered. It joins now, and FLOUNDERS to `?_` on a clash rather than erroring: a runtime value exists, so there is no program to refuse, and under-determined is the honest answer (the M6 / WI-067 convention this file already follows for a cyclic or over-deep value). Driven by `the_value_carrier_joins_its_elements_too`, and measured failing on its back-out.
 (4) `TypeBuildFrame::ListLit`'s doc still described BOTH retired rules ("`element_hint` … else the first element's type"). Rewritten; `SetLit` defers to it.
 (5) The new test file was untracked while its `#[path]` registration sat in a modified file — a `git add -u` would have committed the registration without the file and broken the build. Staged with `git add -A`.
 (6) A RIVAL COLLECTION'S `T` IS NOT THIS LITERAL'S ELEMENT TYPE — the same class as WI-20260826-7JDWY's head test, which I had deliberately written as "both collections for both surfaces". At the typer a `[…]` is always `List`-typed, so a `Set[T = X]` position declares nothing about its elements; reading it as one tagged `-> Set[T = Int64] = [1, "x"]` as `(collection-element)`, claiming a declaration that does not exist. Narrowed to the literal's OWN sort, with a row, and 7JDWY's axis 4 split into the two nested claims it always was (2 fail / 4247 for no head test at all; 1 fail / 4248 for accepting either collection).

WI-20260826-7JDWY's AXES WERE RE-MEASURED ON THE FINAL TREE, because this ticket added rows to the binary and the review narrowed one of them: 12/4237, 4/4245, 3/4246, and axis 4 as 2/4247 (no head test) and 1/4248 (either collection). Axis 1 now also fails this ticket's `control_a_declared_element_type_still_takes_the_other_route` — correctly, since that control asserts the DECLARED tag.

WHAT ELSE MOVED. `kernel-language.md` §4.6's "a position declaring nothing … types from its FIRST element, later elements are not compared against it" is now the join rule. `typer_capability_matrix_test`'s two `SilentlyAccepted` cells naming this WI are positives, and so is the reversed-order CONTROL beside them — its job was to show the asymmetry, and what it pins now is that the asymmetry is gone. The residual assertion WI-20260826-7JDWY left in its own control row is the positive it became.

VERIFICATION. Full workspace 6585 passed / 0 failed. scaland untouched (no scaland or stdlib input changed; its 2 pre-existing `BootstrapTest` failures were verified on a clean HEAD worktree during 7JDWY).

