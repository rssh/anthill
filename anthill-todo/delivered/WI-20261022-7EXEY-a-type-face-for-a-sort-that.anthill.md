## Attributes

- id: WI-20261022-7EXEY-a-type-face-for-a-sort-that
- created: 2026-10-22T05:09:48Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-22T17:02:22Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A TYPE FACE FOR A SORT THAT SHARES ITS NAME WITH AN OPERATION — `requires Positive[T = A]` beside `operation Positive(x)` is the requirement written and `requires Positive(x)` the operation's call, in either declaration order. Filed with the user 2026-10-22 from WI-974 (19f8fe7c), which made the bracketed spelling a load error (`LoadError::BracketRequirementOnAnOperationName`) because nothing downstream can read it: a sort with no constructor has one identity (§4.4; the `Symbol` doc in intern.rs: 'A sort with no constructor of its name (`Int64`, `Cell`) has one face'), so `Positive[T = A]` is stored as `Positive(T: A)` — the same term, headed by the same symbol, as a call — and every reader of a stored clause takes it as the call (the applied reading, `KnowledgeBase::names_only_a_type`). MEASURED 2026-10-22 on 50b9ce5c and on 2827691a (WI-974's parent), over: a spec `sort Positive { sort T = ?; operation sign(x: T) -> Int64 }`, a predicate `operation Positive(x: Int64) -> Bool = x > 0`, `namespace Amount { provides Positive[T = Amount, sign = amountSign] }`, `operation f[A](a: A) -> Int64 requires Positive[T = A] = Positive.sign(a)` and `operation g(x: Int64) -> Int64 requires Positive(x) = x`. BEFORE WI-974: spec first, `f(amount(v: 5))` answered 5 and `g` was refused as the spec `Positive[T = x]` ('no impl provides demo.Positive'); predicate first, `f` was refused as the precondition `Positive(T: A)` and `g` was checked. NOW: `g` is checked in both orders (`g(3)` = 3, `g(-1)` refused); `f` is refused in both, with WI-974's message and the follow-on 'expected precondition `Positive(T: A)`'. CONTROLS: the spec alone answers 5; the predicate alone refuses `g(-1)`. The same lost bracket reaches eval's applied arm (eval.rs, `names_only_a_type`): an unmarked `Both[X = Int64]` — a KB loaded without the typer, or a term-made occurrence — is dispatched as the operation's call. TO BUILD: `KnowledgeBase::type_context_face`, the one place that decides which declarations mint a face (WI-20260902-JB6RS), mints the face for a sort that also plays `Operation`, as it does for every constructor, so `Positive[T = A]` is stored as `Positive†(T: A)` and the call keeps the plain symbol; then delete `BracketRequirementOnAnOperationName` with its check (`Loader::refuse_bracket_requirement_on_an_operation_name`) and the comment at eval's applied arm. DECIDE WITH THE USER — §4.4 changes ('a sort has one identity' gains this exception): how such a type is printed (`Positive[]`, as a constructor's type is); what a BARE `Positive` denotes in a data context (the operation, with its type written `Positive[]` — the constructor's rule mirrored) and in a type context (the face); reflect's `kind` (`Sort` for the face, `Operation` for the plain symbol). REJECTED ALTERNATIVE (user, 2026-10-22): refusing a sort and a same-named operation in one scope — it reverts WI-751, which admits the pair (`wi_xftc7_provided_child_in_type_position_test`, `wi_jb6rs_type_face_test`'s sortop row). ACCEPTANCE (cargo-test, driven): the example's `f` and `g` both work in both orders, each against its control; `wi974_kind_set_order_twin_test::a_bracket_requirement_on_a_sort_named_operation_is_refused_in_both_orders` turned into the positive row; an unmarked bracket application of the pair builds the type in eval; each back-out named at its row.

## Changes

### 2026-10-22T13:00:06Z — feedback — user

Decided with the user 2026-10-22: (1) a BARE sort-and-operation name in a DATA context is the OPERATION (§4.4's 'the context's own reading first', as for a constructor); its type written as data is `Positive[]`, and the printer emits that. This replaces WI-974's 'bare, a sort that is no constructor is the type' for such a name. In a TYPE context the name is the face. (2) reflect's `kind`: the face reports `Sort` (as every face does), the plain symbol `Operation`, whatever the declaration order.

### 2026-10-22T15:11:58Z — feedback — user

Decided with the user 2026-10-22, from /code-review: (3) a later load may not give a SEALED sort with no constructor of its name an operation of that name (LoadError::OperationBesideASealedType, kernel-language §8.3) — the pair's face is a term the sealed load's types do not carry (measured: `operation Cell(…)` in anthill.prelude made `Cell[V = Int64]` not Modifiable). The reverse order (a later sort beside a sealed operation, or an operation beside a sealed constructor) is accepted: every sealed term reads as before. Approved for both directions, narrowed to the harmful one with the user's agreement. (4) Seal only: across an UNSEALED earlier load the pair is not refused, and §8.3 says the earlier load's stored terms are not protected, as for its other later-load rules. (5) reflect facts naming the pair's sort by its face: follow-up WI-20261022-2PZB7.

### 2026-10-22T17:02:20Z — feedback — user

Delivered in 2b9afa9a. Every acceptance row driven: the example's `f` and `g` work in both orders, each against its control (`the_requirement_and_the_call_both_work_in_both_orders`); wi974's refusal row is the positive `a_bracket_requirement_on_a_sort_named_operation_is_the_requirement_in_both_orders`; an unmarked bracket of the pair builds the type in eval (`an_unmarked_bracket_builds_the_type_in_eval`); each back-out named at its row (14 parts, every one failing a row). Beyond the description, from two /code-review rounds: one binding rule for the four producers (`KnowledgeBase::binding_type_face`), a bracket goal headed by the face (also an eponymous entity's, a JB6RS gap), a face never playing `Operation`, alias readers by declaration, and the sealed-sort refusal (§8.3). Gate green on the tree merged with origin/main 14860891 (10384 passed); two-step recipe, families, scaland (710) green. Not this change's: wi_6wvjb's fresh-recipe row and six node-carrier rows (wi4gbqv, wi9pgcm) fail identically on origin/main without it — the first is WI-20261022-JBHQC.

