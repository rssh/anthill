```anthill
fact WorkItem(id: "WI-20260818-YQB1Y-proposal-052-oq5-revision", created: "2026-08-18T19:14:50Z", acceptance: [ToolPasses(tool: "cargo-test"), ToolPasses(tool: "scaland-sbt-test")], depends_on: some(value: ["WI-714"]), status: Open)

fact Feedback(workitem: "WI-20260818-YQB1Y-proposal-052-oq5-revision", author: "claude", at: "2026-08-18T19:29:55Z")
```

## description

Proposal 052 OQ5 REVISION: split the relation SCHEMA from the ROW TYPE, so a one-column relation stops being ambiguous. Filed out of WI-1128 (delivered 2026-08-18), whose delivery left this open with a reason and no owner.

THE DEFECT THAT MAKES THIS URGENT, and it is a SILENT WRONG ANSWER rather than a refusal. `collapse_schema` (rustland/anthill-core/src/kb/typing.rs) erases the relation's ARITY: the 1-arm returns the sole column's TYPE, the 0-arm returns `Unit`. So a schema type that IS a named tuple reads equally as "n columns" and as "ONE column whose type is that n-field tuple". MEASURED on the current tree: over `entity pair_holder(p: (a: Int64, b: String))`, `rule pairs(?p)` has ONE column, and `person_row.join(pairs, ...)` TYPE-CHECKS against a declared four-column `(name, age, a, b)` while the row `join_run` materializes is `(name, age, p)` — three columns, `a`/`b` promised and never delivered, `p` delivered and never promised. Pinned as a recorded limit by `wi1128_a_tuple_typed_column_is_indistinguishable_from_two_columns`.

`Concat` IS THE ONLY MEMBER OF THE FAMILY WITH NO BACKSTOP, structurally rather than by omission. `fix`, `project` and `negate` each ask the VALUE a question it can answer — "is there a column of this name?" — and refuse loudly at runtime (measured: "fix: restricts column `a`, which is not in the relation's schema"; "project_run: the projection selects column `a`, which is not in the relation's schema"). MERGING IS NAME-FREE, so `join` has no such question and nothing to detect: `join_run` merging a 2-column relation with a 1-column one is CORRECT, and only the type is not. No type check can exist either — the two schemas are the SAME TYPE. So this cannot be fixed anywhere except in the representation.

THE DESIGN: `T` currently answers TWO questions — "what is a row's type" (where the collapse is the ergonomic win: `colouring.takeN(20) : List[Board]`) and "what are the columns" (where it is a loss). Split them: the SCHEMA stays the full named tuple, and the ROW type becomes a `Collapse[T]` type constructor in the same family (`Concat` / `Without` / `Project` / `Membership`), reduced at the SAME return-type normalization boundary. Then `join` / `fix` / `project` accept a one-column operand with its real name, `Membership` becomes arity-exact, and the tuple-typed-column case above disappears.

WHAT IT COSTS, so it is costed before it is started rather than discovered:
 * It is a BREAKING CHANGE to a SPECIFIED rule — kernel-language.md 6.8's paired type-and-value convention, which records "revisiting it means moving both halves together". The value half is fixed at the term level (`x.(f)` yields the scalar `x.f`; a single rename collapses too), so the schema half cannot move alone.
 * It moves `where`'s bare-binder spelling. Today a 1-collapsed row is read as `eq(c, 30)` via the `WHOLE_ROW_HOLE` sentinel; with an uncollapsed schema `c` is a 1-field tuple and the spelling becomes `c.age`. Existing tests drive `eq(c, 30)`.
 * It must thread through the `provides LogicalStream[T = T, E = E]` edge in relation.anthill, or every inherited Stream consumer starts seeing the uncollapsed tuple. Whether a ctor reduces across a provides binding (with the sort's own abstract `T` as operand, which WI-734 says leaves it symbolic) is the FIRST thing to measure — it decides whether the design is reachable at all.
 * THE SECOND, INDEPENDENT BLOCKER already found and documented (WI-1128, at `WHOLE_ROW_HOLE` in eval/builtins.rs): the whole-row sentinel is ONE symbol shared by BOTH `join` binders, so it can say neither which row it means nor match `fill_recipe_holes`' sole-column arm over a MERGED column list. It is unreachable today only because `Concat` refuses the operands that would reach it — this redesign REMOVES that gate, so the sentinel must be keyed per binder in the SAME change or the natural spelling `join(r, ages, (c, q) -> eq(c.age, q))` still fails. Today it has no drivable control; under this ticket it does.

ACCEPTANCE: a decision recorded in 052 (do it or decline it, with the measurement that decides); if done — a join / fix / project over a one-column relation RUNS end-to-end with the recovered column name, driving the values; the tuple-typed-column fixture above becomes a correct schema or a loud error, and its recorded-limit test is RETIRED rather than patched; `Membership` distinguishes 0 columns from one `Unit`-typed column (WI-728's recorded limit retires with it); the whole-row sentinel is per-binder; `where`'s changed spelling is migrated with its tests; kernel-language.md 6.8 and relation.anthill updated together; cargo-test green via scripts/test.sh.

## Feedback

### 2026-08-18T19:29:55Z — claude

OPTION A ADDED AND RECOMMENDED — DROP THE COLLAPSE ENTIRELY (user, 2026-08-18: "why we need Collapse[T]? Why we don't want just work with one-element tuple?"). The ticket as filed proposed keeping the collapsed ROW type behind a new `Collapse[T]` constructor. That preserves an ergonomic that is not worth its price, and the simpler option is better than both it and the status quo.

WHAT `Collapse[T]` ACTUALLY BUYS, and it is one line. 052's whole stated rationale for the collapse is: "one free variable -> T is that value (a 1-tuple auto-collapses): a relation with only `board` free is `Relation[Board]`, so `queens.head : Board`". That is the entire justification — `.head` reads as the element instead of a one-field record. `Collapse[T]` is a type constructor whose sole purpose is to keep that sentence true.

OPTION A: no collapse at all. The schema IS the row type, always the full named tuple. `Relation[(age: Int64)]`, `queens.head : (board: Board)`, read as `row.board`.

  * NO NEW CONSTRUCTOR. Option B needs `Collapse[T]` in the family and a reduction at the return-type boundary plus the `provides LogicalStream[T = ...]` threading, which was the measurement most likely to kill it. Option A deletes that risk rather than measuring it.
  * ALL THREE AMBIGUITIES DIE, including one Option B does NOT close by itself: `Membership` becomes exact for free, because a 0-column relation stays `Unit` while a one-`Unit`-column relation is `(u: Unit)`. So WI-728's recorded limit retires without touching the `()`-vs-`Unit` typing gap (measured separately: `()` in an entity field is refused as "expected Unit, got TupleLiteral", so NOT depending on it is a real saving).
  * `Concat` / `Without` / `Project` simply work at arity one. No refusals to write, no messages to phrase, and the WI-1128 refusal messages this ticket would retire become dead code rather than better prose.

MEASURED, THE ERGONOMIC IS BARELY EXERCISED. Census of shipped sources (examples/, stdlib/, rustland/*/anthill/): 46 rules have exactly one head variable, and NONE of them is consumed as a relation VALUE — every one is used as a goal in a rule body, where the schema type never arises. The only 1-column drain anywhere is `examples/classic-mini/ancestor`, and it arrives by APPLICATION (`ancestor("bart")` binds the first column and narrows to the second), then does `length(ofBart.takeN(100))` — it never touches an element, so it is indifferent to the row shape. So the count of places that would have to change from `x` to `x.col` is currently ZERO, and the count that would merely get a more informative type is one.

AND THE APPLICATION CASE IS AN ARGUMENT *FOR* OPTION A, not a cost: `ancestor("bart")` is exactly where a name is lost today. Under Option A the narrowed relation keeps `(is: String)`, so the column stays addressable — the same information WI-1128 spent its whole length explaining could not be recovered.

WI-1131 REMOVED THE OLD OBJECTION. A one-field named tuple was a syntax error as a VALUE until yesterday, so "just use a one-element tuple" was not fully writable when 052 chose the collapse. It is now.

THE ONE REAL COST OF OPTION A, and it is structural rather than ergonomic: kernel-language.md 6.8 desugars `x.(f)` to `x.f` at CONVERT time, before any type exists, and calls the collapse a paired type-and-value convention. So a relation projection `r.(f)` currently becomes a scalar member access — which is precisely why `ages.(age)` reports "no such member" (WI-20260818-7X7NK). Under Option A a one-member relation projection must yield a ONE-COLUMN RELATION with schema `(f: T)`, so relation projection must stop riding the convert-time desugar, and `r.(f)` diverges from `t.(f)` on a plain tuple. Decide whether that divergence is acceptable, or whether the term-level collapse moves too; this is entangled with WI-20260818-7X7NK and the two should be looked at together.

WHAT STAYS TRUE FOR BOTH OPTIONS: it is a breaking change to a specified rule (6.8), `where`'s bare-binder spelling `eq(c, 30)` becomes `c.age` either way, and the whole-row sentinel must be keyed per binder in the same change (it is unreachable today only because `Concat` refuses the operands that would reach it, and both options remove that gate).

RECOMMENDATION: Option A. Option B stays recorded as the fallback if `queens.head : Board` turns out to be load-bearing for a reader that the census above did not find — but the census found no such reader, and Option A is simpler than the code we have today, not merely simpler than Option B.

