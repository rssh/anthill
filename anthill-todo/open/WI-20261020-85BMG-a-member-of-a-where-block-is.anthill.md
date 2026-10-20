## Attributes

- id: WI-20261020-85BMG-a-member-of-a-where-block-is
- created: 2026-10-20T07:56:44Z

- status: Open
- status_agent: user
- status_at: 2026-10-20T07:56:44Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A MEMBER OF A `where` BLOCK IS READ AS AN OPERATION OF THE SORTS THAT PROVIDE THE BLOCK'S SORT. MEASURED on 663ac457, the programs over a program's own sorts the same on 098ce8a9. (a) `sort Shows { sort T = ?  operation show(x: T) -> String }`, `sort Named { sort T = ?  operation name(x: T) -> String }`, `sort NamedShows { sort T = ?  provides Shows[T = T] :- Named[T = T] where operation show(x: T) -> String = Named.name(x) end }`, `sort Dog { entity dog  provides NamedShows[T = Dog]  provides Named[T = Dog] where operation name(x: Dog) -> String = "dog" end }` and `operation via[Q](x: Q) -> String requires NamedShows[T = Q] = NamedShows.show[T = Q](x)`: `via[Q = Dog](dog())` loads and dies, "internal evaluator error: deferred dispatch frame-push: `NamedShows` reads 1 requirement slot(s) but the dictionary layout gives it 0" — the block member dispatched through the slot of the sort that writes it, as if it were that sort's interface operation. The library's `TypeValuePattern` reaches it: `sort Evil { entity evil  provides TypeValuePattern[T = Int64] }` with `requires TypeValuePattern[T = Q]` and `TypeValuePattern.admits[T = Q](t)` dies the same way, and `evil().admits(Int64)` is refused with the member's arity. (b) With `sort Gate { sort T = ?  operation show(g: T, n: Int64) -> String }`, `sort Gate2 { sort T = ?  provides Gate[T = T] }` and `Dog provides Gate2[T = Dog]` beside its `Named` provision (`Named` writing the block member `show` for its provision of `Shows`), `Gate.show(dog(), 1)` loads and dies, "dispatch of `Gate.show` landed on `Named.show`, whose parent `Named` is neither the spec nor the provider of the dictionary": the member is copied onto `Dog`'s operation table. (c) `Named` writing that block member and `Dog` an operation `show` of its own: `Named.show(dog())`, a direct call of the member, answers "own-show" in an operation body and in a rule body alike — the member's body is never run (the dot `dog().show()` is `Dog`'s own operation, and rightly "own-show"). THE RULE: a block member backs only its own provision and remains an ordinary operation of the sort that writes it, and a direct call builds the member's dictionary from the provision's conditions (proposal 066 §7.3, §7.4; kernel-language.md §8.7). THE READERS, found by SQZPQ's first review: eval's value-directed override (`spec_call_runtime_carrier`, reading `spec_op_parent_sort`), `build_sort_ops_table` pass 2 (load.rs), the WI-411 dot redirect (`find_spec_op_for_provided_sort`, dot_rule.rs), the slot classification (`DeferToRequirement` on the providing sort's slot), `defaulted_spec_op_parent`, `check_provider_operations`. A fix in two of them alone (SQZPQ's first version, reverted) turned (c) into a crash, so they move together. ACCEPTANCE: (a) refused at load where nothing supplies `Named[T = Q]`, as a direct call of the member at a ground instance is, and answering "dog" where the caller requires it; (b) refused at load, `Dog` backing no `Gate.show`; (c) "dog" in every spelling; a row per reader, back-outs measured; full gate green.

