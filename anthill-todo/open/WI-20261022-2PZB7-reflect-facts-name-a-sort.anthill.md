## Attributes

- id: WI-20261022-2PZB7-reflect-facts-name-a-sort
- created: 2026-10-22T14:15:49Z

- status: Open
- status_agent: user
- status_at: 2026-10-22T14:15:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

REFLECT FACTS NAME A SORT-NAMED OPERATION'S SORT BY ITS TYPE FACE — follow-up of WI-20261022-7EXEY, chosen with the user 2026-10-22 over keeping the plain symbol. Since 7EXEY a sort that shares its name with an operation (WI-751's pair) has a type face (`KnowledgeBase::declaration_has_type_face`); its plain symbol is the operation, and reflect's `kind` says `Operation` for it and `Sort` for the face (user, 2026-10-22). But the reflect facts the loader stores to DESCRIBE that sort still name it by the plain symbol: `SortInfo(name)`, a provision's spec head in `SortProvidesInfo` (`Loader::sort_inst_to_value` → `make_name_term_from_sym`), `SortRequiresInfo(sort_ref)`, `MemberInfo`/`OperationInfo` owners, `ProvidesConditionInfo`, `ProvisionMemberInfo`, `DescriptionInfo(target)` — ten relations in stdlib/anthill/reflect/reflect.anthill. A reflect program that walks them and asks `kind` of the sort gets `Operation`; one that filters `kind == "Sort"` skips it. (A member's declaring SCOPE owner stays the plain symbol: a scope is the declaration's, not a type.) TO BUILD: each producer names such a sort by `type_face_of`; each typer reader of these relations that compares a head with a plain symbol reads the declaration (`Decl::of` / `canonical_sort_sym`, which already mask the face) — the provider index keys are canonical and need nothing. DECIDE WITH THE USER whether a CONSTRUCTOR's sort (an eponymous or free-standing entity, which has had a face since JB6RS and is stored plain in the same facts) moves too — the principled answer, and a much wider one (every provision whose carrier is an entity). Nothing in the stdlib or the examples calls `kind` today (measured 2026-10-22). ACCEPTANCE (cargo-test, driven): over `sort Positive { sort T = ?; operation sign(x: T) -> Int64 }` beside `operation Positive(x: Int64) -> Bool`, in both orders: `kind` of the spec read from its `SortProvidesInfo` row and of the `SortInfo` name is `Sort`; WI-7EXEY's rows unchanged; the spec alone as control; each back-out named at its row.

## Changes

### 2026-10-22T14:16:10Z — feedback — user

Also a provision's BINDING VALUES: `provides Container[Elem = Positive]` stores `Elem = Positive` plain (`Loader::clause_binding_as_written`), where a `requires` or a signature names the same type by its face. Measured 2026-10-22 under 7EXEY: matching still holds — `requires Container[T = B, Elem = Positive]` is met and `Elem = Int64` is refused, the comparison masking the face — so the gap is what a reflect reader sees in the stored row, as for the spec head.

