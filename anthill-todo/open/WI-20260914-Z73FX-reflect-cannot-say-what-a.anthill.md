## Attributes

- id: WI-20260914-Z73FX-reflect-cannot-say-what-a
- created: 2026-09-14T05:03:08Z

- status: Open
- status_agent: user
- status_at: 2026-09-14T05:03:08Z

- acceptance: cargo-test, scaland-sbt-test

- tags: reflect

## Description

REFLECT CANNOT SAY WHAT A SCOPE MAY NAME: no reflect operation or fact exposes `internal` visibility, so an anthill program that renders "the declarations a candidate programs against" cannot leave out the ones the candidate is not allowed to name.

WHY NOW. WI-20260908-H2GDZ part (b) (its 2026-09-14 feedback records the agreed shape) replaces the guardians generation prompt's paste of `lib/*.anthill` with an anthill `describe(spec, tools)` over reflect that renders THE CANDIDATE'S VIEW of the KB. Point (3) of that shape is "only what a candidate can name": `guardians.Text.text`, `guardians.LiveLlm.live_llm`, `guardians.FakeLlm.fake_llm` and `guardians.Source.source` are `internal` (§8.6), and a prompt offering them is bait the checker refuses (`rejected/relabel.anthill`, `forged_llm.anthill`, `forged_source.anthill`). WI-20260913-2858G made `describe` callable from inside `guardians.attempt`; this is what remains.

MEASURED STATE OF THE SURFACE (read from the code, 2026-09-14):
 * `SortInfo(name, kind, definition, constructors, operations, parameters, requires)`, `MemberInfo(name, kind, parent)`, `OperationInfo`, `FieldInfo`, `EntityInfo`: no visibility field.
 * `intern.rs` has `SymbolTable::is_internal(sym)` and `internal_visible_from(sym, scope)`; nothing in anthill-stl's reflect bridge calls either.
 * NOT a blocker, contrary to a note in stdlib/anthill/reflect/reflect.anthill: `term_as_sort` / `sort_as_term` / `can_be_sort` are said to be "DECLARED, AND BACKED BY NOTHING … they run NOWHERE", but `register_reflect_builtins` (anthill-stl/src/reflect/builtins.rs) registers all three as interpreter builtins through `register_if_present`. The note is right that `operation_map` does not map them (`wi880_reflect_mapping_test` uses `sort_as_term` as its un-mapped control) and appears wrong that they cannot run. NOT YET DRIVEN — the first acceptance row below settles it, and the note is corrected either way.

THE QUESTION IS "VISIBLE FROM WHERE", NOT "IS IT INTERNAL". `internal` hides a name from cross-scope resolution with top-level code outside every declaring scope (WI-977), so one symbol is visible from its own sort and invisible from `guardians.agent`. A bare `internal: Bool` on `MemberInfo` would make every consumer re-derive the scope rule. Two shapes to choose between:
 (a) an operation `visible_from(s: Symbol, scope: Symbol) -> Bool` over `internal_visible_from` — answers the real question, no fact-schema change, no WI-20260823-GMG6N drift exposure (a loader-emitted reflect fact must match its declaration in set and order);
 (b) a `visibility` field on `MemberInfo` / `SortInfo` — queryable from rules, but changes a loader-emitted schema (three places must agree: declaration, loader emitter, anthill-stl `kb_*`) and still leaves the scope rule to the consumer.
(a) is the recommendation; (b) needs an argument this ticket does not have.

WHAT MUST STAY TRUE: reflect remains read-only over visibility (it reports, it does not grant); a scope a candidate cannot name is answered `false`, never a fault; the four guardians `internal` constructors answer invisible from `guardians.agent` and visible from their own sorts.

ACCEPTANCE:
 1. `term_as_sort` driven from an anthill body on a type term read out of `OperationInfo` (e.g. `Text[Trusted]` from `Email.send`'s `body` parameter) answers `some(…)`, and `KB.fields` / `KB.operations` on the result answer `Text`'s; the reflect.anthill note is corrected to what that row shows.
 2. The visibility query: `guardians.Text.text` invisible from `guardians.agent`, visible from `guardians.Text`; `guardians.Text.untrusted` visible from both (CONTROL — a query answering `false` for everything passes row 2's first half); the same for `live_llm` / `fake_llm` / `source`.
 3. A non-`internal` name in another namespace answers visible (CONTROL against a query that only reports "same scope").
 4. Full workspace green via rustland/scripts/test.sh.

