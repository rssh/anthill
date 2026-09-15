## Attributes

- id: WI-20260914-Z73FX-reflect-cannot-say-what-a
- created: 2026-09-14T05:03:08Z

- status: Open
- status_agent: user
- status_at: 2026-09-14T05:03:08Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260914-DV7DP-a-meta-block-on-a-sort-entity

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

## Changes

### 2026-09-14T05:48:04Z — feedback — user

DECIDED WITH THE USER (2026-09-14): `internal` BECOMES A META FLAG, NOT A NEW FIELD — no schema change on SortInfo / MemberInfo / EntityInfo. (1) ONE STATEMENT, TWO SPELLINGS: `internal entity text(…)` is shorthand for `entity text(…) @[internal]`; the grammar already admits a trailing meta_block on sorts, enums, entities and consts. (2) THE MARK IS DECIDED FROM THE PARSE IR, at `record_internal`: modifier OR the declaration's meta block carrying the flag — both are visible in the scan passes, so resolution keeps seeing it before any fact exists. (3) THE FLAG RIDES AS THE CLAUSE META OF THE DECLARATION'S OWN REFLECT ROW (§7: every fact carries metadata) — `MemberInfo(name: text, kind: Constructor, parent: Text) @[internal]`; for an operation it is `OperationInfo.meta`, which is §5.8's meta already. (4) NOT FORGEABLE, NOT LATE: clause meta is written only by the declaration; the mark comes from the IR, never from a row. FOUND WHILE DECIDING: the loader reads `.meta` only for facts, rules and operations — a meta_block on AbstractSort / SortWithBody / Entity / Const is parsed and SILENTLY DROPPED (load.rs reads it at four sites, none of them those); fixing that is step one and wants its own row (a sort's `@[Marker]` reaches the KB). REFLECT SURFACE: `KB.meta_of(kb, s: Symbol) -> Term` (a declaration's meta whichever row carries it; serves @[internal], codegen markers, @[simp]) plus `visible_from(s: Symbol, scope: Symbol) -> Bool` (the flag says internal; a candidate needs visible-from-here). This replaces the description's option (b) and keeps (a). OPEN: refuse `internal … @[public]` as a conflict (public records no flag)? refuse `@[internal]` on a rule or fact (visibility is a name's, not a clause's)?

### 2026-09-14T05:48:44Z — feedback — user

REFLECT SURFACE = EXISTING KERNEL FUNCTIONS, EXPOSED (user, 2026-09-14). Add to `anthill.reflect`'s existing `provides anthill.reflect language rust … operation_map` block (the WI-880 route), each a thin binding: `visible_from(s: Symbol, scope: Symbol) -> Bool` over `SymbolTable::internal_visible_from` (scope via `scope_id`); `meta_has_flag(meta: Term, key: String) -> Bool` over `kb::load::meta_has_flag` (what @[simp] already reads); `meta_value(meta: Term, key: String) -> Option[T = Term]` over `kb::load::meta_value`. The one NEW read is `KB.meta_of(kb, s: Symbol) -> Term` — the declaration's meta term (the clause meta of its reflect row; `OperationInfo.meta` for an operation). Then 'is it internal' is `meta_has_flag(meta_of(kb, s), "internal")`, with no visibility-specific accessor. Each binding driven from an anthill body, per wi880_reflect_mapping_test's pattern.

### 2026-09-14T05:59:18Z — feedback — user

ANSWERED BY THE USER (2026-09-14). (1) YES — `internal … @[public]` (the modifier beside a meta flag that contradicts it) is a LOAD ERROR, not a precedence rule; `public` stays the explicit default and records no flag, so a bare `@[public]` alone is not a conflict. (2) NO — `@[internal]` on a RULE or FACT is NOT refused. Implication to settle in the implementation, and stated here so it is not decided by accident: the flag hides the NAME THE CLAUSE INTRODUCES — the predicate a bodyless declaration / first clause introduces, or a rule's label — through the same `internal_visible_from` mark; a clause extending a predicate declared elsewhere introduces no name, so its flag must either be refused there or apply to nothing, and silently applying to nothing is the one answer the repo's rules exclude. Acceptance gains a row for each: the conflict refused with a message naming both spellings; an internal helper predicate resolvable inside its declaring scope and hidden from outside it.

### 2026-09-14T06:04:38Z — feedback — user

CORRECTION TO THE PREVIOUS NOTE'S (2), agreed with the user (2026-09-14): `@[internal]` IS REFUSED WHEREVER THE `internal` MODIFIER IS NOT LEGAL. Measured in tree-sitter-anthill/grammar.js: `visibility` is admitted on abstract_sort, sort_with_body, the sort binders, effects_sort_item, enum_declaration, operation_declaration, const_declaration, entity_declaration and operation_entry — NOT on rules, facts or constraints. So the flag stays an exact shorthand, legal precisely where the modifier is; on a rule/fact/constraint it would not be a shorthand but a new feature (predicate visibility), with its own questions — clause meta is per-clause provenance so two clauses could disagree, cross-scope clauses extending a hidden predicate, overlap with the gate's containment G2. A refusal can be lifted when that is designed; a permission cannot be withdrawn once relied on. COST, the user's concern: small — the loader already refuses a tag on an unlabeled rule at one of its four meta-read sites ("A `[…]` tag on it has no clause to govern"); this is one `meta_has_flag(kb, meta, "internal")` test at the fact and rule read sites plus one message, and the `internal … @[public]` conflict is one test at `record_internal`. Acceptance: `@[internal]` on a fact, a rule and a labeled constraint each refused naming the declaration kinds that admit it.

