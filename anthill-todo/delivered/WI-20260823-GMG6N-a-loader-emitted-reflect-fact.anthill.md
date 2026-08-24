## Attributes

- id: WI-20260823-GMG6N-a-loader-emitted-reflect-fact
- created: 2026-08-23T11:37:51Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-24T09:05:29Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A loader-emitted reflect fact whose slot set disagrees with its entity declaration is UNREACHABLE from anthill, silently. `convert_term_inner`'s named-arg completion (load.rs, "every fact/pattern of a functor presents the same named slots") gives every term written in source — fact head, rule head, rule-body goal, CLI pattern — exactly the fields the entity DECLARES. A loader-emitted head does not take that path: it is assembled from a hand-written field list at the emitter. When the two lists disagree the facts are in the KB and `rules_by_functor` lists them, but no goal can reach them: the completed goal has the declared slots, the head has the emitted ones, and structural matching never bridges the gap. BOTH spellings fail and neither says why — a goal omitting the extra field matches nothing in silence, and naming it is refused as an unknown field. TWO INSTANCES, both measured: (1) `anthill.reflect.OperationInfo` emitted an eighth slot `type_params` against a seven-field declaration, so all 398 of its facts were unreachable — including `docs/proposals/typing_pass_spec.anthill`'s own rule bodies, which had therefore never matched anything, and every effect-row question an anthill-side checker would ask; (2) `anthill.realization.Implementation` emitted seven of its eight declared slots (WI-089(a)'s `binding` was added to the declaration and never to `emit_implementation_fact`), so a source-written `fact Implementation(...)` — the webots example writes nine — and a loader-emitted one from a `provides ... language rust` block had DIFFERENT shapes and no single query could see both. FIX: declare `type_params : List[Term]` on OperationInfo and thread it through the generated reflect bridge (`anthill-stl/src/reflect/{reader,bridge}.rs` — the struct is generated from the declaration, so the compiler enforces bridge == spec; only the loader's emitter is unchecked); emit `binding: none()` from emit_implementation_fact; and close the class with `check_metadata_slots`, a debug tripwire beside WI-630's `check_metadata_head` that refuses any `assert_metadata_fact*` head whose slot set differs from `entity_field_names(functor)`. Loader-only by construction — a user-written fact goes through `convert_term_inner` to `assert_fact` — so a panic is safe and cannot be provoked from source. ACCEPTANCE: an anthill rule body reading `OperationInfo(name: ?n, effects: ?e)` returns a declared operation's effect row, and one reading `Implementation(target: ..., artifact: ?a)` returns a `provides ... language rust` block's artifact; both return NOTHING when the fix is backed out. The tripwire has a `#[should_panic]` control. Full workspace green via rustland/scripts/test.sh.

