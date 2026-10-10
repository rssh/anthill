## Attributes

- id: WI-20261009-4ZRTG-the-library-is-sealed-a
- created: 2026-10-09T20:34:40Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-09T23:31:19Z

- acceptance: cargo-test

## Description

THE LIBRARY IS SEALED — a program loaded after the standard library may not redeclare what the library declared, as it may not when the two are loaded in one call. The prerequisite of WI-20261009-AN6CQ (the stdlib as its own load in the product), found by /code-review of that ticket and decided 2026-10-09 (user): seal the library first.

THE DEFECT. The loader's "declared once" ledgers are PER LOAD, on purpose — `op_decl_sites` is cleared at each load (WI-1049), `DeclLedger` is a local of `scan_definitions` (WI-997), `decl_sites` is cleared per scan (WI-999) — so that a source an earlier load accepted may be presented again. The cost is that a LATER load's declaration of a name an EARLIER load declared is not seen as a second one. Measured 2026-10-09, the stdlib and one user file, `recipe_load` under each recipe by name:

  shape (the user file)                                        one call                      stdlib, then the file
  redeclares an operation   (`anthill.prelude.Option.isEmpty`) REFUSED, declared twice      LOADS CLEAN — and its body replaces the library's: `anthill run` of `if isEmpty(some(1)) then 42 else 7` exits 42
  reopens an enum           (`Meta.Trust` + a new entity)      REFUSED, a type defined once  LOADS CLEAN — a closed library ADT gains a variant
  redeclares a sort         (`sort Option` + an entity)        THE LOADER PANICS             LOADS CLEAN
  a second entity of a name (`Trust.proved`)                   REFUSED                       REFUSED, by another rule and message
  adds an operation to a library sort's scope                  loads clean                   loads clean
  redeclares a const        (`cli.help.NAME_COLUMN = 99`)      LOADS CLEAN                   LOADS CLEAN
  redeclares an alias       (`platform.Path = Int64`)          LOADS CLEAN                   LOADS CLEAN

So three shapes are refused in one call and accepted in two; one is a PANIC in one call (`kb/fill_derive.rs:425`, index out of bounds — a loader that panics on a user's file, whatever the order); and two are accepted under BOTH, which is no difference between the orders and no rule either (WI-998's member table was to cover consts).

WHO THIS REACHES TODAY, before AN6CQ lands: every test of anthill-core that follows the load switch (WI-059, on main) loads its fixture after the stdlib, so a fixture redeclaring a library operation loads clean where it was refused — no test asserts either way, the suite being green under all three recipes; and `KB.loaded`, whose callers gate a candidate on the layer's own record of what it declared (`LayerDelta::declared`).

WHAT TO BUILD, suggested. The library's declarations REMEMBERED on the KB when its load ends — operations and types at least, each with its site — and a later load refused when it declares one of them, with both sites named, as the one-call refusal names them. Decide, and say in kernel-language.md §8.3 beside the equality rule: (1) what a "second declaration" is across loads when the SAME source is presented again — three suites do that on purpose (`induction_axiom_witness_test`, `scope_axiom_witness_test`, `specialization_witness_test`, `wi1049`), and the CLI given the on-disk stdlib without `--no-stdlib` used to fail loudly on every sort and now loads on top of the embedded copy; (2) whether the seal is a property of every earlier load or only of a library named as one (`load::load_program`, which AN6CQ's branch adds) — the test recipes' shared base must carry it either way, so that a test sees what a user sees; (3) what `KB.loaded` does with it. The record is a new field of `KnowledgeBase`: place it in `kb/deep_clone.rs` and classify it in `kb/layer.rs`, both of which refuse to compile until it is.

ALSO FOUND, same review, same cause (a pass that reads the whole KB in a later load): the program's load registers 15 `ProofRecord(result: Pending)` facts for provisions the LIBRARY's load derived (`register_specialization_witnesses` runs before the derivation passes, so only a later load sees those rows) — `anthill check` on an empty program then lists the stdlib's derived provisions as obligations, and a program's own derived provisions get none.

CONTROL. The table above as rows, each fixture run under both orders by name and through the real binary once AN6CQ is in: every shape refused in one call is refused in two, with the library's site in the message. Back out the record and the three rows fail. The panic gets a row of its own, under one call. The idempotent-across-loads suites stay green, which is the control on (1).

NOT IN SCOPE unless the census grows: consts and aliases redeclared in one call (file under WI-998's member table); making re-presentation of a source truly idempotent (a re-presented stdlib leaves 363 more facts and 185 more rules today).

DONE WHEN: the three shapes are refused when the file is a later load; the one-call panic is a refusal; the proof records are the same under both orders; §8.3 says what a later load may not declare; the gate is green under all three recipes.

## Changes

### 2026-10-09T20:36:26Z — feedback — user

DECIDED 2026-10-09 (user), the two questions the description left open. (1) THE SEAL IS EXPLICIT: a later load is refused for redeclaring an earlier load's operation or type only after the earlier load was sealed — the library's load in the product (`load::load_program`, AN6CQ's branch) and the shared base of the test recipes. Plain sequences of `load_all` and `KB.loaded` behave as they do today; a uniform rule can adopt the same record later. (2) THE SAME SOURCE PRESENTED AGAIN IS THE SAME DECLARATION: same text, same position — not a second one. So the four suites that re-present files stay as they are, and the CLI given the on-disk stdlib without `--no-stdlib` loads it on top of the embedded copy.

### 2026-10-09T22:26:47Z — feedback — user

DECISION (2) REVERSED 2026-10-10 (user): BEHIND A SEAL THERE IS NO PRESENTING AGAIN — every later declaration of a sealed name is refused, the sealed source itself included. Why: 'the same text at the same position is the same declaration' was only true if the loader then SKIPPED it, and it does not. It loads it again: an identical ground fact merges with the first (`fact_dedup`), a record that mentions a type parameter is stored a second time under fresh variables (WI-1049's comment says so of `OperationInfo`), and every rule is stored again — the stdlib presented twice leaves 4 689 facts and 439 rules where once leaves 4 326 and 254. The user's point: a second version of a sort is given a new record instead of being checked against the first, which contradicts what the load is supposed to guarantee. So `same_declaration` is gone; the four suites that present files again on purpose build their KB with `common::load_unsealed`, by name, and are listed in the guard for it; and the CLI given the on-disk stdlib beside its embedded copy will be refused again once AN6CQ seals it, as one call refuses it.

### 2026-10-09T23:31:17Z — feedback — user

DELIVERED 2026-10-10 — the library can be sealed, and the test recipes seal it.

THE SEAL. `load::seal_declarations` records what the last load declared — its types as R1's ledger held them, its operations as `op_decl_sites` did — in `KnowledgeBase::sealed` (an `Arc`, shared by every copy and layer of a sealed KB). A later load that declares one of them is given the one-call refusal with the sealed site first: `DuplicateTypeDeclaration` from the scan, `DuplicateOperationDeclaration` from the pass that already made it; ONE refusal a name, not R1's and another. `seal_declarations_of` seals the first N files of a load that held a library and more in one call. Sealing twice seals once. The seal is EXPLICIT (user): plain `load_all` sequences and `KB.loaded` over an unsealed KB behave as they did. And BEHIND A SEAL THERE IS NO PRESENTING AGAIN (user, reversed 2026-10-10): a declaration presented again is loaded again, not skipped, so the sealed source itself is refused.

WHO SEALS. `tests/common`'s `run_recipe`, for every load it makes: the library, and only the library, under all three recipes — so a test's later load of its own gets one verdict whichever recipe built the KB. The product does NOT yet: that is WI-20261009-AN6CQ, parked on `wi-an6cq-stdlib-first`, which will call it between its two loads.

ALSO IN THIS CHANGE, same cause. (1) A type declared twice no longer takes the loader down: `derive_sort_domains` queued a job for each declaration, the recorded domain paired the last declaration's parameters with conditions over both, and six readers index one by the other — one job a sort in a batch now. (2) `register_specialization_witnesses` skips a provision a derivation asserted (the row's own mark), so a later load registers the proof records one call registers: 127 and 127 for the stdlib and a small file, where two loads gave 142.

CONTROLS. `wi_4zrtg_sealed_library_test`: 17 rows — the three shapes refused as a later load and in one call; the panic by two roads; one refusal for a type the later load declares twice; the sealed source presented again, from the same files and from another copy; another text at the same position; sealing twice; a later load into a KB of each recipe; the unsealed controls; the proof records with a fixture that registers its own. Six back-outs measured after the last change, tabled in its header. The four suites that present files again on purpose (`induction_axiom_witness`, `scope_axiom_witness`, `specialization_witness`, `wi1049`) build their KB with `common::load_unsealed`, by name, and the guard lists them for it.

NOT COVERED, in the spec too: a `const` and an alias declared again, which one call accepts as well.

/code-review ran once (14 findings; 12 taken, one answered at the field it questions — the type ledger is kept beside `decl_sites` because that log counts an alias as a type and R1 does not — and one, the same-source rule, taken to the user, who reversed it). What was changed in answer, the reversal included, was checked by the rows, the back-outs and the runs below, not by a second review.

RUNS ON THE TREE AS DELIVERED: the gate on the shared base 8 902 / 0 / 14, observed SHARED BASE; anthill-core under FRESH 8 022 / 0 / 6, observed one shot; under TWO-STEP 8 022 / 0 / 6, observed TWO-STEP. No existing fixture declares a library name again.

