## Attributes

- id: WI-20261009-S723J-scaland-close-a-composite-s
- created: 2026-10-09T18:53:29Z

- status: Delivered
- status_agent: codex
- status_at: 2026-10-13T14:09:17Z

- acceptance: scaland-sbt-test

- tags: scaland

## Description

SCALAND: CLOSE A COMPOSITE'S EQUALITY AT THE LOAD THAT DEFINES IT, AND LOAD THE STDLIB FIRST — the Scala port of two rules rustland has and scaland does not.

WHAT. (1) kernel-language.md §8.3 (WI-20261006-SZKV7): a load may change nothing about the equality of a composite an EARLIER load defined — who supplies its `eq`, which provisions of `PartialEq` / `Eq` / `NonEq` name it, under what conditions — and doing so is a load error (`EqualityOfEarlierSort` in rustland, decided by comparing each composite's equality signature recorded when a load ends with the one recomputed at the next). scaland has no such check: measured 2026-10-09 by grep, nothing under `scaland/src` names it or an equality signature. (2) The stdlib is its own load in the product (the rustland ticket filed the same day): a program is a later load than the standard library, so rule (1) applies to every program.

WHY A TICKET OF ITS OWN. The first is a pass that is not there — the signature, its recording at every exit of a load, the refusal and its message — not a call site to move. Check first whether scaland's loader can be called a second time on a KB at all, and what its equality derivation does then: rustland's two-step switch found two differences before any rule was written (docs/design/test-infrastructure.md §4 A3), and scaland has never been run that way.

CONTROL. The rows of `wi_szkv7_later_equality_test` are the shapes to port: a witness `eq` for a base composite in a later load is refused; the same file loaded with the base is not; a later load that leaves equality alone loads; a sort with no constructors is outside the rule.

DONE WHEN: scaland refuses what rustland refuses for those shapes, its entry point loads the stdlib before the program, and `sbt testFull` is green.

## Changes

### 2026-10-10T15:56:16Z — feedback — user

SCOPE EXTENDED 2026-10-10 (user): THE SEAL TOO. When this was filed rustland's product did not load the library apart. It does now (WI-20261009-AN6CQ), and it SEALS that load — so a program is held to three rules where this ticket names one, and the port owes all of what kernel-language.md §8.3 now says of a program:

(3) A SEALED LOAD'S DECLARATIONS ARE NOT MADE AGAIN (WI-20261009-4ZRTG; `load::seal_declarations`, `SealedDeclarations`). A later load may not declare an operation, a type or an entity the sealed load declared: it is given the refusal one load of both gives, the sealed site first, and behind a seal there is no presenting again. The seal is EXPLICIT — an unsealed sequence of loads behaves as it did.

(4) WHAT A LATER LOAD WOULD CHANGE IN A SEALED BODY IS REFUSED (WI-20261010-9BKZ4; `ChangesSealedCode`): a `@[simp]` rule that would rewrite a sealed operation's body, a dot rule for a sealed sort's members, a provision whose elements are all a sealed load's and that changes who answers a dispatch written there. In rustland this is also where the second load gets cheap, a sealed load's bodies being typed once; the port owes the VERDICTS, not the optimization.

(5) THE ENTRY POINT SEALS: the stdlib first, sealed, then the program (`load::load_program`). An empty library is one load and no seal, which is what the CLI's `--no-stdlib` over a library's own files is.

CHECK FIRST — measured 2026-10-10 by grep over `scaland/core/src/main`, so absence of a spelling and not of a behaviour: nothing names a seal or either refusal; and no ONE-load refusal of a second declaration of an operation or a type was found either (rustland's R1 / WI-997 and WI-1049). The seal carries those rules across loads, so there may be nothing for it to carry yet, and that would come first. `@[simp]` is parsed (`AnthillParser`) and no use of it where a body is typed was found — if there is none, the first shape of (4) cannot arise there, and the ticket says so rather than porting a refusal of nothing. Loads go through `Loader.load` and `Loader.loadAll`.

CONTROL, beside the description's: the rows of `wi_4zrtg_sealed_library_test` (an operation, an enum and a sort declared again are refused as a later load and in one; a new name in a library scope loads; an unsealed earlier load is not a library), the refusals of `wi_9bkz4_sealed_bodies_test`, and `wi_an6cq_load_program_test` (sealed between the two loads; an empty library seals nothing; an empty program is no second load).

DONE WHEN, added: scaland refuses those shapes as rustland does, or this ticket says which rule has no counterpart there and why; and §8.3's status line about the Scala implementation is taken out.

### 2026-10-13T14:07:56Z — feedback — codex

Implemented Scala load boundaries: Loader.loadAll checks duplicate declarations before symbol mutation and records resolved equality suppliers/provisions (including bindings and conditions) for composites; later changes raise EqualityOfEarlierSort and remain refused on retry. Explicit sealDeclarations protects operations, consts, sorts/enums and entities with the first declaration site. Loader.loadProgram loads the library first, seals it, then loads the program; empty library is one unsealed load and empty program adds no load. StdlibFixture and SMT fixtures now use loadProgram. Scala has no CLI; this is its public product-loading entry point. Counterpart audit: LoadPass drops operation bodies and const values (no typer/evaluator); OpGen emits abstract signatures only; loadProvidesClause drops bindings and has no DictLayout/dispatch resolution. Consequently simp rewriting of sealed bodies, dot-rule member dispatch, and provisions changing a sealed dispatch have no executable counterparts. There is also no structural equality derivation/host equality dispatch to port; the boundary records the source suppliers/provisions independently of the lossy legacy metadata. Updated only the Scala implementation status in spec section 8.3, as required by this ticket; language rules unchanged. Validation: final sbt testFull passed 694 tests (653 core, 40 SMT, 1 Scala generator). LoadBoundaryTest has 17 tests, including actual SLD resolution after the second load, same-load/abstract/unsealed controls, witness/member equality, conditions and new instantiations, equivalent named/positional bindings, redeclarations and empty-load cases. Back-out measurement disabling the two boundary checks: 12 failed, 5 controls passed; restored implementation passes. Manual review and git diff --check completed. The requested /code-review skill is not installed, so it was not run. No Rust sources changed; no Rust test run. Changes remain uncommitted.

### 2026-10-13T14:09:16Z — feedback — codex

Manual review additionally found named requires binders declare types too: added them to declaration/seal checks and a driving regression for a sealed demo.Point.O. Final sbt testFull after this correction: 695 passed, 0 failed (654 core, 40 SMT, 1 Scala generator); 18 LoadBoundaryTest rows. Back-out measurement above covers the preceding 17-row suite. No further source changes after this gate.

