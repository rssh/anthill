## Attributes

- id: WI-20261113-DY84V-proposal-074-stage-5-a
- created: 2026-11-13T23:01:44Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-24T12:37:53Z

- acceptance: cargo-test

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 5 — A `REQUIRES` NAMING A SORT WITH CONSTRUCTORS IS REFUSED (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§2, "A sort with constructors is closed"). First, the count: every such `requires` in the test fixtures, by a traced run of the full gate (the standard library and the examples write none). Each is rewritten, its sort without constructors or the refinement removed, or deleted where it tests only that refinement. Rows: `X1 requires X` refused, naming both sorts; a data sort requiring a spec (`requires Eq[T = K]`) and a spec refining a spec (`Classical requires Constructive`) load and run as today. Spec: §8.2's refinement paragraph ("A sort that refines another is a subtype …") and §5.1's data-sort rule, which today names `provides` only. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

## Changes

### 2026-11-24T12:37:26Z — feedback — user

CENSUS AND DECISIONS (2026-11-24, with the user). Census by a traced full gate (12690 / 0): 48 sort-level requires naming a sort with constructors, in 22 test files; none in the standard library or the examples, nor in docs/, anthill-testcases, testdata or the guardians fixtures (loaded by hand). Mostly error families (Narrow requires Boom, FileNotFound requires IoError) and Dog requires Animal. The operation-level hits of the trace were its own misreading (a goal's first positional), but for wi_fdj0e's operation needs() requires Red. Asked by the user why the clause is refused: a data sort provides itself (kernel-language 5.3, WI-4DYR6), so the demand half of requires X is answered by X, which has no dictionary of its operations, and the clause's whole effect is the subtype; MEASURED with the refusal off, take(e2(j: 5)) over X's match on e1 loads clean and dies match_failed. The user's sort XwithShow { requires X  operation show(x: XwithShow) -> String } (X an enum, the requirer without constructors): MEASURED with the refusal off, display(b) answered "b", codeOf(b) = X.code(x) died (an Instance wrapper reaching X's match), and a second provider Y made y an X; Show[T = X] answers all three. Decided: keep the stage as built -- every sort-level requires naming a data sort refused, XwithShow included; an operation's requires naming one is a goal and not refused. The refining case of a derived domain (J9SSG / YR3N7) removed with the refusal, unreachable after it.

### 2026-11-24T12:37:39Z — feedback — user

DELIVERED (2026-11-24, 3e6a63290): a sort's requires naming a sort with constructors is refused at load, LoadError::RequiresNamesDataSort naming both sorts, through an alias, at a parametric sort, an enum, a named requirement, whatever the requiring sort. Acceptance: rows driven (wi_dy84v_requires_data_sort_test, 6: the refusal and its control, every spelling, a data sort requiring Eq answers true / false, a spec refining a spec 105, Classical refines Constructive and Minimal, a foreign value in no derived domain); the refusal backed out by a temporary switch over all of anthill-core (11607 rows): 4 refusal rows fail, here and in wi_4dyr6 and m460d; 20 census files rewritten, values unchanged; the refining case of a derived domain removed (J9SSG's file, YR3N7's two rows). Gate 12689 / 0; families green on both carriers; scaland testFull 811 + 51 (2 skipped) + 1. kernel-language 5.1, 5.3, 8.2 and proposal 074 agreed with the user.

