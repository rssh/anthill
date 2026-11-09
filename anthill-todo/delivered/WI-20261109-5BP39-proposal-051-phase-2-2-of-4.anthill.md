## Attributes

- id: WI-20261109-5BP39-proposal-051-phase-2-2-of-4
- created: 2026-11-09T14:15:17Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-09T19:57:27Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261109-P07E8-proposal-051-phase-2-1-of-4

- tags: proposal-051

## Description

PROPOSAL 051 PHASE 2 (2 of 4) — EVERY CARRIER SUPPLIES ITS `eq`; A TYPED CALL IS A PIN OR A DICTIONARY (051 §"`=` / `eq` become genuinely dispatched": "For a concrete argument the carrier pins the impl (`Int -> IntEq.eq`, still an `i64` compare); for an abstract argument the requirement dictionary supplies it"; 073 §1). TODAY `PartialEq.eq` is `@[host_implemented]`, the one spec-operation registration WI-880 kept (eval/builtins.rs `partial_eq_eq` -> `semantic_equal`; resolver `SemEq` -> `sem_eq_core`), and that host code decides by the value: IEEE for two `Float`s and field-wise for a composite reaching one, reflexivity, then the load-built index from the outermost constructor to its sort's own `eq` (`sem_eq_dispatch_target`), then raw structure. A typed call at a carrier with an own `eq` is pinned to it (traced 2026-11-09: `PartialEq.eq(pt(1, 2), pt(1, 9))` -> `Pt.eq`), but a typed call at a primitive records no pin (`PartialEq.eq(ax, bx)` at `Int64` inside `Pt.eq`) and runs the value-directed host code. WANTED: each primitive's provision of `PartialEq` binds a host member — `Int64`, `String`, `Bool`, `Symbol` and the other host carriers compare directly, `Float` by IEEE rules — so a typed call at a primitive is pinned as any member is; `PartialEq.eq` keeps no host implementation at the spec; a rule-body `=` goal reads the pin as SM910's ordering goals do (`goal_builtin_tag`: the tag is the primitive the carrier's member runs). The interpreter's semantic `builtin_eq`/`semantic_equal` go from the typed path. NOT HERE: a composite with no own `eq` (3 of 4, field by field), `neq` (4 of 4), and a call no type reaches (a query, a rule variable no head column reaches, host code calling `PartialEq.eq`), which keeps today's route until WI-20261105-CBRD2's row removes the index. Kept: `Eq`'s law at the member's entry (4067661d, `eq_law_of_member`); `AmbiguousEqDispatch` and `CarrierSuppliesNeq` at load. ACCEPTANCE: a typed `eq` at each primitive answered by its member in both bodies (nan pair false, `-0.0`/`+0.0` true), traced or asserted as pinned; the wi616/wi625/wi645/wi664 rows keep their verdicts; each part backed out alone failing the rows its header names; full workspace green via rustland/scripts/test.sh; families green on both carriers.

