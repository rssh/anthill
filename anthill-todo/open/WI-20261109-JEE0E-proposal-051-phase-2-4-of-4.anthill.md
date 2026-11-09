## Attributes

- id: WI-20261109-JEE0E-proposal-051-phase-2-4-of-4
- created: 2026-11-09T14:15:50Z

- status: Open
- status_agent: claude
- status_at: 2026-11-09T14:15:50Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261109-5BP39-proposal-051-phase-2-2-of-4

- tags: proposal-051

## Description

PROPOSAL 051 PHASE 2 (4 of 4) — `neq` IS A BODY IN THE SPEC, `Bool.not(eq(a, b))` (decided with the user 2026-11-09; library/004 and 051 amended, the text agreed with the user first). TODAY `PartialEq.neq` is `@[host_implemented]` beside an inert law `rule neq(?a, ?b) <=> not(eq(?a, ?b))` (`not` is `anthill.kernel.not`, negation as failure); the interpreter's `builtin_neq` is `!semantic_equal(a, b)` and the resolver's `SemNeq` is `sem_eq_core` negated, so `neq` finds `eq` from the value through the index at every call. A typed call gets no pin: at `T = Pt` the dispatch answers `PartialEq.neq` itself (a carrier may not supply one, `CarrierSuppliesNeq`), and the typer passes no dictionary to a host operation whose parameters are of the carrier's type (typing/apply.rs, `reads_the_instance`). MEASURED on e3f98bcd: `neq(pt(1, 2), pt(1, 9))` (`Pt.eq` compares `x`) answers false in an operation body and no solutions as a rule goal — right, by the value's constructor. A spec of the same shape, `operation differ(a: T, b: T) -> Bool = Bool.not(same(a, b))`, is classified with `Pt`'s dictionary and answers through `Pt.same` in both bodies (traced 2026-11-09). WANTED: `operation neq(a: T, b: T) -> Bool = Bool.not(eq(a, b))` in `PartialEq`, replacing the host declaration and the law; `SemNeq`, `builtin_neq` and the resolver's `neq` handler go; a rule-body `neq`/`!=` goal answers through the body at the pin; `CarrierSuppliesNeq` stays; `neq(nan, nan)` is true; the C++ generator keeps `!=`. A `neq` goal no type reaches keeps an answer until WI-20261105-CBRD2's row: read at the type its arguments carry, as SM910's untyped ordering goal. THE STACK CANARY MOVES: wi625's `eval_undecidable_instance_fact_eq_is_loud_not_false` reaches `BRIDGE_REENTRY_CAP` only through `neq`'s lookup from the value; with `neq` pinned it loops in one interpreter. It moves to a circle that crosses the bridge — one through an `eq` written as clauses, which at opt-level 0 needs (2, 3] MiB, more than the default 2 MiB thread, before the cap stops it (measured 2026-11-08) — and whether to lower the cap or keep the opt-level-0 budget documented (the user's choice of 2026-10-06) is decided with the user then. ACCEPTANCE: the `Pt` program answers false/true in both bodies and as a typed goal with no index read (traced or asserted), `neq` at each primitive, a generic caller under `requires PartialEq[T = A]`, the untyped goal, the moved canary; each part backed out alone failing the rows its header names; full workspace green via rustland/scripts/test.sh; families green on both carriers.

