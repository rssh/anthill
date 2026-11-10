## Attributes

- id: WI-20261109-JEE0E-proposal-051-phase-2-4-of-4
- created: 2026-11-09T14:15:50Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-10T14:42:38Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261109-5BP39-proposal-051-phase-2-2-of-4

- tags: proposal-051

## Description

PROPOSAL 051 PHASE 2 (4 of 4) — `neq` IS A BODY IN THE SPEC, `Bool.not(eq(a, b))` (decided with the user 2026-11-09; library/004 and 051 amended, the text agreed with the user first). TODAY `PartialEq.neq` is `@[host_implemented]` beside an inert law `rule neq(?a, ?b) <=> not(eq(?a, ?b))` (`not` is `anthill.kernel.not`, negation as failure); the interpreter's `builtin_neq` is `!semantic_equal(a, b)` and the resolver's `SemNeq` is `sem_eq_core` negated, so `neq` finds `eq` from the value through the index at every call. A typed call gets no pin: at `T = Pt` the dispatch answers `PartialEq.neq` itself (a carrier may not supply one, `CarrierSuppliesNeq`), and the typer passes no dictionary to a host operation whose parameters are of the carrier's type (typing/apply.rs, `reads_the_instance`). MEASURED on e3f98bcd: `neq(pt(1, 2), pt(1, 9))` (`Pt.eq` compares `x`) answers false in an operation body and no solutions as a rule goal — right, by the value's constructor. A spec of the same shape, `operation differ(a: T, b: T) -> Bool = Bool.not(same(a, b))`, is classified with `Pt`'s dictionary and answers through `Pt.same` in both bodies (traced 2026-11-09). WANTED: `operation neq(a: T, b: T) -> Bool = Bool.not(eq(a, b))` in `PartialEq`, replacing the host declaration and the law; `SemNeq`, `builtin_neq` and the resolver's `neq` handler go; a rule-body `neq`/`!=` goal answers through the body at the pin; `CarrierSuppliesNeq` stays; `neq(nan, nan)` is true; the C++ generator keeps `!=`. A `neq` goal no type reaches keeps an answer until WI-20261105-CBRD2's row: read at the type its arguments carry, as SM910's untyped ordering goal. THE STACK CANARY MOVES: wi625's `eval_undecidable_instance_fact_eq_is_loud_not_false` reaches `BRIDGE_REENTRY_CAP` only through `neq`'s lookup from the value; with `neq` pinned it loops in one interpreter. It moves to a circle that crosses the bridge — one through an `eq` written as clauses, which at opt-level 0 needs (2, 3] MiB, more than the default 2 MiB thread, before the cap stops it (measured 2026-11-08) — and whether to lower the cap or keep the opt-level-0 budget documented (the user's choice of 2026-10-06) is decided with the user then. ACCEPTANCE: the `Pt` program answers false/true in both bodies and as a typed goal with no index read (traced or asserted), `neq` at each primitive, a generic caller under `requires PartialEq[T = A]`, the untyped goal, the moved canary; each part backed out alone failing the rows its header names; full workspace green via rustland/scripts/test.sh; families green on both carriers.

## Changes

### 2026-11-10T14:35:43Z — feedback — claude

DECIDED WITH THE USER 2026-11-10, while delivering. (1) A neq goal no type reaches is read as not(eq(a, b)) in the resolver (route b), so it has eq's verdicts — the user: needed for neq(a, a) = false, which is Eq's. Route (a), the body at the carried type, left ensures neq(x, 1) DISCHARGED over a contract parameter (the body's eq compared the skolem by value). (2) Fixed inline (the user): a contract's skolem carries whether its parameter is equal to itself by Eq's law (its type provides Eq, or the operation or its sort requires Eq at it); at Float eq(x, x) and not(neq(x, x)) are undecided — eq(x, x) was discharged before this ticket. (3) The SMT prover reads neq as (not (eq …)); PartialEq has no law (S2, the user). (4) BRIDGE_REENTRY_CAP 16 -> 8 (the user); the wi625 canary moved to a circle through an eq written as clauses: (2.25, 2.5] MiB at opt-level 0 at 16, (1.25, 1.5] MiB at 8, (320, 384] KiB at opt-level 2. Found on the way: in a proof from Γ an eq test with an unbound left operand took every guarded = law as a premise (a hang once Map's law guards read neq as not(eq)); an equality builtin with a result column folded a value-dependent verdict into a forced one (eq(x, 1, false) discharged). Spec text agreed with the user.

