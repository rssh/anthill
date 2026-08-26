## Attributes

- id: WI-20260825-CBRSW-implement-permission-x
- created: 2026-08-25T15:47:44Z

- status: Delivered
- status_agent: user
- status_at: 2026-08-26T12:05:31Z

- acceptance: cargo-test

- depends_on: WI-20260823-VM3YB-fact-effect-t-x-is-documented

## Description

IMPLEMENT `Permission[X]` — proposal 064. An effect denoting the runtime consultation of an ambient grant for capability `X`, written on the operation that MINTS a capability object and nowhere else; holding the object is the authority thereafter. Spec: docs/proposals/064-permission-effect.md. Design note (why the label was reached, and the alternatives): examples/guardians/docs/design/effects.md.

WHAT MAKES IT SMALL: `Permission[X]` is an ORDINARY ROW MEMBER. Subsumption is set inclusion (`{} <: {Permission[X]} <: {Permission[X], Permission[Y]}`), both legs of the existing not-widen check apply unchanged, and there is no family-indexed algebra — 064 drops families deliberately. The only genuinely new typer rule is CONTRAVARIANCE in the capability: `X <: Y => Permission[Y] <: Permission[X]`. Covariance is the wrong direction and admits privilege escalation (a spec granting `Permission[Fs]` would accept an implementation acquiring `Permission[AdminFs]`); contravariance also makes the negative form downward-closed for free, so `-Permission[Model]` cannot be evaded by declaring a sub-capability. Where no subtyping is declared among capabilities — the expected first case — the rule degenerates to name equality, so a first increment can ship with equality and add the order later without changing the rule.

FIRST CONSUMER, and it is the reason to build it: examples/guardians. `Checker.check` must provably not consult a model, which today holds ONLY because no `Oracle` is passed to it — a fact the signature does not state, so a reviewer must audit a parameter list on every regeneration. With this, `effects {External, Error, -Permission[Model]}` says it. And a generated `Triage` implementation cannot grant itself a permission the spec never gave: the spec's row bounds the provider's DECLARED row, and the declared row bounds the row INFERRED FROM ITS BODY — the same two legs `wide_row` ("effects must not widen") and `bad_checker` ("got undeclared effect: Model") already measure.

CONTAINMENT IS PART OF THE CHANGE, not a convention: a capability object's constructor must be `internal`, which kernel-language.md §8.6 makes the only hide gate — it hides from cross-scope resolution AND from field projection, with top-level code outside every declaring scope (WI-977). Without it a program writes `fs_root()` and skips the check, and the effect is advisory. No new mechanism; the increment must show the refusal.

NOT IN SCOPE (064 §Not in scope): release, revocation and lifetimes — a capability is minted and never given back, and no locking is implied; a general object-capability discipline; the `External[mode]` split, which is an unfiled idea in the design note and blocks nothing here.

ACCEPTANCE: `fact Effect[T = Permission[?]]` registers, and an operation declaring `effects {Permission[FileSystem]}` loads. A provider declaring a `Permission` its spec's row lacks is REFUSED, naming the label. A provider declaring the spec's row while its BODY calls a `Permission`-carrying operation is refused on the body leg. `-Permission[Model]` on an operation whose body mints a model capability is refused. Calling an `internal` capability constructor from outside its sort is refused. CONTROLS, and they must be stated at the site: an operation acquiring nothing loads where `{Permission[X]}` is declared (`{} <: {Permission[X]}`), and a provider acquiring only `Permission[X]` loads where the spec grants `{Permission[X], Permission[Y]}` — a suite of refusals alone is consistent with a checker that refuses everything. Contravariance needs its own both-directions pair: with `AdminFs <: Fs`, a spec granting `Permission[AdminFs]` ACCEPTS an implementation acquiring `Permission[Fs]`, and a spec granting `Permission[Fs]` REFUSES one acquiring `Permission[AdminFs]`; say which of these fails when the variance is flipped, since a name-equality implementation passes neither. Say at each site which tests fail when the change is backed out.

OPEN AT FILING (064 §Open questions), to be answered by the increment or reported: whether a lacks-constraint admits a VARIABLE argument — `-Permission[?]`, acquires no authority at all, which needs neither a capability order nor a root and is the general denial; whether handler discharge (045 §5.5) comes free per-label; whether the capability handle has identity, which decides whether the CALL is CSE-able as distinct from the CHECK being idempotent. Full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-08-26T12:05:18Z — feedback — user

DELIVERED. `Permission[X]` per proposal 064. Kind AND its variance in
`stdlib/anthill/prelude/permission.anthill`; rule in kernel-language.md §5.5; 22 rows in
`wi_cbrsw_permission_effect_test.rs` drive it, seven of them red across four separately
measured back-outs and the rest boundary rows that pass either way by design (stated at
the file head).

WHAT THE INCREMENT ACTUALLY COST, and it is the ticket's own "WHAT MAKES IT SMALL"
confirmed with ONE correction. The row half needed NOTHING: `Permission[X]` rides the
existing algebra, both not-widen legs judge it unchanged, and `internal` already contains
the constructor -- measured before writing any Rust, by loading the proposal's own
example. CONTRAVARIANCE needed no kernel code either: it is a DECLARED fact (proposal
035's `Contravariant`), which `check_binding_by_variance` already reads, so
`fact Contravariant(sort: Permission, param: T)` flips the override leg both directions.

THE ONE THING THAT WAS MISSING IS THE ONE THING 064 SAID WOULD BE FREE -- the NEGATIVE
form. Present-vs-absent was decided by label EQUALITY at every site, so a row carrying
`-Permission[Model]` while acquiring `Permission[GptModel]` LOADED CLEAN. That is the
privilege escalation the label exists to block. `typing::permission_entails` decides it
by comparing the capability ARGUMENTS.

AND THE FIRST CUT OF THAT RULE WAS GENERAL AND WRONG, found by /code-review (high) with
two measured programs. Asking `types_compatible(absent, present)` for EVERY label is
BACKWARDS outside this one: `-Color` beside a supplied `Red` (with `Red provides Color`)
STILL loaded clean under it, while `-Red` beside a supplied `Color` -- admissible, and
clean before -- was newly REFUSED. The reason is structural: ENTAILMENT runs COVARIANTLY
in the capability while SUBSUMPTION runs contravariantly, so for `Permission` the two are
opposite, and for an ordinary nominal label they coincide. No reading of the subsumption
order serves both. The verdict now runs only for `Permission`. What a lacks constraint
should mean for an ordinary label under subtyping is LEFT OPEN and recorded at the site:
it predates this ticket (that program loads clean before and after) and is about every
label rather than this one.

A SECOND HOLE FROM THE SAME REVIEW, and it was the cheapest possible evasion of a denial:
writing the label PRESENT beside its own denial (`{Permission[Model], -Permission[Model]}`)
silenced BOTH legs -- the body leg because the label IS declared, and WI-705 because it is
gated on an op type parameter being BOUND. WI-705's own comment names the missing site ("a
literal `{X, -X}` is a load-time concern, not this call-site one"); there was none.
`check_declared_row_contradiction` is it, sharing WI-705's verdict
(`uninhabitable_row_clash`, split out) so the guarded deferral stays one rule -- `{K :- g,
-K}` still defers to WI-067. Load-blocking, for every label; corpus clean.

DIAGNOSTIC. The body leg reported a DENIED effect as "undeclared", and printed the row in
internal syntax (`absent[label = K]`). The two failures have different repairs -- an
undeclared effect is fixed by adding the label, a denied one cannot be -- so it now says
which, and prints `-K` as written. `guardians_test`'s `bad_checker` needle moved with it
(`got undeclared effect: Model` -> `got denied effect: Model`); the refusal did not move,
and the new needle is one no other leg can produce.

THE 064 OPEN QUESTIONS, all four answered or routed:
 1. VARIABLE ARGUMENT IN A LACKS-CONSTRAINT -- the question had the wrong subject. The
    general denial needs no variable: a BARE `-Permission` subsumes every application and
    forbids every capability at once, assuming neither a capability order nor a root.
    `-Permission[?]` parses, loads, and constrains NOTHING; pinned as a trap with the
    working spelling named, since closing it means telling an anonymous wildcard apart
    from a rigid type parameter inside 045's row algebra -- every label's question, and no
    `.anthill` in the tree writes such an atom.
 2. HANDLER DISCHARGE -- FREE, as hoped. A grant is §5.5's ordinary handler shape with no
    kernel semantics: a body performing `{Permission[Model], Error}` under
    `with_model_grant[Rho]` has residual `{Error}`, and claiming to discharge the residual
    too is refused. Both halves driven; the second is what makes the first non-vacuous.
 3. HANDLE IDENTITY -- NO, and the CSE question is VACUOUS rather than affirmative for the
    shape 064's own example uses: a nullary `internal entity` is a constant of its sort,
    so two mints are the same value. Identity must go in a FIELD, and nothing here supplies
    freshness. Driven through the evaluator.
 4. A GRANTED OBJECT OUTLIVING ITS HANDLER -- untouched, still open, already listed under
    064 "Not in scope".

WHERE THE VARIANCE FACT LIVES, and it is not the conventional home. Beside the sort in
`permission.anthill`, not with the other `Covariant`/`Contravariant` facts, for two
reasons: it decides whether a permission budget can be ESCALATED, so the sort and its rule
must not be separable; and declaring it in `anthill.reflect.typing` means importing a
prelude sort into a file SCALAND loads, from a stdlib list (`EmbeddedStdlib.stdlibPaths`)
that does not carry `permission.anthill` -- which would have broken every scaland stdlib
test invisibly to this ticket's `cargo-test` acceptance. Found by review. Scaland is
untouched by this diff and simply has no `Permission`.

NOT TAKEN UP, and routed rather than dropped: examples/guardians still spells its model
effect on the USE (`Llm.complete` carries a bare `Model`, `Checker.check` denies it with
`-Model`) -- the pre-064 shape this proposal argues against. Migrating it means giving
`Llm` an `internal` constructor and a `Permission[Model]`-carrying mint, dropping `Model`
from five lib files' rows, reworking the `bad_checker` fixture (whose body-leg refusal IS
`complete`'s `Model`), and rewriting the design notes that argue the current shape. That
is a restructure of a running example's central safety argument, not an application of
this proposal. Recorded in 064 under "What was NOT taken up".

TESTS: full workspace via rustland/scripts/test.sh -- 36 binaries, 5765 passed, 0 failed.
`wi_tests` 3541/3541, `parse_tests` 452/452, `guardians_test` 17/17 (was 16+1 on the
needle), cli / cmd / cpp-gen / smt-gen / rust-gen / stl / doc-tests all 0 failed. Corpus
swept by hand under both new load checks: stdlib, guardians, github-todo, sql-store,
classic-mini (both), anthill-todo, anthill-stl, anthill-cpp-gen -- all clean.

