## Attributes

- id: WI-20260825-CBRSW-implement-permission-x
- created: 2026-08-25T15:47:44Z

- status: Open
- status_agent: user
- status_at: 2026-08-25T15:47:44Z

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

