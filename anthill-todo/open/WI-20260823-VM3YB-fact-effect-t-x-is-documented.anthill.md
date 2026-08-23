## Attributes

- id: WI-20260823-VM3YB-fact-effect-t-x-is-documented
- created: 2026-08-23T11:10:14Z

- status: Open
- status_agent: claude
- status_at: 2026-08-23T11:10:14Z

- acceptance: cargo-test

## Description

`fact Effect[T = X]` IS DOCUMENTED AS THE REGISTRATION AND CHECKED AT NO SITE. An effect
row may name any sort; nothing asks whether it was registered, so a MISSPELLED label is a
silent new effect rather than an error.

`stdlib/anthill/prelude/effects.anthill:21` states the rule — "Effect kinds are registered
via `fact Effect[T = Kind[?]]`" — and `sort Effect { sort T = ? }` exists for it.

MEASURED, twice, while delivering WI-20260823-39AD2:
  * Deleting `fact Effect[T = Res]` from `wi329_handler_discharge_test`'s DECLS leaves
    that file at 21/21. Its `Res` label is used in effect rows throughout.
  * Deleting `fact Effect[T = Reg]` from `wi698_row_param_refinement_test` leaves it at
    38/38.
And the sharper form, found by /code-review: a fact whose FUNCTOR does not resolve loads
SILENTLY — `fact NoSuchSortXyz[T = Reg]` reports no error, and the wi698 fixture shipped a
whole review cycle with `Effect` missing from its import list, registering nothing at all
while its comment claimed a registration. The suite was green throughout.

THE POPULATION IS SMALL AND LOPSIDED, which is why this is a census before it is a fix:
only SIX `fact Effect[…]` exist in the entire tree (`External`, `Modify[?]`, `Error[?]`,
`Suspension`, `Branch`, plus `Model` / `Filesystem` in the guardians vocabulary), while
effect ROWS across stdlib and examples name many more labels — `Clock`, `ConsoleOutput`,
`ConsoleError` among them — none of them registered. So switching the check on refuses
working programs until the registrations are written, and WHICH of the unregistered labels
are legitimate effects is the actual question.

TWO SEPARABLE DEFECTS, and the second is the wider one:
 1. An effect-row label that names no registered effect is admitted.
 2. A `fact` whose functor does not RESOLVE is admitted silently. That is not specific to
    `Effect` — it is a general loud-over-silent hole in fact loading, and it is what made
    (1) invisible in review. Measure whether it has its own owner before folding it in
    here; it may deserve its own ticket and be the more valuable half.

ACCEPTANCE: an effect row naming an unregistered sort is REFUSED, naming the label and
`fact Effect[…]`; every unregistered label currently in use across stdlib / examples /
`rustland/anthill-todo/anthill` is enumerated in the ticket and either registered or
reported as deliberately exempt; a control names which rows fall when the check is backed
out; the two "NOT load-bearing" notes WI-20260823-39AD2 left in `wi329_handler_
discharge_test` and `wi698_row_param_refinement_test` are removed once the fact is
load-bearing.

