## Attributes

- id: WI-20260829-9NJTX-typing-parameterized
- created: 2026-08-29T23:57:56Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-30T03:54:25Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPING: `parameterized_compatible_view`'s provider instantiation loop binds into the CALLER's substitution and does not roll back when the comparison then fails.

FILED FROM /code-review ON WI-20260829-GNPG7, which WIDENED the population reaching it and declined to repair it in the same commit -- the reviewer's point being that "declined as un-drivable" belongs in a queue, not only in a code comment.

THE SHAPE. `parameterized_compatible_view` (typing.rs) resolves the actual's cross-sort
provider view and then, under `if cross_sort_provider.is_some()`, walks the actual's own
bindings calling `subst.bind_value(...)` on the CALLER's substitution -- so the per-param
comparisons below see the instance's values rather than the provision's canon vars. The
per-param loop can then `return false`, and nothing restores the substitution. A failed
comparison therefore leaves the actual base's canonical param vars bound in a subst the
caller goes on using.

THE NEIGHBOURING ARM ALREADY KNOWS BETTER: the `Some(pv)` branch a few lines down clones
into a `probe` and commits only on success, for exactly this reason, and
`check_binding_by_variance`'s Invariant/Bivariant arms do the same.

WHY GNPG7 DID NOT FIX IT. It could not be DRIVEN. The arms most likely to run a comparison
EXPECTING it to fail -- `Variance::Invariant`'s two directions, `Bivariant`'s `||`,
`join_types`' per-direction hygiene -- already clone, so no fixture was found in which the
residue changes a later verdict. Repairing a hot type relation on the strength of nothing
that fails without it is the thing the repo's principles refuse. But the argument is an
ENUMERATION OF TODAY'S CALLERS, not an invariant: a new caller that probes on the shared
subst inherits the bug silently.

WHAT GNPG7 CHANGED: the loop used to run only for a DIRECTLY-providing actual and now runs
for any TRANSITIVELY-providing one, so more failing comparisons reach it. That is a
population change, not a new defect.

ACCEPTANCE: either a fixture that DRIVES the residue into a wrong verdict (then repair, and
the fixture is the control), or -- if it stays undrivable -- the probe-and-commit applied
anyway with the full suite as the only evidence, and this ticket says plainly that no test
fails without it, in the shape `wi756-an-effect-redundant-by-construction` uses. Do not
credit a neighbouring guard for covering it.

## Changes

DRIVEN, so the repair is the fixture's, not the suite's -- and the DRIVING SHOWED THE
TICKET'S REPAIR IS THE WRONG ONE. Rollback-on-failure fixes half the defect.

THE CALLER THAT MAKES IT VISIBLE was ordinary and always there: `check_call`'s positional
argument loop pushes a `TypeError` and CONTINUES on the same `subst`, so argument 2 is
checked in the substitution argument 1 left behind. Three rows, `List` at an `Iterable`
spec view, `takes(a: ..., b: ...)`:

  | argument types                       | before | after |
  |--------------------------------------|--------|-------|
  | `List[T = Int64]` alone at `Element = Int64` | 0 | 0 | CONTROL: it conforms
  | `(List[T = Row], List[T = Int64])`, arg 1 FAILS   | **2** | **1** | spurious 2nd error
  | `(List[T = Row], List[T = Int64])`, arg 1 SUCCEEDS | **1** | **0** | correct program REFUSED

THE THIRD ROW IS WHY THE TICKET'S REPAIR IS NOT THE REPAIR. Probe-and-commit was written and
MEASURED on these same programs: row 2 went 2 -> 1, row 3 stayed at 1. Rollback on failure
cannot help a comparison that SUCCEEDS, and the succeeding one is where a well-typed program
is rejected.

CAUSE, one level deeper than the ticket read it: the loop binds the ACTUAL BASE's canonical
param var -- one `List.T`, the sort's own `Var::Global` behind its `SortAlias`, shared by
every `List` type and every comparison in that substitution. Its `if
subst.resolve_as_value(vid).is_none()` guard then made the FIRST instance compared decide
what `List.T` meant for all the rest. The binding is not a fact about the caller's world at
all; it is a REWRITE of the provider view.

FIX: the instantiation happens in a scratch `Substitution::with_parent(subst.clone())` --
the idiom `resolve.rs` already uses at two sites -- and the view's values are walked through
it once, up front. The caller's `subst` is never written by it. `with_parent` is what makes
it a rewrite rather than a bind: `bind_value` consults only the child's own map, so this
instance's value SHADOWS whatever the parent chain says, where the old `is_none()` guard
deferred to it.

THE DEFECT IS OLDER THAN GNPG7, which only widened its population (direct -> transitive
providers). `a_direct_one_hop_provider_is_captured_too` uses `List provides
FiniteCollection[C = List[T], Element = T, E = {}]` -- a DIRECT fact, served by
`provider_spec_view_bindings`, reaching none of GNPG7's composition -- and is red on the
backed-out tree.

THE FIRST CUT OF THAT ROW WROTE IT AS `Stream[T = Row, E = {}]`, also one hop, and it was
GREEN BOTH WAYS. `Stream` names its element `T` just as `List` does, so the expected `T`
finds the actual's own by key identity and the provider arm -- the ONLY reader of the
instantiated values -- never runs for it; only `E` reaches that arm, bound to a literal `{}`
that mentions no canonical var. The row has to be a provision that RENAMES the param.

BACK-OUT CONTROL: 3 of the 6 tests red, 3 green by design (measured, not asserted). The
three green ones are the row that conforms alone, the row whose genuine mismatch must still
refuse, and the DEGENERATE row where both arguments share one element type -- the captured
value is then the correct one and the defect is invisible, which is why the fixture varies
the ARGUMENT's element type rather than only the parameter's.

WHAT THE REPAIR ABSORBED. `pv` now arrives instantiated, so the provider arm's second leg
(re-walk through `subst`, gated `pvr != pv`) has nothing left to resolve. Instrumented on
both trees over `wi_tests`: BEFORE 10,313 reaches / 59 resolved further / 39 of those
ACCEPTED a binding the first leg had rejected; AFTER 13,149 reaches / ZERO resolve further.
Those 39 are decided by the first leg now. The leg is kept -- the case it covers (bindings
`subst` gains DURING the loop, after the snapshot the view was walked against) is unreached,
not empty -- and the site carries the numbers so the next reader need not re-derive them.

PERF, because this relation is hot and GNPG7 documented a 1.78x regression on it. Paired,
interleaved, min-of-12 in-process stdlib loads, 4 rounds alternating the two binaries. Once
the machine settles: BASE 555.7 / 550.6 ms, FIX 553.5 / 549.1 ms. No difference. (Rounds 1-2
spread 2x under residual contention and are reported only to say they are unusable, per this
project's own measurement note.)

THE SHADOWING IS NOT A CORNER CASE, and this is the number the ticket did not ask for and
should carry anyway. `with_parent` shadows where the old `is_none()` guard DEFERRED, so it
changes what is compared wherever a canon var is already bound in the caller's chain. Over
`wi_tests` that is 46,107 iterations, and on 40,984 of them the inherited value DIFFERS from
this instance's -- chiefly `MappedStream` / `FilteredStream`, whose params other typer paths
ground. Every one used to be decided against a foreign instance's value. The corpus is green
either way, so the suite is NOT what justifies the direction; the instance being compared
owning the meaning of its own parameter is.

/code-review (high), TWO FINDINGS, both applied, both LATENT and said to be:

  * THE SECOND LEG OF THE PROVIDER ARM was the one remaining write on this arm that could
    bind and then fail -- `check_binding_by_variance`'s Covariant/Contravariant arms hand
    `subst` straight to `types_compatible`, and the leg passed `subst`, not a probe. That is
    the exact residue this ticket is about, in the function whose contract is now that a
    failed comparison leaves nothing. Now probe-and-commit like the leg above it. It fires
    ZERO times (measured), so no test moves either way, and the site says so rather than
    claiming a repair.
  * THREE SILENT `continue`s in the instantiation loop (name unresolvable / not a
    `SortAlias` / alias target not a `Var::Global`) were inert while the loop only wrote
    into `subst` and are load-bearing for the shadowing invariant now: a param reaching one
    still resolves through the parent chain. MEASURED across the whole workspace: ZERO
    firings. Written down at the site rather than turned into a `debug_assert` -- an
    assertion nothing can drive is not a guard.

TESTS: rustland 35 binaries / 5881 passed / 0 failed (baseline 5875 + the 6 new); scaland
524 / 0 -- nothing to port, the Scala side has no typer.
