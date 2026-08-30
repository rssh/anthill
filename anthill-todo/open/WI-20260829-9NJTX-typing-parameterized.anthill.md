## Attributes

- id: WI-20260829-9NJTX-typing-parameterized
- created: 2026-08-29T23:57:56Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T23:57:56Z

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

