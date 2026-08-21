## Attributes

- id: WI-20260821-D0EXD-the-ownership-decision-is
- created: 2026-08-21T13:25:38Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T13:25:38Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE OWNERSHIP DECISION IS BLIND TO WI-898's HEAD KIND, so a defining EQUATION and an
unrelated PREDICATE head of the same short name are merged, and the equation's operation
disappears.

MEASURED (rustland, WI-980's tree), two arms differing in one token:
  sort body identical in both:  sort Rec { entity r(n: Int64)   rule f() <=> 1 }
  caller in a third file:       operation g() -> Int64 = Rec.f()
  WITH a namespace-level `rule f(2)` beside the sort
    -> "3:28: type mismatch in Rec.f.apply: expected known operation or arrow-typed
        variable, got unknown functor" -- `qlib.Rec.f` is GONE.
  rename that head to `rule other(2)`
    -> `qlib.Rec.f` exists; the loader describes it as "defined by equations ... 1
       defining equation".
The diagnostic in the failing arm names only the CALLER, in a file that contains neither
definition, and mentions neither of the two that collided.

MECHANISM. `Ownership`'s `heads` map is keyed `(ScopeId, &str)` and stores
`(SourceId, denoted_before)` -- it never carries `RuleHeadSite::introduced_by`. The MINT
does read it (`scan_rule_goal` passes `site.introduced_by.symbol_kind()` to `define`, so a
predicate head earns `SymbolKind::Goal` and an equation's subject `EquationFunctor`,
WI-898). So the two shapes are distinguished when a symbol is created and indistinguishable
when the pass decides WHETHER to create one.

WHY THEY SHOULD NOT MERGE. WI-898's own reason: an equation's clauses are indexed under
the `eq`/`unify` CONNECTIVE, not under the subject, so an equation head and a predicate
head of one name are not two clauses of one predicate -- they are two different things
that happen to spell the same. Merging them makes the equation's subject resolve to a
`Goal` the equation never indexed, which is how the operation ceases to exist.

CAVEAT ON THE MEASUREMENT (carried from the review that found it): in the fixture the
`[simp]` tag did not take -- the control's own message reports the equation as untagged.
So the merge, the deletion and the kind-blindness are confirmed; any further claim about
what the operation's TYPE degrades to is not.

ACCEPTANCE: the two arms above must agree about `qlib.Rec.f` -- an unrelated
namespace-level predicate head of the same short name must not remove a sort's
equation-defined operation. Drive the caller and assert its value. Keep a control pinning
that two PREDICATE heads of one name in one scope are still two clauses of one predicate.
cargo-test green via rustland/scripts/test.sh.

