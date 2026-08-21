## Attributes

- id: WI-20260821-D0EXD-the-ownership-decision-is
- created: 2026-08-21T13:25:38Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T21:17:03Z

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

## Changes

### 2026-08-21T20:39:28Z — feedback — claude

DELIVERED, inline with WI-980's review-round rewrite rather than as a follow-up — the fix
is one key.

THE MECHANISM THIS TICKET NAMED WAS EXACTLY RIGHT. `Ownership` grouped head sites by name
alone, so an EQUATION's subject and a PREDICATE head of that name were one population and
the subject could yield to the predicate. WI-898's own reason is why they must not: an
equation's clauses index under the `eq`/`unify` CONNECTIVE, never under the subject, so a
subject that yields resolves to a `Goal` the equation never indexed.

THE FIX: `Ownership`'s `by_name` and `verdicts` are keyed by `(name, RuleIntroduction)`
rather than by name, so the two shapes are two populations, each deciding ownership among
its own. `RuleIntroduction` gains `Hash`. ~15 lines.

MEASURED, the ticket's own two arms differing in one token:
  BEFORE  clashing `rule f(2)`  -> "type mismatch in qlib.Rec.f.apply: … got unknown
                                    functor" -- `qlib.Rec.f` GONE
          renamed `rule other(2)` -> `qlib.Rec.f` present, "defined by equations"
  AFTER   both arms give the IDENTICAL message, "`qlib.Rec.f` is defined by equations".

PINNED at `wi980_rule_head_order_test::an_equation_subject_does_not_merge_with_a_predicate_head`.
The two arms are asserted EQUAL — the clashing one is the fixture, the renamed one the
control — and the control is additionally asserted to reach the equation, since two
identical FAILURES would satisfy an equality assert and measure nothing. BACK-OUT
MEASURED: dropping `RuleIntroduction` from the two keys fails exactly that one row.

THE CAVEAT THIS TICKET CARRIED IS UNTOUCHED AND STILL TRUE: in the fixture the `[simp]`
tag does not take, and the control's own message reports the equation as untagged. The
merge, the deletion and the kind-blindness were confirmed and are now fixed; nothing here
claims anything about `[simp]` firing.

Full workspace green via rustland/scripts/test.sh.

### 2026-08-21T21:17:02Z — feedback — claude

REOPENED. The obvious fix was tried under WI-980's review round, MEASURED, and is NOT
AVAILABLE — recording that is worth more than the attempt.

WHAT WAS TRIED: key `Ownership`'s populations by `(name, RuleIntroduction)` so an
EQUATION's subject and a PREDICATE head decide ownership among their own kind. It DOES
repair this ticket's fixture — both arms then report "`qlib.Rec.f` is defined by
equations", and the clashing predicate head no longer deletes the operation.

WHY IT IS WRONG, measured with a paired control one token apart:
  namespace qlib
    rule f(2)
    sort Rec { entity r(n: Int64)   rule f() <=> 1   rule f(3) }
  ARM      -> qlib.f = 1 clause, qlib.Rec.f = 1;  qlib.f(3) -> 0,  qlib.Rec.f(3) -> 1
  CONTROL (equation renamed `other`)
           -> qlib.f = 2 clauses, qlib.Rec.f absent; qlib.f(3) -> 1, qlib.Rec.f(3) -> 0
`rule f(3)` is DECIDED a clause of `qlib.f` and PLACED on `qlib.Rec.f`. Renaming an
UNRELATED head moves it. Both arms load clean.

THE ROOT IS NOT THE KEY. The decision became kind-aware; PLACEMENT did not, and placement
is ordinary name resolution, which maps one name to one symbol per scope. The equation
minted a local `f` at `Rec`, and that shadows whatever the decision concluded. Narrowing
the split to the equation side alone does not help: the capture is caused by the local
symbol existing, not by how the predicate's verdict was reached.

SO THIS TICKET SHARES A ROOT WITH WI-20260820-JR7BB — *the decision does not place the
clause* — and the two should be settled together. JR7BB records three options; the same
three apply here, and only two are coherent for this ticket:
 * CARRY THE VERDICT TO PLACEMENT. Exact, and it makes a rule's head and its body resolve
   one name two ways (JR7BB's recorded cost).
 * REFUSE THE COEXISTENCE. An equation subject and a predicate head of one name in scopes
   that can see each other are, by WI-898's own reasoning, two different things sharing a
   spelling. Refusing is loud and needs a corpus census plus a spec paragraph — neither
   done. LIKELY THE RIGHT ANSWER, and it is a design call rather than a repair.
 * ACCEPT AND DOCUMENT is NOT coherent here: the current behaviour deletes an operation.

WHAT REMAINS TRUE FROM THE ORIGINAL REPORT: `Ownership`'s populations are keyed by name
alone and never carry `RuleHeadSite::introduced_by`, while the MINT does read it
(`scan_rule_goal` passes `site.introduced_by.symbol_kind()` to `define`). The two shapes
are distinguished when a symbol is created and indistinguishable when the pass decides
whether to create one. The original fixture and its diagnostic are unchanged.

A NOTE FOR WHOEVER TAKES THIS: the reverted attempt is documented at `Ownership`'s
`verdicts` field in kb/load.rs, with the measurement, so the same fix is not re-derived.

The `[simp]` caveat carried by the original report still stands: in the fixture the tag
does not take, and nothing here claims anything about `[simp]` firing.

