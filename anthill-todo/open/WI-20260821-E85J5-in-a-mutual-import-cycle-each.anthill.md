## Attributes

- id: WI-20260821-E85J5-in-a-mutual-import-cycle-each
- created: 2026-08-21T21:19:16Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T21:19:16Z

- acceptance: cargo-test, scaland-sbt-test

## Description

IN A MUTUAL-IMPORT CYCLE, EACH SCOPE'S OWN RULE HEAD SILENTLY KILLS THE IMPORT THAT MADE
THE CYCLE. WI-980 decided that two scopes which can each SEE the other, sharing one head
name, each INTRODUCE their own — the only answer that does not depend on file order. What
that decision does to a USE was never measured, and it is this.

MEASURED (rustland, WI-980's tree), with a paired control:
  file A  namespace mA { import mB.*  rule p(1)  rule usesp(?x) :- p(?x) }
  file B  namespace mB { import mA.*  rule p(2) }
  -> LOADS CLEAN.  mA.usesp(1) -> 1,  mA.usesp(2) -> 0.
  CONTROL, mA with the SAME import but no `p` of its own:
  file A' namespace mA { import mB.*  rule usesp(?x) :- p(?x) }
  -> mA.usesp(2) -> 1, mA.usesp(1) -> 0.
So `mA`'s `import mB.*` is DEAD for `p`, and nothing says so. The control is what shows
this is the shadow rather than a broken import.

MECHANISM, and it is not a bug in WI-980's decision: `resolve_in_scope` reads a scope's
own `locals` and RETURNS before it consults any import or parent (intern.rs step 1). The
symbol WI-980 mints at `mA` is a local, so it short-circuits. No ambiguity is raised and
none can be.

WHY IT IS A QUESTION RATHER THAN A DEFECT. It is CONSISTENT with the rest of the
language — a local beats an import everywhere, and an operation declared locally shadows
an imported one of the same name just as silently. Two things pull the other way:
 * 059 R4 clause 3 REFUSES EXACTLY THIS CAPTURE for declarations ("a declaration may not
   capture a name it does not override"), settling WI-939 as its option (c). A rule head
   introducing `p` where `import mB.*` already supplies `p` is that capture, reached by a
   construct the clause does not cover.
 * IT IS A SILENT BEHAVIOUR CHANGE. Before WI-980 the cycle collapsed to ONE predicate
   (by file order — which is the defect WI-980 fixed), so `p(2)` WAS reachable from `mA`.
   The new rule is order-free and reaches less.

OPTIONS:
 * ACCEPT AND DOCUMENT — say in §"A rule head functor is resolved, not declared" that a
   scope's own head shadows an import of that name, as every other local does. Cheapest,
   and it makes the language uniform. Costs: the author of `import mB.*` gets nothing and
   is not told.
 * WARN — a load warning at the head: "this head introduces `p`, shadowing the `p` that
   `import mB.*` supplies". Note WI-961: load warnings are invisible to tests, so a
   warning needs a channel a test can read before it is worth adding.
 * REFUSE, extending 059 R4 clause 3 to rule heads for the CYCLE case only. Loud. Needs a
   corpus census first; note that refusing rule-head/import coexistence GENERALLY was
   measured at 99 stdlib errors across 43 names under WI-980, so any refusal here must be
   narrow enough to miss the stdlib's law layer.

NOT A SEPARATE QUESTION FROM WI-20260820-JR7BB AND WI-20260821-D0EXD, though it is not the
same one either: all three are the loader's DECISION and ordinary name RESOLUTION giving
different answers about one name. Here the decision is right and resolution is merely
narrower than the author expects; in the other two the decision is right and resolution
CONTRADICTS it. Whoever settles the placement question should read all three.

WHERE IT IS PINNED: `wi980_rule_head_order_test::mutual_visibility_introduces_separately_in_either_order`
now DRIVES both the shadow and the control, so a change to this behaviour is visible. It
pins the behaviour; it does not argue it is correct, and it names this ticket at the site.

ACCEPTANCE: a decision recorded in docs/kernel-language.md §"A rule head functor is
resolved, not declared", and whichever of the three options is taken implemented with its
control. If ACCEPT is chosen, this ticket closes by writing the sentence — the test row
already exists.

