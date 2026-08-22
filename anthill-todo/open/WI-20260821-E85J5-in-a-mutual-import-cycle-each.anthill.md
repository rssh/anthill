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

## Changes

### 2026-08-22T10:01:39Z — feedback — claude

NOT OBSOLETE AFTER 061 — BUT THE FILED MEASUREMENT IS, AND THE TICKET NEEDS RE-BASING.
Re-measured on the post-061 tree (2026-08-22), definite answers only.

THE FIXTURE AS FILED NOW MEASURES NOTHING. It spells both heads body-less
(`rule p(1)` / `rule p(2)`), and 061 reads a body-less rule as a DECLARATION that
asserts nothing. So:
    as filed:                mA.usesp(1)=0  mA.usesp(2)=0
    its CONTROL (no own p):  mA.usesp(1)=0  mA.usesp(2)=0
Both rows are 0 and the control no longer discriminates — the table in the description
(`usesp(1) -> 1`, control `usesp(2) -> 1`) is stale, and a reader who re-ran it today
would conclude the defect was gone. It is not.

THE DEFECT REPRODUCES VERBATIM WITH BODIED CLAUSES, which 061 does not touch:
    rule p(1) :- true  in mA, rule p(2) :- true in mB   ->  usesp(1)=1  usesp(2)=0
    CONTROL, mA with the same import and no own p       ->  usesp(1)=0  usesp(2)=1
Same shadow, same silence. So the ticket survives 061 with its fixture rewritten to the
bodied spelling.

A SHARPER WITNESS THAN THE ONE ON FILE — one file, one cycle, the two spellings side by
side and DISAGREEING:
  namespace mA6 { import mB6.*  fact p(1)  rule q(2) :- true
                  rule usesp(?x) :- p(?x)  rule usesq(?x) :- q(?x) }
  namespace mB6 { import mA6.*  fact p(9)  rule q(9) :- true }
    usesp(1)=1  usesp(9)=1     <- the FACT head leaves the import LIVE
    usesq(2)=1  usesq(9)=0     <- the RULE head kills it
A rule head INTRODUCES a scope-local predicate and shadows the import; a fact head does
not. That is worth carrying into this ticket because it is the same defect stated without
any appeal to file order or to a control — and because `fact H` and `rule H :- true` are
supposed to be ONE CLAUSE (§6.1, WI-20260821-FQC85, re-affirmed by WI-20260822-J38JE
item 5, which is why the loader's `:- true` strip stays). Here they are not
interchangeable, and the divergence is in WHICH PREDICATE each touches.

061 ALSO STRENGTHENS THE TICKET'S OWN ARGUMENT rather than retiring it. The description
says the capture is "reached by a construct [059 R4 clause 3] does not cover" — clause 3
refuses a DECLARATION capturing a name it does not override. Under 061 a body-less rule
head IS a declaration, so for that spelling the clause now covers it directly, and the
open question narrows to: does the same refusal extend to a BODIED head, which introduces
the same name by the same mechanism?

WHAT TO CHANGE HERE: re-spell the measured table with bodied clauses, add the one-file
fact-vs-rule witness above, and add the 059-R4-now-covers-the-body-less-case observation
to the two bullets under WHY IT IS A QUESTION RATHER THAN A DEFECT.

