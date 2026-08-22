## Attributes

- id: WI-20260821-E85J5-in-a-mutual-import-cycle-each
- created: 2026-08-21T21:19:16Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-22T11:20:14Z

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

### 2026-08-22T11:20:08Z — feedback — claude

DELIVERED AS **REFUSE**, and 061 is what made the option choosable rather than the
narrowest of three.

WHY NOT ACCEPT. The ticket's ACCEPT case was "it is consistent with the rest of the
language — a local beats an import everywhere". That is true and is KEPT: the shadow
itself is not refused, and the `declare in EACH scope` arm reproduces it exactly, driven.
What is refused is INVENTING it. 061 already says a predicate assembled from more than
one file must be declared; the file check is keyed on the PREDICATE, and WI-980's
tie-break splits a cycle into two SINGLE-FILE predicates *before* that check counts
files. So the one assembly 061 exists to refuse was the one shape it could not see. This
is not a new rule — it is 061's rule reaching the shape its own mechanism hid.

WHY NOT WARN. WI-961: load warnings are invisible to tests, so the ticket's own bar
("a warning needs a channel a test can read") is unmet.

THE NARROWNESS THE TICKET ASKED FOR IS BY CONSTRUCTION, not by a census exclusion. The
99-stdlib-errors measurement was of rule-head/import coexistence GENERALLY — a head whose
name RESOLVES through an import is a clause of it (`denotes`, the law layer), and never
reaches the decision. The tie-break is the only place in the loader where a head
introduces a name its scope can already see. Corpus + fixtures: the refusal fires on
exactly 2 pre-existing test rows and nothing else.

MEASURED (post-061 tree, bodied clauses; the filed body-less table is dead because 061
reads those heads as declarations):

    mA{import mB.*; rule p(1):-true; rule usesp(?x):-p(?x)} | mB{import mA.*; rule p(2):-true}
      before:  loads clean   usesp(1)=1  usesp(2)=0
      CONTROL, mA with no own p:      usesp(1)=0  usesp(2)=1     <- the import DOES work
      after:   REFUSED, naming mA, mB and both files

    REMEDY 1, declare once in mA:  mA.p = 2 clauses, mB.p absent, usesp(1)=1 usesp(2)=1
    REMEDY 2, declare in each:     mA.p = 1, mB.p = 1, usesp(1)=1 usesp(2)=0  (shadow, as written)

TWO NON-CASES BOUND IT, each a pinned row:
 * a NESTED two-file cycle (a facade importing its own submodule) is the ordinary
   `heads in 2 files` error — the enclosing member owns, the heads become one predicate.
   Same two files, same two heads, same name; only the nesting differs and it decides
   WHICH message the author gets. Neither shape is silent afterwards.
 * a cycle inside ONE file keeps auto-declaring, shadow and all — 061's file unit and its
   open question 3, unchanged: both scopes are in front of the one author who wrote them.

THE TICKET'S OWN FEEDBACK CARRIED TWO CLAIMS THAT DO NOT SURVIVE MEASUREMENT.
 * "under 061 a body-less rule head IS a declaration, so for that spelling [059 R4
   clause 3] now covers it directly". It does not. Measured: two body-less `rule p(…)`
   heads in a mutual cycle LOAD CLEAN as two declarations. R4 clause 3 is asked only of
   declarations whose scope owner is a SORT, so a namespace-level declaration never
   reaches it. That spelling is the `declare in EACH scope` remedy, and admitting it is
   correct.
 * the `fact p(1)` vs `rule q(2) :- true` witness measures a DIFFERENT defect. Driven,
   `mA6.p`, `mB6.p` and `p` all resolve to NOTHING while `mA6.q`/`mB6.q` each hold a
   clause: the fact heads are not "leaving the import live", they are UNSCOPED — they
   fall to the WI-476 bare intern and collapse two scopes onto one name. That is
   WI-20260821-RDGQC / P85Z7's enumeration, already filed, not this ticket's shadow.
   The divergence from `rule H :- true` is real and worth keeping; its root is not.

WHERE IT IS RECORDED: `docs/kernel-language.md` §"A rule head functor is resolved, not
declared" (a new paragraph after WI-980's cycle rule) and proposal 061 open question 3.
Pinned by `wi980_rule_head_order_test::{a_multi_file_cycle_is_refused_and_both_-
declarations_repair_it, a_single_file_cycle_still_introduces_separately_in_either_order,
a_nested_cycle_across_two_files_is_the_ordinary_file_error}`, with the back-out named at
the site (drop `splits.push(split)` in `Ownership::owners_for` ⇒ the load succeeds and
the first two assertions fail; the two DECLARED arms pass either way, by design).

