## Attributes

- id: WI-20260821-D0EXD-the-ownership-decision-is
- created: 2026-08-21T13:25:38Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-23T23:56:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A PREDICATE DECLARATION SILENTLY ABSORBS AN INNER SCOPE'S EQUATION SUBJECT, so a sort's
equation-defined operation MOVES to the enclosing scope and ceases to exist at the sort.

REWRITTEN 2026-08-23 against the current tree. THE SLUG AND THE TWO FEEDBACK ENTRIES BELOW
ARE STALE and are kept only as history: `Ownership`, `Owned` and `Reach` were deleted by
WI-20260822-845G7, so this is no longer "the ownership decision", there is no decision /
placement split, and the shared root with WI-20260820-JR7BB is GONE. Read this section,
not them.

MEASURED (driven, current tree), two arms differing in one token in a line that is not
about the sort at all. The equation is written `[simp]` so it actually fires — the
ORIGINAL report's caveat that the tag "did not take" was the fixture omitting it, and is
hereby LIFTED:

  sort body identical in both:
    namespace qlib
      <HEAD>
      sort Rec
        entity r(n: Int64)
        rule f() <=> 1 [simp]
      end
    end

  HEAD = `rule f(2)`      -> qlib.Rec.f ABSENT, qlib.f present.
                             `operation h() -> Int64 = f()` under `import qlib.*`
                                 -> Int(1)
                             `operation g() -> Int64 = Rec.f()`
                                 -> REFUSED "3:28: type mismatch in Rec.f.apply: expected
                                    known operation or arrow-typed variable, got unknown
                                    functor"
  HEAD = `rule other(2)`  -> the exact mirror: qlib.Rec.f present, qlib.f ABSENT.
                             `Rec.f()` -> Int(1); bare `f()` -> REFUSED "`f` is a member
                             of sort Rec, not in scope as a bare name here".

Both arms LOAD. Nothing is reported. The effect is RELOCATION, not deletion — a refinement
of the original report, which said the operation "disappears": it disappears from the sort
and reappears at the namespace, so a caller written against either name is right in exactly
one of two programs that differ by a rename elsewhere.

MECHANISM, at its live site. Under 061 a body-less `rule f(2)` is a DECLARATION, minted in
pass 1. `Rec`'s equation head then RESOLVES `f` through its enclosing scope, and
`name_denotes_for_rule_head` (rustland/anthill-core/src/kb/load.rs:15020) is
`resolve_name_in_kb(..).denotes()` — it asks ONLY whether the name resolves and never reads
`RuleHeadSite::introduced_by`. The MINT still does (`scan_rule_goal` passes
`site.introduced_by.symbol_kind()` to `define`, so a predicate head earns `SymbolKind::Goal`
and an equation's subject `EquationFunctor`, WI-898). So the two shapes are still
distinguished when a symbol is CREATED and indistinguishable when the ladder decides whether
to create one — the original report's sentence, now true of a different function.

TWO WRITTEN RULES DISAGREE, and that is the decision this ticket needs.
 * docs/kernel-language.md:1750 — "This reaches EVERY head shape, an equation's subject
   included." That sentence was written for 845G7's VISIBILITY REFUSAL (its /code-review
   found that exempting equations silently split `zeq.f` / `zeq.Rec.f`), not for
   absorption-by-declaration.
 * 061 §"Equational rules are NOT this construct" — "An equational head neither needs a
   declaration nor is AUTO-DECLARED BY ONE", on WI-898's reason: an equation's clauses index
   under the `eq`/`unify` CONNECTIVE, never under the subject, so an equation head and a
   predicate head of one name are not two clauses of one predicate. Absorbing the subject
   into a declared `Goal` is exactly the merge that reason forbids.

ALREADY SETTLED — do not re-derive:
 * The BODIED spelling is REFUSED. `rule f(2) :- true` at `qlib` beside the equation at
   `qlib.Rec` gives 845G7's visibility error naming both scopes and both repairs. The
   REOPEN's "REFUSE THE COEXISTENCE, LIKELY THE RIGHT ANSWER" is shipped for every spelling
   EXCEPT the body-less one above.
 * The REOPEN's second fixture no longer reproduces. `rule f(2)` / equation / `rule f(3)`
   now LOADS CLEAN with `qlib.f` AND `qlib.Rec.f` both present — under 061 both body-less
   heads are declarations, which is 061's own "one in EACH scope says they are separate
   predicates". The "`rule f(3)` is DECIDED a clause of qlib.f and PLACED on qlib.Rec.f"
   reading died with the fixpoint.
 * The `(name, RuleIntroduction)` key recorded at `Ownership`'s `verdicts` field is moot —
   the field is gone with the struct.

A TRAP FOR WHOEVER TAKES IT, measured. The obvious repair — stop an equation subject from
denoting a `Goal`, so it introduces at `Rec` — does NOT reach the visibility refusal and so
does NOT produce a loud error. `head_name_collisions` skips any head that already denotes
(`if denoted || head.scope == global { continue }`, load.rs:8136), and a DECLARATION's own
head denotes, so it is never a candidate: the equation subject would be the only candidate
at one scope, and the outcome is a SILENT SPLIT — which is the control arm's program, and
arguably the right one, but it is a design call and must be argued rather than fallen into.

ACCEPTANCE: the two arms above must AGREE about `qlib.Rec.f` — an unrelated body-less head
of the same short name at the enclosing scope must not move a sort's equation-defined
operation, or must be REFUSED naming both sites. Drive it: call the operation and assert
`Int(1)` at whichever name the chosen reading keeps, and assert the OTHER name absent, in
BOTH arms. Two identical failures satisfy an equality assert and measure nothing, so the
control arm must be asserted to REACH the equation, not merely to match. Keep a control
pinning that a declaration `rule p(?x)` at `qlib` still collects a PREDICATE head written in
`Rec` (spec §"A declaration is what joins scopes, and that is the point of it") — the split
must be by HEAD KIND, not a retreat from joining. State the back-out and which rows it
fails. cargo-test green via rustland/scripts/test.sh.

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

### 2026-08-23T20:32:02Z — feedback — claude

DESCRIPTION REWRITTEN against the current tree — the two feedback entries ABOVE this one are
now history, and reading the changes tail-first gives the wrong story.

WHY: WI-20260822-845G7 deleted `Ownership`, `Owned` and `Reach`, so this ticket's named
mechanism, its decision/placement split and its shared root with WI-20260820-JR7BB no longer
exist. Re-measured, driven, all three arms:
 * the HEADLINE defect SURVIVES, narrowed to ONE shape — a BODY-LESS enclosing head, which
   under 061 is a DECLARATION, absorbs the inner EQUATION subject through the `denotes`
   ladder. The effect is RELOCATION, not deletion: `f()` at the namespace answers Int(1) and
   `Rec.f()` is "unknown functor"; rename the enclosing head and it is the exact mirror.
 * the BODIED spelling is now REFUSED by 845G7's visibility rule, so the REOPEN's preferred
   option is shipped everywhere except the body-less case.
 * the REOPEN's `rule f(3)` capture NO LONGER REPRODUCES — both heads are declarations now
   and the program loads with both symbols present.
 * the `[simp]` CAVEAT IS LIFTED: the tag "did not take" because the fixture omitted it.
   Written `rule f() <=> 1 [simp]`, the control arm returns Int(1).
The ticket id and slug are kept — they are the handle other notes cite — and the slug's
"the ownership decision" is stale by exactly that deletion.

### 2026-08-23T23:56:03Z — feedback — claude

DELIVERED. An equation's subject may not resolve to another scope's RELATION.

THE RULE. "A clause of what it resolves to" (§"A rule head functor is resolved, not
declared") is coherent for an equation only where what it lands on is a thing equations
DEFINE — an `operation`, or another equation's subject. A rule-introduced RELATION is
neither: an equation's clauses index under the `<=>` connective and never under its
subject (WI-898), so the subject merely points at it and the equation-defined operation the
writing scope meant to name ceases to exist there. Such a subject is now a load error
naming the scope losing the operation and the scope declaring the relation.

REFUSED RATHER THAN SPLIT, and the language's own answer for the same pair is the argument:
where neither side is minted before phase 2, `zi { rule f(true) <=> 7 [simp] }` beside
`zj { import zi.*  rule f(1) :- true }` is ALREADY the visibility refusal, because both
heads introduce and phase 2 reads a pre-mint table. A 061 DECLARATION is minted in pass 1,
so it was the one shape arriving already denoting — a hole in that refusal, not a second
question. Pinned as a control that passes with the whole change backed out.

SCOPED TO ANOTHER SCOPE'S RELATION, on 845G7's own principle — the shadow is not the
defect, INVENTING it is. `sort Rec { rule f(?y)  rule f() <=> 1 [simp] }` is one author
writing both in one place; it works, driven to Int(2), and is not refused.

BOTH PRESCRIBED REPAIRS ARE DRIVEN, not merely loaded: an `operation` in the relation's
scope (replacing the declaration — one name cannot be both), or a body-less `rule` in the
equation's own scope. Each answers Int(1) through the sort's own citation.

WHAT THE WORK TURNED UP THAT THE TICKET DID NOT NAME:
 * 845G7's COLLISION MESSAGE PRESCRIBED AN OWNER THAT PRODUCED THIS DEFECT. Its advice —
   "a body-less `rule f(…)` in 'zeq' makes every one of those heads a clause of it" —
   was TAKEN and measured: `zeq2.Rec.f` absent, the citation "unknown functor". Where a
   colliding head is a subject written outside the named owner, that message now
   prescribes an `operation`.
 * THE 845G7 TEST ASSERTED ONLY THAT ITS REMEDY ARMS LOAD. Both now drive to Int(2), and
   the arm that no longer loads is asserted as the refusal.

WHAT `/code-review` FOUND, over three rounds — eleven findings, no functional defect in
round three, and three of the eleven were mine misreading my own measurements:
 * A RULE LABEL IS A FOURTH LANDING KIND. `DECLARABLE_BY_A_RULE` lists `Goal`,
   `EquationFunctor` and `Rule`. Driven: `lc1 { rule f: p(?x) :- q(?x) … }` beside
   `lc2 { import lc1.*  rule f(true) <=> 7 [simp] }` loaded clean, `lc2.f` ABSENT,
   `lc2.g()` = Int(7) out of `lc1`'s LABEL. My kind census separated cleanly and was still
   the wrong list — no corpus fixture writes a label another scope's equation can reach.
   THE CENSUS MEASURED THE FIXTURES, NOT THE POPULATION. The guard now asks that constant.
 * THE `<global>` ARGUMENT IS DIRECTIONAL AND I TOOK IT BOTH WAYS. It rests on nobody
   OPTING INTO `<global>` — true when a namespace's head is asked to answer for a
   namespace-less file, false in reverse, since a `<global>` head reaches a namespace only
   through an import it wrote. The both-ways cut left the defect live in that half: a
   namespace-less file writing `import pgz.*` defined `pgz`'s predicate, Int(7) visible to
   a third namespace that never saw the file. Excluded as a TARGET only.
 * A ZERO-ROW BACK-OUT IS NOT A DEAD GUARD. I deleted the `Operation` exemption because
   backing it out failed zero rows across 5639 tests, reasoning the combination is
   unreachable in a program that LOADS. Both halves true, conclusion wrong: this pass runs
   on programs that do not load, and `rule f(2)` beside `operation f() -> Int64` is one —
   the refusal then told the author to declare the operation on the preceding line.
 * A PROXY IS NOT THE QUESTION. The message branched on `predicate_scopes.len() > 1` as a
   stand-in for `Ambiguous`; a namespace reopened in two files with different imports
   gives two UNAMBIGUOUS answers naming two scopes, and the text sent the author to settle
   an ambiguity no error reported. The ladder's own answer is carried now.
 * Also: the message prescribed ADDING an operation where it must REPLACE the declaration
   (061 refuses two declarations of one name); the `Ambiguous` branch prescribed a repair
   that leaves the ambiguity standing; one message per CLAUSE instead of per subject; the
   `<global>` row asserted only "it loaded"; my doc block swallowed 845G7's ~40-line
   rationale and left its variant undocumented; a redundant `EquationFunctor` filter split
   one rule across two sites; the census figures did not sum (57 unnamed, of which 16 are
   an equation subject on an ENTITY — a class this rule admits in silence, now stated);
   three stale references to the renamed ladder function; and a backwards rename note.

NINE BACK-OUTS, EACH RUN AND EACH NAMING ITS ROWS: the refusal 7, the scope guard 4, and 1
each for the operation exemption, the label kind, the `<global>` target exclusion, the
`<global>` direction, the grouping, the ambiguous reading, the ambiguity question and the
`equation_elsewhere` prescription. One of them, backed out at the per-head site instead of
the reporting site, fells NOTHING — recorded, because the two sites measure different
things.

MEASURED SIDE-EFFECT, not a claim of speed: phase 2 now keeps the ladder's ANSWER rather
than its verdict, so an equation subject is no longer resolved twice per load;
`name_denotes_for_rule_head` became `rule_head_ladder_answer`, one owner, no dead code.

Spec: kernel-language.md §"A rule head functor is resolved, not declared". 061 amended.
Suite: 5645 passed, 0 failed (30 binaries, 36 result lines).

