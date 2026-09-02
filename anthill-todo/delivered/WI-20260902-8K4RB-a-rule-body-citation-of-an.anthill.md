## Attributes

- id: WI-20260902-8K4RB-a-rule-body-citation-of-an
- created: 2026-09-02T10:09:00Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-02T12:22:52Z

- acceptance: cargo-test

## Description

A RULE-BODY CITATION OF AN EQUATION FUNCTOR ANSWERS NOTHING, IN SILENCE — at every arity,
and WI-20260902-CZJ2N widened who reaches it.

MEASURED on CZJ2N's delivered tree, both spellings, byte-identical:
  namespace zz.e
    rule tauX <=> 7 [simp]          -- and `rule tauX() <=> 7 [simp]`
    rule reader(1) :- tauX
  end
  `zz.e.reader(?x)` -> no solutions. Exit 0, no diagnostic.

WHY IT IS SILENT AND CORRECT-BY-CONSTRUCTION: an equation's clauses index under the
CONNECTIVE, not under its subject (WI-898, kernel-language.md §5.3), so `tauX` owns no
clause. A goal naming it therefore matches nothing — which is exactly the empty relation
SLD answers for any predicate with no clauses. The name RESOLVES, so WI-1034's body-goal
refusal ("names nothing … can NEVER match") does not fire.

WHAT CZJ2N CHANGED, and why this is filed now rather than earlier. Before it, one arity-0
spelling was accidentally loud: `head_subject_name` gated the mint on
`RuleIntroduction::Predicate`, so a BARE undeclared equation subject stayed outside the
symbol table and its citation hit WI-1034's refusal — while the PARENTHESISED spelling
minted and was silent. CZJ2N deleted that guard (the two head spellings are one term, so
refusing at arity 0 only would be a new spelling-dependent rule), which makes the silence
UNIFORM. That is the right direction — one rule at every arity — but it removes the one
place a user got told, so the underlying gap is now unmitigated and needs its own answer.

THE SHAPE OF THE ANSWER. An `EquationFunctor` cited in GOAL position is never satisfiable:
its defining equations are rewrites, and a rule body is not a rewrite site. So the citation
is a static error, not an empty answer — the same argument WI-1034 makes for a name that
resolves to nothing. `LoadError::UnreducedEquationFunctor` (load.rs, WI-898) is the
existing loud channel for "the rewriter left this citation standing"; whether this is that
error or a sibling is the ticket's first question.

WHAT MUST NOT BREAK: an equation subject cited in an OPERATION BODY is legal and answers
(`operation drive(n) = tauX()` -> 7 via the `[simp]` inline). The refusal is about GOAL
position alone, and the pair is the control — a fixture asserting only the refusal would
pass with the operation-body reading broken too.

ACCEPTANCE: `rule reader(1) :- tauX` beside `rule tauX <=> 7 [simp]` is REFUSED, naming
the goal and its `line:col` and saying that an equation's clauses index under the
connective; the PARENTHESISED head and the PARENTHESISED citation behave identically (four
combinations, one verdict); and the op-body citation still answers 7. Say at the site which
rows a back-out fails. `wi_p85z7_paren_less_nullary_head_test::
a_bare_equation_subject_mints_exactly_like_its_parenthesised_twin` asserts the 0 that this
would turn into a refusal, so it flips and must be updated with its reason.

## Changes

### 2026-09-02T12:22:51Z — feedback — user

DELIVERED. `EquationSubjectInGoalPosition`, raised by the rule-body goal-READING pass.

THE TICKET'S FIRST QUESTION — A SIBLING, NOT `UnreducedEquationFunctor`, and the reason
is the REPAIR rather than the subject. That error is the VALUE-position citation the
rewriter left standing, and its census branches send the author to tag the equation
`[simp]` or to inspect the left-hand patterns. On this ticket's own fixture — `[simp]`-
tagged, one defining clause — that census reaches its third branch, "none of its 1
`[simp]` clause(s) fired here. A clause fires only where its left-hand pattern matches
STRUCTURALLY ...", which sends the author to inspect a clause that is fine. Driven:
`the_refusal_names_the_goal_position_not_a_failed_rewrite` asserts the new wording is
present AND that one absent.

WHERE IT IS RAISED, AND WHY NOT BESIDE WI-1034. `check_goal_atom_reading` (typing.rs) —
the pass that already owns "is this term readable as a goal at all?", whose other two
members are `ConstantInGoalPosition` and `NonBoolOpInGoalPosition`. The choice is the
DESCENT, and that pass's own doc states the rule: WI-863/WI-1034 tolerate a bare `or`
branch because an ABSENT name might exist in another program and the sibling may answer,
while a term with NO READING has no such defence. An equation subject is not absent — it
is present and unmatchable, in any program, in any branch, under any binding. So
`rule reader(1) :- base(1) | tauD` is refused too, which WI-1034's walk would not do.
The arm sits BELOW the `op_record` gate so a name that is also a declared `operation`
keeps WI-583's more specific message (driven, both directions).

THE GATE IS `has_kind(EquationFunctor) && !cites_a_relation(f)` — the second half asked
through WI-898's single owner of "does this name denote a relation", not re-derived, so a
scope writing one name in BOTH head shapes keeps its predicate goal answering.

THE SEVERITY WAS UNDERSTATED IN THE TICKET, which said "answers nothing, in silence".
MEASURED on the delivered tree, one file, three rules: `:- tauX` -> 0, `:- tauX()` -> 0,
`:- not(tauX)` -> **ONE**. Negation-as-failure laundered the unsatisfiable goal into a
confident `true` — a WRONG answer, not an empty one, and the same class CZJ2N removed for
`:- flag`. That row is `a_negated_citation_is_refused`.

TWO THINGS MEASUREMENT CHANGED IN THE DELIVERY.
  * "A rule body is not a rewrite site" is FALSE, and I had written it into the message
    before running it: `rule r(?v) :- ?v = tauX()` stores `eq(?_, 7)` — the law already
    inlined. `[simp]` fires in a rule body, in a VALUE slot. The message says
    "`[simp]` rewrites a VALUE, and a goal is MATCHED rather than rewritten", and the
    test asserts that spelling with the reason at its site.
  * `?r = tauX()` is NOT among the recommended repairs. Run, it RESIDUALIZES (`eq` never
    binds) and answers `?x = ?_` with a residual goal — recommending it would have handed
    the author a second silent nothing. The two repairs in the message are both RUN: an
    OPERATION-body citation (answers 7) and a `:-` predicate rule (answers 1).

AND ONE PRE-EXISTING DEFECT FIXED WITH IT. This pass reported ONE goal TWICE on a `-:`
multi-head rule — for `ConstantInGoalPosition` as well, byte-identical at one `line:col`
— because the desugar gives one shared body N `RuleId`s and only WI-1034's channel deduped.
Keyed at the caller on (variant, source, span). Both arms driven
(`a_multi_head_rule_reports_one_goal_once`); the CONSTANT arm is what says the fix is the
pass's and not this ticket's.

FOUR AXES, FOUR WHOLE-BINARY BACK-OUTS (4 036 rows each, exhaustive):
  A  the arm inert (`false &&`, one `&&` chain so the WHOLE arm)   -> EXACTLY 7 fail
  B  gate widened to the kind alone (drop `!cites_a_relation`)     -> EXACTLY 1 fails
  C  the per-goal dedup deleted                                     -> EXACTLY 1 fails
  D  P85Z7's mint guard restored (the flipped row's own claim,
     re-run rather than inherited)                                  -> EXACTLY 8 fail
Per-row lists and what each control RANKS are in the test file's header.

CORPUS CENSUS: ZERO sites across stdlib, rustland/anthill-stl, examples, docs and
anthill-todo, with a positive control that fired 3. A real zero, not an inert walk.

THE FLIPPED ROW: `wi_p85z7_...::a_bare_equation_subject_mints_exactly_like_its_-
parenthesised_twin` asserted the 0. It now asserts the REFUSAL — which is a STRICTLY
STRONGER reading of the mint, its actual subject: a 0 is what a name that minted NOTHING
would also answer, while the refusal is raised on `has_kind(EquationFunctor)` and names
the QUALIFIED symbol, neither of which exists unless the mint happened. Its two positions
now need two programs, since one file carrying both no longer loads.

SIBLING POSITIONS, MEASURED RATHER THAN ASSUMED:
  * CONTRACT CLAUSE — `requires tauX` LOADS CLEAN; only a CALL is refused, and that
    message blames the call site for a precondition no caller can establish. The
    undeclared-name control IS refused at load, so the pass reaches the position and it is
    the QUESTION that misses. Filed WI-20260902-7XFYQ (with the CLI query-explain path as
    the third reader of the same seam) and recorded at `check_contract_clause_goals`. Not
    inline: widening `undefined_query_goal_functors` would make the CLI report an
    equation subject as a name that does not exist.
  * DENIAL CONSTRAINT — inert by design and already driven
    (`wi_719fj_...::a_constraint_body_is_inert_for_every_spelling`); a constant and an
    undeclared name are equally unrefused there. Not a new gap.
  * QUANTIFIED CONSTRAINT — LOUD ("integrity constraint 'q1' is violated"). Not a gap.

SCALAND: no mirror. The refusal is the typer's goal-reading pass and scaland has no
typer; its `SymbolKind.EquationFunctor` comment is the "who reads this" list and it was
stale, so it now names both rustland readers and why neither ports.

SPEC: kernel-language.md §5.3 gains the rule as the third member of the goal-reading
family, and the P85Z7/CZJ2N paragraph's "what stops a citation being silent is
`UnreducedEquationFunctor`" is corrected — there are TWO channels, one per position.

/code-review (high) FOUND TWO THINGS IN THIS DIFF, both fixed here:
  * THE REPAIR NAMED THE GOAL QUALIFIED AND THEN PRESCRIBED THE SHORT NAME. Measured on a
    cross-namespace citation: the message said "cite `tauX(…)`" about
    `zzf9.inner.tauX` — a spelling that need not resolve at the citing scope. It now
    prescribes the QUALIFIED name and spells the parentheses out (`{f}()` at arity 0,
    because an op body's bare call site is not yet a redex — 65BTX). And the repair is
    now DRIVEN cross-namespace: `an_operation_body_citation_still_inlines_and_answers`
    gained an arm that calls `zz8K4RB.xouter.drive` and asserts 7.
  * A CONTROL'S COMMENT NAMED AN ASSERTION THE FLIP REPLACED — the P85Z7 control still
    said "the 0 above" after that 0 became a refusal.

ITS OTHER EIGHT FINDINGS ARE ABOUT THE FIVE UNPUSHED COMMITS, NOT THIS DIFF (its scope is
`origin/main...HEAD`). Filed rather than dropped:
  * WI-20260902-VNWAW — HIGH, and I re-measured it myself rather than taking it on
    report: 719FJ's DOTTED goal-position branch never got CZJ2N's two readings, so
    `:- zzdot.inner.flag` answers 0 where the unqualified control answers 1, and
    `:- not(zzdot.inner.flag)` answers ONE. Same NAF laundering as this ticket, one
    spelling over. Own site, own mechanism, own back-out table — not foldable here.
  * WI-20260902-EQG4F — the remaining six (four scaland, two rustland readers plus a LOW
    span-fallback one), filed as HYPOTHESES WITH SITES and marked NOT re-measured by me,
    with the instruction to build the failing fixture first and drop what dissolves.

