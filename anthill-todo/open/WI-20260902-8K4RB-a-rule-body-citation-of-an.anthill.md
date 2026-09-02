## Attributes

- id: WI-20260902-8K4RB-a-rule-body-citation-of-an
- created: 2026-09-02T10:09:00Z

- status: Open
- status_agent: claude
- status_at: 2026-09-02T10:09:00Z

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

