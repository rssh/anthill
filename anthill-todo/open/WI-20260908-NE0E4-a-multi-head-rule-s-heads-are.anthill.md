## Attributes

- id: WI-20260908-NE0E4-a-multi-head-rule-s-heads-are
- created: 2026-09-08T20:53:59Z

- status: Open
- status_agent: user
- status_at: 2026-09-08T20:53:59Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A MULTI-HEAD RULE'S HEADS ARE NEVER DECLARED, so two sorts' same-named heads COLLIDE into one global symbol and one sort's reader answers from the other's clause. WI-894's defect, still live in the arm that ticket did not reach.

MEASURED IN BOTH IMPLEMENTATIONS (found while measuring WI-20260902-EQG4F item 4, which is
one visible symptom of this).

`ruleIntroducedFunctor` (scaland `load/Loader.scala:1486`) and rustland's
`rule_introduced_functor_name` both open with "a MULTI-head rule, or a denial head,
introduces nothing". So `rule lawP: aa, bb :- …` mints the LABEL and nothing else:

  zzS.P.aa   = None        zzS.P.lawP = Some(68)   <- the label gets a scoped symbol
  zzS.Q.aa   = None        zzS.Q.lawQ = Some(70)      and holds ZERO clauses
  zzS.aa     = None
  aa         = None                                <- registered under no qualified name

  head of rule#2 (in sort P):  carrier=Ident  sym=75  qname='aa'
  head of rule#3 (in sort P):  carrier=Ident  sym=76  qname='bb'
  head of rule#4 (in sort Q):  carrier=Ident  sym=75  qname='aa'   <- THE SAME SYMBOL
  head of rule#5 (in sort Q):  carrier=Ident  sym=77  qname='cc'

A symbol IS created — the head term needs one — but it is an UNRESOLVED symbol carrying the
BARE spelling, so it falls to the `intern(name)` fallback that is ONE GLOBAL NAME. Two sorts
writing `aa` share symbol 75.

AND IT LEAKS, WHICH IS WHY THIS IS A SOUNDNESS BUG AND NOT A NAMING WART. P's own `aa` made
FALSE, Q's made TRUE, reader written INSIDE P:

                                   scaland   rustland
  multi-head, `aa` in both sorts       1          1     <- P's reader answers from Q's clause
  CONTROL distinct names pa/qa         -          0     <- so the 1 is the collision
  CONTROL single-head `rule sa`        -          0     <- WI-894's scoping works where it applies

The single-head control is the decisive row: same short name, two sorts, ZERO leakage —
so the defect is the MULTI-HEAD arm specifically, not same-named predicates in general.
Loads clean, reports nothing, answers with another sort's clause.

THIS IS WI-894's OWN DEFECT CLASS, and its comment three functions away at the mint site
already names it: "A functor with no scoped symbol falls to the bare `intern(name)`
fallback, which is ONE GLOBAL NAME: two sorts defining the same short name then share one
definition and the loser's own laws are ignored INSIDE ITS OWN SORT, on a program that
loads clean." WI-894 fixed that by scoping the mint; the multi-head arm returns `None`
BEFORE reaching the mint, so those heads still take the fallback WI-894 exists to remove.

THE REFUSAL HAS NO STATED REASON, and its two neighbours in the same doc comment do: the
MINTED-subject arm explains itself (WI-618: the desugar's functor is not the rule's), and
the QUALIFIED-head arm explains itself (a dotted head REFERENCES). The multi-head arm just
says it. Nothing found so far says what a multi-head rule is supposed to declare.

FIX DIRECTION (not chosen — this needs the spec read first): mint each head in the scope the
rule is WRITTEN IN, exactly as WI-894 already does for a single-head rule. The single-head
control above is the evidence it works. Check `docs/kernel-language.md` on what a multi-head
rule declares before changing it, and decide what the LABEL is then for (today it is minted
with zero clauses).

WHAT ELSE THIS DISSOLVES: WI-20260902-EQG4F item 4 — `:- aa` answers 1 and `:- aa()` answers
0 (scaland) / is a LOAD ERROR (rustland), because the loader's `isResolved` gate keeps an
undeclared name as `Term.Ident` while `aa()` canonicalizes to `Term.Ref`. Declaring the head
removes the precondition (an unresolved name) and both spellings become one term, which is
the single-head control's 1-and-1. NOTE the census: EQG4F item 4 named only the multi-head
route, but `fact ff` and `fact ns.gg` reach the same split, and §6.1 makes a fact head
introduce no name DELIBERATELY — so this ticket closes the multi-head route only, and the
fact-head route is a separate spec question.

CONTROLS FOR WHOEVER TAKES THIS: the two above must stay at 0, `zzS.P.lawP` must keep
naming something citable, and a multi-head rule whose heads are ALREADY declared elsewhere
must not double-declare or shadow (`refuseDeclarationThatCannotStand` is the neighbouring
refusal that already fires for a name a rule may not take over).

