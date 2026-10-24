## Attributes

- id: WI-20260908-NE0E4-a-multi-head-rule-s-heads-are
- created: 2026-09-08T20:53:59Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-24T12:13:45Z

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

## Changes

### 2026-10-24T11:51:12Z — feedback — claude

DECIDED (user, 2026-10-24): OPTION 1 — each head of a multi-head rule with a body introduces exactly what its single-head rule `Hᵢ :- B` would (at the scope it is written in, or joining what its name already denotes); option 2 (a head must already resolve) and option 3 (split at parse time) declined. In a secondary entry (059 R3) the rule is judged HEAD BY HEAD — the recommendation, taken when the question went unanswered, and kept. The spec wording (`docs/kernel-language.md` §5.1's secondary-entry row; §5.3's scoping rule, its enumeration of what introduces nothing, its paren-less spellings and its multi-head paragraph; proposal 059) kept as written. The labeled-rule-in-a-host-`provides`-block load failure found on the way is filed as WI-20261024-RMZQZ, not fixed here.

### 2026-10-24T11:51:15Z — feedback — claude

/code-review, three rounds (2026-10-24), what each finding became. FIXED: (1) a multi-head rule the load refuses for its SHAPE — no body, no label, `⊥` among its heads — stores nothing, so it mints nothing and files no clause row: ONE decider, `several_heads_refusal` (scaland `severalHeadsRefusal`), read by `load_rule` and by the clause path's mint and by 059 R3's deferral, which skips such a rule (before, the refused line drew "introduces that name at 2 scopes" / "declare it" / R3's "introduces no name at all" too). (2) 059 R3 takes its verdict and its reason off ONE walk: `RuleHeadCollectPass::collect` records a `HeadMiss` (position + reason) for every head of a deferred rule that introduces nothing — a `Query` source's head too — beside its `RuleHeadSite`s; the judge refuses a rule with a miss naming every such head by position and with its own reason (a one-head refusal too), judges the rule's introducing heads all the same (a head refused on its own is reported now, not after the first fix), and refuses a rule with neither a site nor a miss for a head as an internal inconsistency (debug_assert) — before, it inferred a miss from "fewer sites than heads" and re-walked the heads for the reason. (3) Deterministic order where one rule's heads share its span: the site index breaks the tie in R3's report and in the absorbed-equation report. (4) Scaland refuses in rustland's order — the reading, `⊥`, WI-1090's connective, the label — so one program gets one diagnostic in both. (5) A rule with no head is refused (IR-only; the old label arm caught it for the wrong reason). (6) Tests: R3 rows one per test; the label holds no clause; the Scala parser row drives the clause store; Scala's copied load/query helpers moved into `LoadFixture`. (7) Spec: §5.3's paren-less-spellings heading (none remains unscoped), §5.1's R3 row, §5.3's label sentence (true also when a head is spelled as the label). DECLINED, with the reason: per-head refusals in `load_rule` (a non-defining connective in an empty-bodied rule, a const head, a mounted extent's head) are outside the shape decider by design — MEASURED, `rule law: aa, f(1) === 2 :- true` beside a nested `rule aa :- true` reports exactly what the two heads written apart do, `aa`'s collision being `aa`'s own fault; per-head diagnostic spans stay the RULE's, as for every single-head site (a location-convention change across every head diagnostic, not this ticket's); several R3 refusals for one rule are kept — each names a different head, as the rule written apart would.

### 2026-10-24T11:51:18Z — feedback — claude

2026-10-24, the measurements. Rust back-outs (77 rows: this ticket's file, the RDGQC census, APXSS, WI-1001, WI-894, in a temporary binary): 16 back-outs, each failing its rows — the table is the header of `wi_ne0e4_multi_head_introduction_test.rs`; baseline 77/77. Scala back-outs (113 rows over MultiHeadIntroductionTest, HeadIntroductionCensusTest, ParserIntegrationTest, DiagnosticLocationTest): 5, each failing its rows — the table is `MultiHeadIntroductionTest`'s header; baseline 113/113. Full Rust workspace gate on the final tree: 36 binaries, 10 701 passed, 0 failed, 17 ignored (`rustland/target/test-run-20261024-143137.log`). Full scaland `testFull`: 758 + 47 + 1 passed, 0 failed.

### 2026-10-24T12:13:49Z — feedback — claude

Delivered 2026-10-24 (fe7f4669, merged with origin/main in 258ed829). A multi-head rule's heads are scoped where they are written: `rule law: H1, H2 :- B` is N clauses (§5.3), and each head introduces exactly what `Hᵢ :- B` would — so two sorts that each write `rule law: aa, … :- …` have two predicates `P.aa` and `Q.aa`, each sort's reader answers from its own clause, and `:- aa` / `:- aa()` are one term (EQG4F item 4's multi-head route). The label is the citation handle and fans out to the scoped clauses. A multi-head rule the load refuses for its shape mints nothing. In a secondary entry (059 R3) the rule is judged head by head, refused naming every head that introduces nothing, with every introducing head judged too. Both implementations; spec §5.1 and §5.3 and proposal 059 amended. On the merged tree: the full Rust workspace gate, 36 binaries, 10 732 passed, 0 failed, 17 ignored (`rustland/target/test-run-20261024-145419.log`); scaland `testFull`, 758 + 47 + 1 passed, 0 failed. Filed on the way: WI-20261024-RMZQZ (a labeled rule in a host `provides` block does not load).

