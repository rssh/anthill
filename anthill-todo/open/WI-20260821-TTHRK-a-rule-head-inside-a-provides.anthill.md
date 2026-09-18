## Attributes

- id: WI-20260821-TTHRK-a-rule-head-inside-a-provides
- created: 2026-08-21T07:53:20Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T07:53:20Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RULE HEAD INSIDE A `provides ... language ... end` BLOCK IS INVISIBLE TO THE SCAN, so
it is neither scoped nor refused -- and WI-980's two guards both miss it.

MEASURED (rustland, WI-980's tree). Two unrelated namespaces, each with a sort and a
`provides <Carrier> language rust ... rule pcap(N) ... end` block, N = 1 and 2:
`anthill check` reports nothing, `query "pcap(?x)"` answers BOTH 1 and 2 -- one shared
uncitable symbol -- and `nsA.pcap` does not resolve. CONTROL: with only one namespace
present, `pcap(?x)` answers 1. Reported by /code-review against WI-980.

MECHANISM: `RuleHeadCollectPass::at_item` (sub-pass 3) matches `Item::Rule` and
`Item::RuleBlock`; `Item::ProvidesBlock` falls into the `_ => {}` arm, so
`ProvidesItem::Rule` / `ProvidesItem::RuleBlock` never become `RuleHeadSite`s. The LOAD
phase still loads them (`load_provides_block` -> `load_rule`), so the clause is stored --
under `remap_name_str`'s bare `intern(name)`, WI-894's one global name.

WHY IT IS NOT A MISSING MATCH ARM. The scope is the problem, not the walk. A provides
block's rules load into `kb.symbols.scope_id(spec_domain)`, where `spec_domain` is
resolved BY THE LOAD PHASE from the block's `TypeExpr` (`load_provides_block`,
kb/load.rs). Sub-pass 3 has no such scope and no resolved spec term. Adding the arm means
answering WHICH scope a provides-block head is written in, at scan time.

THREE CANDIDATE ANSWERS, and picking one is the ticket:
 (a) Resolve the spec domain in the scan. Correct-looking and the most dangerous: it
     duplicates a load-phase resolution, and a second spelling of one question is exactly
     what WI-980 spent its budget undoing (a hand-written twin of the resolver's parent
     walk falsely refused three programs that load clean).
 (b) Refuse a rule head in a provides block that would INTRODUCE, leaving one that names
     something already resolving. Cheap and loud; needs a corpus census first (the stdlib
     realization files carry provides blocks).
 (c) Record the escape and leave it. 059 R3's enforcement site already records that a
     provides block's interior is classified recursively, so the shape is known.

RELATED: 059 R3 classifies the direct content of a secondary entry and recurses into a
host `provides` block's interior, so the classification pass DOES reach these items --
whatever this ticket decides should agree with what pass 1b already does there, and may
be able to reuse its walk rather than mint a third.

ACCEPTANCE depends on the answer chosen. For (a) or (b): two namespaces whose provides
blocks each write a head of one name must NOT share a predicate -- drive both goals and
assert the answers are separate, with the control being today's single shared answer. For
(c): the record goes at the site and in kernel-language.md beside the `<global>` refusal,
which currently reads as though it closes the shape. cargo-test green via
rustland/scripts/test.sh.

## Changes

### 2026-09-17T10:16:54Z — feedback — user

MEASURED, WITH A CONTROL, AND NOW PINNED IN A TEST (found while delivering
WI-20260821-RDGQC's enumeration, 2026-09-17). This ticket had the mechanism; what it did
not have was the LEAK driven end to end.

TWO SORTS, ONE HEAD NAME, each written in its own host block:

  namespace zzRDGQC.pv
    sort RecP  entity P(v: Int64)  rule see(?x) :- pick(?x)  end
    sort RecQ  entity Q(v: Int64)  rule see(?x) :- pick(?x)  end
    provides RecP language rust  artifact "x.rs"  rule pick(1) :- true  end
    provides RecQ language rust  artifact "y.rs"  rule pick(2) :- true  end
  end

  RecP.see -> 2 answers        RecQ.see -> 2 answers
  CONTROL, the SAME two rules written IN the sorts instead of in a block:
  RecP.see -> 1 answer (its own)   RecQ.see -> 1 (its own)

So each spec's reader answers from the OTHER spec's block. The control is what makes the
2 a measurement of the BLOCK and not of the fixture — it is the same defect class WI-894
fixed for ordinary rule heads, in the arm no scan pass descends into.

THE ROW LIVES IN `wi_rdgqc_head_introduction_census_test::
a_host_provides_block_head_is_unscoped_and_two_specs_share_one_predicate`, beside its
control, and it PINS today's answer: it fails when this ticket is fixed, which is the
point. Closing this makes it (1, 1) — edit that row and the module's ledger table
together.

NOTE THE SPLIT THIS TICKET IS NOT: the block's CLAUSE already lands in the SPEC's scope
(WI-20260827-APXSS made `load_provides_block` set `current_scope` to the base sort). It
is the NAME that lands nowhere. So the fix is not "route the clause" — that is done —
but "mint the head", and the scope to mint it in is the one APXSS already computes.

ALSO WORTH KNOWING BEFORE TAKING IT: a reader OUTSIDE the sort is already loud. A
qualified citation of such a head (`rule seeG(?x) :- Rec.hd(?x)`) is refused at load by
WI-1034 ("rule-body goal `Rec.hd` names nothing"). The silence is only for a reader
INSIDE the sort, where the bare name falls to the same global intern the head did — which
is why the fixture above puts its readers in the sorts.

