## Attributes

- id: WI-20260902-CZJ2N-the-two-nullary-spellings-are
- created: 2026-09-02T04:12:15Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T04:12:15Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE TWO NULLARY SPELLINGS ARE STILL TWO TERMS, so a predicate written one way is not
queryable the other -- and the spec says the opposite in words.

MEASURED (rustland, WI-20260901-719FJ's tree, with 719FJ delivered). NO DOT IN THE
FIXTURE -- this is spelling-independent and predates both P85Z7 and 719FJ:
  namespace zz.sp
    rule tgtA :- b(1)      rule tgtB() :- b(1)
    rule aa(1) :- tgtA     rule ab(1) :- tgtA()
    rule ba(1) :- tgtB     rule bb(1) :- tgtB()
  end
  aa -> 1   ab -> 0   ba -> 0   bb -> 1
Each spelling answers ITS OWN and neither answers the other's. The row that pins it is
`wi_719fj_dotted_paren_less_citation_test::the_two_nullary_spellings_are_still_two_terms`
(green today, deliberately -- it is the measurement, not a claim that it is right).

WHAT THE SPEC SAYS. kernel-language.md 8.6: "**A PAREN-LESS nullary head is an
application of arity 0** (`rule holds :- base(1)`; WI-20260821-P85Z7). It introduces its
predicate and is scoped where it is written, exactly as `rule holds()` is". P85Z7
delivered the SCOPING half -- the name is minted where it is written -- and left the TERM
half: `convert_term_inner`'s `Term::Ident` arm builds `Ref(sym)` while the parenthesised
head builds `Fn{sym, [], []}`, and those do not unify. A reader of that sentence expects
`rule holds :- base(1)` to answer `holds()`.

WHY IT IS NOT A ONE-LINE PATCH, and why 719FJ did not take it. §8.3 makes the same
paren/no-paren distinction LOAD-BEARING for entity terms -- "the expansion applies
whenever the functor is a registered entity ... (bare `account` without parens remains a
reference to the entity/sort)" -- so `account()` is the all-fields-fresh PATTERN and bare
`account` a REFERENCE. For a nullary PREDICATE that distinction has no content, which is
what makes the split look like an accident; but choosing which of `Ref(p)` / `p()` a
nullary proposition IS, is a decision, and it has to be made in FOUR term converters at
once (`convert_term_inner`, `build_body_atom_occurrence_inner`, `convert_query_term`, and
`encode_proof_step` through the first) plus whatever a `fact <EntityName>` head and a
bare-entity QUERY PATTERN should then mean.

WHAT IT COSTS TODAY, so the decision has a driver: 719FJ's own acceptance asked for
"two clauses, the goal answering both" on the MIXED fixture `rule tgt()` inside `nsx`
beside `rule nsx.tgt :- b(1)` outside. After 719FJ that lands two clauses under
`nsx.tgt` -- and NO single goal spelling reaches both, because the two heads are two
shapes. 719FJ's head row therefore writes ONE spelling on both sides, where the goal does
answer both. A user who mixes the spellings gets a predicate with clauses they cannot all
reach, on a program that loads clean.

ACCEPTANCE: drive it. `rule holds :- base(1)` and `rule holds() :- base(1)` must be ONE
predicate a single goal reaches, in BOTH goal spellings, or the two spellings must be
told apart LOUDLY at the point one head joins the other's predicate. Say what
`fact account` (a bare ENTITY reference as a head) and the query pattern `account` mean
under whichever reading is chosen -- 8.3 gives them a meaning today and it must not be
changed silently. The control is
`the_two_nullary_spellings_are_still_two_terms`, whose 2x2 must be moved by this ticket,
and P85Z7's `a_bare_equation_subject_introduces_nothing_and_fires_nothing`, which must
stay green: a `[simp]` head is an APPLICATION and `rule tau <=> ...` must keep firing
nothing (5.3). Both implementations. cargo-test green via rustland/scripts/test.sh.

