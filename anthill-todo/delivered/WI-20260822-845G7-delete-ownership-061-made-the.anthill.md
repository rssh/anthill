## Attributes

- id: WI-20260822-845G7-delete-ownership-061-made-the
- created: 2026-08-22T11:21:56Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-22T14:21:38Z

- acceptance: cargo-test

## Description

DELETE `Ownership` — 061 MADE THE FIXPOINT COMPUTE A CONSTANT, AND THE CENSUS SAYS SO.

`Ownership` (rustland/anthill-core/src/kb/load.rs, ~400 lines with `Owned` and `Reach`)
answers "which scope does an auto-declared predicate land in" with a non-monotone
round-based fixpoint: an optimistic overlay, three settling rules, an SCC tie-break, a
`(scope, name, FILE)` key, a `<global>` two-roles exception and a depth bound. It exists
because a rule head was the one name created during the pass that decides it.

061 removed that: a predicate is DECLARED, minted in pass 1 like every other name, and
auto-declaration is a single-FILE convenience. WI-20260821-E85J5 closed the last shape
where the decision was silently doing work.

CENSUS, instrumenting the verdict loop and running the whole suite (which loads stdlib,
anthill-stl, examples, anthill-todo and every fixture) — 234,078 decisions, one per rule
head that did not already denote, i.e. exactly the population `Ownership` decides:

    Owned::Here          233,917   the head introduces at its own scope
    Owned::Yields(Some)      161   the head JOINS another scope's head
    Owned::Yields(None)        0   yields to an ordinary declaration — never reached

Of the 161: 130 are one fixture (`deep1`..`deep260`). The other 31 are 22 distinct
(name, from, to) triples, EVERY ONE in a fixture written to exercise this machinery —
`wi980.*`, `fqc85.*`, `fa.inner`, `mA/mB/mC/mD`, `nOuter.nInner`, `zdemoq -> zlibq`,
`wi900.user -> wi900.one`. ZERO from the shipped corpus: no stdlib, anthill-stl, examples
or anthill-todo predicate ever joins another scope's head.

THE REPLACEMENT RULE: **an undeclared rule head declares its predicate at the scope it is
written in.** A predicate shared between scopes, or between files, is DECLARED. The
`denotes` ladder stays and is what keeps the stdlib's law layer working (a head whose name
RESOLVES is a clause of what it resolves to — `rule bound: gte(?x,3.0) :- gte(?x,5.0)` is
a lemma about `PartialOrd.gte`), so the 99-stdlib-errors hazard does not come back.

WHAT GOES: the fixpoint, the rounds, `sink_component`/SCC, the per-`(scope, name, file)`
keying, the `<global>` two-roles exception, the depth bound, `Owned`, `Reach`. What stays:
`mint_head_sentinels` and the single-pass overlay `reach`, needed for the cross-scope
refusal below.

WHAT IT REVERSES, and this is the cost to weigh: §"Joining is not confined to one SCOPE,
and that is the point of it" — `demo { rule p(1) :- true; sort Rec { rule p(2) :- true } }`
is ONE predicate at `demo` today and becomes TWO. Corpus cost of the reversal: ZERO,
measured above. The join is still available and is now written down: `rule p(?x)` at
`demo`.

THE OPEN SUB-DECISION IS WHERE THE NEW REFUSAL STOPS. Removing the join replaces an
ASSEMBLY hazard with a SHADOWING one, and 059 §Definitions' file-boundary argument was
about assembly ("two parties that never agreed"), so it does not transfer unchanged. Two
readings:
 (a) FILE BOUNDARY, as E85J5 shipped — refuse only when the two scopes' heads are in
     different files; a same-file split is silent.
 (b) ALWAYS LOUD — refuse whenever a head introduces a name another scope it can SEE also
     introduces, one file or several. Corpus cost is also zero, and it leaves no silent
     meaning change anywhere; it flips E85J5's single-file residue (061 open question 3)
     to a refusal.

TEST CHURN either way: ~12-15 rows in `wi980_rule_head_order_test` change meaning. The
join rows (`sort_body_*`, `nested_namespace_*`, both `a_facade_*`, both `requires_*`) each
need a declared arm driving the join; four dissolve outright
(`a_cycle_does_not_reach_a_bystander`, `nobody_yields_to_a_scope_that_mints_nothing`,
`a_head_that_binds_is_not_an_owner`, the depth row's bound). `wi_fqc85_rule_declaration_test`'s
file rows should survive.

ACCEPTANCE: `Ownership`, `Owned` and `Reach` gone; the rule stated in
docs/kernel-language.md §"A rule head functor is resolved, not declared" replacing
§"And the ladder is asked of the FINISHED program" and §"Joining is not confined to one
SCOPE"; 061 amended; every changed row carrying its own control and a stated back-out.

## Changes

### 2026-08-22T14:21:32Z — feedback — claude

DELIVERED. `Ownership`, `Owned` and `Reach` are gone — the non-monotone fixpoint, the
rounds, the optimistic overlay, `sink_component`/SCC, the per-`(scope, name, file)` key,
the `<global>` two-roles exception and the depth bound with them.

THE RULE, and it is two sentences:
  A rule head whose functor RESOLVES is a clause of what it resolves to. One that resolves
  to NOTHING declares its predicate at the scope it is WRITTEN IN. Two scopes that can see
  each other may not both introduce one name — declare it.

Nothing is asked about any other head, so no order can enter; order-freedom is a property
of the rule rather than a result of a fixpoint over the finished program.

THE SUB-DECISION THE TICKET LEFT OPEN was taken as (b), ALWAYS LOUD: the refusal is stated
over VISIBILITY, not over files, so a same-file `demo { rule p(1) :- true; sort Rec { rule
p(2) :- true } }` is refused exactly as a cross-file pair is. 059 §Definitions' file unit
answers "assembled by two parties that never agreed on it"; this is a different hazard, and
one author writing that pair is one party who would otherwise silently get two predicates
where the language used to give one. Corpus cost of the wider rule: zero, the same as the
narrow one.

THIS SUPERSEDES WI-20260821-E85J5's file boundary and 061's open question 3 (the
single-file cycle residue): both are now the general rule.

THERE IS NO SPEEDUP, AND THE TICKET SHOULD NOT HAVE IMPLIED ONE. Full suite before/after:
`wi_tests` 208.42s -> 206.37s, `cmd_tests` 127.51s -> 128.78s. Noise, and for a reason the
census already contained: with one candidate scope the fixpoint's rule 1 settled in a
single resolver call, so it was O(1) per name in every real program. Where its cost WAS
real it is now flat — marginal chain cost (shared head name minus a distinct-name control,
in-process, min of 3, debug, the method the old numbers used):
    n=200  0.68s -> 0.40s (first-iteration warmup)
    n=300  2.33s -> -0.004s
    n=400  7.63s -> 0.014s
This was a complexity removal, not a speedup.

WHAT `/code-review` FOUND, over two passes — nine findings, three of them defects that
fail SILENTLY, and all of them in code written for this ticket:
 * THE NAMED OWNER WAS A SINK, AND REACH IS NOT TRANSITIVE. A wildcard import is never
   re-exported, so in `zzA -> zzB -> zzC` the sink is `zzC` and `zzA` cannot see it. The
   message promised that declaring at `zzC` collects every head; FOLLOWING IT made the
   refused program LOAD CLEAN with `zzA.cp` still split off and no error at all — the
   refusal defeated by taking its own advice. The test is now "reached by EVERY other
   member".
 * AND THE SAME DEFECT ONE COORDINATE OVER, ACROSS FILES. Reach was unioned per SCOPE, so
   a namespace reopened in two files where only one carries the import still named the
   imported scope; declaring there left the import-carrying head on the local predicate,
   silently. The test is now per (scope, FILE).
 * `<global>`'s EXCLUSION LIVED ONLY IN THE OVERLAY, but the group is the UNDIRECTED
   closure of reach — so a namespace-less file writing `import ns.*` and a head still
   pulled `ns` into a group with `<global>`, refused, and the repair it named DELETED the
   `<global>` head's predicate. `<global>` is now out of the candidate set; the overlay
   test that remained was dead, its stated back-out failed zero rows, and both were
   removed. The cost is a named silence, recorded at the site and in the spec.
 * EQUATION SUBJECTS WERE EXCLUDED FROM THE CHECK, which silently split `zeq.f` /
   `zeq.Rec.f` into two symbols where it had been one — the exact hazard the refusal
   exists for, permitted for half the head shapes. They are a party now, and both
   prescribed remedies are driven and load for an equation subject.
 * Three message defects: the `owner: None` text asserted "they reach each other" (false
   for a chain, and for two siblings under one importer); the headline asserted the scopes
   "can see each other" when the group is WEAKLY connected; and `Display` printed all 261
   scopes where `format_with_source` truncated at 6.
 * Four doc-rot sites still describing the deleted fixpoint's answers.

BACK-OUTS, all run and recorded in the suite header: the collision refusal 14 rows, the
asking file 8, the named owner (sink) 6, the file rule 2, the suppression 1, equations
excluded 1, `<global>` as a candidate 1, the per-file owner 1. ONE LINE HAS NO TARGETED
BACK-OUT and says so: taking every candidate pair as an edge fails 2204 rows because the
stdlib stops loading, so no row ISOLATES the visibility test —
`two_scopes_that_cannot_see_each_other_keep_their_own` is the cheapest witness for what it
is FOR, and the 2204 is the measurement of what it costs to lose.

ONE OBSERVATION SURFACED AND NOT CHASED: `requires` on a sort that declares an ENTITY does
not carry the name across the edge — `Spec.p` and `A.p` split and the program loads clean,
under this design and under the fixpoint alike. Pre-existing, unchanged, and noted at the
`requires` fixture rather than absorbed into it. It deserves its own ticket if the `requires`
edge is meant to be uniform.

Suite: 5479 passed, 0 failed (29 binaries, 35 result lines).

