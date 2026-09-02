## Attributes

- id: WI-20260901-719FJ-a-dotted-paren-less-nullary
- created: 2026-09-01T12:24:10Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-02T04:59:30Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DOTTED PAREN-LESS NULLARY CITATION IS A `field_access` CHAIN, IN EVERY POSITION -- so as a
RULE HEAD it silently drops the whole rule, and as a GOAL it answers a residual.

MEASURED (rustland, WI-20260821-P85Z7's tree, with P85Z7 delivered):
  fact b(1)
  namespace nsx  rule tgt() :- b(1)  end
  rule nsx.tgt :- b(1)          -- loads clean; `nsx.tgt` holds ONE clause, not two
  rule nsx.tgt() :- b(1)        -- the twin: TWO clauses, the reference lands
and in GOAL position, `anthill query 'nsx.shared_pl'` answers
`conditional / residual: eq(field_access(nsx, shared_pl), true)` where
`nsx.shared_pl()` answers `true`. Both spellings of one nullary citation, opposite
programs -- P85Z7's shape, one segment over.

MECHANISM, CONFIRMED. The converter folds a multi-segment `name` into a MINTED
`field_access(object, Ident(field))` chain (parse/convert.rs, the `"name" | "absolute_name"`
arm). `head_subject_name`'s `is_minted` guard therefore refuses it -- correctly, since
the functor is `field_access` and not the source's -- so the head introduces nothing AND
references nothing: its clause is stored under `field_access`. P85Z7 fixed the BARE
spelling by reading `Term::Ident`; the dotted one is a different node.

WHY IT IS NOT A ONE-LINE PATCH, and why P85Z7 left it. The SAME chain is what a dotted
paren-less citation lowers to in EVERY position, and proposal 052 §6.7 gives it a MEANING
there: `try_qualified_rule_ref` reads `Sort.rule` with no trailing `(...)` as the
`Relation[T]` VALUE, deliberately, so a head cannot simply be re-read as a qualified goal
without saying what the goal position and the operation body do. Three positions, one
chain, and today only the value reading is decided.

CORPUS: ZERO sites of the head spelling (censused over every `.anthill` in the tree).
This is a correctness hole, not a migration.

ACCEPTANCE: drive it. `rule nsx.tgt :- b(1)` must either land its clause on `nsx.tgt`
(two clauses, the goal answering both) or be REFUSED naming the spelling -- not load
clean holding one. The control is `wi_p85z7_paren_less_nullary_head_test::a_dotted_paren_less_head_still_lands_no_clause`,
which PINS today's `Some(1)` and must be moved by this ticket. Say what the GOAL position
and an OPERATION BODY do with the same spelling, and drive whichever reading is chosen in
all three. cargo-test green via rustland/scripts/test.sh.

## Changes

### 2026-09-02T04:59:19Z — feedback — user

DELIVERED. A DOTTED PAREN-LESS CITATION IS THE NAME IT SPELLS, IN EVERY LOGICAL POSITION —
and the thing that decides is the POSITION, never the qualification.

THE READING THE TICKET ASKED FOR, taken and written into the spec (§6.7, "A dotted
paren-less name in a LOGICAL position is the name it spells"). `nsx.tgt` lowers to the
converter's minted `field_access` chain EVERYWHERE, so what it lowers to says nothing
about what it means:

 * OPERATION BODY — UNCHANGED, proposal 052 §6.7's `Relation[T]` VALUE
   (`try_qualified_rule_ref`). Driven end to end through the interpreter
   (`Person.rows.isEmpty` / `Person.all.isEmpty`, opposite emptiness) so a silent
   collapse here would FAIL rather than pass.
 * RULE HEAD — the qualified NAME. `rule nsx.tgt :- b(1)` joins the predicate `nsx.tgt`,
   as `rule nsx.tgt()` does. The ticket's control moved from `Some(1)` to `Some(2)`.
 * BODY GOAL — the nullary GOAL. `:- nsx.tgt` runs it.
 * QUERY PATTERN — the same name. The residual is gone.

AND A DATA SLOT IS DELIBERATELY NOT COLLAPSED: `fact holds(nsx.tgt)` and the query
`holds(nsx.tgt)` must build ONE term (WI-756/P9Y67), so only a SUBJECT is read as a name.

THE TICKET NAMED THREE POSITIONS; THE CENSUS FOUND SIX, and the extra three were found by
asking which loader sites convert a term that states a PROPOSITION rather than by reading
the ticket's list:
 * a FACT head — `fact nsx.tgt` filed its clause under `field_access` where
   `fact nsx.tgt()` referenced. It is NOT §6.1's "a fact head introduces no scoped name",
   which is about INTRODUCING; a dotted head REFERENCES, and the reference was dropped.
 * a QUERY PATTERN — its own converter, with no `Loader` to share the walk through, which
   is why the chain-name walk had to be lifted to a free function.
 * a structured PROOF STEP's head AND body goals — the record the prover dispatches on.
   Measured backed out: `body_terms: [field_access(field_access(field_access(zz719,
   pfbare), inner), tgt)]`.

THE SOUNDNESS HALF, which is worse than "answers nothing": `rule r(1) :- not(nsx.tgt)`
SUCCEEDED for a predicate that HOLDS — negation-as-failure read the broken goal's failure
as a refutation. `a_negated_dotted_paren_less_goal_is_not_a_free_proof` is that row.

AND A RESIDUAL THAT WAS BEING COUNTED. `anthill query 'nsx.tgt'` came back
`conditional / residual: eq(field_access(nsx, tgt), true)` — one "solution" that decides
nothing, and `resolve(..).len()` counts it. That is not only this ticket's symptom: P85Z7's
own `a_bare_nullary_clause_is_indexed_under_the_scoped_symbol` asserted "and the goal
reaches them" through a `.len()` on the DOTTED pattern `zzP85Z7.idx.pl`, so it was passing
on a residual — MEASURED, the count stayed 1 with BOTH of that fixture's clause bodies made
false. Its helper now counts definite solutions only, and the row measures for the first
time; it is one of the three D-axis failures.

TWO NEIGHBOURING HOLES CLOSED ON THE WAY, each the same defect one spelling over:
 * WI-1075's marked-absolute refusal never saw a folded path, so `rule ..nosuch.tgt :- b(1)`
   loaded clean while `rule ..nosuch.tgt()` was refused. `head_name_as_written` now spells
   the name the author wrote for all three head shapes, and the FACT side reaches it too.
 * ONE HEAD, ONE FAULT, ONE REPORT: `scan_sort_carrier_bindings` pre-scans a sort's `fact`
   items and read the head through the GENERIC walk while `load_fact` reads it as a
   subject. On an ambiguous root that was TWO errors for one head —
   `ambiguous symbol 'M'` (the root segment, which the author never wrote as a name) plus
   `ambiguous symbol 'M.tgt'`. One reading now.

WHAT DOES NOT MOVE, each with a row that would fail if it did: the value position (052
§6.7), a data slot on all three walks, a HAND-WRITTEN `field_access(a, b)` in either
position (92VA4's provenance gate — three gates keep the reading off everything else:
minted, no named args, name-rooted), and the equation side (`rule Sort.tau <=> 7 [simp]`
still matches no redex).

THE ONE PROPOSITION-SHAPED POSITION LEFT ALONE is a CONSTRAINT body, and that is measured
rather than asserted: a denial is stored inert and registered as no guard, so a goal there
decides nothing whatever it names — driven with an arm that names a namespace which does
not exist and loads just as clean as the two that do.

SCALAND HAD THE SAME DEFECT WITH THE OPPOSITE SYMPTOM, which is why the port is not
cosmetic: `field_access` is a registered builtin whose tag is `BuiltinResult.Delay`, so a
dotted paren-less GOAL SUSPENDED and its residual counted — `rule r(1) :- zz.nope.tgt`,
naming a namespace that does not exist, loaded clean and ANSWERED 1. rustland's goal always
FAILED; scaland's always SUCCEEDED. Fixed at the same three positions it has (rule head,
fact head, top-level body goal).

ONE SCALAND BRANCH I WROTE AND THEN REMOVED, recorded because the removal is the finding:
rustland routes `not`'s NEGAND as a goal of its own (`goal_arg_slots`), and I ported the
twin keyed on the resolved functor's builtin tag. It could never fire — `kb.getBuiltin`
answers `None` for a loaded rule-body `not(…)`, so scaland's NAF is not reached from a rule
body at all. Driven: `not(un(999))` over an EMPTY predicate answers 0, as does `not(un(1))`
over a provable one, and so does every nullary spelling. A branch nothing can drive is not
a fix; the comment at `reallocTerm`'s `Term::Fn` arm says where the descent goes when a
negand position appears.

THE GAP THIS LEAVES, FILED rather than parked: the PAREN-LESS and PARENTHESISED nullary
subjects are still two TERMS (`Ref(p)` vs a zero-argument `Fn`), so `rule holds :- b(1)`
is not queryable as `holds()` and vice versa — spelling-independently, with no dot in it.
§8.6 says the opposite in words ("a paren-less nullary head is an application of arity 0
… exactly as `rule holds()` is"). `the_two_nullary_spellings_are_still_two_terms` pins it
with a 2x2 that has no dot in it at all; WI-20260902-CZJ2N owns it. It is why the ticket's own mixed
fixture (`rule tgt()` inside, `rule nsx.tgt` outside) lands two clauses that no single goal
spelling reaches, and why this ticket's head row is written in ONE spelling on both sides —
where it does answer both.

REVIEW ROUND — /code-review high found THREE defects in this change and all three are
fixed inline:
 * A DOC BLOCK STOLEN BY AN INSERTED FUNCTION, twice in this session: WI-1075's whole
   rationale (including this ticket's own paragraph about the refusal's changed signature)
   had come to sit on `head_name_as_written`, leaving `refuse_unresolvable_absolute_head`
   with no doc at all. Invisible to the compiler and to the suite, and it breaks the
   "grep the rule name, read the enforcement site" convention the repo runs on.
 * A COMMENT THAT WAS FALSE, AND A REAL CHANGE SHIPPED AS A NO-OP UNDER IT. I wrote that
   admitting a bare `Term::Ident` fact head was inert because "an unqualified name is
   never marked absolute". It is not: a ONE-SEGMENT `..zznosuch` IS a `Term::Ident`
   carrying the marker. Measured with the arm gated back out, `fact ..zznosuch` LOADS
   CLEAN and asserts under a symbol nothing can cite — WI-1075's own defect, which the
   RULE head has been refusing since P85Z7 and the FACT head had not. It is now the
   `fact-1seg` arm of the marked-absolute row, and axis G is TWO legs.
 * A DANGLING `[`Self::head_subject_written_name`]` reference to a function that does not
   exist.
The review also verified three things I would otherwise have had to assert: the
`unreachable!` in `subject_introduces` cannot fire, a hand-written `field_access` NESTED
under a minted accessor does NOT collapse (it built the fixture), and the doubled loud
resolution of a sort-body fact head is collapsed by `LoadError::dedup_key`.

CONTROLS: TWELVE BACK-OUT LEGS, each PRESENT-BUT-WRONG and each applied and run over the
WHOLE `wi_tests` binary (4 020 rows). Counts in the test file's header. THREE of the axes
turned out to be written at two call sites each, and each split was found by MEASURING
rather than by reading: `encode_proof_step`'s head and body are separate lines, and an
earlier cut of its row wrote the citation only in the BODY — the head-leg back-out then
PASSED, half the change measured; `fact_head_subject_name` was missed on the first cut of
the clause census, found by re-reading the diff and not by the suite; and axis G's second
leg came from the review.

cargo-test: 6308 passed, 0 failed (36 binaries, rustland/scripts/test.sh).
scaland-sbt-test: 533 passed, 0 failed.

