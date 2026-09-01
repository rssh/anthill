## Attributes

- id: WI-20260821-P85Z7-a-paren-less-nullary-rule-head
- created: 2026-08-21T07:53:13Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-01T14:21:52Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A PAREN-LESS NULLARY RULE HEAD INTRODUCES NOTHING, ANYWHERE. It must either introduce or
be refused; today it does neither, silently.

MEASURED (rustland, WI-980's tree). `rule shared_pl :- b(2)` at top level beside
`namespace nsx { rule shared_pl :- b(1) }` LOADS CLEAN, `query "shared_pl"` answers
`true` -- the namespace's clause landed on the same global bare intern as the top-level
one -- and NEITHER `shared_pl` NOR `nsx.shared_pl` resolves to a symbol. Two scopes
share one uncitable predicate. The parenthesised twin `rule shared_pl() :- b(2)` is
REFUSED by WI-980's `<global>` rule. Two spellings of one nullary predicate, opposite
verdicts.

THIS IS WI-894's DEFECT CLASS, STILL LIVE. §"A rule-introduced functor is scoped where it
is written" exists precisely to stop a rule head reaching `remap_name_str`'s bare
`intern(name)` fallback -- ONE GLOBAL NAME two scopes' same-spelled heads then share,
with the loser's laws ignored inside its own scope on a program that loads clean. The
nullary spelling never entered that fix.

MECHANISM, CONFIRMED NOT ASSUMED: `rule_introduced_functor_name` (kb/load.rs) ends with
`let Term::Fn { functor, .. } = parse_terms.get(subject) else { return None; };`. A bare
identifier is not an application, so the head yields no name, no `RuleHeadSite` is
collected, and WI-980's sub-pass 3 never sees it -- never scopes it, never refuses it.

CORPUS: FOUR live sites, one of them a shipped EXAMPLE and one inside a namespace (so it
is the harmful shape, not only the top-level one):
  rustland/anthill-cli/tests/fixtures/wi754/props.anthill:11  rule holds :- base(1)
  rustland/anthill-cli/tests/fixtures/wi754/props.anthill:12  rule never :- base(999)
  rustland/anthill-cli/tests/fixtures/wi754/multi-query.anthill:8  fact holds
  examples/webots-modelling/lf1/safety_gps.anthill:82  rule gps_drift_axiom :- ...
Four CLI test modules load the wi754 fixtures and depend on `holds` ANSWERING, so a bare
refusal is not available without migrating them -- decide before implementing.
`examples/webots-modelling/lf1/safety_gps.anthill:82` is the shape INSIDE a namespace,
which is the harmful one: it is scoped nowhere today.

THE DECISION THIS NEEDS, and why it is not a one-line patch: `rule_introduced_functor_name`
is ONE function read by BOTH head shapes, and the two want opposite answers.
 * PREDICATE head: `rule holds :- base(1)` is a proposition and wi754 treats it as one.
   It should introduce a nullary predicate, scoped where written.
 * EQUATION LHS: CLAUDE.md and kernel-language.md §5.3 state the opposite deliberately --
   "a `[simp]` head is an APPLICATION, so a nullary head needs its parentheses (`tau()`,
   not `tau`)" -- because a bare identifier matches no redex. `rule tau <=> ...` never
   fires, and that must stay true.
So the fix splits a case the function currently fuses, and every reader of it
(`RuleIntroduction`, the WI-1129 capture, the WI-898 kind choice) has to be checked
against the split. Census the readers per RESOLVER, not per method (WI-1090/888).

ALSO TO SETTLE: whether the minted symbol is reached at LOAD -- confirm the clause is
indexed under the scoped symbol and not still bare-interned; and whether `fact holds`
(the `multi-query.anthill` spelling) follows the rule head or is a separate question.

ACCEPTANCE: drive it. Two scopes each writing a bare nullary head of one name must give
TWO predicates, each answering its own clause and neither answering the other's -- the
control is that today the goal answers `true` from the wrong scope's clause. Assert the
qualified names resolve. Keep an equation row proving `rule tau <=> ...` still fires
NOTHING while `rule tau() <=> ...` does. Say at the site which rows fail on a back-out.
cargo-test green via rustland/scripts/test.sh.

## Changes

### 2026-09-01T13:39:50Z — feedback — user

DELIVERED. A paren-less nullary head is now an APPLICATION OF ARITY 0 on the PREDICATE
path, in both implementations, and the equation path is unchanged.

THE DECISION THE TICKET ASKED FOR, taken: `head_subject_name` gains a `Term::Ident`
arm GATED on `RuleIntroduction::Predicate`. The two readers the ticket named were
checked and neither needed a second change -- `RuleIntroduction` travels with the name
as before, WI-1129's capture reads `ir::Rule::head_captures` (not the head shape), and
WI-898's kind choice is the same `introduced_by` value. `RuleHeadCollectPass::collect`
and `rule_reading` both go through the one walk, so the mint, the clause census and
061's declaration reading moved together.

WHAT THE GATE IS FOR, MEASURED (this is axis C, and its first stated control was WRONG
-- I claimed the ungated change would move `Bare.drive`; RUNNING it says all rows pass
ungated, because `tau` was a declared operation there and the head DENOTES either way).
The real separator is a bare equation subject naming NOTHING:
    rule tauFresh <=> 7 [simp]   rule reader(1) :- tauFresh
  gated   (shipped): REFUSED -- "`tauFresh` names nothing ... can NEVER match"
  ungated:           loads clean, `reader(?x)` answers `no solutions`, in silence
The mint made WI-1034's body-goal refusal resolve, suppressing it. Two controls separate
three readings: the parenthesised equation is admitted and answers nothing (clauses index
under the connective, WI-898), the predicate spelling of the same bare text answers 1.

ALSO CLOSED, same defect class one spelling over: `rule ..nosuch :- b(1)` LOADED CLEAN
and bare-interned while `rule ..nosuch()` was refused. `load_rule`'s head loop now asks
`Term::Ident` too, so WI-1075's refusal reaches both; a RESOLVABLE `..tgt` lands its
clause in either spelling (2 clauses, measured).

THE TWO "ALSO TO SETTLE" QUESTIONS:
 * The clause IS indexed under the scoped symbol, not bare-interned --
   `a_bare_nullary_clause_is_indexed_under_the_scoped_symbol` asserts 2 clauses AND that
   the goal reaches them (one true body, one false), so a minted-but-unreached symbol
   fails it.
 * `fact holds` is a SEPARATE question and stays put. A fact head is unscoped at EVERY
   arity (kernel-language.md 6.1); `fact holds` and `fact holds()` are alike, which is
   the row `a_fact_head_is_unscoped_in_both_spellings` pins. WI-20260821-RDGQC owns the
   fact rule whole, so the paren-less spelling is not a second hole there.

CORPUS: all four sites keep working. wi754's `holds`/`never` answer as before (the CLI
suites are untouched); `examples/webots-modelling/lf1` loads clean -- `gps_drift_axiom`
was the nested harmful shape and is now scoped to its namespace.

SCALAND NEEDED A SECOND FIX, and it is a PARSE bug rustland's tokenizer never had:
`:-` is one token there, but `(simpleName ~ ":")` ate its first character, so
`rule pl :- ba(1)` parsed as the LABEL `pl` with `- ba(1)` for a head and NO body --
measured, `Resolved(pl, ..., Rule, ...)` where a predicate belonged and zero clauses. The
lookahead is `!":-"` and not `!"-"`, so `lbl: -x :- ...` keeps its label.

CONTROLS, each APPLIED AND RUN over the whole binary (rustland 3977 rows, scaland 526):
  A the `Term::Ident` arm            4 fail / 3973 pass  (3 in the new file + fqc85's
                                                           declaration row)
  B the marked-absolute refusal       1 fail / 3976 pass  (its BARE arm only)
  C the predicate-path gate           1 fail / 3976 pass  (the citation row above)
  scaland loader arm / label colon / gate: 1 fail each, and the first two fail the SAME
  row at DIFFERENT assertions.

TWO STALE FIGURES FOUND AND CORRECTED on the way: `wi_fqc85_rule_declaration_test`'s
header credited its DECLARATION READING and PASS-1 MINT back-outs with "eight" and
"seven" wi980 rows; re-measured, both are SIXTEEN. Not this ticket's drift -- wi980
writes no paren-less head -- but a stated back-out nobody re-ran.

FILED: WI-20260901-719FJ, the one paren-less spelling still silent -- a QUALIFIED head
(`rule nsx.tgt :- b(1)`) folds into a minted `field_access` chain and lands its clause
under `field_access`, dropping the rule, while `rule nsx.tgt()` references correctly.
Not decidable alone: the same chain is what a dotted paren-less CITATION lowers to in
every position, and proposal 052 6.7 already reads it as the relation VALUE.
`a_dotted_paren_less_head_still_lands_no_clause` PINS today's behaviour and must be
moved by that ticket.

SPEC: kernel-language.md 8.6's "The refusal does not reach a PAREN-LESS nullary head"
paragraph is replaced by the rule; 5.3's `[simp]` nullary trap now says it is the
EQUATION head alone; 6.1's fact paragraph says the fact rule holds at every arity.
Proposal 061 item 5 drops the paren-less nullary from its refusal list and records why.

cargo-test: 6260 passed, 0 failed (36 binaries, rustland/scripts/test.sh).
scaland-sbt-test: 526 passed, 0 failed.

### 2026-09-01T14:11:51Z — feedback — user

REVIEW ROUND — /code-review high found ONE defect in this change and I fixed it inline;
its other five findings belong to commit 91aae403 (Q68AK) and are now WI-20260901-Q8NH5
and WI-20260901-47VWX.

THE FINDING, and it is this ticket's own defect class surviving in the DIAGNOSTIC:
`bodyless_declares_nothing_detail` re-walks the head to say WHY a body-less rule declares
nothing, and it destructured only `Term::Fn`. So the nullary reading landed in the VERDICT
and not in its EXPLANATION:
  rule ..nosuchxyz     -> "its head is not a functor application, so it names no predicate"
  rule ..nosuchxyz()   -> "`..nosuchxyz` is a QUALIFIED name, and a qualified name
                           references an existing predicate"
One head, one verdict, two sentences. The walk now reads `Term::Fn | Term::Ident`, both
spellings get the qualified sentence, and a bare VARIABLE head (`rule ?x`) keeps the
fallthrough one. It is NOT gated on the predicate path, unlike `head_subject_name`'s arm,
and the site says why that is reachability and not policy: an equation subject arrives
only through a MINTED connective head, which is a `Term::Fn` and reads as `Clause` anyway.

IT ALSO FALSIFIED A COMMENT I HAD WRITTEN. The note added at that site claimed a bare
variable head was "the only shape that does" reach the fallthrough arm; the qualified
paren-less head reached it too. Corrected, and the claim is now DRIVEN --
`a_body_less_qualified_heads_refusal_reads_alike_in_both_spellings` (axis D, EXACTLY 1 row
fails on back-out, its BARE arm).

ALSO CLOSED INLINE, one line: `wi966_loader_verdict_test`'s recogniser gained
`load_all_per_file(`. Q68AK had added `load_all_with(` with a comment explaining that it
does not contain the substring `load_all(`; the same argument holds verbatim for
`load_all_per_file(`, which is `pub`, is a loader entry point and has two `anthill-todo`
callers. No site needed fixing, which is why the name has to be there now rather than when
one appears.

A SCALAND CONTROL TOOK THREE TRIES, recorded at its row because the first two measured
nothing. The parser fix is `!":-"` BEFORE the colon. `!"-"` before the colon does not fix
the bug at all (`~` skips trivia, so the lookahead lands on the `:` and passes);
`":" ~ !"-"` after the colon does fix it but wrongly rejects a label whose head begins
with a prefix minus. The row that separates the third from the second needed the minus at
the FRONT of the head -- a first fixture wrote `negp(-1)`, where the minus sits in an
ARGUMENT, and all three variants passed it.

FINAL: cargo-test 6261 passed / 0 failed (36 binaries); scaland-sbt-test 527 passed / 0
failed. Back-out axes re-measured over the whole 3978-row `wi_tests` binary: A 4 rows,
B 1, C 1, D 1.

