## Attributes

- id: WI-20260823-VM3YB-fact-effect-t-x-is-documented
- created: 2026-08-23T11:10:14Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-25T22:34:53Z

- acceptance: cargo-test

## Description

`fact Effect[T = X]` IS DOCUMENTED AS THE REGISTRATION AND CHECKED AT NO SITE. An effect
row may name any sort; nothing asks whether it was registered, so a MISSPELLED label is a
silent new effect rather than an error.

`stdlib/anthill/prelude/effects.anthill:21` states the rule — "Effect kinds are registered
via `fact Effect[T = Kind[?]]`" — and `sort Effect { sort T = ? }` exists for it.

MEASURED, twice, while delivering WI-20260823-39AD2:
  * Deleting `fact Effect[T = Res]` from `wi329_handler_discharge_test`'s DECLS leaves
    that file at 21/21. Its `Res` label is used in effect rows throughout.
  * Deleting `fact Effect[T = Reg]` from `wi698_row_param_refinement_test` leaves it at
    38/38.
And the sharper form, found by /code-review: a fact whose FUNCTOR does not resolve loads
SILENTLY — `fact NoSuchSortXyz[T = Reg]` reports no error, and the wi698 fixture shipped a
whole review cycle with `Effect` missing from its import list, registering nothing at all
while its comment claimed a registration. The suite was green throughout.

THE POPULATION IS SMALL AND LOPSIDED, which is why this is a census before it is a fix:
only SIX `fact Effect[…]` exist in the entire tree (`External`, `Modify[?]`, `Error[?]`,
`Suspension`, `Branch`, plus `Model` / `Filesystem` in the guardians vocabulary), while
effect ROWS across stdlib and examples name many more labels — `Clock`, `ConsoleOutput`,
`ConsoleError` among them — none of them registered. So switching the check on refuses
working programs until the registrations are written, and WHICH of the unregistered labels
are legitimate effects is the actual question.

TWO SEPARABLE DEFECTS, and the second is the wider one:
 1. An effect-row label that names no registered effect is admitted.
 2. A `fact` whose functor does not RESOLVE is admitted silently. That is not specific to
    `Effect` — it is a general loud-over-silent hole in fact loading, and it is what made
    (1) invisible in review. Measure whether it has its own owner before folding it in
    here; it may deserve its own ticket and be the more valuable half.

ACCEPTANCE: an effect row naming an unregistered sort is REFUSED, naming the label and
`fact Effect[…]`; every unregistered label currently in use across stdlib / examples /
`rustland/anthill-todo/anthill` is enumerated in the ticket and either registered or
reported as deliberately exempt; a control names which rows fall when the check is backed
out; the two "NOT load-bearing" notes WI-20260823-39AD2 left in `wi329_handler_
discharge_test` and `wi698_row_param_refinement_test` are removed once the fact is
load-bearing.

## Changes

### 2026-08-25T16:54:37Z — feedback — claude

THE CENSUS, and it inverts the ticket's premise. The ticket counted `fact Effect[...]` and
found six, concluding that `Clock`, `ConsoleOutput` and `ConsoleError` were unregistered
and that switching the check on "refuses working programs until the registrations are
written". IT MISSED THE SECOND SPELLING. `provides Effect[T = K]` inside a sort is a
registration too -- `load_provides_clause` and `load_fact`'s `maybe_emit_fact_provides_info`
both land one `SortProvidesInfo` provision of `Effect` -- and that is how `Clock`
(time.anthill:16) and the three Console kinds (console.anthill:35-37) register. So the
question "WHICH of the unregistered labels are legitimate effects", which the ticket called
the actual work, HAS NO SUBJECTS: there are none.

REGISTRATIONS IN THE TREE -- eleven, not six:
  fact     Modify[?] / Error[?] / Suspension / Branch  prelude/effects.anthill:190-193
  fact     External                                     prelude/external.anthill:42
  provides Clock                                        prelude/time.anthill:16
  provides ConsoleOutput / ConsoleError / ConsoleInput  prelude/console.anthill:35-37
  fact     Model / Filesystem                           examples/guardians/lib/vocabulary.anthill:102-103

LABELS IN USE. Measured with a temporary census pass over every `.anthill` tree that
loads -- stdlib, examples/github-todo, examples/guardians/lib, examples/classic-mini/{ancestor,
map-colouring}, examples/sql-store, examples/webots-modelling/lf1, all four anthill-testcases,
anthill-cpp-gen/anthill, anthill-stl/anthill, rustland/anthill-todo/anthill -- classifying
each declared row element by `type_head`. Widest tree (anthill-todo) carries 437 row
elements; stdlib alone 91, by head form: 30 sort_ref, 29 parameterized, 21 engine variable,
11 receiver projection `s.E`.

  UNREGISTERED NAMED LABELS: ZERO, in every tree.

  DELIBERATELY EXEMPT, and each is a position that names no kind rather than a label
  granted a pass:
    * a sort's own effect ROW PARAMETER. `effects E = ?` (WI-320) lowers to a type
      parameter, so `effects E` heads as a SortRef to `W.E` -- told apart from a sort
      reference only by its SortAlias. Seven live in the prelude: Function.E, Iterable.E,
      FiniteCollection.E, MappedStream.EF, MappedStream.ES, Iteration.Effect,
      PersistentCollection.Effect.
    * the engine's own variables (opened row params) and a receiver projection `s.E`
      (Stream.head/tail/isEmpty/find/takeN/splitFirst, FiniteStream, LogicalStream,
      Relation). Rows in waiting; whatever they ground to was judged where it was WRITTEN.

WHAT ELSE THE CENSUS DECIDED. Reading registrations off `Effect`-headed CLAUSES is not
merely a redundant second leg, it is WRONG: it finds the five bare registrations and misses
`Modify` and `Error`, because `fact Effect[T = Modify[?]]` carries that binding
POSITIONALLY in the raw head (`Fn{Modify, pos:[?]}`), which `type_head` reads as malformed.
Only the provision path's `canonicalize_fact_binding_value` re-lowers it onto the base
sort's declared params (WI-449). Measured 5-of-11 vs 11-of-11. The pass therefore has ONE
leg -- `all_provisions` -- and both source spellings reach it.

DEFECT 2 HAS AN OWNER, so it is not folded in. `fact NoSuchSortXyz[T = Reg]` loading
silently is not a hole specific to facts-with-brackets: `remap_name_str_inner`'s NotFound
arm ends at `symbols.intern(name)`, and its own comment already names the two sites that
owe a refusal there -- "`scan_rule_goal` (a rule head) and `load_fact` (a fact head)". That
is WI-20260821-RDGQC's FIRST MEASURED BULLET, verbatim ("A FACT HEAD ... the head reaches
`remap_name_str`'s bare `intern(name)` fallback"), and RDGQC's acceptance already requires
the fall-through to be "a located diagnostic, not silence". Folding it here would write a
second policy for a question that ticket exists to state once. Measured while confirming
it: a rule-BODY goal naming nothing IS already loud; a fact head is silent in every shape
(bare, nullary, paren-args, bracket-args, absolute-dotted). The half that IS closed here is
its effects consequence -- the wi698 spelling (`fact Effect[T = Reg]` with `Effect`
un-imported, registering nothing) now fails LOUDLY at the label, pinned by
`an_unimported_effect_registers_nothing_and_the_label_is_refused`.

### 2026-08-25T22:34:35Z — feedback — claude

DELIVERED. `typing::check_effect_registration`, run from `load_phase_inner` beside
`check_modify_targets`: an effect row's label must name a REGISTERED effect kind, load-
blocking. Reads ONE relation -- `SortProvidesInfo` provisions of `Effect` -- which both
source spellings land in. Spec §5.5 and `prelude/effects.anthill` say the rule; 14 rows in
`wi_vm3yb_effect_registration_test.rs` drive it, five of them red when the pass is backed
out and the rest boundary rows that pass either way by design (stated at the file head).

THE FIXTURE POPULATION WAS THE REAL WORK, and it is what the ticket's "the population is
small and lopsided" got backwards. `.anthill` sources: ZERO unregistered, every tree. RUST
FIXTURES: 15 sites across 6 files, all of the same idiom -- a locally declared `sort Boom {
entity Bang }` (or `sort Error`) used as a label and never registered -- surfaced by the
suite as 15 failures across `wi067` / `wi478` / `wi573` / `wi592` / `wi1125` / `parse_test`.
Each now carries `fact Effect[T = Boom]`. One deserves naming: `parse_test`'s
`test.wi342b` declares its OWN nullary `sort Error` and imports only `Int64`, so `effects
Error` there never meant `anthill.prelude.Error` -- it read like the prelude's at a glance
and was an unregistered local sort. That is the confusion this check exists for, found in
the tree rather than in a fixture written to demonstrate it.

FROM /code-review (high), six findings, all addressed; the first changed behaviour:
 1. THE EXEMPTION WAS TOO WIDE. `resolve_sort_alias(base).is_some()` was meant as "a row
    parameter is a hole" and matched EVERY `sort X = Y`. Two verified holes:
    `sort Nope = Boom` + `effects Nope`, and `effects E = Boom` + `effects E` -- the second
    a documented spelling (`effects-runtime.anthill:6`) whose bound is judged NOWHERE else,
    since the declaration site is not walked. An alias is now FOLLOWED to what it names;
    only a chain bottoming out in a hole is exempt, which falls out at the `type_head` match
    rather than needing an arm. Two new test rows; the corpus is still clean under it. The
    prelude's seven row parameters are all holes, which is why nothing in the tree
    exercised the distinction.
 2. The repair advice named the kind SHORT with no "where", so for a sort-NESTED kind it
    sent the author to a namespace-level line yielding `unresolved name`. It now says where
    the short name is in scope, and `the_repair_the_message_names_actually_loads` drives
    the advice by applying it.
 3. Docs overstated `[?]`. Registration keys the BASE SORT, so `fact Effect[T = Modify]` and
    `[T = Modify[?]]` register the same thing -- the argument is inert both ways. §5.5 and
    effects.anthill now say so instead of implying a distinction.
 4. The `Effect`-has-no-type-parameter guard returned empty -- an inert checker, this
    ticket's own defect re-created. Now a LoadError. Its neighbour (no `anthill.prelude.
    Effect` at all) stays quiet on purpose: `Effect` is not pre-registered by
    `register_stdlib_scopes`, so that arm means a KB with no prelude.
 5. A second walk of every `OperationInfo` fact beside `check_modify_targets`. Measured
    rather than argued: 0.98/1.11/1.17 ms against a `type_check_sorts` mark of 806 ms/1.77
    s/1.01 s -- ~0.1%, same order as the neighbour (0.67-0.81 ms). Not merged: the two ask
    different questions of one row and report at different sites.
 6. Dead `Effect` imports in namespaces that needed none -- removed. (The removal pass was
    itself too eager once: `color_program` in wi1125 owns a namespace header whose spliced
    tail carries the registration, so its import is needed and is now commented as such.
    Caught by the suite.)

TESTS: full workspace via rustland/scripts/test.sh -- 36 binaries green; `wi_tests`
3488/3488, `parse_tests` 452/452, `cli_tests` 163/163, `cmd_tests` 248/248, cpp-gen /
smt-gen / rust-gen / stl / doc-tests all 0 failed.

CHECKED AGAINST UPSTREAM: origin/main is 5 commits ahead and adds
`stdlib/anthill/prelude/division.anthill`, whose rows are `Error[DivisionByZero] :- eq(b,0)`
-- registered, and its stdlib loads clean under this pass (`anthill load --no-stdlib` over
an `origin/main` archive). The merge is a TEXT conflict only, in `effects.anthill`,
`typing.rs`, `load.rs` and `wi_tests.rs`.

NOT DONE, and routed rather than dropped: defect 2 (a fact whose functor resolves to
nothing loads silently) belongs to WI-20260821-RDGQC, whose first measured bullet is that
same bare-`intern` fallback at a fact head; the finding is recorded there with the shape
table and the `fact Effect[...]` witness.

