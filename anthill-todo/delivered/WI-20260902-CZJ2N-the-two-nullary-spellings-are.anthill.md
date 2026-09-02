## Attributes

- id: WI-20260902-CZJ2N-the-two-nullary-spellings-are
- created: 2026-09-02T04:12:15Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-02T10:22:30Z

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

## Changes

### 2026-09-02T06:58:41Z — feedback — claude

IMPLEMENTATION PLAN (design settled with the user, 2026-09-02).

THE DECISION: POSITION 1, KEYED ON THE POSITION AND NEVER ON THE SPELLING. In every
LOGICAL position -- rule head, fact head, rule-body goal, query pattern, proof step -- a bare
name IS the nullary application: `rule holds :- b` defines `holds/0`, and `:- holds`,
`:- holds()`, `fact holds`, query `holds` are ONE term. The "reference" reading survives only
where the slot's EXPECTED TYPE asks for the unapplied thing -- an arrow slot (eta, 5.4), a
relation-valued argument (052), a sort in a type slot (WI-391) -- and there it is the
type that decides, exactly as 719FJ ("the position decides"), J38JE (a Bool expression in
goal position is a condition), WI-391 and WI-511 already decide their corners. The
alternative (bare = reference, `p()` = application, two terms) was rejected: it has to refuse
or re-read `rule holds :- …` / `fact yes` / `fact Store` / `fact Monoid` (23 sites in the
test corpus, spec line 4920), it cannot be stated without kind-dependence (WI-511 already
merged the two for sort-nested ctors, so it either undoes WI-511 or keys on the declaration
site -- the load-order-sensitive gate mod.rs:5495 warns about), and it keeps every silent row
below unless each collision is separately made loud.

MEASURED TODAY (goal position unless said; CLI probes on the delivered 719FJ tree):
  sort-nested nullary ctor `Color.red`   red == red()  (WI-511 canon)
  namespace-level `entity red`           Ref(red) != Fn{red}: `fact red` invisible to `:- red()`
  nullary predicate                      aa 1, ab 0, ba 0, bb 1 (this ticket's fixture)
  nullary Bool op `flag`                 `:- flag` -> 0 silently, and `not(flag)` SUCCEEDS
                                         (a wrong answer); `:- flag()` -> condition (WI-580)
  nullary op in a data slot              `?v <=> seven` binds the SYMBOL; `?v <=> seven()` -> 7
  fielded entity `:- account`            silent 0 -- a phantom `account/0` atom (`fact account`
                                         answers it); `account()` -> all-fields-fresh (8.3)
  parametric sort as fact head           `fact Monoid` already == `Monoid[?]` (spec l.4920,
                                         `unwrap_spec_view` takes `Ref(s)` as no-bindings)
  `rule tau <=> 7 [simp]`                fires nothing (P85Z7 gate; 5.3 calls it a trap)
  undeclared equation subject + citation bare: refused "names nothing"; paren: mints, answers 0
So it is one gap on five kinds, wrong (not merely missing) on two of them, and the one kind
that already has the merge is gated on WHERE the entity was declared.

CANONICAL FORM: `Term::Ref(f)` for EVERY nullary application. `Ref` is where WI-391 and
WI-511 already point and where the loader's `Ident` arm (load.rs:19999) lands every resolved
bare name; picking nullary `Fn` instead would reverse two shipped decisions for nothing. The
ticket's fix direction -- edit four converters -- is the wrong layer: with the canon at the
store the four converge without per-site edits, and each only needs its `Ident`/`Ref` arm
CHECKED for a "reference, not application" assumption.

STEP 0 -- CENSUS, WRITERS AND READERS, BEFORE ANY CODE. The anthill-todo store is persisted
anthill, so it is in the population. (a) rule-body GOALS and DATA SLOTS naming a nullary op,
a fielded entity, or a namespace-level entity BARE, in stdlib/, examples/, tests/, and
anthill-todo/ -- these are the B/C/F populations and each hit is a behaviour change to read
before it moves; (b) `rule x() <=> …` with `x` undeclared (E); (c) the 23 bare
`fact x`/`rule x :-` heads (they should simply start answering `x()` goals -- pick two as
fixtures). `grep -c` first, no `| head` (a truncated census is the known footgun).

STEP 1 -- STORAGE CANON (rustland, kb/mod.rs). `alloc` (2571): rewrite `Fn{f,[],[]}` ->
`Ref(f)` UNCONDITIONALLY -- the `is_constructor_symbol` read at 2591 goes. `find_term`
(2566): canonicalize the same way (it deliberately does not today, so a lookup of the
un-canonical shape misses a term that is present). Add a `debug_assert!` in the store that
no nullary `Fn` is ever interned, said at the site: full unrepresentability (non-empty args
by type) would reach into the parse IR and is not worth it. `is_constructor_symbol` STAYS --
66 mentions across 12 src files ask the real question "is this a constructor" (pattern
typing, value-sort membership at typing.rs:61835/61912); what goes is every read of it that
picks `Ref` versus `Fn` for a NULLARY head: `alloc`, `functor_view_head`,
`make_name_term_from_sym`, `resolve_qualified_name_term` (the two rustland/CLAUDE.md names),
node_occurrence.rs:3613. Census the 66 for any other shape decision keyed on it.

STEP 2 -- ONE NULLARY VIEW HEAD (kb/term_view.rs, kb/discrim.rs, kb/typing.rs). DELETE
`ViewHead::Ref` (term_view.rs:56) and read `Term::Ref(s)` / `Value::SymbolRef` / a nullary
`Entity` as `Functor{Some(s), 0, 0}`; `functor_view_head` (106) loses its gate. The compiler
then lists the 74 `ViewHead::Ref` readers, and the 130 `Functor` readers get the bare
spelling for free -- the WI-580 hook (resolve.rs:1542), the bodied-op-call readers
(resolve.rs:3713/3756), the simp head match (`fire_simp_equation`, resolve.rs:3977).
discrim.rs: `DiscrimKey::Ref` (37) is deleted; its six sites (312, 420, 566, 822, 1079 and
the test at 1332-1347) key `Functor(f) -> Arity(0)` like every other application.
typing.rs `type_head` (58937): `is_bare_ref` becomes "functor with pos 0 and named 0", the
`_ if is_bare_ref => SortRef(f)` arm keeps its meaning, and the trailing `_ => Error` that
documented "a no-arg `Fn{S}` of an ordinary sort is malformed" is now unreachable -- delete
it and its comment. The typer readers at 61835/61912 that split `Ref(ctor)` from `Ref(S)` by
KIND stay right; the new population they receive is `Ref(op)` where a nullary `Fn{op}`
arrived before (61911 read it as `*functor`) -- check each reaches the same answer.
CONTROLS FOR STEPS 1+2 (one change, two back-outs): gate restored in `alloc` alone ->
the 2x2 splits again (aa 1, ab 0, ba 0, bb 1); step 2 backed out with step 1 in ->
`?v <=> seven()` REGRESSES from 7 to the symbol (the view merge is what keeps the paren
spelling a call once it is stored as `Ref`), and a `fact holds` stops answering `holds()`
because the discrim keys split.

STEP 3 -- THE SEMANTICS, ONE FIXTURE EACH (every fixture DRIVES the goal and asserts the
VALUE; each names the rows its back-out fails).
 A. NULLARY PREDICATES. Automatic from step 1. Fixture: this ticket's 2x2 -> 1 1 1 1; the
    719FJ MIXED fixture (`rule tgt()` inside `nsx` beside `rule nsx.tgt :- b(1)`) answers
    both clauses from ONE goal spelling. Test `the_two_nullary_spellings_are_still_two_terms`
    is renamed to say they are one and its assertions flipped.
 B. NULLARY BOOL OP AS A GOAL. Once bare reads as `Functor{flag,0,0}`, `declared_arity ==
    0` and `bare_bodied_bool_relation` (resolve.rs:8518) take it. Fixture: `operation
    flag() -> Bool = true`; `r1(1) :- flag`, `r2(1) :- flag()`, `r3(1) :- not(flag)`,
    `r4(1) :- not(flag())` -> 1 1 0 0. Today r1 -> 0 and r3 -> 1: the wrong-answer row, and
    the one the fixture must assert. The typer twin `check_goal_atom_reading`
    (typing.rs:65632) must read the same head -- assert its verdict on both spellings.
 C. NULLARY OP IN A RULE-BODY DATA SLOT IS A CALL. `?v <=> seven` -> 7, matching 5.4's
    op-body rule (`check_bare_ref`, typing.rs:6607, already gives a bare nullary op the
    zero-arg-call TYPE). Automatic from step 2 at the resolver; the rule-body typer must
    agree. Fixture: `c1(?v) :- ?v <=> seven`, `c2(?v) :- ?v <=> seven()` -> 7, 7. Step-0
    hits in the corpus that RELIED on binding the symbol are rewritten, not accommodated.
    ACCEPTED CONSEQUENCE, pinned by a fixture rather than left to be found: in a rule-body
    data slot the two spellings are one term, so an explicitly applied nullary op against a
    NULLARY-ARROW slot (`applyN(seven())` where `applyN(f: () -> Int64)`) now reads as eta
    where today it is a type error. Op bodies keep 5.4 as written (an `Apply` node and a
    `VarRef` node are two shapes there). The reach is one slot type times one author error.
 D. `[simp]` HEADS. `rule tau <=> 7 [simp]` fires exactly like `tau()`: the head match reads
    the canonical head (step 2). P85Z7's `a_bare_equation_subject_introduces_nothing_and_-
    fires_nothing` FLIPS -- `Bare.drive` 1 -> 7 -- and the 5.3 l.2086 trap "a nullary head
    must carry its parentheses" is deleted; this ticket's own "must stay green" clause
    protected exactly the gate Position 1 removes and is withdrawn (below). ADJACENT AND
    FOLDED IN: the op-body CALL SITE. A bare `tau` in an operation body is a `VarRef` that
    `simp_rewrite::is_rewritable` (490) never treats as a redex, so today the rewrite reaches
    `tau()` and not `tau` (5.3 says so). Property to deliver: ONE node shape reaches the
    rewriter for both spellings. Preferred: elaborate the zero-arg-call reading in
    `check_bare_ref` into the same `Apply` node `tau()` produces, so simp, eval and codegen
    see one shape; fallback if that elaboration is not local: teach `is_rewritable`/the
    firer that a `VarRef` of a nullary op is the redex `op()`. Fixture: `operation drive2(n)
    = tau` beside `drive(n) = tau()` under `rule tau() <=> 7 [simp]` -> 7, 7.
 E. AXIS-C MINTING AGREES ACROSS SPELLINGS -- AND THIS CORRECTS THE DESIGN NOTE. I had said
    "refuse an undeclared equation subject in both spellings". That is wrong: an
    equation-defined name is a spec'd feature -- 5.3 l.2022 (D0EXD) prescribes `operation`
    as "the declaration of an equation-defined name", the loader stamps the subject
    `SymbolKind::EquationFunctor`, and `LoadError::UnreducedEquationFunctor` (load.rs:364,
    WI-898) is its own loud channel for a citation the rewriter left standing. Refusing at
    arity 0 only would be a new spelling-dependent rule; refusing at every arity changes
    061. So E is: the bare spelling MINTS exactly as the paren one. Delete the
    `introduced_by == RuleIntroduction::Predicate` guard on the `Term::Ident` arm at
    load.rs:6493 (its comment's justification -- "a `[simp]` head is an APPLICATION, so
    `rule tau <=> …` matches no redex" -- is the sentence Position 1 deletes). The
    `Predicate`-only skip at 4910 (cross-file predicate assembly) is a different question
    and stays. P85Z7's `a_bare_equation_subjects_citation_stays_loud` flips: the bare
    undeclared subject now loads and its citation answers what CONTROL 1 answers today. The
    fixture is a PAIR: `rule tauX <=> 7 [simp]` and `rule tauX() <=> 7 [simp]`, each with a
    rule-body citation and an op-body citation, byte-identical verdicts, plus the absolute
    values (op body -> 7 via the rewrite; rule-body goal -> 0, an EquationFunctor owns no
    clause, WI-898). Whether a rule-body citation of an equation functor should be loud is
    CONTROL 1's question at every arity and is not this ticket's.
 F. BARE FIELDED ENTITY IN A LOGICAL POSITION = THE PATTERN `account()` (F2). Chosen over
    keeping the phantom `account/0` (today) and over refusing: it is what the spec already
    does one level up -- `fact Monoid` in a sort body IS `fact Monoid[?]` auto-bound, and 8.3
    says the type-level counterpart of the partial pattern is expansion during unification
    -- so F2 makes the value level match. `fact account` = `fact account()`, the universal
    fact that is legal today. MECHANISM: NOT in `convert_term_inner`'s `Ident` arm -- that arm
    serves data slots too, where `Ref(WorkItem)` must stay the sort-as-value
    (`facts_of(kb(), WorkItem)`, `check_bare_ref`'s free-standing-entity arm), and
    `expected: None` cannot tell "a goal" from "a data slot of unknown type". Expansion goes
    at the LOGICAL-POSITION entry points, one helper called from each: the rule-head
    converter, `build_body_atom_occurrence_inner` (22437), `convert_query_term` (16596), the
    fact-head path, `encode_proof_step` (28649) -- a converted head that is `Ref(e)` with `e`
    a fielded entity becomes the 8.3 expansion, sharing the `Fn` arm's fill (fresh vars;
    `none()` for optional fields where the arm does that). It must run BEFORE indexing:
    `Ref(account)` and `account(?,?)` key differently, so unification-time expansion cannot
    do it. `subject_name_term` (19293) doc rewritten. Fixture: `entity account(id: Int64,
    name: String)`, `fact account(id: 1, name: "a")`, `f1(1) :- account`, `f2(1) :-
    account()` -> 1 1 (today 0 1); `fact account` bare + goal `account(id: 5, name: ?)` -> 1
    (today 0); query pattern `account` through `convert_query_term` -> the pattern; proof-step
    citation of a bare nullary predicate resolves. CONTROL that expansion is logical-position
    only: `f3(?t) :- ?t <=> account` still binds the reference, and the reflect
    `facts_of(kb(), WorkItem)` corpus tests stay green.

STEP 4 -- PERSISTENCE, CODEGEN, EVAL. persistence/print.rs (1070/1158/1163) already prints
`Ref` as the bare name; after step 1 no nullary `Fn` exists to print, so every nullary
prints bare -- pick that and say so. term_ser.rs 613/622/651 already READS a bare name to
`Ref`; item_per_file_store.rs 1383/2356 and document.rs 1446/1472/1542 read `Ref | Ident`
alike. RETRACT KEYS (indexed_file_store.rs 188/248 compare `Ref` by symbol): both spellings
now re-read to one term, so a store written by the OLD printer with `p()` must still be
retracted by key `p` -- fixture: a hand-written `p()` fact file, load, retract, assert
gone. codegen/rust.rs (its one `Term::Ref` site): a `Ref` to an OPERATION must emit a
call, not a symbol reference. eval.rs:3956 `value_functor` already reads all three carriers
alike -- no change, verify by the C fixture.

STEP 5 -- SCALAND MIRROR. `KnowledgeBase.alloc` (61) is a plain `terms.alloc` with NO canon
today: add the nullary `Fn -> Ref` rewrite in `TermStore.alloc` (term/TermStore.scala:17),
the one store entry point (there is no lookup-by-shape to mirror `find_term`).
`TermView.functorViewHead` (138) loses the `isConstructorSymbol` gate -- delete
`ViewHead.Ref` (6 readers) as in step 2. `discrim/SubstTree.scala` keys `Term.Ref` directly
(51/102/151/218) -> `RefKey` (defined at 17, 7 mentions) goes, functor/arity-0 keys instead. `isConstructorSymbol`
(KnowledgeBase.scala:235) stays for its other readers, census as in step 1. Tests:
`TermViewTest.scala`, `load/LoaderTest.scala` pin the gate and flip; port the A/B/C/F
fixtures that scaland's feature set can drive. Acceptance stays `sbt test`.

STEP 6 -- SPEC (docs/kernel-language.md). 5.3 l.2058: rewrite the P85Z7 paragraph -- the
"still two TERMS" sentence goes, the rule becomes "a bare name in a logical position IS the
nullary application, on the predicate AND the equation path"; the "EQUATION side is the
opposite rule … that gate is load-bearing" paragraph goes. 5.3 l.2086: delete the trap "a
nullary head must carry its parentheses" and the "rewrites `tau()` and not a bare `tau` call
site" sentence (D). 5.4 l.2333: the op-body zero-arg-call rule now also names rule-body data
slots (C), with the arrow-slot eta exception stated as type-directed. 6.1 (3069-3107): fact
heads -- `fact p` and `fact p()` one term; `fact E` of a fielded entity is `fact E()`. 8.3
l.4139: "bare `account` without parens remains a reference" becomes "in a type slot or a
data slot typed as a sort/Type; in a logical position it is the pattern `account()`". 8.6:
query patterns say the same. Every edit is loud -- what changed and from what.

STEP 7 -- TESTS THAT FLIP, TESTS THAT ARE NEW, WHAT EACH BACK-OUT FAILS.
 flip: `the_two_nullary_spellings_are_still_two_terms` (A); P85Z7
 `a_bare_equation_subject_introduces_nothing_and_fires_nothing` 1 -> 7 (D) and
 `a_bare_equation_subjects_citation_stays_loud` (E), header axes A-D rewritten; the
 in-crate gate pins term_view.rs:3259 and discrim.rs:1342-1347; any typing test pinning
 "no-arg `Fn{S}` is malformed".
 new: B, C (+ the eta row), D call-site, E pair, F, retract-key round trip.
 back-outs: step 1 gate -> A splits; step 2 -> C's paren row regresses AND `fact holds`
 stops answering `holds()`; B hook path -> r1 0, r3 1; F helper at ANY one of the entry
 points -> that position's row (name all four, one row each); D call-site -> drive2 1;
 E guard restored -> the bare half of the pair refuses.

ACCEPTANCE, REVISED: (1) the 2x2 -> all 1 and the 719FJ mixed fixture answers both clauses
from one goal spelling; (2) B/C/D/E/F fixtures above green with their controls named at the
site; (3) P85Z7's `a_bare_equation_subject_introduces_nothing_and_fires_nothing` is NOT kept
green as written -- it flips to 7, and the spec trap it guarded is deleted (this replaces the
clause in the description); (4) `fact account` and query `account` mean the 8.3 pattern
(F2), and the 8.3 sentence is edited loudly; (5) both implementations; cargo-test via
rustland/scripts/test.sh and scaland `sbt test`; `/code-review` before commit.

ORDER AND SIZE. Step 0 first (it decides how many corpus edits ride along). Steps 1+2 are
one compiler-led change and land together with A's fixture. Then B, C, F (the loader helper),
then D, E, then step 4, scaland, spec. Risk sits in the step-0 census (a bare nullary op in a
data slot that meant the symbol) and in the persistence writer/reader pair -- not in the
mechanical half.

### 2026-09-02T09:26:33Z — feedback — claude

STEP 0 — THE CENSUS, and it moved two of the plan's decisions.

INSTRUMENTED, not grepped: a probe in `convert_term_inner`'s and
`build_body_atom_occurrence_inner`'s `Ident` arms, logging every resolved bare name whose
symbol is a nullary op / a fielded entity / a nullary entity, with `in_body_goal` and a
`file:line`. Run over the embedded stdlib and then over the whole `cargo test --workspace`
corpus (563k rows, 1614 UNIQUE).

  NULLARY_OP           38 sites / 19 symbols, ALL at `convert_term_inner`, NONE at a body
                       atom. The stdlib's (`Additive.zero`, `Multiplicative.one`,
                       `BoundedLattice.top`/`bottom`, `Map.empty`, `Ring.zero`/`one`,
                       `VectorSpace.vec_zero`) are all EQUATION HEADS — patterns, where
                       merging the spellings has no content. `Int64.minValue`/`maxValue`
                       at `int64.anthill:61` is a CONSTRAINT body. The `smoke.*` /
                       `test.wi1063` / `test.wi1078` ones are OP BODIES (eta), untouched.
  NULLARY_ENTITY      838 — constructors, already merged by WI-511.
  FIELDED_ENTITY      660 — `some`/`cons`/`pair` reached as MATCH-PATTERN names, not
                       logical positions. ZERO fielded-entity hits at `body_atom`.
  subject_name_term     0 — no dotted paren-less citation names a nullary op or entity.

So step C's risky population — a bare nullary op in a rule-body DATA slot — is EMPTY in
stdlib/, examples/, rustland/ tests and anthill-todo/. What C moves is new code only.

(b) `rule x <=> …` with `x` undeclared: 1 in .anthill, 7 in .rs fixtures.
(c) bare `fact x` / `rule x :-` heads: 3 in .anthill (`safety_gps.anthill:82`,
`wi754/props.anthill:11,12`), plus `wi754/multi-query.anthill:8`'s `fact holds`.

CORRECTION 1 — STEP 1's "UNCONDITIONALLY" IS WRONG, MEASURED.
Removing the gate outright makes the STDLIB FAIL TO LOAD. 792 symbols change spelling;
`anthill.prelude.FiniteCollection.collect` stops covering its own `requires` and
`collect.effects` reports `undeclared effect: ?_`. Bisected by exempting `SymbolKind::Sort`
— the stdlib loads again — then traced to `sort_inst_to_value`'s bare-`Simple` arm, whose
own comment states the rule: "Only `Ref`/`Ident` is recognized as a dispatch type-param
WILDCARD (`impl_param_ref`); a nullary `Fn` scores CONCRETE specificity" (WI-387/WI-391,
wi210). `KnowledgeBase::register_self_sort`'s note reports the same thing from the other
side: re-spelling a free-standing entity's name term failed 24 tests with
`expected Type, got WorkItem`.

  THE LINE IS TYPE-HOOD, NOT CONSTRUCTOR-HOOD. `Fn{f,[],[]}` → `Ref(f)` unless
  `has_kind(f, Sort)`. That SUBSUMES WI-511 (a sort-nested constructor carries `Entity`,
  not `Sort`, per WI-926) and is LESS order-dependent than the gate it replaces:
  `constructor_symbols` fills DURING the load — the hazard `register_entity_of`'s note
  measured, `Color` filed under both spellings in one run — while `SymbolKind::Sort` is
  stamped in `scan_definitions` pass 1.

  The ticket's own Position 1 anticipated this ("the reference reading survives … a sort
  in a type slot (WI-391) — and there it is the type that decides"); only step 1's
  "UNCONDITIONALLY" contradicted it.

CORRECTION 2 — THE CANON IS NOT ENOUGH FOR AN OPERATION, and the plan did not say so.
A PREDICATE goal is answered by MATCHING, an OPERATION goal by REDUCING. MEASURED with
the storage canon in and no node change: the WI-580 relational hook fired IDENTICALLY for
`:- flag` and `:- flag()` — same functor, `declared_arity == Some(0)`,
`bare_bodied_bool_relation == true` — and the two still answered 0 and 1. The whole
divergence is the OCCURRENCE shape: a rule body carries occurrences and `reduce_op_value`
opens an `Expr::Apply`, handing anything else back un-reduced. `Loader::nullary_op_call_or_ref`
builds the same `Expr::Apply` for both spellings; `op_info::is_nullary_operation` is the
one owner of "is this name a call", read by three producers (that site, `simp_rewrite::
subst_visit`, `macro_expanded_rhs_head`) that used to tell a call from a name by a stored
shape that no longer exists.

CORRECTION 3 — STEP 1's FIX SITE. The plan put the canon in `KnowledgeBase::alloc`; it is
there, but `resolve_qualified_name_term` (which deliberately BYPASSED WI-511's canon) and
`execute.rs`'s synthesized head reached `terms.alloc` directly. The bypass is removed — a
canon a caller can step around is a second spelling waiting to happen, which is exactly
what WI-1023 had to teach the `Map` key path to tolerate.

### 2026-09-02T09:28:10Z — feedback — claude

WHAT LANDED, AND WHAT DID NOT.

THE DECISION IS POSITION 1, WITH ONE EXCEPTION THE PLAN ANTICIPATED AND STEP 1 CONTRADICTED:
a bare name in a LOGICAL position IS the nullary application, for every name WITHOUT a type
reading. A `SymbolKind::Sort` name keeps both spellings and the SLOT decides (§8.3 / WI-391
/ WI-387) — see the census feedback for the measurement that forced it.

DELIVERED (rustland), each with a driven fixture in
`wi_czj2n_nullary_spelling_test.rs` unless said:

  A  the 2x2 is 1 1 1 1 (`the_nullary_predicate_2x2_is_all_ones`), and the 719FJ MIXED
     fixture answers from either goal spelling
     (`wi_719fj_…::a_predicate_assembled_from_both_spellings_answers_from_either`).
     Written as an INVERTED PAIR after the first draft measured nothing: a nullary goal's
     two clauses produce the same empty substitution and the stream dedups, so "reaches
     both" can never read as 2. Two fixtures with the TRUE clause on opposite sides; 2 of
     the 4 rows fail on the back-out.
  B  `:- flag` runs and `:- not(flag)` FAILS (`a_bare_nullary_op_goal_runs_…`). The wrong
     answer is gone: `not(flag)` used to SUCCEED against a `flag` whose body is `true`.
  C  `?v <=> seven` binds 7 (`a_bare_nullary_op_in_a_data_slot_is_a_call`), asserting the
     VALUE — a count-only row would have been green on the defect, which bound the SYMBOL.
  D  a bare `[simp]` HEAD defines (`a_nullary_simp_head_defines_in_both_spellings`).
     P85Z7's `a_bare_equation_subject_…` flips 1 → 7 and is renamed; wi881's
     `a_bare_nullary_simp_head_never_fires` flips and is renamed. §5.3's trap "a nullary
     head must carry its parentheses" is DELETED.
  E  the mint agrees across spellings. The `RuleIntroduction::Predicate` guard on
     `head_subject_name`'s `Term::Ident` arm is deleted; P85Z7 axis C is WITHDRAWN and its
     row replaced by `a_bare_equation_subject_mints_exactly_like_its_parenthesised_twin`,
     a PAIR over two positions with absolute values (op body → 7, rule-body goal → 0).
  F  F2, at all five logical positions
     (`a_bare_fielded_entity_in_a_logical_position_is_the_pattern`): `fact account` IS
     `fact account()`, `:- account` searches what `:- account()` searches, and the query
     pattern binds BOTH fields. `Loader::convert_subject_term` was already the funnel for
     four of the five (rule head, fact head, sort-body pre-scan, proof step) — the plan's
     "five entry points" over-counted. The DATA-slot control (`?t <=> account` still binds
     the reference) passes either way by design.
  4  persistence: the audit found the retract round trip was BROKEN before and is closed
     now (`p` on disk reloaded as `Ref(p)` while the KB held `Fn{p}`), pinned by
     `a_hand_written_nullary_fact_is_retractable_by_its_bare_key`. `print.rs` needed no
     change — its generic tail already omitted the parentheses. The `reload_faithful`
     `ListLiteral()` branch is NOT dead: `ListLiteral` is a free-standing entity and so
     `SymbolKind::Sort`-bearing, hence canon-exempt.
  5  scaland: the canon in `KnowledgeBase.alloc` (it had NONE — not even WI-511's),
     `ViewHead.Ref` retired, `DiscrimKey.RefKey` deleted with all six `SubstTree` walks
     keying `Functor(f) → Arity(0)`, `makeNameTermFromSym` routed through `alloc`,
     `byFunctor`/`getBuiltin`/`registerEntityOf` and the four reflection builtins reading
     the head off either spelling, and `Loader`'s `Term.Ident` arm promoting a RESOLVED
     name to `Ref` (rustland has always done this; scaland did not, which is what kept
     `ab` at 0 after the canon landed). Two driven rows in `LoaderTest`. 536 green.
  6  spec: §5.3 (both the P85Z7 paragraph and the trap), §5.4, §6.1, §8.3.

NOT DELIVERED, and it is D's SECOND half — the op-body CALL SITE. `operation drive2(n) =
tau` still answers a residual where `= tau()` answers 7, because a bare name in an
OPERATION body lowers to `Expr::VarRef` and `simp_rewrite::is_rewritable` does not treat
one as a redex. The plan's preferred fix is to elaborate `typing::check_bare_ref`'s
zero-arg-call reading into the same `Apply` node — that is a TYPER change reaching every
bare nullary op reference in every operation body, gated on the arrow-slot eta reading
(§5.4), and it is separable from everything above: nothing here depends on it and it has
its own risk. FILED rather than folded in. The spec now states the boundary explicitly
(§5.3: "a bare `tau` call site inside an operation body is a `var_ref` and is still not a
redex, which is §5.4's type-directed reading and a different question from the head's").

CONTROLS, MEASURED OVER THE WHOLE `wi_tests` BINARY (4 020 rows), not a neighbourhood:

  2 — THE NODE ELABORATION (`nullary_op_call_or_ref` always answers `Expr::Ref`).
      EXACTLY 2 ROWS FAIL: `a_bare_nullary_op_goal_runs_and_its_negation_fails` and
      `a_bare_nullary_op_in_a_data_slot_is_a_call`. The 2x2 and the `[simp]` row pass
      EITHER WAY — which is what says the storage canon and the node elaboration are two
      changes and not one with two names. (The three rows that also failed that run —
      `wi202_retrieve`, `wi222_defer_rewrite`, `wi320_bridge_fact` — were failing with the
      change fully in too, and are fixed above; they are not this axis's.)

  1 — THE STORAGE CANON (restore the `is_constructor_symbol` gate): the 2x2, the `[simp]`
      row, `the_two_nullary_spellings_are_one_term`, 2 of the mixed fixture's 4 rows, the
      two flipped P85Z7/wi881 rows, and the in-crate
      `nullary_head_tests::a_nullary_non_constructor_is_one_term_…` /
      `discrim::…::a_nullary_application_matches_its_bare_spelling_for_any_symbol` (its
      `plain` arm). Stated per row at each site.
  3 — THE `[simp]` LHS READ (drop `stored_eq_operand_functor`'s `Term::Ref` arm): fells
      the `[simp]` row on BOTH arms, the PARENTHESISED one included — a regression guard,
      not a second reading of axis 1.
  4 — THE MINT (restore the `Predicate` guard): the `bare` arm of P85Z7's mint pair.

THE SILENT BREAKAGES THE CHANGE CAUSED AND THE AUDIT FOUND — the raw-`Term::Fn` reader
class, ~96 candidate sites swept by three parallel audits plus the suite:

  * `Loader::provides_block_identity` — a `Term::Fn` destructure on a binding block's
    carrier. A NAMESPACE carrier (20 of the 26 reflect mappings) is stored bare, so the
    whole block's `operation_map` was DROPPED: 134 → 114 mappings, and every `?x.y` then
    died `OperationBodyMissing: anthill.reflect.field_access` at eval, on a program that
    LOADED CLEAN. ~50 test failures, one cause.
  * `head_arg_count` — suppressed WI-939 item 4's load refusal for a bodied nullary Bool
    op with clauses.
  * `create_occurrence` — stopped recording `functor_spans` for every nullary predicate /
    operation / equation functor, so their diagnostics lost their location.
  * `typing::collect_op_functors_in_term` — silently dropped WI-702's soundness refusal
    for an EFFECTFUL nullary op in a `[simp]` head.
  * `typing::check_pattern_fragment` — skipped every 0-ary-headed rule entirely.
  * `simp_rewrite::equation_lhs_shapes` — withheld the arity/label diagnostic for any
    functor with a nullary defining equation. Reachable only BECAUSE its sibling
    `stored_lhs_functor` had just been fixed.
  * `resolve::op_call_as_occ`, `simp_rewrite::macro_expanded_rhs_head` + `subst_visit`,
    `smt-gen::classify_head` (a hard `SmtGenError` on any nullary-headed rule),
    `prove.rs::hint_cites_for`, `reflect/bridge.rs::find_entity_schema`,
    `builtins::reflect_replace_named_arg`, `indexed_file_store::pattern_matches` (a bare
    query pattern returned ZERO rows), `typing::type_display_name` (`{Nothing}` for
    `{nothing}`).

TWO DELIBERATE NARROWINGS, stated rather than discovered:
  * The VIEW merges a SORT's two spellings even though the STORE does not, because
    `functor_view_head` has no second head to give a bare name. Every consumer that must
    keep them apart reads the TERM (`typing::impl_param_ref` matches `Term::Ref` /
    `Term::Ident` directly), which is why the stdlib loads. Asserted at
    `nullary_head_tests::a_nullary_sort_name_keeps_both_spellings` and in `map_arena`'s
    key row.
  * `Value::lowers_to_leaf_term` now answers `true` for a 0-FIELD entity, because
    `alloc_from_value` genuinely produces a leaf for one. The predicate restates that
    function; leaving it would be the drift `leaf_lowering_agrees_with_alloc` exists to
    catch.

### 2026-09-02T10:22:19Z — feedback — claude

/code-review (high) — 8 FINDINGS, ALL ADDRESSED. One was WRONG about its consequence and
is recorded as such rather than silently "fixed".

AGREED AND FIXED:
 * THE DOC THEFT (load.rs). The lifted `fill_entity_named_args` had absorbed
   `convert_subject_term`'s whole WI-20260901-719FJ rationale, leaving that function
   undocumented — the known anchoring footgun, invisible to compiler and suite. Restored.
   FIXING IT SURFACED WORSE: an earlier splice had DELETED `pub fn convert_query_term`
   outright. The compiler caught it only because `anthill-cli` calls it by name; nothing
   inside `anthill-core` did. Restored from HEAD with its two CZJ2N edits re-applied.
 * `Value::lowers_to_leaf_term` (execute.rs) LIED, and the reviewer's counterexample is
   exact: a 0-field entity of a `SymbolKind::Sort` functor lowers to `Term::Fn`, not a
   leaf, because that is precisely what the canon EXEMPTS — and this signature has no
   `KnowledgeBase` to ask which functor it has. Reverted to the conservative `false`, and
   the oracle in `leaf_lowering_agrees_with_alloc` weakened to the SOUND direction (a
   `true` must be TRUE — the half `fn_value`'s panic relies on) with `Entity` excluded BY
   NAME from the exactness half, so an `Err`→`Ok` move anywhere else still fails it. New
   row `a_nullary_entity_lowers_by_its_functors_kind` DRIVES both kinds, so the exclusion
   is a measurement and not a hole.
 * `type_head`'s comment still said "a no-arg `Fn{S}` of an ordinary sort is malformed"
   after the widened `is_bare_ref` made that shape `SortRef(S)`. Rewritten to state the
   reclassification and why it is harmless, with `czj2n_nullary_sort_type_head_test`
   driving BOTH halves: the two sort spellings read alike through `type_head`, AND
   `impl_param_ref` — the actual wildcard test, a raw-TERM read — still tells them apart.
   Its second row also pins that the trailing `_ => Error` arm is NOT unreachable, which
   this ticket's plan predicted it would be.
 * SCALAND DIVERGED: it kept the `kind == SymbolKind.Goal` mint guard rustland deleted,
   with a comment restating the §5.3 sentence this ticket removes. Ported;
   `ParenLessNullaryHeadTest`'s row flipped and renamed with its back-out.
 * FORMATTING. Checked every touched `.rs` file's rustfmt delta AGAINST HEAD'S rather
   than absolutely — the tree is not rustfmt-clean, so `--check` is not a gate.
   `execute.rs` and `typing/tests.rs` were clean at HEAD and are clean again; `load.rs`,
   `term_view.rs` and `op_info.rs` are clean; `mod.rs`, `typing.rs` and `smt-gen` are
   dirty at HEAD and my hunks provably do not overlap the dirty regions (line-range
   intersection, not eyeball).
 * FILED, not folded: the equation-functor citation loudness. Deleting the mint guard
   REMOVES a loud case — the bare spelling used to reach WI-1034's "names nothing … can
   NEVER match" and now neither spelling does. One rule at every arity is the right
   direction and the gap it accidentally covered is now unmitigated, so it has a ticket
   and the test site says so.

KEPT, WITH A CENSUS: the reflect repr widening (`reader.rs`). Two shapes move from
`FnRepr(f, [])` to `RefRepr(f)` — a canon-EXEMPT `Fn{S,[],[]}` (the reload-faithful
`ListLiteral()`) and the nullary `Expr::Apply` the loader now mints. The corpus has ONE
consumer of these constructors, `examples/guardians/lib/gate.anthill`'s `repr_name` /
`spec_of_row`, and it reads BOTH arms for a nullary name by its own comment's design — so
the move is invisible to it. The PRINTER is unaffected either way (it reads the raw
`Term::Fn`), so the persistence round trip does not go through here. Both ends documented;
`gate.anthill`'s comment, which stated the WI-436/511 rule this ticket moves, is updated.

DISAGREED ON THE CONSEQUENCE, and the disagreement is measured. Finding 1 said the
`Term::Fn`-gated var-contradiction report means "a sort-scoped rule with a 0-ary head and
contradictory body var types … reported before and now loads clean". DRIVEN on
`wi_9c2pz_per_application_type_params_test`'s own `DECLARED_CONTRADICTION` fixture with
the head rewritten three ways:

    rule bad(?x) :- …   -> 1 contradiction     (both trees)
    rule bad()   :- …   -> 0                   (both trees)
    rule bad     :- …   -> 0                   (both trees)

Something UPSTREAM of that arm already declines a nullary-headed rule — the contradiction
is never flagged, so the branch is not reached — which means the `Term::Fn` gate is not
what suppresses it and closing it fixes no observable behaviour. Closed anyway, because
the assumption is false and the correct read (`rule_sym = kb.head_functor(head)`) was
computed two lines above and DISCARDED; a branch reading a shape the store cannot produce
is a trap for whoever makes the upstream case reachable. Said at the site, as "not
driven", rather than credited as a repair.

FINAL: rustland 6 319 passed / 0 failed (36 binaries, `scripts/test.sh`); scaland 536
passed / 0 failed.

