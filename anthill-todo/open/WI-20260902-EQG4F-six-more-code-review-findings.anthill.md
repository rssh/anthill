## Attributes

- id: WI-20260902-EQG4F-six-more-code-review-findings
- created: 2026-09-02T12:00:08Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T12:00:08Z

- acceptance: cargo-test, scaland-sbt-test

## Description

SIX MORE /code-review FINDINGS ON THE NULLARY-CANON COMMITS (CZJ2N + 719FJ) — NOT RE-MEASURED BY ME.

PROVENANCE AND ITS LIMIT, first, because it decides how to use this ticket. These came
from a `/code-review high` run during WI-20260902-8K4RB, whose scope was
`origin/main...HEAD` — five unpushed commits, wider than the diff being reviewed. I
re-measured only the two findings about 8K4RB's own diff (fixed in that commit) and the
HIGH dotted-citation one (its own ticket, with my own table). The six below are the
reviewer's evidence QUOTED, with the code shape confirmed by reading in one case and
nothing driven in any. TREAT EACH AS A HYPOTHESIS WITH A SITE, NOT A DIAGNOSIS: build the
failing fixture first and drop the ones that dissolve.

1. scaland `discrim/SubstTree.scala:62` (also 114/154/223/300/389) — the index now keys
   `Term.Ref(s)` as `Functor(s)/Arity(0)`, identical to `Fn(s,[],[])`, while
   `KnowledgeBase.alloc:82` deliberately keeps those two DISTINCT for a `SymbolKind.Sort`
   (there is a test asserting `Fn(S) != Ref(S)` — wildcard vs concrete spec identity) and
   `Substitution.unifyMatch:122` still refuses the pair. Claim: a ground
   `:- entity_of(?e, Shape)` retrieves a fact stored with `Fn(Shape)` off the tree walk,
   which for a ground position IS the decision, contradicting `unifyMatch`.

2. scaland `kb/KnowledgeBase.scala:622` — `getBuiltin` now answers through
   `headFunctorOf`, so a NULLARY goal gets a builtin tag; for `BuiltinTag.Not` that
   reaches `stepNaf` (SearchStream.scala:269), whose `Builtins.firstArg:52` falls back to
   `case _ => goal` — the negand becomes the `not` goal itself and a fresh sub-stream is
   made at depth 0, so `maxDepth` never bites. Claim: unbounded recursion, newly
   reachable via 719FJ's dotted spelling (`rule r(1) :- anthill.kernel.not`).

3. scaland `anthill-smt-gen/SmtGen.scala:489` and `:336` — `classifyHead`'s
   `f.posArgs.isEmpty => HeadShape.Bottom` arm is dead now that no zero-arg `Fn` survives
   `alloc`, so a nullary head falls to `HeadShape.Unsupported`; `processBodyGoal`
   likewise hard-errors `non-Fn body goal` for `:- p()`. `Policy.scala` and
   `TacticEmit.scala` were updated for all three carriers; SmtGen is the one missed.

4. scaland `load/Loader.scala:1678` (same at `:1606`) — THE CANON IS SPLIT: `alloc`
   rewrites `Fn(f,[],[])` -> `Ref(f)` unconditionally (modulo the Sort gate) but the
   loader promotes a bare name only `if kb.symbols.isResolved(...)`, so an UNRESOLVED
   name still yields two terms with two discrim keys. Claim: reachable wherever
   `ruleIntroducedFunctor` declines to mint — e.g. a multi-head `rule aa, bb :- base(1)`,
   after which `:- aa` answers and `:- aa()` does not, silently. Note the reviewer's own
   caveat: CZJ2N's 2x2 test uses SINGLE-head rules, which mint, so it passes either way.

5. rustland `anthill-stl/src/reflect/reader.rs:488` — the new
   `Functor{pos_arity:0, named_arity:0} => on_ref` arm is WIDER than the `ViewHead::Ref`
   it replaced, while the inverse walk (`reflect_walk`, ~571) rebuilds `RefRepr` as
   `CoreTerm::Ref`. Claim: a canon-EXEMPT Sort-kinded `Fn{S,[],[]}` (the empty
   `ListLiteral()`) changes `TermId` across a reify round trip, and
   `persistence/print.rs:985` writes the parentheses only for `Term::Fn` — so it
   persists as a bare name and reloads as a name reference, which is the WI-1099 failure
   that arm exists to prevent.

6. rustland `anthill-stl/src/reflect/bridge.rs:267` — CODE SHAPE CONFIRMED BY READING,
   behaviour NOT driven. `find_entity_schema`'s new
   `CoreTerm::Ref(_) | CoreTerm::Ident(_) => return Some(Vec::new())` RETURNS where the
   old `if let CoreTerm::Fn` CONTINUED the scan. Claim: with `fact p` written before
   `fact p(x: 1)`, the scan takes the empty schema off the first row and the `p(x: 1)`
   rows silently vanish. The reviewer's proposed shape is `_ => {}` plus `Some(vec![])`
   only when the whole scan found nothing — which has its own control, since the arm was
   added to fix a real zero-rows bug (its comment records it).

7. rustland `anthill-core/src/kb/load.rs:19375` (LOW) — `create_occurrence` now records a
   `functor_spans` entry for every `Term::Ref`/`Ident`, not only applications. The map is
   FIRST-WRITE-WINS and is the declaration-site fallback (load.rs:15619,
   typing.rs:61317/61480/61574/61731/62301). Claim: an eta reference or data-slot mention
   in an earlier-loaded file claims the span, so a later `DuplicateOperation` / pattern /
   effect diagnostic points at the USE site instead of the declaration.

SPLIT THIS if the measurements diverge — items 1-4 are scaland and 5-7 rustland, and
nothing couples them but the commit they came from.

## Changes

### 2026-09-08T19:39:20Z — feedback — user

ALL SEVEN MEASURED (2026-09-08). Three real, two belong to WI-20260902-JB6RS, two dissolve.
Only item 4 is left open here; the rest are answered below with their evidence.

DELIVERED IN THIS COMMIT — items 2 and 3, both scaland.

 2. CONFIRMED, AND WIDER THAN WRITTEN. `:- anthill.kernel.not` AND the bare one-segment
    `:- not` BOTH die `StackOverflowError`, so 719FJ's dotted spelling is not required —
    CZJ2N alone opened it (a nullary goal is `Term.Ref`, `getBuiltin` reads it through
    `headFunctorOf`, `firstArg` falls back to the goal, the sub-stream re-enters `stepNaf`
    at depth 0). Fixed: `Builtins.firstArg` returns `Option`, and its THREE readers take
    the `None` the way rustland does — `stepNaf` pops the frame, `nonvar`/`ground` return
    `Failure` (they used to read the GOAL as their own argument and SUCCEED silently, which
    the back-out re-measures). Test: `core/…/resolve/NullaryBuiltinGoalTest.scala`.
    A CONTROL THE TICKET DID NOT HAVE: `anthill.kernel.not(un(999))` answers 1 — NAF IS
    reachable in scaland. `DottedParenLessCitationTest`'s note that a rule-body `not(…)`
    "does not reach NAF here AT ALL" was too strong (its four rows vary the NEGAND, all
    written with the one-segment `not`); corrected in place.

 3. CONFIRMED, BOTH HALVES, and `flagP()` gives the SAME error as `flag` — so the
    `posArgs.isEmpty => Bottom` arm is dead for both spellings, not one. Fixed with one
    reader, `SmtGen.goalAsFn`, used by `classifyHead` AND `processBodyGoal` (rustland's
    `occ_as_fn`; its body goals are `NodeOccurrence`s whose nullary `Expr::Apply` already
    answers with empty argument lists, which is why only scaland needed it).
    WHAT IT BUYS, MEASURED: the HEAD half is a capability — `emitSatisfiabilityCheck` on a
    nullary-headed rule went from a hard `SmtGenError` to a 9-line document. The BODY half
    is a DIAGNOSTIC only: a 0-ary PREMISE still does not translate, it falls to the loud
    `unhandled body goal functor`, which is where rustland's own tail leaves it too — what
    changed is that the refusal now names the SYMBOL instead of `Ref(1161)`. That shared v0
    limit is NOT fixed and the test row says so.
    Test: `anthill-smt-gen/…/NullaryHeadAndGoalTest.scala`.

STILL OPEN HERE — item 4, because the repair is a decision and not a patch.

 4. CONFIRMED WITH CONTROLS. `rule lawE4: aa, bb :- base4(1)` (a multi-head rule needs a
    label) leaves `zzE4.aa` resolving to None; `:- aa` answers 1 and `:- aa()` answers 0.
    Controls: single-head `rule cc :- base4(1)` MINTS and both spellings answer 1; a name
    nothing declares answers 0 both ways — so the asymmetry needs a STORED head under an
    unresolved symbol, which is what the multi-head rule supplies.
    RUSTLAND CARRIES THE IDENTICAL `is_resolved` GATE (`convert_term_inner`) AND IS
    UNAFFECTED: WI-1034 refuses the reader at load ("rule-body goal `aa` names nothing"),
    so the split cannot be observed there. The two repairs are therefore: drop scaland's
    `isResolved` gate, or port WI-1034's refusal (which is what makes rustland immune).
    Not chosen unilaterally.

MOVED TO WI-20260902-JB6RS — items 1 and 5 are the SAME decision it already owns
("is the Sort exemption real?"), and answering it here would answer it twice.

 1. Confirmed by reading both sites. Scaland adds one thing rustland does not have: an
    INTERNAL contradiction — `SubstTree.insertWalk` keys `Term.Ref(s)` as
    `Functor(s)/Arity(0)`, identical to `Fn(s,[],[])`, while `Substitution.unifyMatch`
    refuses that pair outright ("Head-kind mismatch … has no shared structure").
 5. MEASURED, and by a different route than the ticket gives. `Fn{Shape,[],[]}` = TermId(14)
    and `Ref(Shape)` = TermId(24) — distinct, as the exemption intends — but
    `reify` → `RefRepr(Shape)` → `reflect` returns TermId(24). Constructor and predicate
    controls round-trip STABLE (both canonicalized), so the loss is exactly at the
    canon-exempt Sort, i.e. §8.3's concrete spec identity becomes the dispatch wildcard.
    The ticket routed this through `persistence/print.rs`; that is WRONG — CZJ2N's comment
    is right that the printer bypasses `reify_walk`. The loss is at `reflect_walk`'s
    `ReflectShape::Ref(sym) => CoreTerm::Ref(sym)`, with no persistence involved. That
    comment censused the repr's READERS and the printer but not the INVERSE walk.

DISSOLVED — items 6 and 7.

 6. THE REGRESSION CLAIM IS FALSE, and the paired back-out says so. Fixture: `fact Marker` /
    `fact Marker(x: 1)` on a canon-exempt SORT name — the only way I could reach the scan at
    all (an undeclared fact functor registers no symbol; a declared entity short-circuits via
    `entity_field_types`; a rule-defined predicate PANICS, see below).
      bare→named   WITH the arm: schema [],  1 of 2 rows | BACKED OUT: schema [x], 1 of 2
      named→bare   WITH the arm: schema [x], 1 of 2 rows | BACKED OUT: schema [x], 1 of 2
      bare only    WITH the arm: schema [],  1 of 1 row  | BACKED OUT: schema None, 0 of 1
    The arm is LOAD-BEARING (bottom row is the zero-rows bug it was added to fix) and the
    truncation is present BOTH ways — it is the pre-existing first-row-wins rule, and the arm
    only swaps WHICH row vanishes. The proposed fix (`_ => {}` plus `Some(vec![])` when the
    scan found nothing) restores bare-only and leaves bare→named at 1 of 2; no row stops
    vanishing. CENSUSED TOO: across the whole workspace suite the scan runs for exactly two
    functors, both with `Fn` heads — NO test drives that arm.
 7. POPULATION ZERO. Instrumented `create_occurrence` to record both the current first-span
    and the pre-CZJ2N (`Fn`-only) first-span, over all of `examples/` (65 files) + stdlib:
    total 62, with_fn_span 61, gained 1, stolen 0. No symbol's declaration span changed. The
    mechanism is real; nothing drives it. Residue is doc drift only — `typing.rs:37773` and
    `:66755` still say `functor_span` "keys off a converted `Term::Fn` FUNCTOR", which CZJ2N
    widened. Not corrected here.

FOUND WHILE PROBING, NOT IN THIS TICKET AND NOT FIXED HERE: `find_entity_schema` does
`read_facts(...).unwrap_or_else(|e| panic!("KB.fields: {e}"))`, so `KB.execute(sort_query(P))`
PANICS for any functor carrying a bodied rule — which is how I first hit the scan. Bridge-only
(core's `lower_query_with` lowers `sort_query` to `is_entity_of` instead) and it predates
CZJ2N (bf7126bc, 2026-07-26). The trait method returns `Result`.

### 2026-09-08T19:52:33Z — feedback — user

/code-review ON THE ITEM-2/3 FIX FOUND TWO SILENT-FAILURE REGRESSIONS THAT THE FIX ITSELF
INTRODUCED. Both re-measured by me, both fixed here with their own controls, before commit.

 A. AN OBLIGATION ON A HEAD THAT BINDS NO RESULT VARIABLE emitted invalid SMT-LIB as
    `Right`. `renderUpperBoundWith` interpolates `resultVar` unguarded, so
    `emitObligation(…flag, 5.0)` produced `(assert (not (<=  5.0)))` — a document Z3
    cannot parse, and `Z3Runner` discards stderr, so it would have surfaced as "not
    unsat". Before the widening the same call was `Left("rule head must be Fn or Bottom")`,
    so reading a nullary head turned a loud refusal into a silent malformed answer.
    THE HOLE IS OLDER THAN THE ARM THAT FOUND IT, and I measured that rather than taking
    the reviewer's framing: `HeadShape.Predicate` — an entity- or comparison-headed rule —
    has ALWAYS left `resultVar` empty and always emitted that exact document. So the
    refusal is keyed on the empty `resultVar`, not on a head shape, and covers both ways
    in. Test row runs `flag` AND `entityHead`; remove the guard and both come back `Right`.

 B. A BARE ENTITY PREMISE WAS SILENTLY DROPPED. `rule bareEntity(?r) :- Params, …` reached
    the entity-destructure arm through the nullary carrier, where the field loop had no
    slot to walk and `return Right(())` claimed it encoded. Measured: the emitted document
    contained no trace of `Params`. This is the unsoundness rustland's own
    `process_body_goal` names at WI-897 — a lift renders a body as an implication's
    antecedent, so a dropped premise WEAKENS it and the spliced lemma is stronger than
    anything proved. Now refused when the citation carries no arguments at all (`Params()`
    is refused identically — CZJ2N made the two spellings one term). Control beside it: a
    real destructure still emits AND still carries its bound field, which is what says the
    guard is not written too wide. NOT FIXED, and recorded at the site: a destructure whose
    slots are all literals binds nothing either and this arm still accepts it.

 C. `firstArg`'s `None` also fires for a goal carrying only NAMED arguments
    (`ground(x: 1)`), which used to `Delay` and now `Fail`. VERIFIED AS PARITY rather than
    accepted as a finding: rustland's `pos_arg` reads `pos_args` alone, so the same shape
    reaches `builtin_ground`'s `None => Failure`. The doc said "carries none" where the
    guard tests "no POSITIONAL argument"; corrected, and the shape now has its own test row
    so it is censused instead of rediscovered.

 D. `DottedParenLessCitationTest`'s row was still NAMED "negation in a rule body does not
    reach NAF, for any spelling" after its comment was corrected — the name is what shows
    in test output. Renamed to "a ONE-SEGMENT `not` does not reach NAF, for any NEGAND
    spelling", with the two other references (its own header, `Loader.scala:2162`) updated.

SUITE STATE AT COMMIT: scaland core 570 passed / 2 failed, smt-gen 31/31, scala-gen 1/1.
The two failures are `codegen.scala.BootstrapTest` (`WI-1066 CORPUS CONTROL` and `WI-1055`)
and are PRE-EXISTING — verified identical with every change of mine stashed. Not touched
here and not caused here.

### 2026-09-08T20:07:42Z — feedback — user

SECOND /code-review ROUND, ON THE FIXES FROM THE FIRST. Six more, all re-measured by me
before acting; four were live defects, one was MY OWN WRONG MEASUREMENT CLAIM, one was a
parity divergence the first round's fix created.

 E. THE INEQUALITY ARM SWALLOWED ITS ERROR (HIGH, pre-existing, inside the hunk this ticket
    rewrote). It computed the `for/yield` and then `return Right(())` regardless, so a
    `translateExpr` failure lost its error AND skipped the `assertions +=`. Measured:
    `lte(?b, weirdo(1.0))` emitted a document with no `<=` in it at all, returned as
    `Right`. Same antecedent-weakening class as B above. Now returns the `Either`.

 F. MY OWN GUARD FROM B WAS TOO NARROW. Written `posArgs.isEmpty && namedArgs.isEmpty`, it
    let a POSITIONAL destructure through — and the field loop walks `namedArgs` only, so
    `Params(?b)` bound nothing and left `?b` a FREE var in the encoding. That is worse than
    the bare case the guard was added for: under-constrained rather than merely omitted.
    Now: no named slot at all is refused, and any positional slot is refused separately.

 G. ABSTRACT MODE WAS AN UNGATED FAIL-OPEN, and the widening landed on it. `if abstractMode
    then visitedRules += qn; return Right(())` dropped whatever reached it; reading a
    nullary carrier newly routed a 0-ary premise there. Measured with
    `ProofConfig(abstractBody = true)`: `flag` gone from the document, `Right` returned.
    Gated now on rustland's own predicate (the functor names a bodied clause) PLUS one row
    stricter: a 0-ary premise is excluded even when it names one, because the doctrine that
    makes skipping safe — "its vars stay FREE and an ambient lift re-states it" — says
    nothing about a premise with no vars. Control beside it: an applied rule call is still
    skipped, so the gate is not "refuse everything in abstract mode".

 H. I CREDITED A ROW WITH A PROPERTY IT DOES NOT HAVE. My comment on the result-variable
    guard said `entityHead` was the `HeadShape.Predicate` row proving the hole predates the
    nullary arm. It is not: `rule entityHead(base: 3.0)` has an ORDINARY functor and an
    empty positional list, so it classifies `Bottom`. Probed: Bottom / Bottom / Predicate
    for the three shapes, and only an ENTITY-functor head is a `Predicate`. The row still
    earns its place (its head is a `Term.Fn`, so it took this path before the widening —
    which IS the pre-existence evidence), but the claim was wrong and a real `Predicate`
    row (`Marker`) now sits beside it. ALSO FIXED IN BOTH SUITES: the three-row loop
    short-circuited on the first failure, so "all three rows fail on a back-out" had never
    been measured. It collects now, and the back-out reports `3 of 3 rows wrong`.

 I. A MISATTACHED SCALADOC in `NullaryBuiltinGoalTest` — a census row inserted between a
    doc block and the test it documents. Reattached.

 J. THE FIRST ROUND'S FIX CREATED A PARITY DIVERGENCE, and I closed it rather than
    recording it. rustland's `render_upper_bound_with` interpolates `result_var` unguarded
    too, with no check in `emit_obligation_with`. MEASURED THERE, not inferred: all three
    head shapes returned `Ok` with `(assert (not (<=  5.0)))`. The same guard, keyed the
    same way (on the empty `result_var`, not on a head shape), now sits in
    `emit_obligation_with`, with `anthill-smt-gen/tests/eqg4f_obligation_result_var_test.rs`
    and its own back-out ledger. rustland's nullary row has been reachable since CZJ2N gave
    `classify_head` its `Term::Ref` arm — this ticket did not open it there.

SUITES: scaland core 570/2 (the two PRE-EXISTING `BootstrapTest` failures, verified
identical with everything stashed), smt-gen 35/35, scala-gen 1/1. rustland full suite run
for the `emit_obligation_with` guard.

### 2026-09-08T20:54:21Z — feedback — user

ITEM 4's ROOT CAUSE IS FILED AS WI-20260908-NE0E4, and item 4 is now downstream of it
rather than a repair to choose here.

WHAT CHANGED MY EARLIER READING — two corrections to what this ticket's item 4 note said:

 1. "RUSTLAND IS IMMUNE" WAS WRONG. I had measured only a fixture carrying BOTH readers and
    read the single load error as covering both. Measured per spelling:

                       scaland          rustland
        `:- aa`        answers 1        answers 1
        `:- aa()`      answers 0        LOAD ERROR

    rustland has the same split; WI-1034 makes one half LOUD instead of removing it. So
    "port WI-1034" does not deliver CZJ2N's rule — it makes the disagreement audible.

 2. THE MULTI-HEAD ROUTE IS NOT THE POPULATION. Censused, three shapes put a stored head
    under an undeclared symbol, all showing bare=1 / paren=0 in scaland:
        rule law: aa, bb :- base(1)     <- the route this ticket named
        fact ff                         <- the COMMON one
        fact ns.gg
    with the single-head `rule hh :- base(1)` as the control at 1 and 1. §6.1 makes a fact
    head introduce no name DELIBERATELY, so the fact-head route is a spec question and not
    a bug to fix alongside.

AND THE ROUTE THIS TICKET NAMED CARRIES A WORSE DEFECT THAN THE SPELLING SPLIT. A multi-head
rule's heads take the bare `intern(name)` fallback, so two sorts' same-named heads are ONE
symbol (measured: `sym=75` for both `zzS.P.aa` and `zzS.Q.aa`), and a reader in P answers
from Q's clause — 1 in BOTH implementations, against 0 for a distinct-names control and 0
for a single-head control. That is WI-894's own defect class in the arm WI-894 did not
reach, and it is what NE0E4 is for.

SO ITEM 4's STANDING: leave it recorded, do not repair it here. NE0E4's fix (mint each head
in the scope the rule is written in) removes item 4's precondition for the multi-head route
— an unresolved name — and the single-head control already shows both spellings answer once
the name is declared. The `isResolved` gate itself stays, and stays observable through the
fact-head route until §6.1 is decided; that is the residue, stated rather than closed.

DIRECTIONS EXAMINED AND NOT TAKEN, with why:
  (a) drop scaland's `isResolved` gate — fixes all three scaland routes, but is a trap to
      port: `ff` is still not DECLARED, so rustland's WI-1034 would then refuse the bare
      spelling too and break `fact ff` + `:- ff`, which works today.
  (b) port WI-1034 to scaland — parity, and loud beats silent, but per correction 1 it
      leaves the two spellings disagreeing.

