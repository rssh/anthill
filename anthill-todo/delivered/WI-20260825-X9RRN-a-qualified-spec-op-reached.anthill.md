## Attributes

- id: WI-20260825-X9RRN-a-qualified-spec-op-reached
- created: 2026-08-25T19:23:39Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-26T06:14:48Z

- acceptance: cargo-test

## Description

a QUALIFIED `Spec.op(...)` reached through a `provides` chain is 'unknown functor' — the member IMPORT works and the call does not, so proposal 004's source compatibility holds for only one of the two spellings

## Changes

### 2026-08-25T19:24:08Z — feedback — claude

PRE-EXISTING AND SHIPPED — WI-20260825-1WBZT only WIDENED the population, and the widening is what makes it worth a ticket. Measured on the delivered tree:

  operation same(a: Int64, b: Int64) -> Bool  = Eq.eq(a, b)         -> "type mismatch in Eq.eq.apply:
                                                                       expected known operation or arrow-typed
                                                                       variable, got unknown functor"
  operation q(a: Float, b: Float) -> Float    = Field.div(a, b)     -> same message
  operation plus(a: Int64, b: Int64) -> Int64 = Numeric.add(a, b)   -> same message   <- NEW under 1WBZT
  operation dbl(a: Float) -> Float            = Ring.add(a, a)      -> same message   <- NEW under 1WBZT
  operation dbl(a: Float) -> Float            = Additive.add(a, a)  -> LOADS

The last row is the separator: `add` exists, is backed, and answers — the failure is about the ADDRESS, not the operation. `Eq.eq` has been in this state since WI-1109/WI-1110 moved `eq` onto `PartialEq`, `Field.div` since WI-20260824-VT8CF moved `div` onto `Divisible`; 1WBZT moved `add`/`sub`/`mul`/`neg` onto `Additive`/`Multiplicative` and `Ring`'s five onto the same, so four more addresses joined.

A RULE BODY GIVES THE SAME VERDICT, and twice over — `rule twice(?x, ?y) :- ?y = Numeric.add(?x, ?x)` reports BOTH "rule-body term `Numeric.add` names nothing: no rule, fact, operation, entity, const or builtin is declared under that name" and the typer's "unknown functor".

THE OTHER SPELLING WORKS, which is what makes this a half-kept promise rather than a design. `import anthill.prelude.Numeric.{add, sub, mul, neg}` RESOLVES through the chain and every one of the ~43 corpus sites written that way still loads — measured, that import population is untouched by 1WBZT. `eq.anthill`'s own comment claims the general form: "Filed correctly it brings the scope with it (`Eq.eq` still resolves to the inherited `PartialEq.eq`, which proposal 004 wanted for source compatibility)". Half of that is true. The comment should say which half once this is settled.

AND A THIRD SPELLING WORKS, which localizes the mechanism: `anthill.prelude.algebra.VectorSpace` writes `Ring.sub(Ring.zero, Ring.one)` in a rule body and loads clean — because `VectorSpace` has `requires Ring[F]`, and a `requires` edge brings the target's scope (including what the target reached by `provides`). So the members ARE reachable through the chain; what is not reachable is the qualified `Spec.op` address from a scope that merely IMPORTS `Spec`. `by_qualified_name` has no `anthill.prelude.Numeric.add` entry any more, and the qualified-call path reads that rather than walking the provision.

NOT A SILENT DEFECT and the repair is one word (`Numeric.add` -> `Additive.add`), which is why 1WBZT did not absorb it — VT8CF did not absorb the `Field.div` instance either. WHAT TO DECIDE: whether the qualified form SHOULD walk the chain (then the fix is in the qualified-name path and the ladder doc §8.6 gains a rung), or whether it should not (then the message must stop saying "unknown functor" about a name that is defined, and name the declaring spec instead — the same complaint WI-944's second finding makes about "should be unreachable"). Do not leave it saying a defined name is unknown.

SUBJECT MOVED, RECORDED: `vec3_ops_test::control_ring_now_loads_and_its_residual_failure_is_the_unbacked_provision` was the row pinning `Ring.add`'s "loads, then dies at eval with 'operation has no body'". Under 1WBZT it is refused at LOAD instead, so that row was rewritten to assert the new verdict and to attribute it HERE rather than to WI-944's unbacked `fact Ring[Float]`.

### 2026-08-25T23:56:22Z — feedback — claude

THE CAUSE IS LOCATED, and it says why this is not a small patch — measured rather than predicted, after WI-20260825-N2865's sibling defect turned out to BE one.

`load::dotted_by_head` is a pure STRING JOIN with no scope walk at all:

    kb.symbols.by_qualified_name.get(&format!("{head_qualified}.{tail}")).copied()

So `Mid.b` asks for the literal key `probe.x92.Mid.b`. When `Mid` reaches `b` only through `provides Base[T = T]`, no such key exists and the path MISSES — there is no rung at which the provision chain could be consulted, which is why no narrowing or widening of an existing predicate reaches it.

REPRODUCED ON PURE USER SORTS, so it is not a property of the prelude:

  sort Base { sort T = ?  operation b(x: T) -> T = x }
  sort Mid  { sort T = ?  provides Base[T = T] }                    -- declares nothing
  sort User { operation viaMid(x: T) -> T = Mid.b(x) }
    -> "type mismatch in Mid.b.apply: expected known operation or arrow-typed variable,
        got unknown functor"

…with or without a `requires Mid[T]` on `User`. And the CONTROL that pins the axis: the same file with `Base.b` DECLARED on `Base` and reached as `Base.b(x)` loads clean through BOTH a `requires` and a `provides` — so `Sort.member` works; what fails is `Sort.member` where the member is the PROVISION'S.

WHY IT IS NOT INLINE, in one sentence: the fix is a NEW RUNG on the §8.6 ladder, and which rung is the decision this ticket exists to take. Three questions the patch cannot avoid answering, none of them settled anywhere today:

  * Does the fallback follow `provides` ONLY, or `requires` too? Following `requires` is wrong — `requires` means "I need one", not "I have one to offer under my name", and it is exactly the shadow `Polynom.add` already warns about. Following `provides` only is now MECHANICALLY AVAILABLE for the first time: WI-20260825-N2865 added `ImportOrigin::Provision` and `parent_edge_is_provision_only`, so the two edge kinds are finally distinguishable. That is the one thing this ticket got cheaper.
  * What happens when TWO provision paths reach two same-named members? `dotted_by_head` returns `Option<Symbol>` and has no ambiguity arm; a scope walk has one, and the two callers read the result differently.
  * `dotted_by_head`'s own doc records that head-qualification ALREADY over-hits (WI-751's field case). A scope-walking fallback widens it again, and my memory of this codebase is that narrowing or widening a shared resolver set serves one reader and breaks another (WI-1090, WI-1095, WI-1098).

SO THE CHEAP HALF IS THE OTHER ONE, and it needs no decision: the MESSAGE. "unknown functor" about `Eq.eq` / `Numeric.add` / `Field.div` is false — the operation exists, is backed, and answers under its declaring address. Whoever takes this should either add the rung or make the diagnostic name the declaring spec ("`Eq` reaches `eq` through `provides PartialEq`; write `PartialEq.eq`"), but not leave a defined name reported as unknown.

### 2026-08-26T06:14:44Z — feedback — claude

DELIVERED. The relative reading gained a PROVISION RUNG — `load::dotted_by_provision`, below the declared-member join — so a member reached through a `provides` conversion answers to its head's address in every position that reads the ladder. `Eq.eq`, `Numeric.add`, `Field.div`, `Ring.add` and a pure-user `Mid.zug` all resolve to the DECLARING spec's operation and COMPUTE.

TWO CLAIMS IN THIS TICKET'S OWN BODY WERE FALSE, and both are worth reading before the design, because one of them was the evidence for a question the design had to answer.

  * "AND A THIRD SPELLING WORKS … `anthill.prelude.algebra.VectorSpace` writes `Ring.sub(Ring.zero, Ring.one)` in a rule body and loads clean — because `VectorSpace` has `requires Ring[F]`." It is not a rule body, it is an equational LAW, and a law's head and RHS are UNCHECKED positions — WI-20260825-1WBZT's own /code-review found exactly this and repaired those laws. Driven in a CHECKED position: a sort writing `requires Mid[T]` and calling `Mid.zug(x)` qualified is "unknown functor". A `requires` never made the qualified spelling work.
  * "`parent_edge_is_provision_only`, so the two edge kinds are finally distinguishable" — the VARIANT (`ImportOrigin::Provision`) exists; that predicate never did. WI-20260825-N2865's review replaced its first cut with the `all`-quantified `parent_edge_stops_enclosing` and left a dangling intra-doc link behind, which this change repairs.

THE DESIGN QUESTION WAS SETTLED BY A CONTROL, NOT BY JUDGEMENT. The obvious fix is to reuse the walk the member IMPORT already uses (`process_imports` strategy 2, a full `resolve_in_scope` in the base scope). Measured on the delivered tree, that walk answers two questions an address must not:

  import anthill.prelude.Numeric.{List}  -> LOADS   `List` is a SIBLING of `Numeric`
  import anthill.prelude.Numeric.{lt}    -> LOADS   `lt` is `PartialOrd`'s, by `requires`

Copying it would have minted `Numeric.List` and `Numeric.lt` as addresses — the WI-751 over-hit shape one clause over. So the rung follows `ImportOrigin::Provision` edges ONLY, joining `by_qualified_name` at each provided sort's own path: a sort answers with what it DECLARES, never with what it merely has in view. `requires` costs nothing by being excluded, because what a requirement brings is already reachable BARE inside the requiring scope — driven on `zug`, a name the implicit prelude cannot rescue (a bare `lt` or `add` would have measured the tier, not the edge).

ANSWERING THE TICKET'S THREE QUESTIONS, in its own order:
  1. `provides` only. Measured above.
  2. Two hits AT ONE LEVEL are `ResolveResult::Ambiguous`, reported with both candidates by the ladder's existing arm — and pinned in BOTH clause orders, because WI-20260825-EBMG8's finding is that this shape otherwise resolves by SOURCE ORDER. A DIAMOND is not an ambiguity: two routes to one declaration are deduped by the walk's `visited` set, which is what keeps `algebra.anthill`'s benign shape loading.
  3. The over-hit worry does not transfer: this rung is not a widening of `dotted_by_head`'s join but a second, differently-keyed join below it. Rung 1 still wins outright — pinned with bodies that DISAGREE (`Mid.zug` adds 1, `Base.zug` adds 100), so the number names the winner.

THE CHEAP HALF THE TICKET OFFERED WAS NOT TAKEN, and should not be: it proposed either the rung or a better MESSAGE ("`Eq` reaches `eq` through `provides PartialEq`; write `PartialEq.eq`"). The rung makes the message unnecessary, and library proposal 004's migration step 1 is explicit that it wanted the address to work — "keep `Eq.eq` resolving to the inherited `PartialEq.eq` … so most call sites are source-compatible". (The citation is to `docs/proposals/library/004`, not `docs/proposals/004-tuple-sorts.md`; the tree has two 004s and `eq.anthill` now says which.)

/code-review (high) FOUND A REAL CAPTURE THE 11 ROWS DID NOT, and it is the finding to read first.

  A PROVISION HIT REJECTED FOR VISIBILITY FELL THROUGH TO THE ABSOLUTE READING. The first cut let the hit leave its arm into the ladder's tail, where WI-752's fall-through re-reads the literal path text as a top-level FQN. Driven: `lib.Base.zug` INTERNAL, `lib.Mid provides Base`, plus an unrelated top-level `namespace Mid { operation zug -> 999 }` — `Mid.zug(1)` in a third scope LOADED CLEAN and answered 999, bound to the foreign namespace. My own `an_internal_provided_member_is_refused_not_delivered` row passed throughout, because it had nothing to capture. WI-752's fall-through is right for the WI-751 COLLISION, where rung 1's string join lands on a stranger by coincidence; a conversion hit is deliberate, so an unusable one REFUSES the path. Fixed by returning from the arm; the precise `internal` diagnostic survives, since `resolve_dotted_reported` re-reads with `DottedVisibility::Any`.

  THE AMBIGUITY ARM COUNTED CANDIDATES IT WOULD NOT DELIVER. Hits were collected raw and only the WINNER was gated, so one `internal` route beside one public one reported `ambiguous symbol 'Mid.b' … ["lib.L.b", "lib.R.b"]` — withholding the one reachable answer and printing a name the scope may not see. The gate now runs at COLLECTION, because the SIZE of the set is the verdict. Rung 1 can filter afterwards; a set-valued rung cannot.

  THE THIRD FINDING WAS REFUTED BY THE TWIN IT SHOULD BE MEASURED AGAINST, and the refutation changed the spec text rather than the code. It read the population (`TotalFloat.neq` names nothing, a carrier's concrete `provides` binding wires no edge, `LogicalStream.isEmpty` resolves) as a gate borrowing WI-1110's visibility question. Driven against the MEMBER IMPORT in each case, the two spellings agree exactly: `import …TotalFloat.{neq}` is "unresolved import", `import lib.Cell.{zug}` is refused (and the loader independently refuses that provision as unbacked), `import …LogicalStream.{isEmpty}` loads. Sharing the import's population is the ticket's GOAL, not a defect. What was wrong was my §8.6 sentence, which stated the rule unconditionally.

  AND MY REPAIR OF IT OVERSHOT, caught by the row I wrote for it: I asserted the two populations were EQUAL and `Numeric.lt` answered `qualified=false, import=true`. The true statement is CONTAINMENT — the address's population is a strict subset, and the difference is exactly the two edge kinds this rung refuses. `the_qualified_population_is_contained_in_the_member_imports` asserts the containment and names both witnesses. The import's own over-hit is filed as WI-20260826-NB88H.

  Also applied: two `\`-continuations swallowed by a python heredoc had baked 10-space runs into assert messages.

TWO RESIDUALS FILED, both with their measurement and their control:
  * WI-20260826-XFTC7 — a TYPE reference does not read this ladder. `Mid.Inner` is a type PROJECTION answered by a separate member table ("type 'Mid' has no member 'Inner'") while the declared `Base.Inner` loads and `Mid.f()` resolves. Not widened here: "what does this NAME denote" and "does this TYPE have this member" are different questions, and whether a value-level conversion conveys a nested SORT is a claim nothing in the language makes. FOUND BY A UNIFORMITY ROW, not by reading — extending `wi752_dotted_ladder_test`'s "same spelling, every position" claim to the new rung is what failed.
  * WI-20260826-NB88H — the selective import's over-hit, above.

WI-944 IS DISSOLVED, measured and recorded on that ticket. `Ring.add(2.5, 2.5)` answers 5.0 on BOTH the generic and the concrete route. Its premise was that `Ring` and `Numeric` were two specs declaring one short name; 1WBZT removed the duplication and this made the address resolve to the survivor. Its second finding (a message claiming to be unreachable) was answered earlier by WI-1092.

ROWS: 14 new (`wi_x9rrn_provided_member_address_test`) plus one in `wi752_dotted_ladder_test`. THREE EXISTING ROWS FLIPPED, each of which had asked for it in its own doc:
  * `wi_1wbzt_…::the_member_import_still_reaches_the_moved_declaration` — its refusal half said "if this now loads, that ticket landed and this half should become the positive row it wants to be". It is, and it computes 7 through both spellings.
  * `wi_1wbzt_…::the_scalar_side_law_addresses_are_live_and_the_ring_ones_are_not` -> `…_and_a_dead_one_is_still_loud`. `Ring.*` resolves now, so "names nothing" is no longer available as the control; the row asserts which SYMBOL each address lands on (via the nullary "ambiguous dispatch of …", which spells the target) and keeps a `Ring.nope` / `Additive.nope` row that must stay loud — so it cannot be satisfied by a ladder that accepts everything.
  * `vec3_ops_test::control_ring_now_loads_…` -> `control_ring_add_loads_and_answers_through_the_provision_chain`, carrying all three verdicts it has had.

SPEC: kernel-language.md §8.6 gains the rung, the conversion-vs-carrier distinction, the two edge kinds refused with their witnesses, the containment, and the type-position residual. `eq.anthill`, `arithmetic.anthill` and `algebra.anthill` had their now-false claims repaired rather than deleted — `arithmetic.anthill`'s header still carried 1WBZT's refuted "`VectorSpace` … writes `Ring.sub(Ring.zero, Ring.one)` in its laws and loads", which was true and proved nothing.

PRE-EXISTING, NOT TOUCHED: `SymbolTable::parent_edge_is_import_only` warns "never used" (present at baseline too) — N2865's review left it dead while four doc links still name it.

FINAL: rustland 5744 passed / 0 failed across 36 binaries (baseline 5729); scaland 538 passed / 0 failed.

