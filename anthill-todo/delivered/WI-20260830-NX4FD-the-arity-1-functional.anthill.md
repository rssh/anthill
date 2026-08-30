## Attributes

- id: WI-20260830-NX4FD-the-arity-1-functional
- created: 2026-08-30T18:55:49Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-30T23:58:58Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE ARITY+1 FUNCTIONAL-RELATION VIEW STILL REFUSES A PARAMETRIC EFFECT ROW, SO `size(?ls, ?n)` ANSWERS NOTHING WHERE `length(?ls, ?n)` ANSWERS `Int(2)`.

WI-20260830-DQD5W made the arity+0 BOOL view read an effect row's MEMBERS instead of its length: `Iterable.isEmpty(c: C) -> Bool effects E` declares a row PARAMETER (its sort declares `effects E = ?`), which `List` instantiates to `{}`, so a `!effects.is_empty()` test was asking about the SPEC's abstraction where the goal asks about the CALL. `bare_bodied_bool_relation` now calls `effect_row_admits_relational_view`.

`functional_relation_arity` — the arity+1 sibling, WI-938 — DELIBERATELY DOES NOT, and its doc says so with the measurement. This ticket owns the remainder.

MEASURED, one file, one `List`, two goals at arity+1:

    entity Box(items: List[T = String])
    fact Box(items: ["a", "b"])

    rule own_len(?n)  :- Box(items: ?ls), length(?ls, ?n)   -> [(Int(2), definite)]
    rule spec_len(?n) :- Box(items: ?ls), size(?ls, ?n)     -> []

`length` is `List`'s own operation; `size` is `anthill.prelude.FiniteCollection.size(c: C) -> Int64 effects E = List.length(collect(c))`, reached through `List`'s provision.

WHY DQD5W DID NOT JUST WIDEN THE SIBLING TOO — both halves TRACED, not guessed:

1. With `functional_relation_arity` switched to `effect_row_admits_relational_view`, the HOOK FIRES (`dispatched_relation_arity` returns `Some(1)` against a `pos_arity` of 2) and `spec_len` STILL answers `[]`. The bridge suspends one level down, on a DIFFERENT slot: "cannot resolve a required dictionary for `anthill.prelude.FiniteCollection.size` at these argument types: `anthill.prelude.Iterable[C = anthill.prelude.List[T = anthill.prelude.String], Element = anthill.prelude.FiniteCollection.Element, E = anthill.prelude.FiniteCollection.E]` is not fully pinned by the argument types". The argument pins `C` and nothing pins `Element` or `E` — they are the spec's parameters, not the operation's. This is the `all_pinned` gate in `resolve_bridge_requirements` (kb/typing.rs), and it is the SORT half, which WI-1091 widened only for the OP half (`unique_provider_completion`) and left alone on purpose: "its slots are what the callee's dictionary LAYOUT is measured against ... widening it is a different question from the one this ticket measured". THAT is the question this ticket has to settle.

2. Worse than not working: on a chain that IS pinnable the widened hook answers WRONG. `rule flag(?r) :- Box(items: ?ls), Iterable.isEmpty(?ls, ?r)` — `Iterable`'s chain is the `EffectsRuntime` kind-anchor alone, which DQD5W already made a structural leaf — answered ONE **DEFINITE** solution with `?r` still a free `Var`, over two Boxes whose true answers are `true` and `false`. So the widening trades an honest zero for a definite-looking wrong answer, which is exactly what kernel-language.md §5.3 warns about for this view.

SCOPE. Make the arity+1 view of a bodied operation whose declared row is entirely PARAMETERS answer the way the arity+0 Bool view now does, which needs BOTH:
  * the effect clause in `functional_relation_arity` to read `effect_row_admits_relational_view` (one line, already written and backed out — its doc carries the measurements verbatim); and
  * the sort half of `resolve_bridge_requirements` to complete an open spec element from the carrier's providers where they leave exactly one possibility, or some other answer to "`Element`/`E` are not pinned by the arguments". `unique_provider_completion` is the op-half precedent and its "sole provider is exact rather than lenient" argument is the one to re-examine for the sort half.

THE SECOND READER MOVES WITH IT. `collect_covered_calls` (kb/typing.rs, WI-1040) gates weaving on `functional_relation_arity(..).is_some()` for one stated reason — "a reader must exist for a woven goal", and that predicate "is exactly that recognition". So widening it also widens the weaving population; that is arguably correct (the two must agree) but it is a second measurement, and `wi1045_one_dictionary_representation_test` is what would move. WI-1057 chose the other way for a DIFFERENT reason (a body-less op genuinely has no reader), so its split is not a precedent here.

ACCEPTANCE: `rule spec_len(?n) :- Box(items: ?ls), size(?ls, ?n)` answers `Int(2)`, definite. CONTROLS, each passing today and required to keep passing: `length(?ls, ?n)` at arity+1 (the row above); `wi_dqd5w_spec_op_relational_view_test::spec_op_bare_goal_decides` (the arity+0 view DQD5W delivered); `an_arity_mismatched_bool_goal_takes_the_functional_relation_view` (a Bool op's arity+1 goal, which reaches this hook and must keep BINDING its result rather than answering a free var); and the weaving rows named above.

## Changes

### 2026-08-30T23:58:53Z — feedback — user

DELIVERED. `rule spec_len(?n) :- Box(items: ?ls), size(?ls, ?n)` answers `Int(2)`, definite, beside the `length(?ls, ?n)` control. Two halves, each with its own back-out row.

(1) THE EFFECT CLAUSE, one line as the ticket said. `functional_relation_arity` now reads `effect_row_admits_relational_view` — the row's MEMBERS, not its length — which is what the Bool sibling has read since DQD5W. That gate's doc now names THREE readers instead of two.

(2) THE SORT HALF OF `resolve_bridge_requirements`, and it took a DIFFERENT answer from the one the ticket proposed. The ticket's "complete an open spec element from the carrier's providers where they leave exactly one possibility" IS half of it and is now asked of both chain halves — but it CANNOT answer this ticket's own row. `FiniteCollection requires Iterable[C, Element, E]` at a `List` carrier has NO unique completion, and would not resolve even fully pinned: `ResolvedRequiresNode::Unavailable`'s own doc already records why — "`FiniteCollection requires Iterable[C = C]` holds for a `List` carrier only through `List provides Stream provides Iterable`, which no `Iterable[C = List[…]]` provision matches … Refusing to build the dictionary there would reject every program that dispatches such a spec op without ever reading the evidence (MEASURED: 33 tests)".

So the answer is the one the COMPILE-TIME producer has given since WI-857: the sort half KEEPS ITS SLOT as a recorded absence and lets the call run, instead of returning `Unresolvable` for the whole call. The two producers of one dictionary had disagreed about exactly this slot — the typer placed a marker and 33 tests passed, the bridge refused and the same call answered nothing. Soundness is untouched: nothing resolves an under-pinned goal, so no wrong dictionary is built, and `marker_refusal` refuses any read (measured: `an_under_determined_slot_with_no_completion_answers_nothing`).

A fifth `UnavailableWhy` arm carries the reason. `NoProvider` would have been a FALSEHOOD here — `List` DOES provide `Iterable` — and "declare a provider for it" the wrong repair.

THE TICKET'S SECOND OBJECTION DID NOT REPRODUCE, and the doc it came from is corrected rather than inherited. `rule flag(?r) :- Box(items: ?ls), Iterable.isEmpty(?ls, ?r)` was said to answer "ONE DEFINITE solution with `?r` still a free `Var`". RE-MEASURED with the effect clause alone applied: TWO definite solutions, `Bool(true)` and `Bool(false)`, correctly one per Box; with it backed out, `[]`. That symptom is verbatim the UN-GATED Bool hook's, which DQD5W's own arity gate closed in the same commit — the objection was measured before its sibling fix landed and expired with it.

CENSUS, whole `wi_tests` binary, both new arms instrumented: the marker arm fires 74 times (`FiniteCollection` 38, `Iterable` 30, `Eq` 6); the completion arm fires on the SORT half only for the fixture written for it, and on the op half only for WI-1091's own. Neither arm is undriven and each has its own back-out row.

BACK-OUTS, all three measured:
 * effect clause -> `spec_op_arity_plus_one_goal_binds_its_result` + `a_parametric_row_op_whose_chain_needs_nothing_binds` fail.
 * completion arm (`if op_half` guard) -> `an_under_determined_sort_half_slot_completes_from_a_sole_provider` fails ALONE.
 * marker arm (`None if !op_half` returns `Unresolvable`) -> `spec_op_arity_plus_one_goal_binds_its_result` fails ALONE.
 * restoring the ORIGINAL `!all_pinned && !op_half` return fails both, because it stood before the completion point — named in the test's own table because it is the back-out a reader reaches for first and it does not attribute.

THE SECOND READER: `collect_covered_calls` (WI-1040) gates weaving on `functional_relation_arity(..).is_some()` and its population widens with this. The two SHOULD move together — the reader this predicate now recognizes is the reader that gate is about. No corpus row moved: `wi1045_one_dictionary_representation_test` and the whole workspace suite are green either way, so the widened weaving population is recorded as a consequence, not claimed as a measured effect.

ACCEPTANCE: cargo — full workspace suite 6209 passed, 0 failed (36 binaries). scaland — `sbt test` 524 passed, 0 failed (untouched; the Scala port has no typing/dictionary layer). Controls named by the ticket all pass: `wi_dqd5w_spec_op_relational_view_test::spec_op_bare_goal_decides`, `an_arity_mismatched_bool_goal_takes_the_functional_relation_view`, `wi1045_one_dictionary_representation_test`.

Spec: kernel-language.md §5.3's "the arity+1 view does NOT yet mirror that" paragraph replaced.

/code-review (high) RAISED SIX; FOUR CHANGED THE WORK.

 * "the completion arm CAN build a wrong dictionary — the one new row's sole provider is right whatever the rule is". The objection was right that the row could not discriminate. DRIVEN: `a_completion_selects_the_provider_the_pinned_element_names` — `Marked[M, N]` with TWO ground providers, the argument pins only `M`, and `alpha()`/`beta()` must answer 11/22. A guess answers one number twice. `rival_completions_leave_the_slot_unfilled_rather_than_guess` is its pair: nothing pinned, two providers, NO answer (and a one-provider arm answering 1 beside it, so the zero is not an un-drivable fixture). The review's own scenario (`Ghost.describe(w: Box[B = G])` with `U` unpinned) does not load — `unpinnable_impl_requirement_is_refused_before_it_can_run` asserts exactly that — so the two halves of it cannot hold at once. The soundness paragraph WAS over-broad, though: it asserted the marker's argument over both arms. Split.
 * "the removed cheap bail is on a per-dispatch path, unmeasured". COUNTED: across the whole `wi_tests` binary (3929 tests) `resolve_bridge_requirements` is entered past the empty-chain bail 272 times, of which 79 reach the completion attempt. The extra work is 79 `unique_provider_completion` calls in the corpus. Recorded at the site.
 * "the value-directed consumer now gets a `__req_self` stand-in where it had no channel, untested". TRUE and NOT DRIVEN — recorded at the site as such, with why it is the right reading (the bridge is an entry with no caller dictionary, like a host entry, and a stand-in is the invitation to the value-directed rescue) and what driving it would need (the host-entry route is not it: `seed_entry_op_requirements` takes the op half out of this resolution).
 * "the weaving consequence has no row, and a green corpus missed exactly this last time". CONFIRMED AND DRIVEN, and it found a real gap: `require[FiniteCollection[…]], size(?ls, ?n)` DELAYS where the plain `size(?ls, ?n)` answers `Int(2)`. NOT a regression — with the effect clause backed out both spellings answer `[]` — so the woven spelling simply does not receive the win. The gap is the `require[X]`/`find_dictionary` dictionary, not this view. Driven by `the_woven_spelling_does_not_yet_receive_the_win` (which asserts today's answers and says at its site to re-aim it) and owned by WI-20260830-X9PB4.
 * Two smaller ones taken: the stale "a failure in the SORT half aborts the whole supply, as it always has" comment, and `body_less_relation_arity` as a fourth reader of the effect question — kept on the strict spelling with the exemption stated (its subject is body-less, so the owner's bodied-op safety argument does not carry, and routing it through would widen SILENTLY if that clause were relaxed).
 * `UnavailableWhy::UnderDetermined` is now FIELDLESS: its `goal` could only ever equal `AbsenceRecord::Slot.spec`, unlike its four siblings, whose goal is the level that actually failed.

FOLLOW-UP FILED: WI-20260830-X9PB4 — `require[X]` hands a woven call a dictionary whose under-determined sub-slot was never completed. Filed rather than inlined because it is a THIRD producer of one dictionary (`find_dictionary`) needing its own answer and its own measurement, not a small edit.

