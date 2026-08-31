## Attributes

- id: WI-20260830-X9PB4-require-x-hands-a-woven-call-a
- created: 2026-08-30T23:47:57Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-31T04:51:28Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`require[X]` HANDS A WOVEN CALL A DICTIONARY WHOSE UNDER-DETERMINED SUB-SLOT WAS NEVER COMPLETED, SO `require[FiniteCollection[C = List[T = String]]], size(?ls, ?n)` DELAYS WHERE THE PLAIN `size(?ls, ?n)` ANSWERS `Int(2)`.

MEASURED, one file, one `List`, two spellings of one goal (driven by `wi_nx4fd_functional_relation_row_param_test::the_woven_spelling_does_not_yet_receive_the_win`, which asserts TODAY'S answers and says at its site that it must be re-aimed when this lands):

    rule woven(?ls, ?n) :- require[FiniteCollection[C = List[T = String]]], size(?ls, ?n)   -> ONE INDEFINITE solution
    rule plain(?ls, ?n) :- size(?ls, ?n)                                                    -> [(Int(2), definite)]

NOT A REGRESSION, and that half is measured too: with WI-20260830-NX4FD's effect clause backed out (restore `if !sig.effects.is_empty() { return None }` in `functional_relation_arity`) BOTH spellings answer `[]`. NX4FD gave the plain spelling the win and left the woven one where it was — the two agreed at zero and now disagree.

WHY. NX4FD had to settle exactly this question one route over. `FiniteCollection requires Iterable[C = C, Element = Element, E = E]` at a `List` argument pins only `C`; `resolve_bridge_requirements`' SORT half now completes an open element from a sole provider (`unique_provider_completion`) and, where nothing completes uniquely, KEEPS THE SLOT as a `ResolvedRequiresNode::Unavailable` recorded absence instead of aborting the whole call — which is what the COMPILE-TIME producer has done for this same slot since WI-857. `find_dictionary` — the kernel relation `require[X]` lowers to (WI-1040) — has had neither treatment, so the dictionary it hands the woven `ApplyWithin` is not one `size`'s body can run on, the reduction comes back undecided, and the arity+1 site routes to `unify` and DELAYS (which is correct there: WI-1040's own clause exists so a woven call whose dictionary is not bound re-fires later rather than binding `?r` to the call term).

SCOPE. Give `require[X]`/`find_dictionary` the same answer the bridge now has for an under-determined sub-slot, or establish that it needs a different one. The two are separate producers of one dictionary and WI-857's 'one owner for the readers that must agree' discipline says they must not drift — NX4FD's whole argument for the marker arm was that the bridge had drifted from the typer about this exact slot, so a THIRD producer disagreeing is the same defect one route over.

WHAT TO WATCH. `collect_covered_calls`'s weaving gate is `functional_relation_arity(..).is_some()`, and NX4FD widened that predicate — so this population is NEW and its members are precisely the bodied spec ops whose declared effect row is entirely PARAMETERS. WI-1040's doc records that the last wrong move in this population took `require[PartialEq[T]], eq(?x, ?y)` from ONE solution to ZERO with a green corpus, so a corpus run is not evidence here; the row above is.

ACCEPTANCE: `rule woven(?ls, ?n) :- require[FiniteCollection[C = List[T = String]]], size(?ls, ?n)` answers `Int(2)`, definite, equal to the plain spelling; `the_woven_spelling_does_not_yet_receive_the_win` re-aimed at that equality. CONTROLS, each passing today: `wi1040_require_clause_dictionary_test::a_covered_call_dispatches_through_the_clause_dictionary` (an effect-free bodied spec op under `require`, which already answers 7); `wi1045_one_dictionary_representation_test`; and NX4FD's own `spec_op_arity_plus_one_goal_binds_its_result` (the plain spelling, which must not move).

## Changes

### 2026-08-31T04:51:15Z — feedback — user

DELIVERED — and the ticket's DIAGNOSIS was wrong about the mechanism. The proposed fix was BUILT and DRIVEN before it was dropped, so this is a measurement rather than a preference.

WHERE IT ACTUALLY BROKE, and it is not a sub-slot. `resolve` answered `NoMatch { hint: "no impl provides anthill.prelude.FiniteCollection" }` for the TOP-LEVEL goal `FiniteCollection[C = List[T = String]]` — ZERO candidates, on a spec `List` provides outright. `require[X]`'s bracket is stripped at convert (channel doc §10 item 1), so `witness_sort_goal` rebuilds the goal from the WITNESS call's carried types; `FiniteCollection.size(c: C)` names `C` and OMITS `Element`, and an omitted type param is DISCRIMINATING at `collect_provides_candidates` (wi325 / wi237 — "else every concrete `Eq` impl would match a bare `Eq` goal"), so `List provides FiniteCollection[C = List[T], Element = T, E = {}]` was rejected on the element the goal never had an opinion about. Writing `require[FiniteCollection[C = List[T = String], Element = String]]` changed nothing — MEASURED; the bracket is gone before the goal exists.

THE TICKET'S PROPOSED FIX CANNOT REACH IT, measured rather than reasoned. `unique_provider_completion` was extended to match the goal's PINNED bindings against each provider head and substitute what that determines into the open elements — the natural generalization of "a provider's own GROUND value". It still answered `None`: the iteration meets `FiniteStream provides FiniteCollection[C = FiniteStream, Element = T, E = E]` first, `List[T = String]` matches its bare `C` (a `List` IS a `FiniteStream`), its `Element` stays abstract, and that is the OPEN-ENDED RIVAL veto — which is correct and must not be relaxed. That extension was backed out; nothing shipped credits it, and the bridge is untouched.

WHAT SHIPPED. `witness_sort_goal` carries every element the witness does not name as WI-507's wildcard (`Ref(Spec.Element)`) instead of omitting it — the shape `goal_from_requires_entry` has had for free all along, because a written `requires Iterable[C = C, Element = Element, E = E]` spells every element. WI-507's own doc names this exact shape ("a carrier-only `clear(c)` pins only the carrier `C`, so the spec's sibling `Element` arrives as `Ref(Sort.Element)`"). Monotone at the matcher: a wildcard is still refused against a CONCRETE candidate binding, so the coherence rule is untouched; what it admits is a candidate whose value for the element is its OWN parameter, which is universally quantified and cannot discriminate.

SCOPE, CENSUSED RATHER THAN ASSUMED. `witness_sort_goal` has ONE caller (`fetch_dictionary`), which has ONE (`read_dictionary_into`, the `out` arm of `builtin_find_dictionary`), so the change is confined to `require[X]` / `?d = require[X]`. WI-300's check-only `requires(X)` takes `find_dictionary_guard`, which builds no `SortGoal` at all.

THE EFFECT-ROW EXCLUSION IS DRIVEN, and it needed a purpose-built fixture: the WHOLE 3934-test binary passes with it removed. `provides Walk[C = Src, E = Error]` keeps answering `require[Walk[C]]` with the guard and STOPS with it dropped (`?d` falls to one indefinite solution), while the `E = {}` sibling is unmoved either way. `an_effect_row_element_is_left_to_its_own_owner` drives both arms.

NOT CLOSED, and it is a different question: channel doc §10 item 1 stays open — the bracket's own values are still not read, so `require[Spec[Element = String]]` still says nothing the witness did not. What this ticket removed is one CONSEQUENCE of the stripping, not the stripping.

EIGHT ROWS in `wi_x9pb4_require_dictionary_element_test`. FOUR fail on back-out — the acceptance equality; the dictionary's named carrier (`List`, not the rival `FiniteStream`, and the candidate list really is `[FiniteStream, List]`, measured); the open-element arm; the self-representing row — plus NX4FD's re-aimed `the_woven_spelling_receives_the_win`. THREE pass either way and say so at their sites: the concrete-element arm (the coherence rule is unchanged), the WI-1040 population (nothing un-named, goal byte-identical), and the effect-row control (which measures one line, not the change). ONE passes with the ticket wholly in AND wholly out and ABORTS in between — the tie row.

/code-review (high) RAISED SIX, AND ITS TOP FINDING WAS A REAL REGRESSION THIS TICKET INTRODUCED — driven, then closed, before delivery.

1. A TIE NOW REACHED `debug_assert!(false)`. The wildcard makes the goal non-discriminating on the un-named element, so the candidate set grows and can TIE; `fetch_dictionary` maps a tie to `FindDictFetch::Defect`, which aborts in every debug build. CONFIRMED on the review's own shape (`Carrier provides MidA` + `provides MidB`, each `provides Spec[C = Mid?, Note = <its own N>]`): `panicked at resolve.rs: find_dictionary: two providers answer …: MidA, MidB`. CONTROL, measured: with the wildcard loop backed out the identical program answered ONE INDEFINITE solution. `Defect`'s contract — "overlap is refused at typing/load, so reaching this means the coherence machinery let one through" — needs the goal to be decided ENTIRELY by the witness's carried types, which a SYNTHESIZED element is not. FIXED: `witness_sort_goal` now returns a `WitnessGoal` carrying whether it invented anything, and a tie on such a goal is `Undecided` (delay) rather than `Defect`. Driven by `a_tie_on_a_synthesized_element_delays_rather_than_reporting_a_defect`, which passes with the whole ticket in, passes with it out, and ABORTS in between.

2. SELF-REPRESENTING SPECS SHIPPED UNMEASURED. True — all four original fixtures were carrier-PARAMETER specs. Driven rather than excluded: `a_self_representing_spec_receives_its_dictionary_too`. It is EVIDENCE, not just a control — backed out, `?d` yields one indefinite solution and names no carrier; with the change it binds and names `IntBag`.

3. THE SIBLING PRODUCER `sort_goal_from_subst` STILL OMITS. Right question, answered by measurement instead of symmetry, and recorded at the site. It is not the same question: there an unresolved param is a FLEX VAR the typer may still pin, here nothing more will ever arrive; and the compile-time route has a mechanism this one does not (an un-pinnable SLOT becomes WI-857's `Unavailable` inside a dictionary that still gets built, whereas `fetch_dictionary`'s goal IS the whole dictionary). MEASURED on this ticket's own shape — the same spec, provision and carrier dispatched with NO `require` answers `Int(7)` on the typer path — so the two are not observably in disagreement about it. Whether they should be ONE producer is a separate question with its own population.

4/5. NX4FD's RESIDUE, not this ticket's: the undriven `requirements_for_value_directed_impl` consequence, and the per-dispatch cost of the removed early return. Both are recorded in that commit's own doc; naming them here so they are not lost between the two tickets.

6. THE NEW TEST FILE WAS UNTRACKED while `wi_tests.rs` already named it — a tree where `cargo test -p anthill-core` would not compile for anyone else. `git add`ed.

