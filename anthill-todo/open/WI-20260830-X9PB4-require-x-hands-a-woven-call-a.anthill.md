## Attributes

- id: WI-20260830-X9PB4-require-x-hands-a-woven-call-a
- created: 2026-08-30T23:47:57Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T23:47:57Z

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

