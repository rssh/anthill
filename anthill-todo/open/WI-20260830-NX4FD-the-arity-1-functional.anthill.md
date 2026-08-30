## Attributes

- id: WI-20260830-NX4FD-the-arity-1-functional
- created: 2026-08-30T18:55:49Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T18:55:49Z

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

