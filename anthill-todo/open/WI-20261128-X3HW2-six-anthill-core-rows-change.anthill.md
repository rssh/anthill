## Attributes

- id: WI-20261128-X3HW2-six-anthill-core-rows-change
- created: 2026-11-28T08:00:17Z

- status: Open
- status_agent: user
- status_at: 2026-11-28T08:00:17Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

SIX anthill-core ROWS CHANGE VERDICT UNDER ANTHILL_TEST_NODE_CARRIER=1 ON HEAD: the switch puts every sort named in a type on an alias occurrence (`TypeNode::Aliased`) standing for itself, which changes no meaning, so every test must keep its verdict (rustland/CLAUDE.md); `ANTHILL_TEST_NODE_CARRIER=1 ANTHILL_TEST_OPT=2 scripts/test.sh -p anthill-core` fails six, measured 2026-11-28 on 5dfa94d13 (the six rerun on HEAD alone, and the same six beside WI-20261103-95S43's change; only anthill-core measured, the other crates not run under the switch). (1) `wi_cxr5b_dictionary_application_test::the_reflect_faces_read_the_application_the_dispatch_reads`: the dictionary prints `Dictionary(impl: WT)`, with no `at: SortView(…)` — it does not say which application it is for. (2) `wi_cxr5b_dictionary_application_test::two_applications_apart_in_a_type_var_the_operation_does_not_take_a_value_of`, (3) `wi_cxr5b_own_two_applications_test::a_call_reads_the_provision_at_what_it_fixes_in_either_order` and (4) `wi_qg6zr_witness_at_the_application_test::through_a_requirement_each_application_answers_its_own` stop at run time with `UndeterminedDictionaryDispatch` — "provides `Coll` at 2 applications and supplies `first` differently at them … and a dictionary names its provider, not the application it is for" (`Sp`/`count` in (4)) — the run-time face of (1). (5) `wi_cxr5b_concrete_bracket_test::a_bracketed_self_result_is_the_provider_at_what_the_call_fixed` is refused at load, "type mismatch in useAt.o (op-arg): expected Ones[T = Int64], got Ones[T = o.T]" — a projection left unread. (6) `wi_szkv7_later_equality_test::a_later_restatement_of_a_derived_provision_is_accepted` is refused "the equality of 'test.le.total.Point' is closed, and has changed since the load that defined it: its own provision of `Eq` for it is new; its own provision of `PartialEq` for it is new" — a restated provision not recognized as the one held. Each is a reader that matches the carrier (a `Value::Term` gate, a `_ => false`) and not the carrier-neutral view (`TermView`, `extract_type`): (1)–(4) where a dictionary's application is recorded or read, (5) where the projection is read, (6) where a later provision is compared with a sealed one. WHAT: find each reader — rustland/CLAUDE.md's method: print every `unify_types` / `types_compatible` pair in both modes and diff — and read it through the view. ACCEPTANCE: the six rows pass under the switch; each fix is proved WITHOUT the switch by a row that puts the type on an occurrence on its own (as `value_holding_type_readers_test` does) and fails with the fix backed out; `ANTHILL_TEST_NODE_CARRIER=1 scripts/test.sh` over the whole workspace green, or what it finds in the other crates recorded here; full workspace green via rustland/scripts/test.sh.

