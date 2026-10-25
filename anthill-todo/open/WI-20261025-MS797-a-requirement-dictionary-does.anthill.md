## Attributes

- id: WI-20261025-MS797-a-requirement-dictionary-does
- created: 2026-10-25T10:51:24Z

- status: Open
- status_agent: user
- status_at: 2026-10-25T10:51:24Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A REQUIREMENT DICTIONARY DOES NOT SAY WHICH APPLICATION IT IS FOR — `Dictionary(subs, impl: P)` names its provider and nothing else, so where `P` provides one spec at several applications and supplies a DEFAULTED operation differently at them (`sort W provides Desc[T = A, name = aName]` beside `provides Desc[T = B]`; or `Desc[T = Box[E = Int64]]` beside `Desc[T = Box[E = String], name = sName]`), a dispatch through the dictionary has no answer. WI-20261025-ZAWX9 refuses it at the call (`EvalError::UndeterminedDictionaryDispatch`), and the typer, which knows the application (`tree_application` → `resolve_op_target_at`), answers each call by name but enters a default it pins at such a provider WITHOUT the instance's dictionary — so a default body that reads the instance raises at the read. MEASURED rows: `wi_zawx9_defaulted_dictionary_dispatch_test::a_witness_supplying_differently_at_two_sorts_is_refused_through_the_dictionary` and `::two_applications_of_one_sort_are_two` (by name 7/1 and 1/9; through the dictionary refused). WHAT: a dictionary built for an application can be dispatched at it — carry the application in the dictionary, or let a dispatch the typer already pinned not be re-resolved through it. DESIGN POINT FOR THE USER FIRST: the dictionary is ONE representation (docs/design/requirement-channel.md §9: one functor, one key set, one comparison), so a new key reaches every producer (the typer's `build_dictionary_term` / `dictionary_value_of_tree`, eval's `alloc_dictionary`, the SLD `find_dictionary` crossing) and every comparison of two dictionaries. Related shapes this ticket would also settle: the SLD crossing's silent residual for such a refusal (`dictionary_dispatch_target`), and `Dictionary.ops` listing the provider's whole table whatever spec the dictionary is for. Filed at the user's request (2026-10-25).

