## Attributes

- id: WI-20261013-WPVVY-a-labelled-call-of-a-builtin
- created: 2026-10-13T08:03:50Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:03:50Z

- acceptance: cargo-test

- tags: proposal-068

## Description

A LABELLED CALL OF A BUILTIN-TAGGED OPERATION IS READ BY POSITION IN A RULE BODY — a wrong answer at goal position, an undecided one in a value slot. Split from WI-20260926-DSEXA (its two notes of 2026-10-12, found with WI-20260930-MHRN1); it needs nothing else of the 068 sequence. MEASURED, before and after MHRN1 alike: `:- Int64.lt(a: 1, b: 5)` answers no solutions — a DEFINITE failure, so `not(Int64.lt(a: 1, b: 5))` holds — where `Int64.lt(1, 5)` answers 1; `?c <=> Int64.sub(a: 5, b: 1)` and `?c <=> Int64.sub(1, a: 5)` are conditional residuals where `Int64.sub(5, 1)` answers 4 and the operation-body spellings answer 4. WHERE: a tagged operation's call never reaches the parameter pairing MHRN1 moved to `typing::bound_args` (kb/typing/args.rs). The VALUE entry (`run_builtin_for_value`, kb/resolve/evaluate.rs) declines a call with `named_arity != 0`, so the call is left standing; the GOAL entry (`execute_builtin` -> `builtin_cmp` / `builtin_arith`, kb/resolve.rs) has no such check, finds no operand 0 and answers Failure. FIX, one place: before a tag's handler is dispatched, at both entries, rewrite a labelled goal into positional order through `bound_args` over the operation's declared parameters — only where every label names a declared parameter, since some tagged names take labels by design (`find_dictionary(…, out: ?d)`). ACCEPTANCE (cargo-test via rustland/scripts/test.sh; driven): the three labelled spellings answer as their positional twins; `not(Int64.lt(a: 1, b: 5))` fails; `find_dictionary(…, out: ?d)` unchanged; the back-out named at its site.

