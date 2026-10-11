## Attributes

- id: WI-20261011-WFC1Q-a-duplicate-or-dotted
- created: 2026-10-11T05:27:59Z

- status: Open
- status_agent: claude
- status_at: 2026-10-11T05:27:59Z

- acceptance: cargo-test

## Description

A DUPLICATE OR DOTTED DECLARATION TRIPS A LOADER ASSERTION WHERE A REFUSAL IS DUE — measured 2026-10-10 on 5273d5a2 and again on 5ba58df5 (the loader is the same on both), found while probing WI-20261008-JMMHQ.

THE PROGRAMS, each under `anthill load` in a build with debug assertions (the dev CLI and every test build), each inside `namespace lib`:
(a) two bodied operations of one name in one sort, their parameter names differing — `sort Desc { operation label(x: Int64) -> Int64 = x; operation label(y: Int64) -> Int64 = 5 }` — panics in `emit_operation_equation` (kb/load.rs): "operation parameter `x` has no registered arg place". With the assertion off the load reports what it should, "operation 'lib.Desc.label' is declared more than once in its scope (2 declarations)". The same with the second declaration written dotted beside the sort, `operation Desc.label(y: Int64) -> Int64 = 5`. With equal parameter names, or a body-less first declaration, the refusal is reported and nothing panics.
(b) a dotted operation over an `internal` member — `sort Desc { internal operation label(x: Int64) -> Int64 }` beside `operation Desc.label(x: Int64) -> Int64 = 5` — the same assertion. With it off: "'Desc.label' is internal to 'lib.Desc' and cannot be referenced from scope 'lib'", then two cascaded "unresolved name 'Int64' in scope 'Desc.label'". The parameterless spelling reports the refusal and one cascade with no panic.
(c) `entity Desc.mk(w: Int64)` beside `sort Desc { internal entity mk(v: Int64) }` — "internal error: entered unreachable code: dotted declaration `Desc.mk` reached load without the declaring scope pass 1 recorded". Not a debug assertion: every build.
(d) `sort Desc.Inner … end` beside `sort Desc { entity one; internal sort Inner … end }` — "the scope `lib.Desc.Inner` opens: sub-pass 1 defined `lib.Desc.Inner`, but the written name resolves to `Desc.Inner` here". An `assert_eq!`: every build.

MECHANISM, as far as read — two causes. (1) `scan_operation_params` runs once per DECLARATION on the one symbol the two share and ends with `set_arg_places(op_sym, …)`, so the second declaration's parameter places replace the first's; `emit_operation_equation` then looks the first declaration's `x` up among `[y]`, and its `debug_assert!` says the miss is reachable only for a parameter named `result`. (2) A declaration's own name is resolved as a REFERENCE (`load_operation`: `self.remap_name(&o.name)`; the entity and sort paths in their own way), so a dotted head whose target `internal` hides from the scope it is written in resolves to a symbol the scan never declared, and the load goes on under it.

WHAT. One refusal for each program and no panic. For (a): the duplicate is refused before either declaration's body is lowered, or the scan keeps each declaration's own places. For (b)–(d): decide which refusal a dotted declaration over an `internal` member gets, and resolve a declaration's own name to the symbol the scan declared for it. A dotted declaration is an entry of the sort — `operation Desc.other(x: Int64) -> Int64 = Desc.label(x)` written there loads, the body seeing the `internal` member — so "declared more than once", the refusal a public member of the name gets, is the candidate.

NOT THE FIX: an early return in `load_operation` when resolving the name pushed an error. Written and backed out during JMMHQ — it makes (b) one refusal and leaves (b) with a bodied first declaration and a different parameter name panicking, by cause (1).

CONTROL. The programs as rows, each failing on the tree before. `wi1049_duplicate_operation_declaration_test` and `wi929_dotted_secondary_entry_test` pass either way by design.

