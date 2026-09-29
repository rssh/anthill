## Attributes

- id: WI-20260929-AAQT5-an-application-whose-head-is
- created: 2026-09-29T16:03:52Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T16:03:52Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN APPLICATION WHOSE HEAD IS NOT A SORT DROPS ITS POSITIONAL ARGUMENTS SILENTLY: `operation h(s: foo[3]) -> Int64 = s.v` (an entity `foo`), `g[3]` (an operation), `Buf.buf[Int64]` load clean with the argument gone. `check_sort_type_args` returns Ok for any head that is not SymbolKind::Sort (kb/mod.rs: `if !self.has_kind(sort_sym, Sort) { return Ok(()) }`), and the type position (`type_expr_to_child_inner`) then drops the unslotted positional ("already reported above" — false for these heads). The binding position (`sort_binding_to_value`) instead carries it in a `reflect.SortView` wrapper (`assemble_binding_value`'s over-application branch), which refuses such a provision only by accident, printing the wrapper ("parameter 1 is `buf` where the spec's is `SortView(buf, Int64)`"), and which also adds `SortView(…)` follow-on cascades to already-failed SORT-head loads: `provides Store[State = Buf[Int64, 3, Bool]]` adds a member-fit refusal printing `SortView(Buf, Bool)[…]`; `sort X = Tagged[Int64, Bool]` + `provides X` adds a bogus "not a sort". FOUND by WI-20260924-F3FYJ's review (V9/V15/V19), PRE-EXISTING. FIX: report an over-applied positional for any RESOLVED head at both lowering sites (only an unresolved name, already reported, stays silent) — in `check_sort_type_args` before its sort gate or at each site; then drop the SortView over-application branch (`parameterized_value` unconditionally), the `Value::Entity` gate beside it, `sort_application`'s SortView arm (typing/sort_alias.rs), and the type arm's own carrier split in favour of `parameterized_value`. A SPEC QUESTION for the user first: is a NAMED argument on a constructor head (`Buf.buf[T = Int64]`, which loads and is compared today) admitted? ACCEPTANCE: each non-sort-head spelling refused where it is written; a sort-head over-application reported once, with no SortView cascade; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-09-29T16:28:23Z — feedback — user

ALSO (found by the F3FYJ follow-up review, 2026-09-29): a TypeExtractor META-CONSTRUCTOR head with a NAMED argument — `operation f(x: anthill.prelude.TypeExtractor.TypeVar[name = Int64]) -> Int64 = 1` — is not a sort, so `check_sort_type_args` reports nothing and the builder is reached: it PANICS in `KnowledgeBase::make_parameterized_type` (the Sep 20 build and HEAD alike). F3FYJ's first cut read that builder's base structurally and turned the panic into a clean load with the parameter typed as a FORGED type variable (MEASURED), so the builder now admits a sort reference or the declared bottom sort `anthill.prelude.Nothing` only (`typing::bottom_sort_sym`), and this spelling panics again. Refusing an application to a non-sort head where it is written retires that panic too.

