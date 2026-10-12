## Attributes

- id: WI-20261012-6SAAP-a-constant-written-by-its
- created: 2026-10-12T14:23:40Z

- status: Open
- status_agent: claude
- status_at: 2026-10-12T14:23:40Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

A CONSTANT WRITTEN BY ITS PARAMETER'S NAME AS A BRACKET'S ENTRY IN A TERM IS READ AS A NAME SPELLED WITH ITS TEXT — over `sort Vec[T, N] { operation tag() -> Int64 = 9 }`, `sort Box[V]` and `operation nm(t: Type) -> Int64 = 1`, `fact holds(Vec[T = Int64, N = 3])` is refused "unresolved name '3'", so is the fact head `fact Vec[T = String, N = 4]`, and in an operation body `nm(Vec[T = Int64, N = 3])` adds "type mismatch in 3.name: expected resolved name, got unresolved"; a string is reported with its quotes (`N = "a"`: "unresolved name '"a"'"). The positional spelling is refused one bracket down — `fact holds(Box[V = Vec[Int64, 3]])` — and loads at the top of the term: `fact holds(Vec[Int64, 3])` stores `Vec(Int64, 3)`, `fact Vec[Int64, 3]` loads, and `nm(Vec[Int64, 3])` loads. The companion call answers in the named spelling: `Vec[T = Int64, N = 3].tag()` is 9, its bracket being lowered as a type. Measured 2026-10-12 on 930dba3b; found with WI-20261012-TCSGT.

WHY. `convert_type_value` (parse/convert.rs) has no arm for a literal: its default arm reads the node's text as a name. A named entry and every entry of a nested bracket go through it; the top-level positional arm of `convert_instantiation_term` hands a literal to `convert_term`, which is why that one spelling is the constant. TCSGT gave the tuple type, the arrow type and the effect row their own arm there and left the literal on the default one.

WHAT. Read a literal entry as the constant on both routes. MEASURED with that arm added (one line, `convert_term`; TCSGT's first full run, then taken back out): two rows that pin today's reading fail, and have to be decided rather than edited. `wi1106_parametric_data_sort_test::a_binding_that_resolved_to_nothing_is_refused_not_filed` holds that `fact Spec[T = 1]` "names no type, so the bracket must be refused", and the unresolved name is the refusal it asserts. `wi_qhdgc_require_spec_logical_variable_test::a_literal_stays_refused` holds that `require[Desc[T = 3]]` is refused naming `3`: the drop rule (`Loader::report_dropped_spec_binding`) reads that name off the term the entry was lowered to, and with a constant there the bracket is still refused, by the sentence that names nothing. So say first whether a fact's bracket may hold a constant written by name as it does one written positionally, and have the drop rule name a literal by its text as it names a tuple type.

NOT THIS TICKET'S, measured beside it: a constant entry in an operation body loads and is not evaluated — `nm(Vec[Int64, 3])` is "expected Type (a type argument), got Int64" (eval's `expect_type_arg` takes a term) — so the named spelling made to load gets the positional one's answer there.

CONTROL. An integer, a string and a boolean, each as a fact's stored entry matched by a goal (`holds(Vec[T = Int64, N = ?n])` binds 3), in a fact's head, as an operation body's argument, and one bracket down in both spellings. Fences: the top-level positional spelling, the companion call, a variable entry, a tuple-type entry. Say which rows fail with the change backed out.

DONE WHEN: a constant written by its parameter's name, and one a bracket down, is the constant the top-level positional spelling is; the two pinned rows say what was decided; the gate is green.

