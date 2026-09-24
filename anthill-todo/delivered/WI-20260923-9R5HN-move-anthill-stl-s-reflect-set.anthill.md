## Attributes

- id: WI-20260923-9R5HN-move-anthill-stl-s-reflect-set
- created: 2026-09-23T11:45:42Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-23T23:05:58Z

- acceptance: cargo-test

- tags: typing

## Description

MOVE ANTHILL-STL'S REFLECT SET OFF QUALIFIED-NAME REGISTRATION, SO ITS OPERATIONS CAN BE CLAIMED @[host_implemented] — the gap WI-20260922-BRT4Y left, recorded at its delivery.

WHAT EXISTS. BRT4Y made `@[host_implemented]` the declaration's claim and an `operation_map` entry its evidence, held to each other at LOAD (`load::check_host_implemented_claims`), and moved all 46 hardcoded registrations in anthill-core's `register_standard_builtins` to `HOST_FNS` rows named by binding blocks. One registrar was out of reach: anthill-stl's `reflect::builtins::register_reflect_builtins` (called from `runner::register_runtime`, i.e. `anthill run` and anthill-todo, and from guardians_test) still registers 24 operations by qualified name through the silent-skip `register_if_present`: `anthill.reflect.KB.{sorts, operations, constructors, fields, rules, descriptions, sort_template, reify, reflect}`, `anthill.reflect.{qualified_name, short_name, lookup_symbol, scope, kind, nonvar, ground, sort_as_term, can_be_sort, term_as_sort, resolve_sort_instantiation_param}`, `anthill.reflect.Substitution.{apply, compose, bindings}` and `anthill.kernel.not`. They are INVISIBLE to `is_host_mapped_op` / `is_interpreter_mapped_op` (WI-884's split: a rule body cannot reduce them, the typer does not count them as backed), UNMARKED (so `reflect.anthill`'s declarations still do not say they are body-less by design), and a KB missing their declarations skips them in silence. `wi_brt4y_host_implemented_test::every_operation_the_interpreter_registers_is_interpreter_mapped` covers `register_standard_builtins` only and says so.

WHY IT WAS NOT DONE INLINE — two obstacles, both structural:
 (1) THE FUNCTIONS LIVE IN THE WRONG CRATE. `HOST_FNS` is anthill-core's closed registry. A mapping in `rustland/anthill-stl/anthill/reflect.anthill` naming anthill-stl functions is a 'broken binding block' at EVERY interpreter build in anthill-core's own tests, which load that file without anthill-stl's crate — and since BRT4Y they must load it, because the stdlib does not load without its binding layer.
 (2) ELEVEN OF THEM CLOSE OVER `Rc<ReflectSyms>`, resolved from the KB AFTER load. WI-1122's embedder table (`kb.register_host_fn`) must be written BEFORE load — `set_host_op_mappings` seals it — so the embedder seam does not fit as the functions stand.

WHAT TO DECIDE AT PICKUP.
 (a) WHERE THE FUNCTIONS GO. Moving them into anthill-core as `HOST_FNS` rows answers (1) outright and matches where `term_field` / `extract` / `KB.facts_of` went (WI-880); `ReflectSyms` then resolves per call or is cached per KB, which answers (2). The alternative — registering through WI-1122 with lazily resolved symbols — keeps them in anthill-stl but leaves anthill-core's closure unable to load the binding without them, i.e. it re-opens (1).
 (b) `anthill.kernel.not`'s eval-side function belongs beside `kernel_struct_eq` in `rustland/anthill-stl/anthill/kernel.anthill`'s block; the resolver primitive (NAF) is untouched by this, as it was for `struct_eq`.
 (c) PREREQUISITE, DO IT FIRST: the SUBSTITUTION arena still reads with the receiver-arena shape BRT4Y removed from Map and Cell (`arena.x(&h)` indexing the CALLER's slot table with the handle's slot). The moment `Substitution.*` become interpreter-mapped, a rule body reduces them in scratch bridge interpreters and a handle crosses arenas — BRT4Y MEASURED the Map twin as a panic, and a populated slot answers from a DIFFERENT value silently. Move the reads onto the handle, with a cross-arena unit test like `cell_arena::a_handle_reads_the_arena_that_minted_it`.
 (d) VISIBILITY HAS CONSEQUENCES, as BRT4Y measured for Map (a rule-body operand now decides where it suspended; a carrier override now picks the host member). Measure the effect-free ones here — the KB readers and `Substitution.*` — at a rule-body operand, both polarities, and pin what changes.

ACCEPTANCE: the 24 are `HOST_FNS` (or equivalently checked) rows named by binding-block entries and their declarations carry `@[host_implemented]`; `every_operation_the_interpreter_registers_is_interpreter_mapped` covers the whole runtime registry (the reflect set merged into the standard registration, or the test extended), with a count before/after; `register_if_present` deleted if no caller remains; the substitution arena reads through the handle, driven by a cross-arena test; the rule-body consequences of (d) measured and pinned; full workspace green via rustland/scripts/test.sh.

REFERENCE: `anthill-stl/src/reflect/builtins.rs` (`register_reflect_builtins`, `ReflectSyms`), `anthill-stl/src/runner.rs` (`register_runtime`), `eval/builtins.rs` (`HOST_FNS`, `register_if_present`'s doc), `kb/host_fns.rs` (WI-1122 seal), `eval/map_arena.rs` / `eval/cell_arena.rs` (the handle-read shape), WI-20260922-BRT4Y.

## Changes

### 2026-09-23T23:05:43Z — feedback — user

Delivered (2026-09-24, 38102d2e). Decision (a): the functions MOVED to anthill-core (eval/reflect_builtins.rs; the shared reader to kb/reflect_reader.rs, which anthill-stl's bridge now reads across the crate boundary) as 24 HOST_FNS rows; ReflectSyms resolved per call. (b) kernel.not mapped in its own kernel.anthill block (artifact reflect_builtins.rs), resolver NAF untouched. (c) SubstHandle::with_subst reads the minting arena; slots hold Rc<Substitution> so no borrow is held during a read. Measured pre-ticket: cross-interpreter lookup answered some(1) for 7 (silent) or panicked; with the receiver read restored the rule-body chain panics the CLI. register_reflect_builtins and register_if_present deleted; anthill-core drops its anthill-stl dev-dep. Counts on the full runtime registry: 183 -> 207 rust-mapped, 24 -> 0 invisible (pinned by name + claimed in wi_brt4y). (d) wi_9r5hn_reflect_set_test pins before/after at a rule-body operand: not(KB.constructors(..)=[..]) and not(can_be_sort(Color)) were 1 DEFINITE (unsound), now 0; positives 0 -> 1, wrong-value rows 0. Needed by-content reads: TermView for shape-only Term args, TermRepr decoder through the view, substitution operands via Value::carried; reflect.unify lowers by content. Also fixed: KB.sorts namespace filter compared the SHORT name (wrong answer everywhere). New load refusal HostMappingDuplicate: two operation_map/const_map entries for one member in one language (loaded clean, last-wins). NOT fixed, reported: closure/stream arenas still read via the receiver interpreter (enter_closure, stream_split_first); Map/Cell ops match by carrier (a <=>-bound Map suspends at Map.size); Substitution.apply(..) cannot be written in a rule body (typer reads 'apply' as the reflect form; pre-existing); reader read_facts failures panic inside a bridge. Workspace 7421/0 across 36 binaries; scaland 614/0.

