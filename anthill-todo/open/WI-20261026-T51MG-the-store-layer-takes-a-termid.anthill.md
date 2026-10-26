## Attributes

- id: WI-20261026-T51MG-the-store-layer-takes-a-termid
- created: 2026-10-26T09:10:36Z

- status: Open
- status_agent: claude
- status_at: 2026-10-26T09:10:36Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE STORE LAYER TAKES A TERMID, SO ITS ROW IS LOWERED AT THE BOUNDARY — the one place WI-20261024-QJ6X1 left a host builtin reading its `Term` argument by lowering rather than through the carrier-neutral view. Filed by the user's decision, 2026-10-26.

WHAT IS LOWERED TODAY (rustland/anthill-core, after 428e25fd). The builtins `Store.persist` (fact), `QueryableStore.retrieve` (pattern) — `eval/builtins.rs`, `persistence_persist` / `persistence_retrieve`, through `reflect_builtins::expect_term` — and the KB entry points `persist_mirrored`, `update_persistent`, `assert_persistent`, `assert_checked_persistent` (`kb/extent.rs`; the last is also called by `anthill-stl/src/reflect/bridge.rs`) each lower their row with `node_occurrence::value_to_term`, because everything below them is `TermId`-typed: the `Store` trait (`persistence/mod.rs`: `persist(kb, fact: TermId, …, meta: Option<TermId>)`, `update(…, new: TermId, …)`, `retrieve(kb, pattern: TermId) -> Vec<TermId>`), its three backends (`FileStore` prints with `print::print_fact(kb, TermId, …)` and cancels a buffered write by comparing `TermId`s; `IndexedFileStore::retrieve` matches with `pattern_matches(kb, TermId, head)`, `extract_string_id(kb, TermId)` and `kb.get_term(pattern)`; `ItemPerFileStore::buffer_write(kb, fact: TermId, …)`), and the resident copy, asserted with `assert_fact(term)` / `assert_checked(term, …)`. Until QJ6X1 these sites used `alloc_from_value`, which refused an occurrence (`persist` and `retrieve` as an `Internal` error); `value_to_term` reads one, but it interns every row it is handed, an occurrence-carried row included.

WHAT. The row crosses the store boundary as a `Value` and is read through `TermView`: the trait takes the row, the pattern and the meta as values and `retrieve` answers values; a backend prints with `TermPrinter::print_value` (which reads every carrier) and matches through the view; the resident row is asserted on its own carrier (`assert_fact_value` exists for a value head). A store that must key a row by content keys it by its structural fingerprint (`term_view::goal_fingerprint`), as `MapKey` does since QJ6X1, not by a `TermId`. Interning stays only where the KB itself requires a term, and is stated at that site.

CONTROLS. A row per backend and per operation — persist, update, retract, retrieve — over one fact on each carrier: an entity an operation built, the fact's term, an occurrence (`node_occurrence::value_as_occurrence`), and an entity holding an occurrence child; each writes the same text and answers the same retrieve. That no row is interned is driven with `KnowledgeBase::term_store_len` around the call. The rows of `tests/include/wi_qj6x1_a_builtin_judges_the_value_test.rs` and `persistence_builtins_test.rs` pass either way; they are the floor, not the measure.

