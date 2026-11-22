## Attributes

- id: WI-20261122-517Y5-contract-clauses-as-written
- created: 2026-11-22T16:45:02Z

- status: Open
- status_agent: user
- status_at: 2026-11-22T16:45:02Z

- acceptance: cargo-test, scaland-sbt-test

## Description

Contract clauses as written: per operation, each requires / ensures clause with its source site and its goals as occurrences, and the clauses the loader adds told apart from the written ones
WHO NEEDS IT. anthill-traces (outside this repository; design: its docs/design/high-level-design.md §4.5) checks recorded traces against the contracts of a spec's operations and reports each violated clause by its index, the line it is written on and its text as written. Its spec model (its WI-20261122-KJ4CZ) lists an operation's value clauses and must leave out the ones the loader added. It reads the spec from the loaded KB only: the parse IR is pre-resolution and untyped, and pairing its clauses with OperationInfo's by position would be a second answer to what the loader already decided.
WHAT IS THERE TODAY (read from the code on 2026-11-22, at 6ee8780f7, unless marked measured).
- OperationInfo.requires / .ensures hold one Value per written clause: a hash-consed Value::Term, or conjunction(...) of the goals for a clause of several; a Value::Node only where a binding was written through a type alias (Loader::contract_goal_as_written). Loader::convert_clause_list_with_extra (kb/load.rs) converts each goal from its ParseTermId, where the span is at hand (Loader::source_span_of), and keeps none.
- kb.term_span(t), measured: None for every clause of cancelOrder, checkout, pay, getCart and getOrders of the explicit-state shop example, and of a one-operation probe spec. Where a span is recorded it is first-write-wins over hash-consed terms (the doc of term_spans), so two goals written alike would share one site.
- The typed form: OperationRecord.typed_contract (op_info.rs) holds a typed NodeOccurrence only for each conjunct that holds a comparison, read through typed_contract_conjunct / op_record, both pub(crate).
- The clauses the loader adds ride in requires after the written ones, as convert_clause_list_with_extra's extra_terms: WI-320's EffectsRuntime[Effects = E] for each free row variable of the effects, and WI-201's requires Spec[Member = ?P] for the bare-spec members the signature names. The one reader that tells any of them apart, typing::synth::is_effects_runtime_clause, is pub(super), matches the functor's name and knows nothing of the WI-201 clauses; all_operation_contract_clauses documents that it does not filter them.
- Source text: the SourceRegistry keeps each file's text (register_file), but KnowledgeBase.sources is pub(crate); the public reads are render_site (path:line:col) and source_name.
- WI-20261122-3QJ36 asked, among other things, for each clause's index and source span. anthill-traces' spike feedback narrowed that item to options on execute (WI-20261122-96QKW, delivered) and computed consts, and the span part dropped out with it. This item is that part, on its own.
WHAT IS ASKED.
- Each written contract clause kept as occurrences, as an operation body is (op_body_node): the clause's goals as NodeOccurrences, each with its own span, and the clause's written site.
- A public read per operation (name open, e.g. a method on the KB or a field of OpInfoRecord): for each written requires and ensures clause, in source order, its kind, its index among the written clauses of that kind, its site (a SourceSpan from its first goal to its last), the stored clause (the very Value OperationInfo holds for it, so a caller pairs the two without counting), and its goals as occurrences, the conjunction split.
- The loader's clauses (WI-320, WI-201) not read as written: left out of that read, or listed apart with no written site and the rule that added them. Either way a caller does not re-derive which clauses were synthesized.
- A public read of the text a SourceSpan covers (e.g. a source's text by SourceId, or the slice for a span).
- Open for the design: whether each goal's occurrence is the typed one (the typer's form, as typed_contract holds for comparisons today, then for every goal) or the one as loaded. anthill-traces types the goals it builds after substituting values either way (its design §4.4), so it needs the sites and the goals at least.
WHAT IS NOT ASKED. Changing what OperationInfo.requires / .ensures hold or what their readers compare (the override-refinement check compares stored clauses structurally); substituting values into clauses (WI-20261122-3QJ36).
DONE WHEN. A test in anthill-core loads a spec in which one operation has a requires of one goal, a requires of several goals, a goal written in two clauses so that both hash-cons to one term (a ?variable shared between them), an ensures over result, and effects with a row variable (so WI-320 adds a clause), and another operation names a bare-spec member (so WI-201 adds one). For each written clause it asserts the kind, the index, that the stored clause is OperationInfo's at that position, the text under its site exactly as written and the text under each goal's site; that the goal written twice has two different sites; and that neither loader-added clause is read as written. The test site states which assertions fail when the sites are backed out.

