## Attributes

- id: WI-20261124-RX9Z3-a-sort-s-constructors-are
- created: 2026-11-24T20:03:25Z

- status: Open
- status_agent: user
- status_at: 2026-11-24T20:03:25Z

- acceptance: cargo-test

## Description

A sort's constructors are listed in the order of a std HashMap, another in each process: constructors_of_sort and field_constructors_of_sort
WHO NEEDS IT. Any caller that reads a sort's constructors as a sequence and lets the order show. anthill-traces' value generator (its WI-20261122-219KE) picks a constructor by its index with a seeded PRNG, so one seed drew another constructor in another run, and the same inputs did not give the same trace. In anthill, term_ser's NoFieldSchema error lists a sort's constructors in this order (persistence/term_ser.rs:1775), and eq_derive sorts them by Symbol::index before it emits a match (kb/eq_derive.rs:755, :952), which reads as a guard against the same thing.
WHAT HAPPENS. Read from code (48878b3a1): KnowledgeBase::constructors_of_sort (kb/mod.rs:8532) collects the constructors by iterating entity_parent, a std HashMap<Decl, Symbol> (kb/mod.rs:1455) with its RandomState, so it answers in that map's order; field_constructors_of_sort (kb/mod.rs:8558) starts from it. sort_children (kb/mod.rs:9593) reads sort_entities, a Vec per sort pushed in registration order; the two maps are written together, and only, in register_entity_of and register_self_sort.
MEASURED 2026-11-24 on 48878b3a1, debug, through anthill-traces' test binary (one load of its fixtures per process, four processes): an enum declared with three nullary constructors A, B, C came out of field_constructors_of_sort as [A, B, C], [C, A, B], [B, C, A], [C, B, A]; List's constructors as [nil, cons] twice and [cons, nil] twice; an enum declared S, F as [F, S] four times (stable by chance, and not the declared order). sort_children gave the declared order in all four runs, for each of them.
WHY IT MATTERS. Output that walks a sort's constructors changes between runs with no input changed, and only sometimes: a run may happen to match, so a test of it passes or fails by chance. A caller cannot fix the order without knowing to sort, and by what: Symbol::index (eq_derive's choice) is interning order, which is declaration order only where nothing interned a constructor's name before its declaration (read from code, not measured).
WHAT IS ASKED. constructors_of_sort, and so field_constructors_of_sort, answer in declaration order (the order sort_children holds), and their docs say so. One way: read sort_entities instead of scanning entity_parent, which also visits a sort's own constructors instead of every entity of the KB. eq_derive's sort may then be dropped or kept; that is its call.
DONE WHEN. (1) A test loads a sort of at least three constructors, declared in an order that is not their names' order, into several fresh KnowledgeBases (std gives each RandomState its own keys, so one process should suffice; read, not measured) and reads declaration order from constructors_of_sort and field_constructors_of_sort every time; the control: the same read from entity_parent's iteration differs between the loads. (2) A free-standing entity still lists itself, once. (3) term_ser's NoFieldSchema error names the constructors in declaration order.

