## Attributes

- id: WI-20261120-FTP2S-a-computed-const-whose-value
- created: 2026-11-20T22:26:55Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-20T23:04:27Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A COMPUTED CONST WHOSE VALUE IS NO LITERAL IS ITS NAME IN A QUERY (found writing WI-20261113-24ZZ0; filed with the user 2026-11-20). kernel-language 5.9's query exception says a const with no load-time value is evaluated in a query pattern, as an operation body would evaluate it; load::query_slot_const evaluates it (KnowledgeBase::evaluated_const_literal) and keeps the value only where it is a literal, keeping the symbol otherwise. Measured on f794036d with the debug CLI: over const origin: P = pt(x: 4), the query ?r <=> origin answers ?r = origin; P.getX(origin) is left undecided (residual unify(?r, getX(origin))); the same for const xs: List[T = Int64] = [1, 2] (?r <=> xs answers xs, len(xs) undecided). A const holding a dictionary is refused there since 24ZZ0 (LoadError::DictionaryConstInQuery), which this ticket keeps. To decide with the user first: either the query takes the evaluated value of a non-literal const where the value has a term form (an entity, a list; a closure has none), so a pattern matches a fact holding it and a call is handed it, or such a const is refused in a query naming it, and 5.9's sentence is narrowed to a literal value. ACCEPTANCE: each row driven to its value; the part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

## Changes

### 2026-11-20T22:33:30Z — feedback — user

MEASURED FIRST on e2fce05e with the debug CLI (2026-11-20), over const origin: P = pt(x: 4), xs: List[T = Int64] = [1, 2], so: Option[T = Int64] = some(3), tup: (a: Int64, b: String) = (a: 1, b: "x") beside fact at(p: pt(x: 4)), hasXs(l: [1, 2]), hasO(o: some(3)): at(p: origin), hasXs(l: xs) and hasO(o: so) answer NO SOLUTIONS (a silent wrong no, the miss 5.9's query exception exists to prevent); ?r <=> origin, ?r <=> xs, ?r <=> tup answer the name; P.getX(origin) and len(xs) are undecided, and written dotted (p.k.P.getX(p.k.origin)) the argument stays a field_access chain. A computed scalar (const sum: Int64 = 2 + 3) works: hasN(n: sum) true, ?r <=> inc(sum) 6. A const's value cannot raise: a dividing body is refused at load (Divisible.div declares Error). DECIDED WITH THE USER (2026-11-20): a query evaluates the const and takes its value wherever it has a term form (node_occurrence::value_to_term), and refuses one with none (a closure), naming the const, as a dictionary const is since 24ZZ0. Filed apart, with the user: a const applied as a function, rule viaF(?r) :- ?r <=> f(1) over const f: (x: Int64) -> Int64 = lambda (x: Int64) -> x + 1, answers the term f(1), in a rule body and a query.

### 2026-11-20T22:59:01Z — feedback — user

DONE, NOT COMMITTED (2026-11-20; spec text awaiting the user's approval). load::query_slot_const (the data-slot fold of convert_query_node's three const sites) evaluates a const with no load-time value (KnowledgeBase::evaluated_const_value, replacing evaluated_const_literal) and holds a literal, or the term of a value with one (node_occurrence::value_to_term) spliced and typed at the const's declared type; it refuses, naming the const (LoadError::QueryConstHasNoValue, which DictionaryConstInQuery became), a dictionary at the declared type's head (24ZZ0) or inside the value (found by /code-review: spliced, ?r <=> od answered some(value: Dictionary(impl: Int64))), a function, and a const the evaluator cannot compute (a host const with no binding: a silent no before). A Bool const at a goal is query_goal_const, as before. Rows: wi_ftp2s_query_const_value_test (4: facts found through an entity, list, option, tuple and an element-open list const, with controls; a call handed the value, bare and dotted, getX 4 and len 2; the refusals; literal, scalar and Bool goal as before). Back-outs over the whole wi_tests (9687), one optimized build: control 0 fail; the value kept out (the name kept) 3; the refusals off 1; the nested-dictionary refusal off (local, 53 rows) 1. /code-review high: 5 findings, 2 fixed (the nested dictionary; 'holds a function', not the runtime variant), 1 no change (the host const refused: the loud form of the silent no), 2 skipped (a const evaluated again per reference in a query, as before; no row lowers a value through value_to_term's Node arm, a Type const being refused at load by the purity gate). Gate 12432 / 0 / 17 (36 binaries); families.sh green on both carriers; scaland testFull 811 + 51 (2 skipped) + 1.

### 2026-11-20T23:04:26Z — feedback — user

DELIVERED (2026-11-20): committed 0f4bdd411; kernel-language 5.9's query exception approved by the user. Gate 12432 / 0 / 17; families green on both carriers; scaland testFull green.

