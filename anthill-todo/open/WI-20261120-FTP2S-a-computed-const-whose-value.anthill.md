## Attributes

- id: WI-20261120-FTP2S-a-computed-const-whose-value
- created: 2026-11-20T22:26:55Z

- status: Open
- status_agent: user
- status_at: 2026-11-20T22:26:55Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A COMPUTED CONST WHOSE VALUE IS NO LITERAL IS ITS NAME IN A QUERY (found writing WI-20261113-24ZZ0; filed with the user 2026-11-20). kernel-language 5.9's query exception says a const with no load-time value is evaluated in a query pattern, as an operation body would evaluate it; load::query_slot_const evaluates it (KnowledgeBase::evaluated_const_literal) and keeps the value only where it is a literal, keeping the symbol otherwise. Measured on f794036d with the debug CLI: over const origin: P = pt(x: 4), the query ?r <=> origin answers ?r = origin; P.getX(origin) is left undecided (residual unify(?r, getX(origin))); the same for const xs: List[T = Int64] = [1, 2] (?r <=> xs answers xs, len(xs) undecided). A const holding a dictionary is refused there since 24ZZ0 (LoadError::DictionaryConstInQuery), which this ticket keeps. To decide with the user first: either the query takes the evaluated value of a non-literal const where the value has a term form (an entity, a list; a closure has none), so a pattern matches a fact holding it and a call is handed it, or such a const is refused in a query naming it, and 5.9's sentence is narrowed to a literal value. ACCEPTANCE: each row driven to its value; the part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

