## Attributes

- id: WI-20261023-9XXBW-proposal-069-stage-5-rule
- created: 2026-10-23T05:46:24Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T05:46:24Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261023-CX743-proposal-069-stage-3-operation

- tags: proposal-069

## Description

PROPOSAL 069 STAGE 5 — RULE-COLUMN DEFAULTS (§1.5). Only a predicate's body-less declaration (proposal 061) writes a column default: `rule within(?x, ?limit = 10)`, optionally typed `?limit: Int64 = 10`. At a call — a rule-body goal, a query, a Relation citation — an omitted column takes its declared default, a column with no default is free, and an explicit `?` suppresses the default; the default is inserted as though written, so for an output column it is checked against the clauses' answers. Omission reads positional arguments from the left and named ones by name; it rests on one arity per predicate (kernel-language §5.3, WI-20260821-6WVJB), so a short clause or fact beside a defaulted declaration is already refused as another arity and no clause head is ever filled. `?v = e` in a declaration head is the default; in a clause or fact head it is refused naming the declaration (census the existing `?v = e` clause-head arguments first; each is rewritten to `eq(…)` or is a misplaced default). The default may name earlier columns and visible constants, constructors and operations (an operation call evaluated as 068 does); a forward reference is refused. The column has one type — the declared one, else the relation-schema join across all clauses — and the default is checked once against it, after schema synthesis; a defaulted column with neither is refused at the default, which never invents a type. Goal insertion and `resolve_relation_arg_columns` share one owner. ACCEPTANCE driven by value, with back-out controls: the §1.5 table (`within(x: 5)` / `within(x: 5, limit: ?)` / `within(x: 5, limit: 3)`, with and without the default) at a goal, a query and a citation; an output column's default checked; positional `within(5)`; a clause-head default and a clause-head `?v = e` refused naming the declaration; a default outside its schema type refused naming that type; an untyped defaulted column with no clauses refused. Acceptance: rustland/scripts/test.sh, scaland sbt testFull, npx tree-sitter test.

