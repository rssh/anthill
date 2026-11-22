## Attributes

- id: WI-20261122-WC18Y-proposal-021-1-serialize-one
- created: 2026-11-22T13:20:07Z

- status: Open
- status_agent: claude
- status_at: 2026-11-22T13:20:07Z

- acceptance: cargo-test, scaland-sbt-test

## Description

Proposal 021.1: serialize ONE value at a declared type — the JSON codec of term_ser as public API, over TermView

WHO NEEDS IT. anthill-traces (a tool outside this repository, not yet published) reads and writes traces of operation calls as JSON: each step's inputs and output are values of the spec's types — an Int64 parameter, a ShopState with lists of entities, a labelled tuple result `(state: ShopState, order: Order)`. Its design takes proposal 021's mapping for these values so that a trace value and a persisted fact read the same. Its codec item (WI-20261122-GF9FA there) would otherwise copy 021 into a second implementation that can drift from this one. Any embedder that exchanges typed values with JSON (an MCP tool, an LLM reply) is in the same position.

WHAT IS THERE TODAY (read from persistence/term_ser.rs at d1b3d716b; the three marked MEASURED were run with `anthill query -p <dir>` on an anthill.json data file):
- The per-value pair is private: `value_to_term_typed` (JSON -> TermId at an optional type) and `term_to_value` (TermId -> JSON). The public API is file-level only: `load_json` / `load_toml` take the `meta` + `data` envelope, ASSERT each entry as a fact and return a count, so a caller gets no term back and cannot decode a bare Int64; `serialize_json` / `serialize_toml` take fact RuleIds.
- Encoding reads a TermId only. A `Value` (what `Interpreter::call` returns) or an occurrence has to be lowered first.
- MEASURED: a nested entity with more than one field does not decode. `S(ps: List[P])`, `P(id: Int64, name: String)` with `"ps": [{"id": 1, "name": "a"}]` fails with `inline object with multiple keys must be inside a data entry`: below the top level an object is read only as `{"Ctor": value}`. 021 says nested entities "follow the same rules recursively"; a one-field nested entity is read as a constructor key instead.
- MEASURED: a string beginning with `?` is a variable everywhere (021 §Variables): `"name": "?who"` loads as a fact holding the variable ?who. Right for hand-written fact files, wrong for data that came from a running system, where "?who" is a string and a variable makes every goal over it hold or go residual.
- MEASURED: numbers are read by their JSON shape, not the declared type: `"x": 3` under `x: Float` loads as the Int64 3 (the fact matches `x: 3`, not `x: 3.0`); a non-integral number under Int64 is read as a Float instead of refused.
- Errors (`SerError`) carry no location: a bad value deep in a document is reported without saying where.
- 021 has no rule for tuple types, Set or Map. Option is specified only as a field present or absent; the code reads JSON null as none(), which 021 does not say, and an Option as a list element, tuple element or top-level value has no spelling in 021.
- Key order of an encoded object is serde_json::Map's: alphabetical, unless some crate in the build enables serde_json's `preserve_order` feature, which makes it insertion order. So the bytes of an encoding depend on the dependency graph.

WHAT IS ASKED: write docs/proposals/021.1-<name>.md amending 021, and implement it.
1. The VALUE is the unit. 021's mapping rules define how one value of a declared type is written; a file of facts (the `meta` + `data` envelope) becomes one use of that mapping, unchanged on disk.
2. Public API in anthill-core, two functions (names open): decode(kb, &serde_json::Value, type, options) -> Result<TermId, error> and encode(kb, &impl TermView, type, options) -> Result<serde_json::Value, error>. The type is required at this entry point (no schema-less guessing). `load_json` / `serialize_json` (and the TOML pair) are rebuilt on them and keep their behavior.
3. Variables are an option of decode, OFF by default: then "?x" is the string "?x" and no `\?` escape is read. The fact-file loader turns them on, as today. Encoding a term that holds a variable with variables off is an error.
4. Numbers follow the declared type: an integral number under Float is a Float; a non-integral or out-of-range number under Int64 is an error; BigInt as today.
5. Nested entities decode at any depth (the MEASURED failure above). An object under an entity type is that entity's fields; `{"Ctor": ...}` is read only under a sort with several constructors. 021.1 states how the single-field shorthand (`{"ToolPasses": "cargo-test"}`) is told apart from a one-field constructor whose field is itself an entity.
6. Specified in 021.1, each either mapped or refused with an error naming the type: tuples (a labelled tuple as an object keyed by its labels; positional ones as arrays, or refused); Option outside an object field (null = none(); say what Option[Option[T]] does); Set and Map.
7. Errors carry the JSON path of the value (e.g. `$.steps[3].output.stocks[1].reserved`) and the expected type.
8. Encoding is deterministic and does not depend on cargo features: object keys in the order the entity declares its fields (or another stated order), whatever serde_json's features.

WHAT IS NOT ASKED: changes to the data-file convention of the CLI (WI-746); TOML beyond following the same value mapping (TOML still cannot hold a null); publishing anything to crates.io.

DONE WHEN: 021.1 is written and the public pair is driven by tests in anthill-core:
- round trips through decode and encode for an entity with a List of multi-field entities, a nested entity, an enum value, a constructor with fields and the shorthand, Option in a field and in a list, a labelled tuple, BigInt, and a Float written as `3`;
- with variables off, "?x" under String decodes to the string "?x"; with them on, as today;
- `3.5` under Int64 is an error whose message holds the JSON path and the type;
- the encoding of an interpreter `Value` and of a TermId of the same term are the same bytes;
- the existing term_ser and data-file tests pass through the rebuilt `load_json` / `serialize_json`.
The test site names which of these fail against today's private functions (the three MEASURED faults at least).

