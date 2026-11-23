## Attributes

- id: WI-20261122-WC18Y-proposal-021-1-serialize-one
- created: 2026-11-22T13:20:07Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-23T01:11:42Z

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

## Changes

### 2026-11-23T01:11:36Z — feedback — claude

Implemented 2026-11-23. The ticket asks for docs/proposals/021.1; with the user, 021 was revised IN PLACE instead (6ee8780f7, "Revision of 2026-11-22"), and what implementation settled is folded into 021 in this change.
Rust (anthill_core::persistence::term_ser): decode_value(kb, &json, ty: &impl TermView, CodecOptions) -> Result<TermId, ValueError>; encode_value(kb, value: &impl TermView, ty: &impl TermView, CodecOptions) -> Result<serde_json::Value, ValueError>; type_from_text / type_to_text. CodecOptions { variables, entity_tags, tag_names, big_int, wider_tuple }, CodecOptions::data_file() for the files. ValueError { path: JsonPath, expected, problem: ValueProblem }, rendered `{path}: expected {T}, {problem}`; the path is into the JSON as written, so it passes through tags ($.S.ps[1].P.id). load_json / load_toml / serialize_json / serialize_toml are rebuilt on the pair with their signatures; serialize_json_at / serialize_toml_at are added, because a meta.entity with type arguments is a type, and lowering a type's text needs &mut KB (the writers taking a name refuse a bracket, naming them). SerError gains Row { index: Option<usize>, error } (None for a `data` object; rendered data[2].x / data.x) and EntityType; UnknownField, MissingField, UnknownConstructor and InvalidValue moved into ValueProblem, which also has NotTagged and NotAType beyond 021's first table.
The type walk reads types through typing::extract_type; a sort's parameters are bound in an environment (canonical variable -> the type written there in ITS environment, or the declared default, or Open(param), named in the refusal since the variable itself is anonymous), so a parameter is substituted at any depth without building a type term (the encoder has &KB). A type's text is lowered by load::lower_type_text: the loader's own lowering (Loader::type_expr_to_value, then refuse_annotation_naming_no_type, split out of annotation_type_to_value) of the one host-supplied `const` the text is wrapped in, at <global>, on behalf of no file, under one name-only source (SourceRegistry::synthetic). `List[T = ?]` reads as the bare List, as in a declaration; `?x` is refused. anthill-core enables serde_json and toml `preserve_order`.
Tests: anthill-core tests/include/wi_wc18y_value_codec_test.rs (wi_tests), 12 rows, 14 back-outs measured and recorded at their rows. The ticket's faults measured against e25f0b734 at the file level, the only public level it had: its writer wrote nested entities untagged and its own file failed to load back ("inline object with multiple keys"); "f": 3 loaded a second fact, distinct from the source's; a bracketed meta.entity was "unknown entity"; "id": 3.5 under Int64 loaded as a Float. Existing tests: error variants moved into ValueProblem (github_todo_test, wi926, wi912, toml_ser_test, wi_9wvt7_review7); wi_jb6rs's type-with-bindings row now asserts it round-trips as its text (decision D) where it asserted the writer's refusal; toml_ser_test's hand-built Holder fact is given its required `tags`, since the writer now refuses a fact missing a declared field.
/code-review high: 9 findings, all folded: one source entry per type-text call; the annotation's refusal at Type (a const's or a namespace's name read as a type); the asking file; out-of-range negatives reported NotAnInteger; two silent skips in the parameter environment (now a panic on the WI-954 invariant); a field type's own problem masked as MissingField; a self-contradicting shorthand message; two same-named variables written alike (pre-existing; now ?x, ?x_2, and an anonymous one occurring twice is named); a `data` object's rows reported as data[0].
Gate: scripts/test.sh, 36 binaries, 12 607 passed, 1 failed (the toml_ser_test Holder fixture above, fixed test-only; builtin_tests rerun 101 / 0), 26 ignored; anthill-cli 323 + 19; scripts/families.sh green; scaland unchanged (no Scala source touched; testFull 811 + 51 + 1 passed).

### 2026-11-23T06:09:34Z — feedback — claude

Second /code-review (run by the user), folded in the same day; this supersedes the previous note where they differ. 15 findings.
Decided with the user (2026-11-23), changing 021: (1) a labelled tuple is written in the VALUE's own order and read in the order the object writes, since its order is its identity (kernel §4.5); measured before: fact H(p: (n: 3, state: Open)) at p: (state: Status, n: Int64) was written {"state":…,"n":3} and reloaded as a SECOND fact. Entities stay in declared order; a positional tuple stays an array. (2) CodecOptions::data_file() refuses a wider tuple (WiderTuple::Refuse), while encode_value's default still projects: measured before, fact Wide(p: (state: Open, n: 3, extra: 1)) loads and was written without `extra`.
Fixed: reading a type's text asserted a DescriptionInfo for `?x {< … >}?` (the loader is lent as to a query, lent_to_query, which gates nothing else); OmitAtEntityType decoded a runtime account at its constructor's own type; the encoder dropped arguments beyond the declared fields (now UnknownField, in the file writer too); NotOneField for a one-field constructor named both spellings; a trailing top-level import in a type's text was accepted (ParsedFile.imports); the writer wrote a namespace's or a const's name at Type, which the reader refuses (is_type_term now: a face, or a type reading with no face beside it); `?x` under Option[Option[…]] was read as some(?x), which the writer refuses; a TOML nan aborted the whole file (now the error of its row, at its place and declared type, beside the others: toml_to_json records the place, the row's decoder refuses it there); the test's term_of assumed a type rides a term (the rows now compare through the type's text; the file is green under ANTHILL_TEST_NODE_CARRIER=1); stale docs (KnowledgeBase::build_list's, 021's error example); back-out notes for the two rows without one.
Not changed: (a) "a program-written variable is De Bruijn and the writer refuses it" does not reproduce: fact Likes(who: ?x, what: ?x) is written "?x"/"?x" and loads back (measured). (b) A data file naming a generic entity whose parameter has no default is refused, naming the parameter: 021 states it ("one with no default is refused") and lists it among the changes for files that loaded before; meta.entity with a bracket, or serialize_json_at, is the spelling for such a file. (c) "1e19 is reported OutOfRange, not NotAnInteger": serde_json without arbitrary_precision keeps no trace of how a rounded number was written, so a number past the range is out of range however written; 021 says so.
Tests: wi_wc18y_value_codec_test, 12 rows, 26 back-outs measured, each recorded at its row. Gate on the final code: scripts/test.sh, 36 binaries, 12 608 passed, 0 failed, 26 ignored; scripts/families.sh green (after the annotation split; the later load.rs change is inside lower_type_text only); scaland unchanged (testFull 811 + 51 + 1).

