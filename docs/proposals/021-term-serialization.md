# Proposal 021: Term Serialization to TOML/JSON

**Status:** Proposed; revised 2026-11-22 (WI-20261122-WC18Y, see [Revision of 2026-11-22](#revision-of-2026-11-22))
**Depends on:** None
**Affects:** Persistence layer (`rustland/anthill-core/src/persistence/term_ser.rs`), KB load pipeline, Stage 0 design

## Motivation

The anthill language is designed for **logic** — rules, queries, constraints, sort definitions. But much of what tools read and write is **data** — entity instances like tasks, tool definitions, project config. Writing data in the anthill DSL works but is verbose and requires parsing the full grammar:

```anthill
fact Task(id: "WI-AUTH-001", description: "Define auth traits",
          status: Open, depends_on: nil,
          acceptance: cons(head: ToolPasses(cargo-test), tail: nil),
          context: cons(head: "src/models/user.rs", tail: nil))
```

Standard formats (TOML, JSON) are better for structured data: tools already know how to read/write them, they have mature libraries in every language, and they're familiar to developers.

Both representations produce the same KB fact. This proposal defines the standard mapping between anthill terms and TOML/JSON, so any entity type can be serialized without custom code.

The mapping is defined for **one value at a declared type**. A file of facts is one use of it. A tool that exchanges typed values with JSON outside any file uses the mapping directly: a trace of operation calls, whose inputs and outputs are values of a spec's types, or an MCP tool reply.

Such a tool needs an API over `TermView`, and until 2026-11-22 there was none. The per-value conversions were private. The public API was file-level only: `load_json` asserts each entry as a fact and returns a count, so a caller gets no term back and cannot decode a bare `Int64`, and `serialize_json` takes fact `RuleId`s. The writer read a `TermId` and nothing else. A `Value` an operation returned (`Interpreter::call`), or a value or type riding an occurrence, had to be lowered into the term store before it could be written. The pair below reads both the value and its declared type through `TermView`, on whichever carrier each rides.

## Design

### The unit: one value at a declared type

A value is written at a DECLARED TYPE. The type is a term, the same term the KB holds for an entity's field or an operation's parameter, on whichever carrier it rides. The type is required: there is no reading without one. Encoding checks the value against the type as decoding does, so an `Int64` under `Float`, or a constructor of another sort, is an error and not a guess.

### API

Everything below is public in `anthill_core::persistence::term_ser`. The names are proposals.

```rust
#[derive(Clone, Copy, Debug, Default)]
pub struct CodecOptions {
    pub variables: bool,             // false
    pub entity_tags: EntityTags,     // Always
    pub tag_names: TagNames,         // Short
    pub big_int: BigIntSpelling,     // NumberWhenItFits
    pub wider_tuple: WiderTuple,     // Project
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum EntityTags { #[default] Always, OmitAtEntityType }
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TagNames { #[default] Short, Qualified }
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum BigIntSpelling { #[default] NumberWhenItFits, AlwaysDigits }
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum WiderTuple { #[default] Project, Refuse }

pub fn decode_value(kb: &mut KnowledgeBase, json: &serde_json::Value,
                    ty: &impl TermView, opts: CodecOptions) -> Result<TermId, ValueError>;

pub fn encode_value(kb: &KnowledgeBase, value: &impl TermView,
                    ty: &impl TermView, opts: CodecOptions) -> Result<serde_json::Value, ValueError>;

pub fn type_from_text(kb: &mut KnowledgeBase, text: &str) -> Result<TermId, ValueError>;

pub fn type_to_text(kb: &KnowledgeBase, ty: &impl TermView) -> Result<String, ValueError>;

#[derive(Clone, Debug)]
pub struct ValueError {
    pub path: JsonPath,        // where, e.g. `$.steps[3].output`
    pub expected: String,      // the type declared there, printed as the KB prints a type
    pub problem: ValueProblem, // what was wrong
}
```

**`CodecOptions`** configures the mapping. Each default is the mapping as the rest of this proposal states it. The JSON does not record which options wrote it, so a value is read with the options it was written with. Where an option chooses between two spellings, the reader takes the chosen one and refuses the other, except `big_int`, whose reader takes both.

| option | default | alternative |
|---|---|---|
| `variables` | `false`: a string is the string it spells | `true`: `"?name"` is a variable, and a leading `\` escapes it (see [Variables](#variables)) |
| `entity_tags` | `Always`: every constructed value carries its tag (see [Entities and sorts](#entities-and-sorts)) | `OmitAtEntityType`: a value whose declared type's one constructor is the type itself is the object of its fields, at any depth (`{"x": 1, "y": 2}` at `Point`). That covers a free-standing entity, an eponymous sort with no other constructor, and a constructor's own type. A value at a sort's type is tagged still, and so is one at `Mix`, whose eponymous constructor has a sibling. |
| `tag_names` | `Short`: the constructor's short name, `"Open"`, `{"Verified": …}` | `Qualified`: its qualified name, `"app.Status.Open"`, `{"app.Status.Verified": …}`, which reads without the schema at hand |
| `big_int` | `NumberWhenItFits`: a number in the `i64` range, digits past it | `AlwaysDigits`: always its digits, for a reader that loses integers past 2^53 |
| `wider_tuple` | `Project`: a wider tuple value is written at the declared labels (see [Tuples](#tuples)) | `Refuse`: it is an error (`ValueProblem::WiderThanDeclared`) |

The file readers and writers use the defaults with `variables` on, so a data file has one format.

**`decode_value`** reads `json` as one value of type `ty` and returns its term. The term is hash-consed into `kb`'s term store. With `variables` on, its variables are fresh, and their scope is this one call. Nothing is asserted, so the KB's facts and rules are as they were. To pass the result to an operation, wrap it as `Value::term(id)`.

**`encode_value`** writes `value` at type `ty`. It reads `kb` and changes nothing. `value` may ride any carrier: a `TermId`, a `Value` an operation returned (`Value::Entity`, `Value::Tuple`, a scalar, `Value::Term`), or an occurrence. One term encodes to the same bytes on every carrier. A value that is not data, such as a closure, a stream, a map or a cell handle, is refused.

**The type** `ty` is a term on any carrier. An embedder takes it from the KB, as an operation's declared parameter or result type or an entity's field type (`KnowledgeBase::entity_field_types`), or reads it from text with `type_from_text`. A sort parameter it leaves unwritten takes its declared default (see [Mapping rules](#mapping-rules)). Any other type variable in it is refused.

**`type_from_text` / `type_to_text`** read and write a type as text, which is how a `Type` value is spelled (see [Mapping rules](#mapping-rules)). They are public because a type kept as text is read back by the same rule, whether it is a trace's record of a declared type or `meta.entity`. `type_to_text` writes every name qualified, one text per type. `type_from_text` resolves names at `<global>` and refuses one that is absent, ambiguous or `internal`.

**`ValueError`** says where the problem is, what type was expected there, and what went wrong. `Display` renders `{path}: expected {expected}: {problem}`. The `problem` is one of:

| `ValueProblem` | when |
|---|---|
| `WrongShape { found }` | the JSON value is not of a shape the type takes (a string under `Int64`, an array under an entity) |
| `NotAnInteger`, `OutOfRange` | a number under `Int64` or `BigInt` written with a fraction or exponent, or past the range |
| `UnknownField { name }` | a key that names no field of the constructor, or no label of the tuple |
| `MissingField { name }` | a required field or tuple component is absent |
| `UnknownConstructor { name, sort }` | a tag that is no constructor of the declared type |
| `NotOneField { constructor }` | a shorthand payload for a constructor without exactly one field, or a bare tag for one with fields |
| `RuntimeAccount { constructor }` | a constructor reserved to the runtime, at any depth |
| `NoDataSpelling` | the declared type has no data spelling (`Set`, `Map`, a function type) |
| `WiderThanDeclared { labels }` | with `wider_tuple: Refuse`, a tuple value with components its declared type does not name |
| `UnboundParameter { name }` | a field's type still holds a parameter after substitution and defaults |
| `Variable` | a variable where none has a spelling: any with variables off, a rigid or de Bruijn one, one standing for a whole `Option` |
| `Unrepresentable { what }` | a value with no spelling: `some(none())`, a list with a variable tail, a non-finite float |
| `UnknownName`, `AmbiguousName`, `InternalName` | a name in a type's text that is absent, ambiguous or `internal` at `<global>` |

**The file readers and writers** keep their signatures:

```rust
pub fn load_json(kb: &mut KnowledgeBase, source: &str, domain: Symbol) -> Result<usize, Vec<SerError>>;
pub fn load_toml(kb: &mut KnowledgeBase, source: &str, domain: Symbol) -> Result<usize, Vec<SerError>>;
pub fn serialize_json(kb: &KnowledgeBase, entity: &str, rule_ids: &[RuleId]) -> Result<String, SerError>;
pub fn serialize_toml(kb: &KnowledgeBase, entity: &str, rule_ids: &[RuleId]) -> Result<String, SerError>;
```

`load_json` and `load_toml` read the envelope, decode each row with variables on, assert it as a fact in `domain`, and return the number of rows. Every row's error is reported, not only the first. `serialize_json` and `serialize_toml` write the facts `rule_ids` as one envelope whose `meta.entity` is `entity`, the text of their constructor's type. A fact of another constructor is refused. `SerError` keeps its envelope errors (`Format`, `MissingMeta`, `UnknownEntity`, `AmbiguousName`, `ForbiddenInternalEntity`, `NoFieldSchema`) and gains `Row { index, error: ValueError }` for an error inside a row. The value errors it held (`UnknownField`, `MissingField`, `UnknownConstructor`, `InvalidValue`, `RuntimeAccount`) move into `ValueProblem`.

### Mapping rules

The declared type decides how a JSON value is read. A JSON value of a shape the type does not take is an error naming the type (see [Errors](#errors)).

| Declared type | TOML / JSON | Example |
|---|---|---|
| `String` | string | `"hello"` |
| `Int64` | number written as an integer, in `i64` range | `42` |
| `Float` | any number | `3.14`, and `3` is the Float 3.0 |
| `BigInt` | integer number in the `i64` or `u64` range, or a string of its decimal digits | `42`, `"123456789012345678901234567890"` |
| `Bool` | boolean | `true` |
| `Type` | the type's anthill text, names qualified | `"anthill.prelude.List[T = test.shop.Order]"` |
| `Option[T = U]` | `null` for `none()`, otherwise the value at `U` | |
| `List[T = U]` | array of values at `U` | `["a", "b"]` |
| a tuple type | array, or object keyed by label | `[1, "a"]`, `{"state": …, "order": …}` |
| a sort or an entity | the constructor's tag | `"Open"`, `{"Verified": {"at": "2027-03-15"}}`, `{"Point": {"x": 1, "y": 2}}` |

Under `Int64`, `3.5`, `3.0` and `1e3` are errors: a number written with a fraction or an exponent is not read as an integer, since past 2^53 it cannot be read exactly. Under `Float`, NaN and ±∞ have no JSON spelling and are refused when encoding. A `BigInt` is written as a number where it fits `i64` and as its digits past that. An unquoted integer past the `u64` range is refused under `BigInt`: the JSON parser has already rounded it to a float before the mapping sees it, so it must be written as its digits.

A value whose declared type is `Type` is a type, and a type is a term, so it is written as the text the language writes it in. Every name is qualified and an application's bindings are in the order of their keys' names, so one type has one text in every load: `anthill.prelude.Int64`, `anthill.prelude.List[T = test.shop.Order]`, `(state: test.shop.ShopState, order: test.shop.Order)`. The reader parses the text with the grammar's type rule and resolves its names at `<global>`, as `meta.entity` is resolved. A type holding a variable is refused.

The declared type's arguments are substituted into each field's type, at any depth: `cons.head` at `List[T = Stock]` is a `Stock`, and over `entity Box(items: List[T = T])` the field `items` at `Box[T = Int64]` is a `List[T = Int64]`. A parameter the declared type leaves unwritten takes its declared default (`sort T = ? default Int64`). A field whose type still holds a parameter after both is an error naming the parameter.

#### Lists

`List[T]` maps to arrays:

```
cons(head: "a", tail: cons(head: "b", tail: nil))  →  ["a", "b"]
```

The loader builds the cons-list from the array. The serializer flattens cons-lists to arrays. A list whose tail is neither `nil` nor a cell (a variable tail) has no array spelling and is refused when encoding.

#### Entities and sorts

**Every constructed value carries its constructor's TAG**, whatever its declared type. That holds for a sort with several constructors, for one with a single constructor of another name (`sort Shape { entity Circle(r: Float) }`), and for an entity, which is a sort with an eponymous constructor (`sort Vec3 { entity Vec3(…) }`), as a free-standing `entity P(…)` is. The tag is the constructor's short name, looked up among the constructors the declared type admits and nowhere else. A constructor with no fields is its tag as a string:

```
Open    →  "Open"
Draft   →  "Draft"
```

A constructor with fields is an object with its tag as the one key, and the object of its fields under it:

```
Verified(at: "2027-03-15")    →  { Verified = { at = "2027-03-15" } }
p = Point(x: 1, y: 2)         →  p = { Point = { x = 1, y = 2 } }
```

In the object of fields, a key that names no field is an error, and so is an absent required field. An absent `Option` field is `none()`.

The declared type does not decide the spelling, so adding a constructor to a sort re-spells nothing written before. A sort that declares its eponymous constructor beside others (`sort Mix { entity Mix(x: Int64)  entity Other }`) is the same rule: a value at type `Mix` is `{"Mix": {"x": 3}}` or `"Other"`. Only a row of a data file is written without its tag, since `meta.entity` names its constructor (see [File structure](#file-structure-meta--data-envelope)).

**The payload is read by its JSON shape alone.** An object payload is the constructor's fields object, as above. Any other payload is the single-field shorthand, the value of the constructor's one field. It is an error for a constructor that does not have exactly one field:

```
ToolPasses(tool: "cargo-test")  →  { ToolPasses = "cargo-test" }
```

A nullary constructor written `{ Closed = {} }` reads as `Closed` by the first rule. It is not written so.

**The writer uses the shorthand only where the field's encoding is not an object.** Over `entity Moved(to: Point)`, the value `Moved(to: Point(x: 1, y: 2))` is written `{"Moved": {"to": {"Point": {"x": 1, "y": 2}}}}`. As a shorthand it would be `{"Moved": {"Point": {"x": 1, "y": 2}}}`, which the reader takes as `Moved`'s fields, with `Point` as a field name.

#### Option

`null` is `none()` wherever an `Option` is declared: a list element (`[1, null, 3]` under `List[T = Option[T = Int64]]`), a tuple component, a top-level value. A present value is `some(…)` of it:

```
some(value: "x")  →  key = "x"
none()             →  (key omitted)
```

In an object of fields an `Option` field may be absent, which is `none()`, or `null`. The writer omits it.

Under `Option[T = Option[T = U]]`, `null` is the outer `none()`, and any other value is `some(…)` of the inner reading. `some(none())` has no spelling and is refused when encoding.

TOML has no `null`. A `none()` where a field cannot be omitted, as in a list or a tuple, is refused when writing TOML. TOML has `nan` and `inf`, which JSON does not, and the TOML reader refuses them, naming the field's path. It used to turn them into `null`, so `f = nan` under `Option[T = Float]` read as `none()`.

#### Tuples

A tuple type is `NamedTuple` applied to its components, one per label, in the type's order.

- If every label is positional (`_1`, `_2`, …), the value is an ARRAY with exactly that many elements: `(1, "a")` is `[1, "a"]`.
- Otherwise the value is an OBJECT keyed by its labels, with any positional components under their `_N` label: `(state: s, order: o)` is `{"state": …, "order": …}`, and `(_1: 1, b: 2)` is `{"_1": 1, "b": 2}`.
- The tuple of no components, `()`, which `Unit` is, is `[]`.

Encoding writes the components the declared type names and no others. An operation declared to return `(a: Int64)` may return `(b: 2, a: 1)`, which conforms to it by width (kernel §4.5). At that type the value is written `{"a": 1}`. A value carries no type of its own, so the declared type is all a reader of the trace can know of it.

#### Types with no data spelling

A type whose values are not data is refused, naming the type, at both ends: a sort with no constructors that is none of the types above (`Set`, `Map`, `Stream`), a function type, `Cell`. A `Map` value is a host handle, which `TermView` shows as opaque, so the KB alone gives nothing to encode. `SortedSet` is a data sort (`tip`, `bin`) and is mapped like any other.

### Variables

Variables are an option of the pair, OFF by default. The file of facts turns them on.

**Off:** a JSON string is the string it spells. `"?x"` under `String` is the string `"?x"`, and no escape is read. Encoding a value that holds a variable is an error.

**On:** a string value starting with `?` is a variable, at whatever type is declared, and `?` alone is anonymous. Under an `Option` the variable is the present value's: `"?x"` at `Option[T = String]` is `some(?x)`, as a data file has always read it, so the fact does not match `none()`. A variable standing for the whole `Option` has no spelling and is refused when encoding. A literal string starting with `?` is escaped with a leading `\`:

```toml
assignee = "?agent"          # variable ?agent
name = "alice"               # string "alice"
note = "\\?not-a-variable"   # literal string "?not-a-variable"
```

The writer prefixes one `\` to a `String` that begins with zero or more `\` followed by `?`. The reader removes one leading `\` from a string that begins with one or more `\` followed by `?`. So `?x` is written `\?x` and `\?x` is written `\\?x`, and both read back exact. Only a flex variable has a spelling. A rigid or de Bruijn variable is refused when encoding.

Variable scope is one `decode_value` call. A file of facts decodes each `[[data]]` entry in its own call, so each entry is an independent scope, like each `fact` declaration in `.anthill`. Two occurrences of `?x` within one entry share identity; across entries they are independent.

### Errors

Every error names where it occurred, as a path into the JSON value, and the type expected there, printed as the KB prints a type:

```
$.steps[3].output.stocks[1].reserved: expected Int64, found 3.5
```

A key that is not an identifier is written `["a key"]`. The file readers prefix the entry: `data[2].status: 'Opne' is not a constructor of sort 'app.Status'`.

### Key order

An encoded object's keys are in DECLARED order: an entity's fields in the order the entity declares them, a tuple's labels in the type's order. `anthill-core` enables `serde_json`'s `preserve_order` feature itself. Cargo features only add, so no crate in a build that links `anthill-core` can switch it off, and the bytes of an encoding do not depend on the dependency graph.

### File structure: `meta` + `data` envelope

A serialization file has two sections:
- **`meta`** — declares the entity type (fully-qualified name)
- **`data`** — one or more entity instances

`meta.entity` names a CONSTRUCTOR, by name or applied to its type arguments (`entity = "test.Box[T = anthill.prelude.Int64]"`). Each `data` entry is the object of that constructor's fields, each field decoded with variables on at its declared type, and is asserted as a fact. A type parameter the fields use that `meta.entity` leaves unwritten takes its default; one with no default is refused, naming the parameter.

Selecting the constructor of a row is a separate rule from reading a value at a type. `sort Mix { entity Mix(x: Int64)  entity Other }` is legal: at the declared type `Mix` a value may be either constructor, while `entity = "review.Mix"` names the constructor `Mix`, so the entry `{"x": 3}` is the row `Mix(x: 3)`.

Two checks hold every row to the constructor `meta.entity` names:

- An entry that is not an object is refused. With variables on, `data = ["?row"]` would otherwise be a row holding a variable, of no constructor at all.
- A constructor reserved to the runtime (one of its accounts, `RuntimeAccount`) is refused wherever it is named: by `meta.entity`, or by a tag at any depth. A program does not construct one, by writing it or by reading it in. The refusal is the pair's, so it holds for `decode_value` called directly as for the file readers.

**TOML:**

```toml
[meta]
entity = "anthill.stage0.Task"

[[data]]
id = "WI-AUTH-001"
status = "Open"
depends_on = []

[[data]]
id = "WI-AUTH-002"
status = "Open"
depends_on = ["WI-AUTH-001"]
```

**JSON:**

```json
{
  "meta": { "entity": "anthill.stage0.Task" },
  "data": [
    { "id": "WI-AUTH-001", "status": "Open", "depends_on": [] },
    { "id": "WI-AUTH-002", "status": "Open", "depends_on": ["WI-AUTH-001"] }
  ]
}
```

For a single entity (not a list), `data` is an object instead of an array:

```toml
[meta]
entity = "anthill.stage0.Project"

[data]
name = "my-app"
language = "rust"
build = "cargo"
```

### Multiple entity types per file

Use scoped sections. Each section has its own `meta` + `data`:

```toml
[project.meta]
entity = "anthill.stage0.Project"

[project.data]
name = "my-app"
language = "rust"
build = "cargo"

[tools.meta]
entity = "anthill.stage0.ToolDef"

[[tools.data]]
name = "cargo-test"
command = "cargo"
args = ["test"]
success = "ExitZero"
```

### Name resolution

`meta.entity` is read by the name ladder at `<global>`, as a host names a KB name. A name that is absent, ambiguous, or `internal` to its namespace is refused. The KB's entity schema (field names and their declared types) then interprets the structure:

- Field names must match entity field names
- A tag must be a constructor of the declared sort
- The KB must have entity/sort definitions loaded before loading serialized data

## Examples

### Stage 0: tasks.toml

```toml
[meta]
entity = "anthill.stage0.Task"

[[data]]
id = "WI-AUTH-001"
description = "Define User entity and auth traits"
status = "Open"
depends_on = []
acceptance = [{ Compiles = "src" }, { ToolPasses = "cargo-test" }]
context = ["src/models/user.rs", "docs/auth-design.md"]

[[data]]
id = "WI-AUTH-002"
description = "Implement JWT token generation"
status = "Open"
depends_on = ["WI-AUTH-001"]
acceptance = [{ Compiles = "src" }, { ToolPasses = "cargo-test" }]
context = ["src/auth/jwt.rs"]
```

Loads as:
```anthill
fact Task(id: "WI-AUTH-001", description: "Define User entity and auth traits",
          status: Open, depends_on: [],
          acceptance: [Compiles("src"), ToolPasses("cargo-test")],
          context: ["src/models/user.rs", "docs/auth-design.md"])
```

### Stage 0: anthill.toml (config)

```toml
[project.meta]
entity = "anthill.stage0.Project"

[project.data]
name = "my-app"
language = "rust"
build = "cargo"

[tools.meta]
entity = "anthill.stage0.ToolDef"

[[tools.data]]
name = "cargo-test"
command = "cargo"
args = ["test"]
success = "ExitZero"

[[tools.data]]
name = "cargo-clippy"
command = "cargo"
args = ["clippy", "--", "-D", "warnings"]
success = "ExitZero"
```

### JSON: MCP tool response

```json
{
  "meta": { "entity": "anthill.stage0.Task" },
  "data": [
    {
      "id": "WI-AUTH-001",
      "description": "Define User entity and auth traits",
      "status": "Open",
      "depends_on": [],
      "acceptance": [{ "Compiles": "src" }, { "ToolPasses": "cargo-test" }]
    }
  ]
}
```

### JSON: one value, no envelope

An operation `place(state: ShopState, order: Order) -> (state: ShopState, order: Order)` returns a labelled tuple. A trace writes it with `encode_value` at the operation's declared result type:

```json
{
  "state": { "ShopState": { "stocks": [{ "Stock": { "sku": "A1", "reserved": 2 } }] } },
  "order": { "Order": { "id": 7, "status": "Placed" } }
}
```

TOML is preferred for files (human-readable config). JSON is preferred for machine exchange (APIs, MCP responses).

## Relationship to existing persistence

| Format | Extension | Written by | Good for |
|--------|-----------|-----------|----------|
| Anthill language | `.anthill` | Humans | Rules, sorts, operations — logic |
| Term serialization | `.toml`, `.json` | Tools | Entity data — facts in bulk |

Both formats produce the same KB facts. The loader detects the format by extension and dispatches accordingly.

### How the CLI finds data files (WI-746)

Data is **opt-in by convention**, never by discovery. For each *directory* named on the command line, `anthill load` / `check` / `query` / `run` / `codegen cpp` read:

| Path | Read as data |
|---|---|
| `<dir>/anthill.toml`, `<dir>/anthill.json` | yes |
| any other `.toml` / `.json`, at any depth | no |
| `<dir>/sub/anthill.toml` | no — the lookup is not recursive |

Every fault in a file found this way is a **hard error**: unreadable, unparseable, or missing its `meta.entity` envelope. The name is the declaration, so a malformed file is a fault to report rather than grounds to conclude it was never ours.

Data under other names or locations is tool output and is loaded programmatically via `term_ser::load_toml` / `load_json`; the CLI has no channel for it.

Two commands deliberately do **not** read data files, for reasons specific to each:

- **`codegen rust`** generates Rust types per parsed file (`generate_rust(&ParsedFile)`) and never builds a KB. It emits structs and enums from *sort/entity declarations*; facts play no part, so there is nothing for it to read.
- **`codegen bundle`** vendors the program's `.anthill` *source text* into a standalone crate. Data is the program's *input*, not its code, and baking `anthill.toml` in at bundle time would **freeze** it — the point of the `.toml`/`.json` channel is that tool-written data changes without touching the logic. A bundled binary that needs data should read it at *its own* runtime; that is a separate capability, not a gap in bundling.

`anthill run` is the opposite case and does read: it re-reads on every invocation, so nothing is frozen, and a program querying facts its own project declared is the ordinary use. It assembles its own KB in `run::build_kb` rather than going through `load_kb_with_stdlib`, which is exactly why it shipped blind to data files at first — both now call the shared `load_conventional_data`.

> Extension alone used to be the whole rule — every `.toml`/`.json` under a named path was claimed recursively. That conflated *in the directory* with *addressed to us*: pointing `anthill load` at the anthill repo read 1620 files, 1588 of them Cargo build-cache fingerprints, to find zero data files, and an ordinary `Cargo.toml` failed the load outright. Sniffing content for the envelope (WI-744) suppressed the noise but could not recover intent — a data file with a syntax error yields no envelope, so it was indistinguishable from a foreign file and skipped in silence. A fixed name supplies the intent that sniffing could only guess at.

## Implementation

1. **The pair** (`term_ser::decode_value` / `encode_value`): one walk directed by the declared type, reading the value through `TermView`. The type arguments reach the fields through `typing::field_type_at`.
2. **The file readers and writers** (`load_json` / `load_toml`, `serialize_json` / `serialize_toml`): the envelope, and one call of the pair per entry with variables on. TOML is converted to and from `serde_json::Value`.
3. **Schema lookup**: the entity's declared field names and types (`entity_field_names`, `entity_field_types`); a tag is looked up among the declared sort's constructors.
4. **Type text**: written by `typing::type_qualified_text`, the text a proof record's name is made of; read by a new entry point that parses one type and converts it at `<global>`, as a query's goal is converted (`load::convert_query_term`).
5. **Key order**: `serde_json` with `preserve_order` in `anthill-core/Cargo.toml`.

## Not in this proposal

- Encoding `Set`, `Map` and other host-carried values. It needs the interpreter's arenas, not the KB, and their spelling (`Set` as an array, `Map` as an array of pairs) is left to that proposal.
- TOML beyond following the same mapping. It still cannot hold `null`.

## Revision of 2026-11-22

WI-20261122-WC18Y made the mapping a public API over `TermView` and restated it for one value at a declared type. Before it, the only public entry points were the file readers and writers above, the writer read a `TermId` only (see [Motivation](#motivation)), and the mapping was stated for entity fields only. Where it was silent the code decided. Measured with `anthill query -p <dir>` over an `anthill.json` data file:

- A nested entity with more than one field, written untagged, did not decode: below the top level only `{"Ctor": …}` was read. A one-field one was read with its field's name taken for a constructor's. The tagged form is the mapping's, so the measured row is refused still, with an error that names the tag.
- `"x": 3` under `x: Float` loaded as the `Int64` 3, a fact that does not match the source `x: 3.0`.
- `"?who"` always loaded as a variable. There was no reading of one value in which it is the string.

An error carried no location, so a bad value deep in a document was reported without saying where. The mapping had no rule for tuple types, `Set` or `Map`. `Option` was specified only as a field present or absent, so the code's reading of `null` as `none()` and an `Option` as a list element, a tuple component or a top-level value had no spelling here.

Read in the code: the writer wrote a nested free-standing entity as its bare field object and a one-field entity's entry as the field's bare value, and the reader refused both. A type was written by name only: under `Type` a constructor's type with bindings was refused, and a sort's own application (`List[T = Int64]`) was written as the object `{"T": "anthill.prelude.Int64"}`, which the reader refuses. It wrote `"?who"` unescaped. The reader took a string under `Int64`, or under a sort it names no constructor of, as a `String`. The key order of a written object was alphabetical, or insertion order in a build where some other crate enabled `serde_json`'s `preserve_order`.

What changes for a file that loaded before:

- A nested entity is written with its tag, `{"Point": {"x": 1, "y": 2}}`, the one form that loaded before. The writer wrote it without one, which did not load. The untagged form (`[{"id": 1, "name": "a"}]` under `List[T = P]`) stays refused, now with an error naming the tag it lacks.
- A number under `Float` is a Float. A number under `Int64` that is not an integer in range is an error.
- A string under a type other than `String` is an error, unless it names a nullary constructor of the declared sort, or a type under `Type`.
- A type with bindings is written and read as its text. `meta.entity` can apply a generic entity to its type arguments. A parameter its fields use that it leaves unwritten takes its default, and one with no default is refused, where its fields were read with no type.
- An unquoted integer past `u64` under `BigInt`, and a TOML `nan` or `inf`, are refused.
- The writer escapes `?` strings, writes a one-field entity's entry as its object, writes keys in declared order, and refuses a list with a variable tail and a variable that is not a flex one.

An earlier example of this proposal loaded provisions (`entity = "anthill.prelude.Eq"`, `T = "Int64"`, as `fact Eq[T = Int64]`). It has been refused since WI-926, because `Eq` declares no fields, and is removed: a provision is a declaration, not data.
