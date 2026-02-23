# 013: Abstract Effect Parameters

## Status: Draft

## Depends on: none

## Blocks: 011 (Type Resolution — Stream needs abstract effect parameter)

## Motivation

Stream operations need effects (at minimum `Read{kb}` for KB queries), but the Stream sort doesn't know *which* effect — that depends on the concrete stream source. This requires **abstract effect parameters**: a sort declares `sort E = ?` and uses `E` in effect clauses.

Currently the grammar requires concrete effects: `effects (Read{kb})`. There's no way to write `effects (E)` where `E` is abstract.

More broadly: effects are abstract sorts. An effect like `Read{kb}` is just an entity — a label. The kernel treats effects as opaque labels for composition and checking. It never interprets them. The interpretation (what "reading the KB" actually does) lives outside, in the realization layer.

## The Insight: Effects as Facts

Effects are terms, and effect kinds are declared via facts:

```
sort Effect { sort T = ? }

fact Effect{T = Reads(?)}       -- Reads(anything) is a valid effect
fact Effect{T = Modifies(?)}    -- Modifies(anything) is a valid effect
fact Effect{T = Emits(?)}       -- etc.
```

This means:
- **New effect kinds are just fact assertions.** `fact Effect{T = Logs(?)}` declares a user-defined effect kind — no grammar or kernel change needed.
- **Effect checking is KB querying.** When an operation declares `effects (Foo(bar))`, the kernel checks `fact Effect{T = Foo(?)}` in the KB. Unknown effect kind = missing fact.
- **Effect relationships are rules.** `Reads` implied by `Modifies` is: `rule Effect{T = Reads(?r)} :- Effect{T = Modifies(?r)}`.
- **Effects are queryable.** "What effects exist?" is a KB query.

```
┌─────────────────────────────────────┐
│  Kernel (safe, verifiable)          │
│  - Effect sort + fact declarations  │
│  - effect composition (union, §5.6) │
│  - checking via KB query:           │
│    fact Effect{T = Kind(?)} exists? │
│  - abstract effect parameters       │
└──────────────┬──────────────────────┘
               │ abstract boundary
┌──────────────┴──────────────────────┐
│  Realization (unsafe, host-language)│
│  - effect interpretation            │
│  - state passing, IO, FFI          │
│  - Rust impl of Read{kb}, etc.    │
└─────────────────────────────────────┘
```

The kernel knows:
- Which effect kinds exist (via `fact Effect{T = Kind(?)}` in KB)
- Effects compose (sequential = union, see §5.6)
- Effect relationships (`Reads` implied by `Modifies` — a rule)
- Operations declare their effects

The kernel does NOT know:
- What `Read{kb}` means at runtime
- How state is threaded through effectful operations
- How effects map to host-language constructs

Effect interpretation is inherently unsafe — it touches the real world (IO, state, FFI). Therefore it belongs in the realization layer, not the kernel.

### User-defined effects

Because effect kinds are facts, users can define their own:

```
sort MyApp {
  sort AuditLog { entity audit_log }

  -- Declare a new effect kind
  fact Effect{T = Audits(?)}

  operation create_account(name: String) -> Account
    effects (Modify{store}, Audits(audit_log))
}
```

No grammar change, no kernel change — just a fact assertion.

## Grammar Change

The current `effect` rule is too restrictive — it only accepts `Name(Name)`. Effects are terms: they can be concrete (`Read{kb}`), abstract (`E`), logical variables (`?E`), or instantiation terms (`MyEffect{param = value}`). The grammar should accept the same expressions as type/term positions.

```js
// Current (too restrictive):
effect: $ => seq(
  field('kind', $.name),
  '(',
  field('target', $.name),
  ')',
),

// Proposed: effect is a general term (instantiation, variable, or name)
effect: $ => choice(
  $.instantiation_term,   // Read{kb}, Modify{store}, MyEffect{target = x}
  $.variable_term,        // ?E — logical variable
  $.identifier,           // E — abstract sort parameter name
),
```

This allows:
```
effects (Read{kb})                 -- concrete: instantiation term
effects (E)                        -- abstract sort param: identifier
effects (?E)                       -- logical variable
effects (MyEffect{target = store}) -- parameterized effect
effects (Read{kb}, E)              -- mix of concrete and abstract
effects (Read{kb}, ?extra)         -- mix with logical variable
```

**Breaking change**: the effect syntax changes from `Reads(kb)` (fn_term, old) to `Read{kb}` (instantiation term, new). Effects use sort instantiation syntax because effects ARE sort instantiations — `Read{kb}` is `Read` instantiated with target `kb`, declared via `fact Effect{T = Read{?}}`.

Note: `Read{kb}` is already a valid `fn_term` (name + parenthesized args). So the existing concrete syntax is just a special case of the general term form — no backwards compatibility issue.

## Usage in Sort Definitions

A sort can declare an abstract effect parameter and use it in operation signatures:

```
sort Stream {
  sort T = ?         -- element type (abstract)
  sort E = ?         -- effect (abstract)

  operation splitFirst(s: Stream) -> Option{T = Pair{A = T, B = Stream}}
    effects (E)
  operation head(s: Stream) -> Option{T = T}
    effects (E)
  operation tail(s: Stream) -> Stream
    effects (E)
  operation takeN(s: Stream, n: Int) -> List{T = T}
    effects (E)
  operation collect(s: Stream) -> List{T = T}
    effects (E)
}
```

Concrete sorts bind `E` when satisfying the spec:

```
sort LogicalStream {
  sort T = ?
  fact Stream{T, E = Read{kb}}    -- bind E to a concrete effect

  operation splitFirst(s: LogicalStream{T = ?A})
    -> Option{T = Pair{A = ?A, B = LogicalStream{T = ?A}}}
    effects (Read{kb})            -- concrete here
}
```

A file reader:
```
sort FileStream {
  sort T = ?
  fact Stream{T, E = Read{file}}
  ...
}
```

## Effect Interpretation in Realization

The interpretation of effects is provided by the host language via the realization layer:

```
-- In an .anthill file: declare effect resources
sort KB { entity kb }
sort FileSystem { entity file }

-- In Rust realization: implement what Read{kb} means
impl ReadEffect for KBReader {
    fn read(&self, kb: &KnowledgeBase) -> ... { ... }
}
```

This is analogous to:
- Haskell's `IO` — the runtime provides interpretation
- Algebraic effects — handlers provide interpretation
- Capability-based systems — capabilities are passed, not interpreted by the type system

The kernel verifies that effects are declared and compose correctly. The realization provides the semantics. The boundary is clear: the kernel is safe; interpretation is unsafe.

## Rust Implementation

### Parse IR change

Since effects are now general terms, the parse IR representation simplifies — an effect IS a term:

```rust
// Current: effects are a special (kind, target) pair
// Proposed: effects are just terms

// In the operation's parsed representation:
struct ParsedOperation {
    // ...
    effects: Vec<TermId>,  // was: Vec<(Symbol, Symbol)>
}
```

Each effect is stored as a term in the `SimpleTermStore`:
- `Read{kb}` → `Fn("Reads", [Ref("kb")])` — same as any fn_term
- `E` → `Ref("E")` or `Ident("E")` — name reference
- `?E` → `Var(VarId)` — logical variable
- `MyEffect{target = store}` → `Fn("MyEffect", [target: Ref("store")])` — instantiation

### Converter change

In `parse/convert.rs`, the effect conversion dispatches on node type instead of extracting `kind`/`target` fields:

```rust
// When converting an effect node:
fn convert_effect(&mut self, node: Node) -> TermId {
    // Effect is a general term — reuse existing term conversion
    self.convert_term(node)
}
```

This is simpler than the current code — no special-case parsing of `kind`/`target` fields.

### KB representation

Effects on operations become a list of term IDs, where each term is:
- `Fn("Reads", [Ref("kb")])` — concrete effect
- `Ref("E")` — abstract sort parameter (resolved during loading)
- `Var(v)` — logical variable (bound during spec satisfaction checking)
- `Fn("MyEffect", [target: Ref("store")])` — parameterized effect

This is consistent with types-are-terms: effects are terms too.

## Scope

This proposal is intentionally small:
1. Grammar: replace the rigid `effect` rule with a `choice` over general term forms
2. Parse IR: effects become term IDs (simpler, not more complex)
3. Converter: delegate to existing `convert_term` (less code, not more)
4. KB: effects already stored as terms — abstract effects are just variables/refs

It does NOT cover:
- Effect interpretation semantics (realization concern)
- Effect polymorphism with constraints (`E includes Reads`) — see proposal 003
- Effect composition rules beyond what §5.6 already defines
- Arrow sorts with effects — see proposal 003

## Relationship to Other Proposals

- **003 (Effect Arrow Sorts)**: Covers `(A) => B effect [E]` — effects on function types. This proposal covers abstract effects in operation `effects(E)` clauses. Complementary.
- **011 (Type Resolution)**: Stream's `sort E = ?` needs this proposal. 011 depends on 013.
- **002 (Arrow Sorts)**: Independent. Abstract effects work without arrow sorts.
