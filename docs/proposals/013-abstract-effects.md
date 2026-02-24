# 013: Abstract Effect Parameters

## Status: Partially implemented (grammar + parse IR + codegen + KB loading; effect checking not yet done)

## Depends on: none

## Blocks: nothing (no longer blocks 011 — abstract effect parameters work)

## Motivation

Stream operations need effects (at minimum `Read{kb}` for KB queries), but the Stream sort doesn't know *which* effect — that depends on the concrete stream source. This requires **abstract effect parameters**: a sort declares `sort E = ?` and uses `E` in effect clauses.

More broadly: effects are sorts. An effect like `Read{kb}` is a sort instantiation — `Read` parameterized with target `kb`. The kernel treats effects as opaque labels for composition and checking. It never interprets them. The interpretation (what "reading the KB" actually does) lives outside, in the realization layer.

## The Insight: Effects as Sorts and Facts

Effect kinds are declared as sorts with entity constructors, and registered via facts:

```
-- Effect kinds are sorts with type parameter and entity constructor
sort Read     { sort T = ? entity Read(target: T) }
sort Modify   { sort T = ? entity Modify(target: T) }
sort Emit     { sort T = ? entity Emit(target: T) }
sort Error    { sort T = ? entity Error(target: T) }

-- Registration: each kind is a valid effect
fact Effect{T = Read{?}}
fact Effect{T = Modify{?}}
fact Effect{T = Emit{?}}
fact Effect{T = Error{?}}

-- Relationships: Modify implies Read
rule Effect{T = Read{?r}} :- Effect{T = Modify{?r}}
```

This means:
- **New effect kinds are just sorts + fact assertions.** `sort Audits { sort T = ? entity Audits(target: T) }` + `fact Effect{T = Audits{?}}` declares a user-defined effect kind — no grammar or kernel change needed.
- **Effect checking is KB querying.** When an operation declares `effects (Foo{bar})`, the kernel checks `fact Effect{T = Foo{?}}` in the KB. Unknown effect kind = missing fact.
- **Effect relationships are rules.** `Read` implied by `Modify` is: `rule Effect{T = Read{?r}} :- Effect{T = Modify{?r}}`.
- **Effects are queryable.** "What effects exist?" is a KB query.

```
┌─────────────────────────────────────┐
│  Kernel (safe, verifiable)          │
│  - Effect sort + fact declarations  │
│  - effect composition (union, §5.6) │
│  - checking via KB query:           │
│    fact Effect{T = Kind{?}} exists? │
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
- Which effect kinds exist (via `fact Effect{T = Kind{?}}` in KB)
- Effects compose (sequential = union, see §5.6)
- Effect relationships (`Read` implied by `Modify` — a rule)
- Operations declare their effects

The kernel does NOT know:
- What `Read{kb}` means at runtime
- How state is threaded through effectful operations
- How effects map to host-language constructs

Effect interpretation is inherently unsafe — it touches the real world (IO, state, FFI). Therefore it belongs in the realization layer, not the kernel.

### User-defined effects

Because effect kinds are sorts + facts, users can define their own:

```
sort MyApp {
  sort AuditLog { entity audit_log }

  -- Declare a new effect kind
  sort Audits { sort T = ? entity Audits(target: T) }
  fact Effect{T = Audits{?}}

  operation create_account(name: String) -> Account
    effects (Modify{store}, Audits{audit_log})
}
```

No grammar change, no kernel change — just a sort declaration and fact assertion.

## Grammar Change (Implemented)

The old `effect` rule was removed. The `effects_clause` now accepts type expressions directly:

```js
// Old (removed):
effect: $ => seq(field('kind', $.name), '(', field('target', $.name), ')'),
effects_clause: $ => seq('effects', '(', commaSep1($.effect), ')'),

// Implemented:
effects_clause: $ => seq('effects', '(', commaSep1($._type), ')'),
```

Where `_type` is `simple_type | parameterized_type | variable_term`. This accepts:
```
effects (Read{kb})                 -- parameterized_type: sort instantiation
effects (E)                        -- simple_type: abstract sort parameter
effects (?E)                       -- variable_term: logical variable
effects (Read{kb}, E)              -- mix of concrete and abstract
effects (Read{kb}, ?extra)         -- mix with logical variable
```

### Why types, not terms?

Effects in operation signatures are **sort instantiations** — `Read{store}` is `Read` parameterized with `store`. This is `Name{bindings}` syntax, which is a type expression (`parameterized_type`). The same syntax works in type position (`List{T = Int}`) and in fact position (`fact Eq{T = Int}`).

Values can appear in sort binding positions because types are terms. `Read{store}` where `store` is an operation parameter is a sort instantiation referencing a concrete value — a natural form of value-dependent typing that requires no special mechanism. The KB's unification handles abstract bindings (`Read{?}`) and concrete ones (`Read{store}`) uniformly. This is equivalent in power to dependent type theory (DOT, Martin-Löf), expressed as Horn clause resolution instead of typing judgments — the complexity is inherent in what's being checked, not in the formalism.

### Sort bindings accept variables

Sort bindings were extended to accept logical variables as standalone bindings:

```js
sort_binding: $ => choice(
  seq(field('param', $.name), optional(seq('=', field('type', $._type)))),
  field('type', $.variable_term),  // Read{?}, Read{?r}
),
```

This enables effect registration facts like `fact Effect{T = Read{?}}` where `?` means "for any target".

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

## Rust Implementation (Done)

### Parse IR

Effects are stored as `TypeExpr` in the parse IR — matching their syntactic form as type expressions:

```rust
pub struct Effect {
    pub type_expr: TypeExpr,  // was: { kind: Name, target: Name }
}
```

Each effect is a `TypeExpr`:
- `Read{kb}` → `TypeExpr::Parameterized { name: "Read", bindings: [{param: "kb", bound: Simple("kb")}] }`
- `E` → `TypeExpr::Simple(Name("E"))`
- `?E` → `TypeExpr::Variable { term_id, description: None }`

### Converter

In `parse/convert.rs`, effects_clause handling iterates over type child nodes:

```rust
"effects_clause" => {
    for type_child in child.named_children(&mut cursor) {
        match type_child.kind() {
            "simple_type" | "parameterized_type" | "variable_term" => {
                effects.push(Effect { type_expr: self.convert_type(type_child) });
            }
            _ => {}
        }
    }
}
```

### Codegen (Rust)

`analyze_effects` extracts kind/target from `TypeExpr::Parameterized`:

```rust
match &effect.type_expr {
    TypeExpr::Parameterized { name, bindings } => {
        let kind = symbols.name(name.last());   // "Modify", "Read", etc.
        let target = bindings.first()...;        // "store", "kb", etc.
        match kind { "Modify" => ..., "Read" => ..., "Error" => ..., "Emit" => ... }
    }
    TypeExpr::Simple(_) | TypeExpr::Variable { .. } => {} // abstract — skip
}
```

## What's Not Yet Implemented

- **Effect checking via KB query** — the kernel does not yet verify `fact Effect{T = Kind{?}}` exists when an operation declares an effect
- **Effect composition** — sequential composition (union of effect sets) is not yet enforced
- **Effect polymorphism with constraints** (`E includes Read`) — see proposal 003
- **Arrow sorts with effects** — see proposal 003

## Relationship to Other Proposals

- **003 (Effect Arrow Sorts)**: Covers `(A) => B effect [E]` — effects on function types. This proposal covers abstract effects in operation `effects(E)` clauses. Complementary.
- **011 (Type Resolution)**: Stream's `sort E = ?` needs this proposal. 011 depends on 013. The typing lattice in 011 now documents entity instances as sort members, which grounds the value-dependent typing that effects rely on.
- **002 (Arrow Sorts)**: Independent. Abstract effects work without arrow sorts.
