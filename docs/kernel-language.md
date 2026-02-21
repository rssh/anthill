# Kernel Language Specification

The kernel language is the minimal formal language of the anthill knowledge base. It defines four constructs that the reasoning engine understands natively — everything else in the anthill is built on top of these as entity types in standard namespaces.

This specification is **self-contained**: it can be implemented without reference to the high-level design document ([metasystem-design-draft.md](../metasystem-design-draft.md)), which provides motivation and vision but is not formal.

## 1. Design Principles

1. **Minimal kernel.** Four constructs: `namespace`, `sort`, `rule`, `operation`. The kernel is deliberately small — analogous to the kernel of a proof assistant (Lean, Coq) that is small, trusted, and verifies proofs, while tactics (large, untrusted) find them. `entity` is syntactic sugar (see §6).

2. **Rule is THE knowledge primitive.** All knowledge in the KB is expressed as rules (Horn clauses). `fact` and `constraint` are syntactic sugar that desugar to rules. This unifies ground assertions, derived knowledge, and integrity constraints under one mechanism.

3. **Algebraic specification.** The kernel is in the tradition of algebraic specification languages (OBJ, CafeOBJ, Maude): a namespace declares sorts (abstract or defined types), operations (typed behavioral specs with contracts), and rules (laws).

4. **Partial formalization.** Any term can be `Unspecified` — described in natural language, to be refined later. This allows a spectrum from fully informal to fully formal within the same language.

5. **Everything carries metadata.** Every fact has provenance (who, when, trust level, iteration). Trust is attached to facts, not to agents.

## 2. Lexical Conventions

### 2.1 Encoding

Source files are **UTF-8**.

### 2.2 Comments

```
-- single line comment (to end of line)
{- multi-line
   comment -}
```

Comments nest: `{- outer {- inner -} still outer -}`.

### 2.3 Identifiers and Names

```
Identifier ::= Letter (Letter | Digit | '-' | '_')*
             | '"' [^"]+ '"'                          -- quoted identifier

Name       ::= Identifier                             -- simple: "transfer"
             | Name '.' Identifier                    -- qualified: banking.accounts.transfer
```

Quoted identifiers allow arbitrary strings as names: `"my weird name"`.

### 2.4 Literals

**Primitive literals** (the four built-in types):

```
StringLit   ::= '"' [^"]* '"'
IntLit      ::= '-'? Digit+
FloatLit    ::= '-'? Digit+ '.' Digit+
BoolLit     ::= 'true' | 'false'
```

**Compound literal sugar** (desugars to `Fn` terms using prelude constructors):

```
DurationLit ::= IntLit ('ms' | 's' | 'm' | 'h' | 'd')   -- 5m → Duration(5, "m")
ListLit     ::= '[' Term (',' Term)* ']'                  -- [a, b] → cons(a, cons(b, nil))
```

### 2.5 Keywords

All keywords are **context-dependent** (soft), following the Scala 3 approach: a word is a keyword only in a syntactic position where it is expected; elsewhere it is an ordinary identifier. Only `true` and `false` are reserved.

| Context | Soft keywords |
|---------|--------------|
| Top level / namespace body | `namespace`, `sort`, `rule`, `operation`, `requires`, `entity`, `fact`, `constraint` |
| Namespace header | `import`, `export`, `end` |
| Visibility (prefix) | `internal`, `export`, `public` |
| Operation | `requires`, `ensures`, `effects` |
| Rule | `:-` (operator, not keyword) |
| Metadata | `trust`, `agent`, `iteration`, `source`, `supersedes` |
| Trust levels | `proved`, `verified`, `tested`, `empirical`, `proposed`, `stale`, `axiom`, `decision` |
| Block delimiters | `end` (only after a block body) |

### 2.6 Whitespace

Whitespace (spaces, tabs, newlines) separates tokens but is not significant for parsing. No indentation sensitivity.

## 3. Block Delimiters

All compound constructs support two styles:

```
Body[F] ::= '{' F '}'    -- brace-delimited
           | F 'end'      -- end-marker-delimited
```

Both styles are interchangeable. A file may mix styles freely.

## 4. Terms

Terms are the building blocks of all knowledge. They appear inside rules, constraints, operation contracts, entity fields, and metadata.

```
Term ::= Const(type, value)            -- ground value: 42 : Int, "hello" : String
       | Var(type, name)               -- unification variable: ?x : Int
       | Fn(name, args: [Term])        -- compound: account(?id, ?owner, ?bal)
       | Ref(Name)                     -- reference to named entity: banking.Money
       | Unspecified(text, hints, id)  -- not yet formalized (see §4.1)
       | Quoted(language, source)      -- verbatim host-language fragment (see §4.2)
```

### 4.1 Unspecified Terms

`Unspecified(text, hints, id)` represents knowledge that exists but is not yet formal. It can appear **anywhere a Term can appear**, creating a spectrum from fully informal to fully formal within a single statement.

```
-- Inline syntax:
<"human-readable description">

-- With hints for search/matching:
<"non-negative balance", hints: [domain: banking, type: constraint]>
```

Each `Unspecified` term has a stable `id` for tracking refinement. **Refinement** replaces an `Unspecified` with a more formal term (which may itself contain `Unspecified` subterms).

**Key property:** Unspecified terms **cannot participate in proofs** — they can be stored and queried, but cannot be premises in derivations or achieve trust above `proposed`. This creates a natural incentive to formalize.

### 4.2 Quoted Terms

`Quoted(language, source)` embeds host-language fragments verbatim. Unlike `Unspecified`, a `Quoted` term IS formal — just in a different language. Host-language embeddings can interpret it.

```
Quoted("scala", "case class Account(id: Long, balance: BigDecimal)")
```

### 4.3 Primitive Types

The kernel has only four primitive types for `Const` values:

| Type | Values |
|------|--------|
| `String` | `"hello"`, `"src/main/scala"` |
| `Int` | `0`, `42`, `-1` |
| `Float` | `3.14`, `-0.5` |
| `Bool` | `true`, `false` |

**Everything else is a compound type** — defined via `sort` and `operation` in the `anthill.prelude` standard namespace (see §4.4). Literal syntax for compound types is sugar:

| Literal | Desugars to |
|---------|------------|
| `5m` | `Duration(5, "m")` |
| `30s` | `Duration(30, "s")` |
| `[a, b, c]` | `cons(a, cons(b, cons(c, nil)))` |

### 4.4 The Prelude Namespaces

Common compound types are defined in standard prelude sorts using the kernel's own constructs. **Parametric types are sorts with abstract sub-sorts** — instantiated via **inline type expressions** `Name{bindings}`. **Sum types are sorts with entity constructors** — `sort S { entity C₁(...), entity C₂(...) }` enumerates constructors (see §5.2).

> **Canonical source:** The prelude definitions below are extracted from `stdlib/anthill/prelude/`. Those `.anthill` files are the canonical source; this section is for reference.

```
-- Duration: a non-parametric prelude sort
sort anthill.prelude.Duration {
  entity Duration(amount: Int, unit: String)         -- duration(5, "m")
}

-- Timestamp: a non-parametric prelude sort
sort anthill.prelude.Timestamp {
  entity Timestamp(value: String)
}

-- List: a parametric sort (T is the abstract sort parameter)
sort anthill.prelude.List
  export List, nil, cons, length

  sort T                                             -- type parameter (abstract)
  entity nil                                         -- empty list
  entity cons(head: T, tail: List)                   -- cons cell

  operation length(l: List) -> Int
  rule length(nil) = 0
  rule length(cons(?x, ?xs)) = add(1, length(?xs))
end

-- Option: a parametric sort
sort anthill.prelude.Option
  export Option, none, some

  sort T                                             -- type parameter (abstract)
  entity none                                        -- absent
  entity some(value: T)                              -- present
end

-- Eq: equality
sort anthill.prelude.Eq
  export eq, neq

  sort T
  operation {
    eq(a: T, b: T) -> Bool
    neq(a: T, b: T) -> Bool
  }
  rule neq(?a, ?b) = not(eq(?a, ?b))
end

-- Ordered: total ordering (requires Eq)
sort anthill.prelude.Ordered
  export gt, gte, lt, lte

  sort T
  requires Eq{T}

  operation {
    gt(a: T, b: T) -> Bool          -- >
    gte(a: T, b: T) -> Bool         -- >=
    lt(a: T, b: T) -> Bool          -- <
    lte(a: T, b: T) -> Bool         -- <=
  }

  rule {
    lt(?a, ?b)  = gt(?b, ?a)
    lte(?a, ?b) = gte(?b, ?a)
    gte(?a, ?b) = not(lt(?a, ?b))
    antisymmetric: ⊥ :- gt(?a, ?b), gt(?b, ?a)    -- can't have both
  }
end

-- Numeric: basic arithmetic (requires Ordered)
sort anthill.prelude.Numeric
  export add, sub, mul, zero-val

  sort T
  requires Ordered{T}

  operation {
    add(a: T, b: T) -> T           -- +
    sub(a: T, b: T) -> T           -- -
    mul(a: T, b: T) -> T           -- *
    zero-val() -> T                -- additive identity
  }

  rule {
    add_comm:  add(?a, ?b) = add(?b, ?a)
    add_assoc: add(add(?a, ?b), ?c) = add(?a, add(?b, ?c))
    add_identity: add(?a, zero-val) = ?a
  }
end
```

Infix operators `>`, `>=`, `<`, `<=`, `+`, `-`, `*`, `=` are sugar for the corresponding operations — `a > b` desugars to `gt(a, b)`, `a + b` to `add(a, b)`, etc. These are available when the corresponding prelude sort is required (e.g. `requires Numeric{T = Money}`).

**Instantiation** — via inline type expressions (`Name{bindings}`):

```
entity Project(
  name   : String,
  tools  : List{T = String},
  modules: Option{T = Module}
)

operation lookup(key: String) -> Option{T = Account}
```

The inline form `List{T=Int}` refers to the sort `List` with abstract sort parameter `T` bound to `Int`. This is the Maude view mechanism expressed as a type expression.

**Grammar:**

```
Type ::= Name                                        -- simple type reference
       | Name '{' SortBinding (',' SortBinding)* '}' -- inline instantiation
```

Import and instantiation are separate concepts: `import` makes names visible, inline `Name{bindings}` instantiates sort parameters. They are not bundled together.

**Instantiation as term:** The `Name{bindings}` syntax is valid both in type position and in term position. In term position, it represents a sort instantiation as a first-class value — used to assert that a type satisfies a parametric spec:

```
-- "Int satisfies Eq" — a fact in the KB
fact Eq{T = Int}

-- "String satisfies Ordered" — scoped to the declaring namespace
fact Ordered{T = String}
```

This follows the "types are terms" principle: sort instantiations are knowledge, expressible as facts. Different namespaces can provide different instantiations (see §5.1 on namespace scoping).

Additional types are introduced via `sort` declarations (abstract or defined) in any namespace.

## 5. Kernel Constructs

Four constructs the reasoning engine understands natively.

### 5.1 Namespace

The unit of encapsulation and independent evolution. A namespace scopes sorts, entities, operations, and rules. Namespaces can be nested.

```
Namespace ::= 'namespace' Name
                Import*                             -- explicit imports
                ['export' NameList]                 -- what is visible outside (default: nothing)
              Body[NamespaceContent*]

Import ::= 'import' ImportPath
ImportPath ::= Name                               -- import a specific name
             | Name '.' '{' NameList '}'           -- selective: specific names from a namespace
             | Name '.' '*'                        -- wildcard: everything from a namespace

NameList    ::= Name (',' Name)*
SortBinding ::= Name '=' Type                   -- explicit: binds an abstract sort to a concrete type
              | Name                             -- punning: Eq{T} is shorthand for Eq{T = T}
```

When a sort binding omits the `= Type` part, the parameter name is used as both the binding name and the bound type. This **punning** shorthand (analogous to TypeScript's `{x}` for `{x: x}`) is useful when a sort parameter has the same name as a type in scope:

```
-- These are equivalent:
requires Eq{T = T}       -- explicit
requires Eq{T}           -- punned: T binds to T

-- Mixed: punned and explicit bindings in the same type expression
requires Bifunctor{A, B = Int}   -- A binds to A, B binds to Int

-- Explicit is required when names differ:
requires Numeric{T = Money}      -- T binds to Money
```

Import makes names from another namespace visible in the current scope. Sort parameters remain abstract — they are instantiated separately via inline type expressions (`Name{bindings}`), not at import time.

Three import forms:

```
-- Import a specific name from a namespace:
import anthill.prelude.List                   -- imports "List" from anthill.prelude

-- Import selected items from a namespace:
import anthill.prelude.{List, Option}         -- imports "List" and "Option" from anthill.prelude

-- Import everything from a namespace:
import anthill.prelude.*                      -- imports all exported names from anthill.prelude
```

**Visibility** controls what crosses namespace boundaries, expressed as a prefix modifier on declarations:

```
Visibility ::= 'internal'    -- visible only within this namespace (default, can be omitted)
             | 'export'      -- visible to namespaces that import this one
             | 'public'      -- visible everywhere (use sparingly)
```

Default visibility is `internal`. The namespace-level `export` clause lists exported names; individual `export`/`public` prefixes on declarations must be consistent with it.

**Namespace content** — what can appear inside a namespace:

```
NamespaceContent ::= Sort | Rule | Operation         -- Sort: only sorts-with-body (not abstract)
                   | RequiresDecl           -- sort-level constraint (see §5.2)
                   | Entity                 -- sugar (desugars to single-constructor Sort, see §6.3)
                   | Fact | Constraint      -- sugar (desugars to Rule, see §6.1, §6.2)
                   | OperationBlock | RuleBlock  -- sugar (desugars to individual declarations, see §6.4)
                   | Namespace              -- nested namespaces
```

### 5.2 Sort

A type declaration. Sort has two forms — **abstract** (declared, not defined) and **defined** (inhabitants enumerated as a closed ADT):

```
Sort ::= [Visibility] 'sort' Name                            -- abstract
           ['meta' ':' Meta]
       | [Visibility] 'sort' Name '=' Body[Constructor*]     -- defined (ADT)
           ['meta' ':' Meta]

Constructor ::= 'entity' Name ['(' FieldList ')']            -- variant/constructor
FieldList   ::= Field (',' Field)*
Field       ::= Name ':' Type
```

**Abstract sort** — declares that a type exists without specifying its representation. Abstract sorts appear only inside sort bodies, where they serve as **type parameters** — their carrier is provided later by an implementation or by inline instantiation.

```
sort T                               -- abstract: type parameter (inside a sort body)
```

Abstract properties are expressed as accessor operations within the enclosing sort body:

```
sort linear_algebra {
  sort Vector                        -- abstract: type parameter
  operation dim(v: Vector) -> Int     -- accessor
}
```

**Sort with body** — a sort can have a body containing entities (constructors), sub-sorts (parameters), `requires` declarations (sort-level constraints), operations, rules, and other items. When a sort body contains entity declarations, they are constructors of that sort, making it a closed ADT:

```
sort Color {                         -- closed set of constructors
  entity red                         --   nullary constructor
  entity green
  entity blue
}

sort List {
  entity nil
  entity cons(head: T, tail: List)
}
```

A sort with entity constructors is **closed** — exactly the listed constructors exist. Pattern matching in rules works via unification on constructor terms:

```
rule length(nil) = 0
rule length(cons(?x, ?xs)) = add(1, length(?xs))
```

**Requires declaration** — a standalone `requires` in a sort or namespace body declares a sort-level constraint: the enclosing scope depends on another algebraic spec. This is distinct from operation-level `requires` clauses (preconditions on individual operations).

```
RequiresDecl ::= 'requires' Type
```

The `requires` declaration takes a type expression — either a simple sort name or a parameterized sort with bindings:

```
sort Ordered {
  sort T
  requires Eq{T}                     -- this sort depends on Eq over T

  operation gt(a: T, b: T) -> Bool
}

sort banking {
  sort Money
  requires Numeric{T = Money}         -- this sort (algebra) depends on Numeric over Money
}
```

When loaded into the KB, a `requires` declaration emits a `Requirement` fact scoped to the enclosing sort or namespace.

**Standalone `entity`** is syntactic sugar for a single-constructor sort (see §6.3):

```
entity Account(id: AccountId, balance: Money)
-- desugars to: sort Account { entity Account(id: AccountId, balance: Money) }
```

### 5.3 Rule

**THE knowledge primitive.** A Horn clause. All knowledge in the KB is expressed as rules. Two important special cases are given syntactic sugar (see §6):

- `fact X` = bodyless rule (ground assertion)
- `constraint I :- G` = integrity constraint (invariant `I` must hold when guard `G` holds)

```
Rule ::= 'rule' [Name ':'] Head [':-' RuleBody]
           ['meta' ':' Meta]

Head ::= Term                          -- what the rule asserts
       | '⊥'                           -- bottom (for denials)

RuleBody ::= Term (',' Term)*          -- conjunction of conditions
```

**Three forms:**

```
-- Derivation rule: head holds when body holds
rule ancestor(?X, ?Z) :- parent(?X, ?Y), ancestor(?Y, ?Z)

-- Ground assertion (= fact): bodyless rule
rule parent("alice", "bob")

-- Denial / integrity constraint: desugared from constraint syntax
rule non_negative: ⊥ :- balance(?a, ?b), lt(?b, 0)
```

Rules can optionally be **named** (e.g., `non_negative:`) for reference in error messages, retractions, and documentation.

### 5.4 Operation

A typed behavioral specification with contracts. Kernel-level because sorts + operations + laws = **algebra** — the foundation of the verification system. The kernel type-checks signatures and generates proof obligations from contracts.

```
Operation ::= [Visibility] 'operation' Name '(' [ParamList] ')' '->' Type
                ['requires' RuleBody]            -- precondition
                ['ensures' RuleBody]             -- postcondition
                ['effects' '(' Effect (',' Effect)* ')']
                ['meta' ':' Meta]

ParamList ::= Param (',' Param)*
Param     ::= Name ':' Type
```

Parameters are **named bindings** — referenced by name (without `?`) in `requires`/`ensures` clauses. This distinguishes them from rule variables (`?x`), which are pattern-matching unification variables. `requires` clauses may reference parameter names only (precondition: checked before execution). `ensures` clauses may additionally reference `result`, which binds to the return value (postcondition: checked after execution). Using `result` in `requires` is a semantic error.

**Contracts** (`requires`/`ensures`) are scoped constraints — they generate denials over the operation's input/output bindings when an implementation is asserted:

```
operation deposit(a: Account, m: Money) -> Account
  requires gt(m, zero-val)
  ensures eq(balance(result), add(balance(a), m))
  effects (modifies Ledger)

operation balance(a: Account) -> Money           -- pure, no contract
```

An operation without an implementation is an **open obligation** — it emits a pheromone signal attracting implementing agents.

### 5.5 Effects

Effects are part of operation declarations, not standalone constructs:

```
Effect ::= Modifies(target: Name)       -- mutates state
         | Reads(source: Name)          -- depends on external state
         | Emits(event: Name)           -- produces events
         | Errors(error: Name)          -- can fail with typed error
         | Requires(capability: Name)   -- needs a capability
```

### 5.6 Effect Semantics (State-Passing Interpretation)

Effects give operations a precise execution semantics via a state-passing interpretation. An operation

```
operation op(x1: A1, ..., xm: Am) -> R
  effects (Modifies S, Reads T, Emits E, Errors Err, Requires Cap)
```

is interpreted as a function that threads an **environment** — a mapping from resource names to their current state:

```
op_e : Env × A1 × ... × Am → (R × Env × Event list) + Error
```

where:
- **`Env`** is a partial map from resource names (symbols) to terms representing their current state.
- On success, the operation returns the result value `R`, an updated environment `Env`, and a list of emitted events.
- On failure, the operation returns an error term.

An operation without effects is **pure**: it receives the environment unchanged and must return it unchanged.

#### Environment and Resources

Each `Modifies(target)` and `Reads(source)` effect declares a **resource** — a named slot in the environment. The environment maps resource names to their current state as terms.

- `Reads(S)` — the operation may inspect `Env(S)` but must not change it.
- `Modifies(S)` — the operation may inspect and update `Env(S)`. Every `Modifies` implicitly grants `Reads`.
- `Emits(E)` — the operation may append events of type `E` to the output event list.
- `Errors(Err)` — the operation may fail, returning an error of type `Err` instead of a result.
- `Requires(Cap)` — the operation requires capability `Cap` to be present (non-`None`) in the environment.

#### Effect-Env Condition

An effectful operation **respects its effect-env condition** if it only modifies the resources declared in its `Modifies` effects:

> For all resource names `s` not in the `Modifies` set: `Env_after(s) = Env_before(s)`.

This is the fundamental correctness property: an operation's declared effects are an upper bound on what it may change. Pure operations (no effects) must preserve the entire environment.

#### Composition

Sequential composition of effectful operations threads the environment and concatenates emitted events:

```
(g ∘ f)(env, args) =
  case f(env, args) of
    Error err → Error err
    Ok (r1, env1, events1) →
      case g(env1, [r1]) of
        Error err → Error err
        Ok (r2, env2, events2) → Ok (r2, env2, events1 ++ events2)
```

If `f` respects effects `E1` and `g` respects effects `E2`, then `g ∘ f` respects effects `E1 ∪ E2`.

#### Capability Checking

Before executing an operation, the kernel verifies that all `Requires(Cap)` capabilities are present in the environment. If any required capability is absent (`Env(Cap) = None`), execution is rejected before the operation body runs.

#### Verification Obligations

When an `Implementation` fact links code to an operation with effects:

1. The implementation must **respect the effect-env condition** — it may only modify declared resources.
2. The implementation must **check capabilities** — all `Requires` resources must be present.
3. `requires` clauses are checked against input parameters and the pre-environment.
4. `ensures` clauses are checked against input parameters, the result, and the post-environment.

These generate proof obligations (see §8.4) that can be discharged at various trust levels.

### 5.7 Monadic Interpretation of Effects

The same effects admit an equivalent **monadic interpretation**. An operation

```
operation op(x1: A1, ..., xm: Am) -> R
  effects (Modifies S, Reads T, Emits E, Errors Err, Requires Cap)
```

is interpreted as a computation in a combined monad `M_E`:

```
op_m : A1 → ... → Am → M_E(R)
```

where `M_E` layers:
- **`StateT Env`** — for `Reads`/`Modifies` (thread mutable state),
- **`WriterT (Event list)`** — for `Emits` (accumulate events),
- **`ExceptT Error`** — for `Errors` (short-circuit on failure),
- **`ReaderT Caps`** — for `Requires` (access capabilities).

Concretely, `M_E(R) = Env → (R × Env × Event list) + Error`.

#### Monadic Operations

The monad provides primitive operations corresponding to each effect kind:

| Effect | Monadic primitive | Type |
|--------|-------------------|------|
| `Reads(S)` | `get_resource(S)` | `M_E(Term option)` |
| `Modifies(S)` | `put_resource(S, v)` | `M_E(Unit)` |
| `Emits(E)` | `emit_event(e)` | `M_E(Unit)` |
| `Errors(Err)` | `throw_error(err)` | `M_E(A)` for any `A` |
| `Requires(Cap)` | `require_capability(Cap)` | `M_E(Unit)` |

Sequencing is monadic bind:

```
bind : M_E(A) → (A → M_E(B)) → M_E(B)
bind m f = λenv.
  case m env of
    Error err → Error err
    Ok (a, env', events1) →
      case f a env' of
        Error err → Error err
        Ok (b, env'', events2) → Ok (b, env'', events1 ++ events2)
```

The monad laws hold: `bind (return x) f = f x`, `bind m return = m`, and `bind (bind m f) g = bind m (λx. bind (f x) g)`.

#### Equivalence of Interpretations

The state-passing interpretation (§5.6) and the monadic interpretation are **isomorphic** — conversion functions `to_monad` and `from_monad` form a round-trip in both directions. The effect-env condition is preserved by the correspondence.

The two interpretations have the **same expressivity** when the environment can contain:
1. **Duplicated state** — the environment may hold copies of resource values, allowing the monad's internal state to be embedded in the environment representation.
2. **Continuated expressions** — the environment may hold suspended computations (closures), allowing monadic bind/sequencing to be represented as data.

Since the kernel language does not yet have execution semantics (flow expressions, sequencing), continuations cannot currently be expressed in the non-monadic form. The monadic interpretation therefore provides a natural way to reason about sequential composition of effectful operations — once execution semantics are introduced, both forms will be fully interchangeable.

For the formal development of both interpretations and their equivalence proofs, see `isabelleland/kernel/Anthill_Kernel.thy`.

## 6. Syntactic Sugar

Readable shorthand that desugars to kernel constructs. The reasoning engine only sees rules and sorts.

### 6.1 Fact (bodyless rule)

A ground assertion — the most common way to add knowledge to the KB.

```
Fact ::= 'fact' Term
           ['meta' ':' Meta]
```

**Desugars to:**

```
fact parent("alice", "bob")
→  rule parent("alice", "bob")
```

### 6.2 Constraint (headless rule / denial)

An integrity invariant — the KB rejects any state that violates it.

```
Constraint ::= 'constraint' [Name ':'] Invariant [':-' Guard]
                 ['meta' ':' Meta]
```

The invariant (head) states what must be true; the guard (body after `:-`) states when it must be true. Without a guard, the invariant must always hold.

**Desugars to:**

```
constraint non_negative: gte(balance(?a), 0) :- balance(?a, ?b)
→  rule non_negative: ⊥ :- balance(?a, ?b), lt(balance(?a), 0)
```

### 6.3 Entity (single-constructor sort)

A standalone entity declaration is sugar for a sort with one constructor. This is the most common case — a named record type.

```
Entity ::= [Visibility] 'entity' Name ['(' FieldList ')']
             ['meta' ':' Meta]
```

**Desugars to:**

```
entity Account(id: AccountId, balance: Money)
→  sort Account { entity Account(id: AccountId, balance: Money) }

entity Marker
→  sort Marker { entity Marker }
```

### 6.4 Operation and Rule Blocks

Multiple operations or rules can be grouped under a single keyword using block syntax. Each entry inside the block has the same grammar as the standalone form minus the leading keyword, and desugars to an individual `operation` or `rule`.

```
OperationBlock ::= 'operation' Body[OperationEntry*]
OperationEntry ::= [Visibility] Name '(' [ParamList] ')' '->' Type
                     ['requires' RuleBody]
                     ['ensures' RuleBody]
                     ['effects' '(' Effect (',' Effect)* ')']
                     ['meta' ':' Meta]

RuleBlock      ::= 'rule' Body[RuleEntry*]
RuleEntry      ::= [Name ':'] Head [':-' RuleBody]
                     ['meta' ':' Meta]
```

**Desugars to** individual declarations:

```
operation {
  add(a: T, b: T) -> T
  sub(a: T, b: T) -> T
  div(a: T, b: T) -> T
    requires neq(b, zero-val)
}
→  operation add(a: T, b: T) -> T
   operation sub(a: T, b: T) -> T
   operation div(a: T, b: T) -> T
     requires neq(b, zero-val)

rule {
  add_comm:  add(?a, ?b) = add(?b, ?a)
  add_assoc: add(add(?a, ?b), ?c) = add(?a, add(?b, ?c))
}
→  rule add_comm:  add(?a, ?b) = add(?b, ?a)
   rule add_assoc: add(add(?a, ?b), ?c) = add(?a, add(?b, ?c))
```

Block and individual forms can be mixed freely — use blocks for groups of simple declarations, individual form when you want visual separation:

```
operation {
  add(a: T, b: T) -> T
  sub(a: T, b: T) -> T
  mul(a: T, b: T) -> T
}

operation div(a: T, b: T) -> T
  requires neq(b, zero-val)
  ensures eq(mul(result, b), a)
```

Since `meta: { ... }` has clear delimiters and `requires`/`ensures`/`effects` are keyword-prefixed, the parser always knows where each entry ends — there is no ambiguity.

### 6.5 Requires / Ensures (scoped constraints)

The `requires` and `ensures` clauses in operations are scoped constraints — they generate denials tied to the operation's input/output bindings. When an `Implementation` fact (from the `anthill.realization` standard namespace) pairs with an operation, the kernel generates corresponding obligation rules.

## 7. Metadata

Every fact in the KB carries metadata. `Meta` is an **entity** in the `anthill.prelude` namespace — not a special grammar production. It is a regular Fn term with named arguments.

> **Canonical source:** `stdlib/anthill/prelude/meta.anthill`

```
namespace anthill.prelude.Meta
  import anthill.prelude.Option
  export Meta, Trust, ProofResult

  -- Meta is an open-keyed entity: it has well-known fields,
  -- but any Name : Term pair is allowed as an entry.
  -- Unknown keys are stored as-is and available for queries.
  --
  -- Well-known keys have semantic meaning to the kernel:
  --   trust      — verification status (see Trust sort below)
  --   agent      — who asserted this fact
  --   timestamp  — when it was asserted
  --   iteration  — which iteration of the project
  --   source     — file, line, language
  --   supersedes — which previous fact this replaces
  --
  -- Additional keys are project-defined:
  --   Meta(trust: axiom, agent: "author", reviewer: "rssh", priority: 3)

  entity Meta(entries: Term)
    -- entries is an open structure: any named arguments are accepted.
    -- In practice, Meta is constructed with named-arg syntax:
    --   Meta(trust: axiom, agent: "author")
    -- The kernel recognizes well-known keys; all others pass through.

  -- Trust: verification status of a fact
  sort Trust {
    entity proved                        -- formally proved (Lean/Isabelle kernel)
    entity verified                      -- mechanically verified (Z3, ctproof)
    entity tested(n: Int)                -- passed n test runs (Hypothesis, sbt-test)
    entity empirical                     -- observed but not formally checked
    entity proposed                      -- asserted by agent, not yet verified
    entity stale                         -- was valid, environment changed
    entity axiom                         -- ground truth (domain knowledge)
    entity decision                      -- architectural choice
  }

  -- ProofResult: outcome of discharging an obligation
  sort ProofResult {
    entity Proved(witness: Term, solver: String, duration: Duration)
    entity Disproved(counterexample: Term, solver: String)
    entity Timeout(strategies: Term)
    entity Unknown(reason: String)
  }
end
```

**Usage in terms.** `Meta` is a regular `Fn` term, used anywhere a term is expected:

```
-- As an argument in generates:
generates: [Fact("cps2.matchSupported", Meta(trust: tested-47))]

-- As part of an Implementation fact:
fact Implementation("banking", artifact: "src/bank.scala",
                    Meta(trust: proposed, agent: "llm-coder"))
```

**Syntactic sugar.** The `[...]` MetaBlock shorthand on declarations desugars to a `Meta(...)` term:

```
-- Sugar:
fact parent("alice", "bob") [trust: axiom, agent: "author"]

-- Desugars to:
rule parent("alice", "bob")
  meta: Meta(trust: axiom, agent: "author")
```

The `tested-N` surface syntax (e.g., `tested-47`) is sugar for the `tested(N)` constructor:

```
-- Sugar:        tested-47
-- Desugars to:  tested(47)
```

### 7.1 Trust Levels

Trust is attached to **facts**, not to agents. The system does not ask "who produced this?" — it asks "is this verified?"

Ordering: `proved` > `verified` > `tested(N)` > `empirical` > `proposed` > `stale`.

`axiom` and `decision` are outside the ordering — they represent ground truth and choices, not verification results.

### 7.2 Open Keys

`Meta` accepts any `Name : Term` pair as a named argument. The kernel recognizes well-known keys and gives them semantic meaning:

| Key | Type | Kernel behavior |
|---|---|---|
| `trust` | `Trust` | Determines verification status; affects what can participate in proofs |
| `agent` | `String` | Recorded as provenance |
| `timestamp` | `String` | Recorded as provenance (when fact was asserted/loaded) |
| `last-modified` | `String` | When the fact's content last changed (distinct from `timestamp` — does not update on re-load if content is unchanged). Used by codegen to detect stale implementations (see [rust-forward-mapping.md §3.5](rust-forward-mapping.md#35-staleness-detection-via-timestamps)). |
| `iteration` | `Int` | Tracks project evolution |
| `source` | `String` | File/line reference |
| `supersedes` | `Name` | Links to previous version of this fact |

Additional keys are stored and queryable but have no built-in kernel behavior:

```
Meta(trust: axiom, agent: "rssh", reviewer: "team-lead", jira: "PROJ-123")
```

This makes metadata extensible without changing the kernel — projects define their own conventions.

### 7.3 Proof Results

When an obligation is discharged, the result is recorded as a `ProofResult` term (see sort definition above). The solver field identifies which agent or tool produced the result.

## 8. Semantics

### 8.1 Type System

The kernel enforces a **structural type system**:

- **Abstract sorts** (`sort T` inside a sort body) introduce type parameters without representation. Can appear in operation signatures and fields within the enclosing sort, but have no constructors until a carrier binding is provided.
- **Sorts with constructors** (`sort S { entity C₁(...), entity C₂(...) }`) introduce closed algebraic data types. All constructors are enumerated; pattern matching in rules is exhaustive.
- **Operations** have typed signatures: `operation op(x: A, y: B) -> C`. Parameters are named bindings; the kernel type-checks that actual arguments match declared types.
- **Terms** are typed: `Const` carries its type, `Var` declares its type, `Fn` has the type of its sort's constructor, `Ref` refers to a named type.

### 8.2 Subsorting

Constructors of a sort are **subsorts** of that sort. If `sort S { entity C₁(...), entity C₂(...) }`, then `C₁ <: S` and `C₂ <: S`. A term classified as sort `C₁` is also of sort `S`.

This is the standard **order-sorted algebra** approach (as in Maude/OBJ):

- Each constructor name is a sort in its own right.
- The subsort relation `C <: S` is registered when a sort with entity constructors is declared.
- Subsorting is **transitive**: if `A <: B` and `B <: C`, then `A <: C`.
- Querying by sort `S` returns facts of sort `S` and all subsorts of `S`.

```
sort Color {
  entity red
  entity green
  entity blue
}

-- This establishes:
--   red   <: Color
--   green <: Color
--   blue  <: Color
-- A query for sort Color matches terms of sort red, green, and blue.
```

Subsorting does **not** arise from nesting. A sort `T` declared inside a namespace or sort body is a **parameter**, not a subsort. Only the constructor-of relationship creates subsorting.

### 8.3 Rule Evaluation

The kernel's reasoning engine supports:

**Forward chaining (bottom-up):** When a new fact is asserted, the engine checks all rules whose body might be newly satisfiable. If a rule's body is fully satisfied, its head is derived as a new fact.

**Backward chaining (top-down):** Given a query `?- goal`, the engine searches for rules whose head unifies with the goal, then recursively proves the body terms.

**Unification:** Standard first-order unification. `Var` terms unify with any term of the same type. `Fn` terms unify if their names match and all arguments unify pairwise.

**Termination:** The kernel uses stratification and loop detection to ensure rule evaluation terminates. Recursive rules must be stratifiable (no negation through recursion in the basic mode; stratified negation is supported for constrained cases).

### 8.4 Constraint Enforcement

Constraints (denials) are checked whenever a new fact is asserted:

1. For each denial `rule ⊥ :- B1, B2, ...`, check if the new fact, combined with existing facts, satisfies the body.
2. If the body is fully satisfied, the assertion is **rejected** — the constraint is violated.
3. The rejection includes the constraint name and the bindings that caused the violation.

This is the kernel's integrity mechanism — it prevents logically inconsistent states.

### 8.5 Operation Contracts and Obligations

When an operation has `requires`/`ensures` clauses and an `Implementation` fact links code to it:

1. The kernel generates **proof obligations** — facts of entity type `Obligation` (from the `anthill.realization` standard namespace, see `stdlib/anthill/realization/`).
2. The obligation states: "prove that the implementation satisfies the contract."
3. Agents attempt to discharge the obligation. The kernel verifies submitted proofs.
4. Successfully discharged obligations elevate the implementation's trust level.

The kernel recognizes `Implementation` as a **well-known entity type** and triggers obligation generation automatically.

### 8.6 Namespace Visibility

The kernel enforces namespace boundaries:

- Declarations without a visibility prefix are **internal** — visible only within the declaring namespace.
- **`export`**-prefixed declarations are visible to namespaces that explicitly `import` them.
- **`public`**-prefixed declarations are visible everywhere (discouraged).
- A query or rule body can only reference facts visible from the querying namespace's scope.
- `import Name.{names}` makes specific names from another namespace visible.

Visibility is enforced at query time and assertion time.

### 8.7 Algebras

An algebra is not a separate syntactic construct — it is the **typing structure that emerges** from declarations within a sort body:

- **Abstract sub-sorts** (`sort T` inside a sort body) define the type parameters of the algebra.
- **Entity constructors** define concrete inhabitants (ADT variants).
- **Operations** define typed behaviors with contracts.
- **Rules** (including constraint sugar) express laws.

A sort-with-body that contains abstract sub-sorts, operations, and laws IS an algebra. When an `Implementation` fact provides carrier bindings (`carrier: { Scalar = float, Vector = CudaDeviceBuffer[float] }`), it instantiates the algebra for a specific host language.

**Parametric structure:** Abstract sorts inside a sort body serve as type parameters. A sort with abstract sub-sort `T` is a parametric module — instantiated via inline type expressions `List{T = Int}`. For example, `anthill.prelude.List` has abstract sub-sort `T`; using `List{T = Int}` inline produces a list-of-integers.

This also supports type class-like patterns: a sort declaring `sort A` and `operation combine(x: A, y: A) -> A` with laws is a specification that any type with a `combine` operation must satisfy. Using `MyType` in place of `A` via inline binding instantiates the specification for a concrete type.

**Spec satisfaction:** To declare that a concrete type satisfies a parametric spec, assert the instantiation as a fact:

```
-- Int satisfies Eq, Ordered, and Numeric
fact Eq{T = Int}
fact Ordered{T = Int}
fact Numeric{T = Int}
```

For built-in types, the operations are primitive (provided by the runtime). For user-defined types, rules define the operations:

```
fact Eq{T = Color}
rule eq(red, red) = true
rule eq(green, green) = true
rule eq(blue, blue) = true
rule eq(?_, ?_) = false
```

Since facts are scoped to namespaces, different namespaces can provide different instantiations of the same spec for the same type (e.g. different orderings). A consumer chooses which instantiation to use via `import`.

**Namespaces** group sorts, operations, and rules for encapsulation and visibility control, but do not introduce type parameters. A namespace may contain sorts (both parametric and concrete), but abstract sorts (no body) appear only inside sort bodies as type parameters — never directly in a namespace.

## 9. Connections to Existing Systems

The kernel language connects to three traditions:

**ML-style modules.** A sort-with-body (containing abstract sub-sorts and operations) ≈ signature (declares abstract types and operations), Implementation with carrier bindings ≈ structure (provides concrete types), inline `Name{bindings}` ≈ functor application. But anthill sorts are richer — they contain rules (logic) and contracts (requires/ensures), making them algebraic specifications rather than pure type signatures. Namespaces provide encapsulation and visibility control (like ML structures), but type parameters live in sort bodies, not namespaces.

**Maude / OBJ / CafeOBJ.** The closest match:

| Kernel language | Maude |
|----------------|-------|
| `namespace` | theory (`fth`) or module (`fmod`) |
| `sort T` (abstract) | `sort` |
| `sort S { entity ... }` | sort with constructor ops (`op ... : -> S [ctor]`) |
| `operation` | `op` (operator declaration) |
| `rule` (derivation) | equation (`eq`) or rewrite rule (`rl`) |
| `constraint` (denial) | membership axiom / conditional axiom |
| `Implementation.carrier` | view (maps theory sorts to module sorts) |
| `List{T = X}` (inline instantiation) | view instantiation (binds sort parameter) |
| sort with abstract sub-sort | parameterized module (`fmod X{Y :: TRIV}`) |

The anthill adds: `Unspecified` (partial formalization), metadata (trust, provenance, agent), host-language embeddings (bidirectional mapping to Scala/Python/etc.), and the stigmergic agent layer.

**Proof assistants (Lean, Coq, Isabelle).** The kernel/tactic split: the kernel (small, trusted) checks proofs; tactics (large, untrusted) find proofs. In the anthill: the kernel grammar verifies, agents construct. The `trust` level on facts plays the role of Lean's `axiom` vs `theorem` distinction.

## 10. Examples

### 10.1 Banking Algebra

A complete algebra with type parameters, operations, contracts, and laws. Because the algebra is parametric over `Money` (an abstract sort whose carrier is provided by an implementation), it uses `sort` — not `namespace` — as the enclosing construct:

```
sort banking
  export Account, Money, deposit, withdraw, balance

  sort Money                                         -- type parameter (abstract)
  requires Numeric{T = Money}                        -- gives us +, -, >, >=, = for Money

  entity Account(                                    -- sugar: sort Account { entity Account(...) }
    id      : AccountId,
    balance : Money
  )

  operation deposit(a: Account, m: Money) -> Account
    requires gt(m, zero-val)                          -- m > 0
    ensures eq(balance(result), add(balance(a), m))   -- balance(result) = balance(a) + m

  operation withdraw(a: Account, m: Money) -> Account
    requires gt(m, zero-val)                          -- m > 0
    requires gte(balance(a), m)                       -- balance(a) >= m
    ensures eq(balance(result), sub(balance(a), m))   -- balance(result) = balance(a) - m

  operation balance(a: Account) -> Money

  -- Laws (as rules):
  rule deposit_positive: gt(balance(deposit(?a, ?m)), balance(?a))
    :- gt(?m, zero-val)

  -- Integrity constraint (sugar):
  constraint non_negative: gte(balance(?a), zero-val) :- balance(?a, ?_)
    -- desugars to: rule non_negative: ⊥ :- balance(?a, ?b), lt(?b, zero-val)
end
```

With infix sugar (once defined), the same algebra reads more naturally:

```
sort banking
  export Account, Money, deposit, withdraw, balance

  sort Money
  requires Numeric{T = Money}

  entity Account(id: AccountId, balance: Money)

  operation {
    balance(a: Account) -> Money

    deposit(a: Account, m: Money) -> Account
      requires m > 0
      ensures balance(result) = balance(a) + m

    withdraw(a: Account, m: Money) -> Account
      requires m > 0, balance(a) >= m
      ensures balance(result) = balance(a) - m
  }

  rule deposit_positive: balance(deposit(?a, ?m)) > balance(?a)
    :- ?m > 0

  constraint non_negative: balance(?a) >= 0 :- balance(?a, ?_)
end
```

### 10.2 Linear Algebra with Parametric Sorts

Abstract algebra with sort variables, instantiated by different implementations. Parametric over `Scalar` and `Vector`, so it uses `sort` as the enclosing construct:

```
sort linear_algebra
  export Scalar, Vector, add, scale, dot, dim

  sort Scalar                                        -- type parameter (abstract)
  sort Vector                                        -- type parameter (abstract)

  operation {
    dim(v: Vector) -> Int
    add(a: Vector, b: Vector) -> Vector
      requires dim(a) = dim(b)
      ensures dim(result) = dim(a)
    scale(s: Scalar, v: Vector) -> Vector
      ensures dim(result) = dim(v)
    dot(a: Vector, b: Vector) -> Scalar
      requires dim(a) = dim(b)
  }

  rule {
    add_comm: add(?a, ?b) = add(?b, ?a)
    add_assoc: add(add(?a, ?b), ?c) = add(?a, add(?b, ?c))
    scale_distrib: scale(?s, add(?a, ?b)) = add(scale(?s, ?a), scale(?s, ?b))
  }
end
```

Two implementations (in the `anthill.realization` standard namespace, see `stdlib/anthill/realization/`) could provide different carrier bindings:

```
-- CPU implementation:
fact Implementation("linear_algebra",
  artifact: "src/linalg/cpu.scala", language: "scala",
  carrier: { Scalar: "Double", Vector: "Array[Double]" })
  [trust: proposed]

-- GPU implementation:
fact Implementation("linear_algebra",
  artifact: "src/linalg/cuda.py", language: "python",
  carrier: { Scalar: "float32", Vector: "CudaDeviceBuffer[float32]" })
  [trust: proposed]
```

### 10.3 Namespace with Nested Sub-namespaces

```
namespace finance
  import banking.{Account, Money}
  export risk, audit

  namespace risk {
    sort RiskLevel {                              -- defined sort (not abstract)
      entity Low
      entity Medium
      entity High
    }
    operation assess(a: Account) -> RiskLevel
    constraint bounded: lte(assess(?a), maxRisk) :- assess(?a, ?_)
  }

  namespace audit {
    entity AuditEntry(
      account : Account,
      action  : String,
      amount  : Money,
      at      : Timestamp
    )
    rule must_audit: ⊥ :- withdraw(?a, ?m), gt(?m, threshold), not(AuditEntry(?a, "withdraw", ?m, ?_))
  }
end
```

## 11. Collected Grammar

```
-- =================================================================
-- Lexical
-- =================================================================

Identifier  ::= Letter (Letter | Digit | '-' | '_')*
              | '"' [^"]+ '"'
Name        ::= Identifier ('.' Identifier)*
StringLit   ::= '"' [^"]* '"'
IntLit      ::= '-'? Digit+
FloatLit    ::= '-'? Digit+ '.' Digit+
BoolLit     ::= 'true' | 'false'

-- Literal sugar for compound types (desugars to Fn terms):
DurationLit ::= IntLit ('ms' | 's' | 'm' | 'h' | 'd')   -- 5m → Duration(5, "m")
ListLit     ::= '[' Term (',' Term)* ']'                  -- [a,b] → cons(a,cons(b,nil))

Body[F]     ::= '{' F '}'  |  F 'end'

-- =================================================================
-- Terms
-- =================================================================

Term        ::= Const(type, value)
              | Var(type, name)              -- written as ?name
              | Fn(name, args: [Term])
              | Ref(Name)
              | Instantiation(Name, SortBinding+)  -- Eq{T = Int} in term position
              | Unspecified(text, hints, id) -- written as <"text">
              | Quoted(language, source)

-- =================================================================
-- Kernel Constructs (4)
-- =================================================================

Namespace   ::= 'namespace' Name
                  Import*
                  ['export' NameList]
                Body[NamespaceContent*]

Import      ::= 'import' ImportPath
ImportPath  ::= Name                                           -- import a name
              | Name '.' '{' NameList '}'                      -- selective import
              | Name '.' '*'                                   -- wildcard import
NameList    ::= Name (',' Name)*
SortBinding ::= Name ['=' Type]                 -- without '= Type': punning (Eq{T} = Eq{T = T})

NamespaceContent ::= Sort | Rule | Operation
                   | RequiresDecl                 -- sort-level constraint
                   | Entity                       -- sugar (§6.3)
                   | Fact | Constraint            -- sugar (§6.1, §6.2)
                   | OperationBlock | RuleBlock   -- sugar (§6.4)
                   | Namespace

Visibility  ::= 'internal' | 'export' | 'public'

Sort        ::= [Visibility] 'sort' Name                           -- abstract (only in SortContent)
                  ['meta' ':' Meta]
              | [Visibility] 'sort' Name                           -- sort with body
                  Import*
                  ['export' NameList]
                Body[SortContent*]
                  ['meta' ':' Meta]

-- Note: abstract sorts (first form, no body) may only appear inside a sort body
-- as type parameters. Namespaces contain only sorts-with-body (second form).

SortContent ::= Sort | Entity | Operation | Rule
              | RequiresDecl
              | Fact | Constraint | OperationBlock | RuleBlock
              | Namespace

FieldList   ::= Field (',' Field)*
Field       ::= Name ':' Type

Type        ::= Name                                           -- simple: Account, Int
              | Name '{' SortBinding (',' SortBinding)* '}'    -- inline instantiation: List{T=Int}

Rule        ::= 'rule' [Name ':'] Head [':-' RuleBody]
                  ['meta' ':' Meta]
Head        ::= Term | '⊥'
RuleBody    ::= Term (',' Term)*

Operation   ::= [Visibility] 'operation' Name '(' [ParamList] ')' '->' Type
                  ['requires' RuleBody]
                  ['ensures' RuleBody]
                  ['effects' '(' Effect (',' Effect)* ')']
                  ['meta' ':' Meta]
ParamList   ::= Param (',' Param)*
Param       ::= Name ':' Type

Effect      ::= 'Modifies' '(' Name ')' | 'Reads' '(' Name ')'
              | 'Emits' '(' Name ')' | 'Errors' '(' Name ')'
              | 'Requires' '(' Name ')'

RequiresDecl ::= 'requires' Type                -- sort-level constraint (in sort/namespace body)

-- =================================================================
-- Syntactic Sugar
-- =================================================================

Fact        ::= 'fact' Term ['meta' ':' Meta]
              -- desugars to: rule Term

Constraint  ::= 'constraint' [Name ':'] Invariant [':-' Guard]
                  ['meta' ':' Meta]
              -- desugars to: rule [Name ':'] ⊥ :- Guard, ¬Invariant

Entity      ::= [Visibility] 'entity' Name ['(' FieldList ')']
                  ['meta' ':' Meta]
              -- desugars to: sort Name { entity Name [( FieldList )] }

OperationBlock ::= 'operation' Body[OperationEntry*]
              -- desugars to: individual Operation declarations
OperationEntry ::= [Visibility] Name '(' [ParamList] ')' '->' Type
                     ['requires' RuleBody]
                     ['ensures' RuleBody]
                     ['effects' '(' Effect (',' Effect)* ')']
                     ['meta' ':' Meta]

RuleBlock   ::= 'rule' Body[RuleEntry*]
              -- desugars to: individual Rule declarations
RuleEntry   ::= [Name ':'] Head [':-' RuleBody]
                  ['meta' ':' Meta]

-- =================================================================
-- Metadata
-- =================================================================
--
-- Meta is an entity in anthill.prelude.Meta (see §7).
-- It is a regular Fn term with open named arguments:
--   Meta(trust: axiom, agent: "author", custom-key: "value")
--
-- Well-known keys: trust, agent, timestamp, iteration, source, supersedes.
-- Any other Name : Term pair is also accepted (open-keyed).

-- Trust sort (defined in anthill.prelude.Meta):
Trust       ::= 'proved' | 'verified' | 'tested' '(' IntLit ')'
              | 'empirical' | 'proposed' | 'stale'
              | 'axiom' | 'decision'

-- =================================================================
-- Inline Metadata Shorthand (sugar)
-- =================================================================
--
-- Square-bracket syntax on declarations desugars to Meta(...) Fn term:
--   fact X [trust: axiom, agent: "author"]
--     → rule X  meta: Meta(trust: axiom, agent: "author")
--
-- The tested-N surface form desugars to the tested(N) constructor:
--   tested-47  →  tested(47)

MetaBlock   ::= '[' MetaEntry (',' MetaEntry)* ']'
MetaEntry   ::= Name ':' Term                   -- any key-value pair
```
