# Kernel Language Specification

The kernel language is the minimal formal language of the anthill knowledge base. It defines four constructs that the reasoning engine understands natively — everything else in the anthill is built on top of these as entity types in standard domains.

This specification is **self-contained**: it can be implemented without reference to the high-level design document ([metasystem-design-draft.md](../metasystem-design-draft.md)), which provides motivation and vision but is not formal.

## 1. Design Principles

1. **Minimal kernel.** Four constructs: `domain`, `sort`, `rule`, `operation`. The kernel is deliberately small — analogous to the kernel of a proof assistant (Lean, Coq) that is small, trusted, and verifies proofs, while tactics (large, untrusted) find them. `entity` is syntactic sugar (see §6).

2. **Rule is THE knowledge primitive.** All knowledge in the KB is expressed as rules (Horn clauses). `fact` and `constraint` are syntactic sugar that desugar to rules. This unifies ground assertions, derived knowledge, and integrity constraints under one mechanism.

3. **Algebraic specification.** The kernel is in the tradition of algebraic specification languages (OBJ, CafeOBJ, Maude): a domain declares sorts (abstract or defined types), operations (typed behavioral specs with contracts), and rules (laws). An algebra is not a separate construct — it IS a domain.

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
| Top level / domain body | `domain`, `sort`, `rule`, `operation`, `entity`, `fact`, `constraint` |
| Domain header | `extends`, `import`, `export`, `where`, `end` |
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

**Everything else is a compound type** — defined via `sort` and `operation` in the `anthill.prelude` standard domain (see §4.4). Literal syntax for compound types is sugar:

| Literal | Desugars to |
|---------|------------|
| `5m` | `Duration(5, "m")` |
| `30s` | `Duration(30, "s")` |
| `[a, b, c]` | `cons(a, cons(b, cons(c, nil)))` |

### 4.4 The Prelude Domains

Common compound types are defined in standard prelude domains using the kernel's own constructs. **Parametric types are domains with abstract sorts** — instantiated via `import ... where` or via **inline type expressions** `Name{bindings}`. **Sum types are defined sorts** — `sort S = { entity C₁(...), entity C₂(...) }` enumerates constructors (see §5.2).

```
-- Duration: a non-parametric prelude domain
domain anthill.prelude.Duration
  export Duration

  sort Duration = {
    entity Duration(amount: Int, unit: String)       -- duration(5, "m")
  }
end

-- Timestamp: a non-parametric prelude domain
domain anthill.prelude.Timestamp
  export Timestamp

  sort Timestamp = {
    entity Timestamp(value: String)
  }
end

-- Nat: natural numbers (Peano)
domain anthill.prelude.Nat
  export Nat, zero, succ

  sort Nat = {
    entity zero                                      -- base case
    entity succ(pred: Nat)                           -- successor
  }
end

-- List: a parametric domain (T is the abstract sort parameter)
-- The primary sort shares the domain's name (same-name convention)
domain anthill.prelude.List
  export List, nil, cons, length

  sort T                                             -- type parameter (abstract)
  sort List = {                                      -- defined: closed ADT
    entity nil                                       -- empty list
    entity cons(head: T, tail: List)                 -- cons cell
  }

  operation length(l: List) -> Nat
  rule length(nil) = zero
  rule length(cons(?x, ?xs)) = succ(length(?xs))
end

-- Option: a parametric domain
domain anthill.prelude.Option
  export Option, none, some

  sort T                                             -- type parameter (abstract)
  sort Option = {                                    -- defined: closed ADT
    entity none                                      -- absent
    entity some(value: T)                            -- present
  }
end

-- Eq: equality
domain anthill.prelude.Eq
  export eq, neq

  sort T
  operation {
    eq(a: T, b: T) -> Bool
    neq(a: T, b: T) -> Bool
  }
  rule neq(?a, ?b) = not(eq(?a, ?b))
end

-- Ordered: total ordering (extends Eq)
domain anthill.prelude.Ordered
  export gt, gte, lt, lte

  sort T
  import anthill.prelude.Eq where { T = T }

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

-- Numeric: basic arithmetic (extends Ordered)
domain anthill.prelude.Numeric
  export add, sub, mul, zero-val

  sort T
  import anthill.prelude.Ordered where { T = T }

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

Infix operators `>`, `>=`, `<`, `<=`, `+`, `-`, `*`, `=` are sugar for the corresponding operations — `a > b` desugars to `gt(a, b)`, `a + b` to `add(a, b)`, etc. These are available when the corresponding prelude domain is imported for the sort.

**Instantiation** — two equivalent mechanisms:

**1. Import-level binding** (`import ... where`) — binds once, reuse throughout the domain:

```
domain my_project
  import anthill.prelude.List where { T = Int }
  -- now List, nil, cons, length are all bound to Int

  import anthill.prelude.Option where { T = String }
  -- now Option, none, some are bound to String
end
```

**2. Inline type expression** (`Name{bindings}`) — one-off usage in a field or signature:

```
entity Project(
  name   : String,
  tools  : List{T = String},
  modules: Option{T = Module}
)

operation lookup(key: String) -> Option{T = Account}
```

The inline form `List{T=Int}` refers to the primary sort of domain `anthill.prelude.List` with `T` bound to `Int`. Domain name and sort name share the same name (same-name convention); they live in different namespaces so there is no collision.

**Grammar:**

```
Type ::= Name                                        -- simple type reference
       | Name '{' SortBinding (',' SortBinding)* '}' -- inline instantiation
```

Both mechanisms are exactly Maude's parameterized module + view mechanism, with the inline form as syntactic convenience.

Additional types are introduced via `sort` declarations (abstract or defined) in any domain.

## 5. Kernel Constructs

Four constructs the reasoning engine understands natively.

### 5.1 Domain

The unit of encapsulation and independent evolution. A domain scopes sorts, entities, operations, and rules. Domains can be nested.

```
Domain ::= 'domain' Name
             ['extends' Name (',' Name)*]       -- inherit from parent domains
             Import*                             -- explicit imports
             ['export' NameList]                 -- what is visible outside (default: nothing)
           Body[DomainContent*]

Import ::= 'import' Name ['.' '{' NameList '}']
             ['where' '{' SortBinding (',' SortBinding)* '}']

NameList    ::= Name (',' Name)*
SortBinding ::= Name '=' Type                   -- binds an abstract sort to a concrete type
```

The `where` clause on imports provides **sort bindings** — the Maude view mechanism. When importing a parametric domain (one with abstract sorts), the `where` clause binds those sorts to concrete types:

```
-- Import a parametric domain, binding its sort parameter:
import anthill.prelude.List where { T = Int }

-- Import selected items:
import anthill.prelude.List.{List, nil, cons} where { T = Int }

-- Import without binding (sorts remain abstract — re-exported as parameters):
import anthill.prelude.List.{List, nil, cons}

-- Import everything from a domain:
import banking
```

**Visibility** controls what crosses domain boundaries, expressed as a prefix modifier on declarations:

```
Visibility ::= 'internal'    -- visible only within this domain (default, can be omitted)
             | 'export'      -- visible to domains that import this one
             | 'public'      -- visible everywhere (use sparingly)
```

Default visibility is `internal`. The domain-level `export` clause lists exported names; individual `export`/`public` prefixes on declarations must be consistent with it.

**Domain content** — what can appear inside a domain:

```
DomainContent ::= Sort | Rule | Operation
                | Entity                 -- sugar (desugars to single-constructor Sort, see §6.3)
                | Fact | Constraint      -- sugar (desugars to Rule, see §6.1, §6.2)
                | OperationBlock | RuleBlock  -- sugar (desugars to individual declarations, see §6.4)
                | Domain                 -- nested domains
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

**Abstract sort** — declares that a type exists without specifying its representation. Used for type parameters in parametric domains, and for types whose carrier is provided later by an implementation.

```
sort Scalar                          -- abstract: no inhabitants defined
sort T                               -- abstract: type parameter
```

Abstract properties are expressed as accessor operations:

```
sort Vector
operation dim(v: Vector) -> Nat        -- accessor
```

**Defined sort** — enumerates all constructors (inhabitants). This is the kernel's algebraic data type mechanism. Each constructor is declared with the `entity` keyword and optional named fields:

```
sort Nat = {                         -- defined: closed set of constructors
  entity zero                        --   nullary constructor
  entity succ(pred: Nat)             --   constructor with field
}

sort List = {
  entity nil
  entity cons(head: T, tail: List)
}
```

A defined sort is **closed** — exactly the listed constructors exist. Pattern matching in rules works via unification on constructor terms:

```
rule length(nil) = zero
rule length(cons(?x, ?xs)) = succ(length(?xs))
```

**Standalone `entity`** is syntactic sugar for a single-constructor defined sort (see §6.3):

```
entity Account(id: AccountId, balance: Money)
-- desugars to: sort Account = { entity Account(id: AccountId, balance: Money) }
```

### 5.3 Rule

**THE knowledge primitive.** A Horn clause. All knowledge in the KB is expressed as rules. Two important special cases are given syntactic sugar (see §6):

- `fact X` = bodyless rule (ground assertion)
- `constraint C` = headless rule / denial (integrity constraint)

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

-- Denial / integrity constraint: headless rule (head = ⊥)
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

## 6. Syntactic Sugar

Readable shorthand that desugars to kernel constructs. The reasoning engine only sees rules and defined sorts.

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
Constraint ::= 'constraint' [Name ':'] RuleBody
                 ['meta' ':' Meta]
```

**Desugars to:**

```
constraint non_negative: balance(?a, ?b) => b >= 0
→  rule non_negative: ⊥ :- balance(?a, ?b), lt(?b, 0)
```

### 6.3 Entity (single-constructor sort)

A standalone entity declaration is sugar for a defined sort with one constructor. This is the most common case — a named record type.

```
Entity ::= [Visibility] 'entity' Name ['(' FieldList ')']
             ['meta' ':' Meta]
```

**Desugars to:**

```
entity Account(id: AccountId, balance: Money)
→  sort Account = { entity Account(id: AccountId, balance: Money) }

entity Marker
→  sort Marker = { entity Marker }
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

The `requires` and `ensures` clauses in operations are scoped constraints — they generate denials tied to the operation's input/output bindings. When an `Implementation` fact (from the `anthill.verification` standard domain) pairs with an operation, the kernel generates corresponding obligation rules.

## 7. Metadata

Every fact in the KB carries metadata. `Meta` is an **entity** in the `anthill.prelude` domain — not a special grammar production. It is a regular Fn term with named arguments:

```
domain anthill.prelude.Meta
  import anthill.prelude.Option
  import anthill.prelude.Nat
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
  sort Trust = {
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
  sort ProofResult = {
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
| `timestamp` | `String` | Recorded as provenance |
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

- **Abstract sorts** (`sort S`) introduce types without representation. Can appear in operation signatures and fields, but has no constructors until a carrier binding is provided.
- **Defined sorts** (`sort S = { entity C₁(...), entity C₂(...) }`) introduce closed algebraic data types. All constructors are enumerated; pattern matching in rules is exhaustive.
- **Operations** have typed signatures: `operation op(x: A, y: B) -> C`. Parameters are named bindings; the kernel type-checks that actual arguments match declared types.
- **Terms** are typed: `Const` carries its type, `Var` declares its type, `Fn` has the type of its sort's constructor, `Ref` refers to a named type.

### 8.2 Rule Evaluation

The kernel's reasoning engine supports:

**Forward chaining (bottom-up):** When a new fact is asserted, the engine checks all rules whose body might be newly satisfiable. If a rule's body is fully satisfied, its head is derived as a new fact.

**Backward chaining (top-down):** Given a query `?- goal`, the engine searches for rules whose head unifies with the goal, then recursively proves the body terms.

**Unification:** Standard first-order unification. `Var` terms unify with any term of the same type. `Fn` terms unify if their names match and all arguments unify pairwise.

**Termination:** The kernel uses stratification and loop detection to ensure rule evaluation terminates. Recursive rules must be stratifiable (no negation through recursion in the basic mode; stratified negation is supported for constrained cases).

### 8.3 Constraint Enforcement

Constraints (denials) are checked whenever a new fact is asserted:

1. For each denial `rule ⊥ :- B1, B2, ...`, check if the new fact, combined with existing facts, satisfies the body.
2. If the body is fully satisfied, the assertion is **rejected** — the constraint is violated.
3. The rejection includes the constraint name and the bindings that caused the violation.

This is the kernel's integrity mechanism — it prevents logically inconsistent states.

### 8.4 Operation Contracts and Obligations

When an operation has `requires`/`ensures` clauses and an `Implementation` fact links code to it:

1. The kernel generates **proof obligations** — facts of entity type `Obligation` (from the `anthill.verification` standard domain).
2. The obligation states: "prove that the implementation satisfies the contract."
3. Agents attempt to discharge the obligation. The kernel verifies submitted proofs.
4. Successfully discharged obligations elevate the implementation's trust level.

The kernel recognizes `Implementation` as a **well-known entity type** and triggers obligation generation automatically.

### 8.5 Domain Visibility

The kernel enforces domain boundaries:

- Declarations without a visibility prefix are **internal** — visible only within the declaring domain.
- **`export`**-prefixed declarations are visible to domains that explicitly `import` them.
- **`public`**-prefixed declarations are visible everywhere (discouraged).
- A query or rule body can only reference facts visible from the querying domain's scope.
- `import Name.{names}` makes specific names from another domain visible.

Visibility is enforced at query time and assertion time.

### 8.6 Algebras

An algebra is not a separate syntactic construct — it is the **typing structure that emerges** from declarations within a domain:

- **Abstract sorts** define the type parameters of the algebra.
- **Defined sorts** define concrete types with constructors (ADTs).
- **Operations** define typed behaviors with contracts.
- **Rules** (including constraint sugar) express laws.

The algebra IS the domain. When an `Implementation` fact provides carrier bindings (`carrier: { Scalar = float, Vector = CudaDeviceBuffer[float] }`), it instantiates the algebra for a specific host language.

**Parametric structure:** Abstract sorts in a domain serve as type parameters. A domain with abstract sort `T` is a parametric module — instantiated via `import ... where { T = ConcreteType }` or via inline type expression `List{T = Int}`. For example, `anthill.prelude.List` has abstract sort `T`; importing it with `where { T = Int }` or using `List{T = Int}` inline produces a list-of-integers.

This also supports type class-like patterns: a domain declaring `sort A` and `operation combine(x: A, y: A) -> A` with laws is a specification that any type with a `combine` operation must satisfy. Importing it with `where { A = MyType }` binds the specification to a concrete type.

## 9. Connections to Existing Systems

The kernel language connects to three traditions:

**ML-style modules.** Domain ≈ signature (declares abstract types and operations), Implementation with carrier bindings ≈ structure (provides concrete types), `import ... where` ≈ functor application. But anthill domains are richer — they contain rules (logic) and contracts (requires/ensures), making them algebraic specifications rather than pure type signatures.

**Maude / OBJ / CafeOBJ.** The closest match:

| Kernel language | Maude |
|----------------|-------|
| `domain` | theory (`fth`) or module (`fmod`) |
| `sort T` (abstract) | `sort` |
| `sort S = { entity ... }` (defined) | sort with constructor ops (`op ... : -> S [ctor]`) |
| `operation` | `op` (operator declaration) |
| `rule` (derivation) | equation (`eq`) or rewrite rule (`rl`) |
| `constraint` (denial) | membership axiom / conditional axiom |
| `Implementation.carrier` | view (maps theory sorts to module sorts) |
| `import ... where { T = X }` / `List{T = X}` | view instantiation (binds sort parameter) |
| domain with abstract sort | parameterized module (`fmod X{Y :: TRIV}`) |

The anthill adds: `Unspecified` (partial formalization), metadata (trust, provenance, agent), host-language embeddings (bidirectional mapping to Scala/Python/etc.), and the stigmergic agent layer.

**Proof assistants (Lean, Coq, Isabelle).** The kernel/tactic split: the kernel (small, trusted) checks proofs; tactics (large, untrusted) find proofs. In the anthill: the kernel grammar verifies, agents construct. The `trust` level on facts plays the role of Lean's `axiom` vs `theorem` distinction.

## 10. Examples

### 10.1 Banking Domain

A complete algebra with sorts (abstract and defined), operations, contracts, and laws:

```
domain banking
  export Account, Money, deposit, withdraw, balance

  sort Money
  import anthill.prelude.Numeric where { T = Money }   -- gives us +, -, >, >=, = for Money

  entity Account(                       -- sugar: sort Account = { entity Account(...) }
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
  constraint non_negative: gte(balance(?a), zero-val)
    -- desugars to: rule non_negative: ⊥ :- balance(?a, ?b), lt(?b, zero-val)
end
```

With infix sugar (once defined), the same domain reads more naturally:

```
domain banking
  export Account, Money, deposit, withdraw, balance

  sort Money
  import anthill.prelude.Numeric where { T = Money }

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

  constraint non_negative: balance(?a) >= 0
end
```

### 10.2 Linear Algebra with Parametric Sorts

Abstract algebra with sort variables, instantiated by different implementations:

```
domain linear_algebra
  export Scalar, Vector, add, scale, dot, dim

  sort Scalar
  sort Vector

  operation {
    dim(v: Vector) -> Nat
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

Two implementations (in the `anthill.verification` standard domain) could provide different carrier bindings:

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

### 10.3 Domain with Nested Subdomains

```
domain finance
  import banking.{Account, Money}
  export risk, audit

  domain risk {
    sort RiskLevel
    operation assess(a: Account) -> RiskLevel
    constraint bounded: assess(?a) <= maxRisk
  }

  domain audit {
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
              | Unspecified(text, hints, id) -- written as <"text">
              | Quoted(language, source)

-- =================================================================
-- Kernel Constructs (4)
-- =================================================================

Domain      ::= 'domain' Name
                  ['extends' Name (',' Name)*]
                  Import*
                  ['export' NameList]
                Body[DomainContent*]

Import      ::= 'import' Name ['.' '{' NameList '}']
                  ['where' '{' SortBinding (',' SortBinding)* '}']
NameList    ::= Name (',' Name)*
SortBinding ::= Name '=' Type

DomainContent ::= Sort | Rule | Operation
                | Entity                       -- sugar (§6.3)
                | Fact | Constraint            -- sugar (§6.1, §6.2)
                | OperationBlock | RuleBlock   -- sugar (§6.4)
                | Domain

Visibility  ::= 'internal' | 'export' | 'public'

Sort        ::= [Visibility] 'sort' Name                           -- abstract
                  ['meta' ':' Meta]
              | [Visibility] 'sort' Name '=' Body[Constructor*]    -- defined (ADT)
                  ['meta' ':' Meta]

Constructor ::= 'entity' Name ['(' FieldList ')']
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

-- =================================================================
-- Syntactic Sugar
-- =================================================================

Fact        ::= 'fact' Term ['meta' ':' Meta]
              -- desugars to: rule Term

Constraint  ::= 'constraint' [Name ':'] RuleBody
                  ['meta' ':' Meta]
              -- desugars to: rule [Name ':'] ⊥ :- ¬RuleBody

Entity      ::= [Visibility] 'entity' Name ['(' FieldList ')']
                  ['meta' ':' Meta]
              -- desugars to: sort Name = { entity Name [( FieldList )] }

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
