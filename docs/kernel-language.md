# Kernel Language Specification

The kernel language is the minimal formal language of the anthill knowledge base. It defines four constructs that the reasoning engine understands natively — everything else in the anthill is built on top of these as entity types in standard namespaces.

This specification is **self-contained**: it can be implemented without reference to the high-level design document ([metasystem-design-draft.md](../metasystem-design-draft.md)), which provides motivation and vision but is not formal.

## 1. Design Principles

1. **Minimal kernel.** Four constructs: `namespace`, `sort`, `rule`, `operation`. The kernel is deliberately small — analogous to the kernel of a proof assistant (Lean, Coq) that is small, trusted, and verifies proofs, while tactics (large, untrusted) find them. `entity` is syntactic sugar (see §6).

2. **Rule is THE knowledge primitive.** All knowledge in the KB is expressed as rules (Horn clauses). `fact` and `constraint` are syntactic sugar that desugar to rules. This unifies ground assertions, derived knowledge, and integrity constraints under one mechanism.

3. **Algebraic specification.** The kernel is in the tradition of algebraic specification languages (OBJ, CafeOBJ, Maude): a namespace declares sorts (unspecified, type aliases, or defined types), operations (typed behavioral specs with contracts), and rules (laws).

4. **Partial formalization.** Any declaration can have one or more **description blocks** (`{< >}`) — free-form text preserved as KB facts. Each block is stored as its own indexed `Description` fact. Combined with anonymous variables (`?`), this allows a spectrum from fully informal to fully formal within the same language.

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
| Namespace header | `import`, `end` |
| Visibility (prefix) | `internal`, `public` |
| Operation | `requires`, `ensures`, `effects` |
| Rule | `:-` (operator, not keyword) |
| Infix operators (word) | `or`, `and`, `mod`, `div` |
| Infix operators (symbol) | `@` (effect annotation on `->`) |
| Prefix operators (word) | `not` |
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
Term ::= Const(type, value)            -- ground value: 42 : Int64, "hello" : String
       | Var(type, name)               -- unification variable: ?x : Int64
       | Fn(name, args: [Term])        -- compound: account(?id, ?owner, ?bal)
       | Ref(Name)                     -- reference to named entity: banking.Money
       | Quoted(language, source)      -- verbatim host-language fragment (see §4.2)
```

### 4.1 Description Blocks

Description blocks (`{< >}`) attach human-readable text to declarations. Unlike comments (`--`, `{- -}`), description blocks are **structural** — they are preserved as `Description` facts in the KB. Multiple description blocks can be attached to the same target; each block is stored as its own `Description` fact, ordered by an index argument.

```
-- Inline description on an abstract sort:
{< The element type >}
sort T = ?

-- Multiple description blocks on a sort with body:
{< Core banking entity >} {< See RFC-042 for rationale >}
sort Account
  entity account(id: AccountId, balance: Money)
end

-- Standalone describe declaration (appends to existing descriptions):
describe Eq.T {<
  The type that supports equality comparison.
  Must be a concrete type, not a type constructor.
>}

-- Inline description on a variable in any term position (trailing ? closes):
rule test: foo(?x {< the x value >} ?)
constraint positive: gt(?amount {< must be non-negative >} ?, 0)

-- Multiple description blocks on a variable:
operation withdraw(amount: ?T {< monetary type >} {< must support subtraction >} ?) -> ?T
```

Description blocks can appear in three positions:

1. **Before a declaration keyword** (`sort`, `operation`, `rule`, `entity`, `fact`, `constraint`, `namespace`) — describes the declaration that follows.
2. **After `describe Name`** — standalone, can reference any named symbol. Appends to existing descriptions.
3. **After a variable (`?` or `?name`), closed by trailing `?`** — describes what the variable represents in that rule, constraint, fact, or operation contract. The trailing `?` delimiter disambiguates variable descriptions from declaration descriptions.

Multiple `{< >}` blocks on the same target each emit a separate fact with an increasing index, preserving declaration order. The `describe` construct emits additional `Description` facts for its target, enabling incremental annotation across files (the index counter is per file, so declaration order is encoded within a file, not across files).

Descriptions are stored as `Description(target, text, index)` facts — one fact per block, with a 0-based per-target `index` — queryable via `by_functor("Description")`. For variables, the target is the variable's term in the KB.

| Purpose | Syntax | Structural? |
|---------|--------|-------------|
| Commenting out code | `--` (line), `{- -}` (block) | No — discarded by parser |
| Description / documentation | `{< >}` (description block) | Yes — preserved as KB facts |

### 4.2 Quoted Terms

`Quoted(language, source)` embeds host-language fragments verbatim. A `Quoted` term IS formal — just in a different language. Host-language embeddings can interpret it.

```
Quoted("scala", "case class Account(id: Long, balance: BigDecimal)")
```

### 4.3 Primitive Types

The kernel has only four primitive types for `Const` values:

| Type | Values |
|------|--------|
| `String` | `"hello"`, `"src/main/scala"` |
| `Int64` | `0`, `42`, `-1` |
| `Float` | `3.14`, `-0.5` |
| `Bool` | `true`, `false` |

**Everything else is a compound type** — defined via `sort` and `operation` in the `anthill.prelude` standard namespace (see §4.4). Literal syntax for compound types is sugar:

| Literal | Desugars to |
|---------|------------|
| `5m` | `Duration(5, "m")` |
| `30s` | `Duration(30, "s")` |
| `[a, b, c]` | `ListLiteral(a, b, c)` — desugared by typing to concrete constructors via `Collection` |
| `{a, b, c}` | `SetLiteral(a, b, c)` — desugared by typing to concrete constructors |

### 4.4 The Prelude Namespaces

Common compound types are defined in standard prelude sorts using the kernel's own constructs. **Parametric types are sorts with unspecified sub-sorts** — instantiated via **inline type expressions** `Name[bindings]`. **Sum types are sorts with entity constructors** — `sort S { entity C₁(...), entity C₂(...) }` enumerates constructors (see §5.2).

> **Canonical source:** The prelude definitions below are extracted from `stdlib/anthill/prelude/`. Those `.anthill` files are the canonical source; this section is for reference.

```
-- Duration: a non-parametric prelude sort
sort anthill.prelude.Duration {
  entity Duration(amount: Int64, unit: String)         -- duration(5, "m")
}

-- Timestamp: a non-parametric prelude sort
sort anthill.prelude.Timestamp {
  entity Timestamp(value: String)
}

-- List: a parametric sort (T is the unspecified sort parameter)
sort anthill.prelude.List
  sort T = ?                                         -- type parameter (unspecified)
  entity nil                                         -- empty list
  entity cons(head: T, tail: List)                   -- cons cell

  operation length(l: List) -> Int64
  rule length(nil) <=> 0
  rule length(cons(?x, ?xs)) <=> add(1, length(?xs))
end

-- Option: a parametric sort
sort anthill.prelude.Option
  sort T = ?                                         -- type parameter (unspecified)
  entity none                                        -- absent
  entity some(value: T)                              -- present
end
```

**`some`-coercion (WI-408).** A value of type `T` supplied for an
`Option[T]` slot — an entity field or an operation argument — is implicitly
wrapped in `some(...)`, so the value is properly `Option`-typed at runtime
(the first slice of the implicit-conversion framework; the general framework
is deferred). The insertion happens once per boundary: in the typer for
operation-body constructors and calls (a synthesized `some(...)` node), and
in the loader for term-world content asserted before the typing pass —
fact fields and rule-body entity atoms, so a bare pattern (`depends_on:
cons(...)`) matches the wrapped facts. A variable in the slot binds the
whole `Option` value and is never wrapped; a value already headed by
`some`/`none` is left alone; a bare value under a *nested*
`Option[Option[T]]` is rejected (one wrap is inserted, never a guessed
double-wrap). The canonical in-KB term form of `some` is the named
`some(value: v)`; a source-written positional `some(v)` is canonicalized at
load.

```
-- Eq: equality
sort anthill.prelude.Eq
  sort T = ?
  operation {
    eq(a: T, b: T) -> Bool          -- =
    neq(a: T, b: T) -> Bool         -- !=
  }
  rule neq(?a, ?b) <=> not(eq(?a, ?b))              -- equational rule head: `<=>` (unify), not `=` (test)
end

-- Ordered: total ordering (requires Eq)
sort anthill.prelude.Ordered
  sort T = ?
  requires Eq[T]

  operation {
    gt(a: T, b: T) -> Bool          -- >
    gte(a: T, b: T) -> Bool         -- >=
    lt(a: T, b: T) -> Bool          -- <
    lte(a: T, b: T) -> Bool         -- <=
  }

  rule {
    lt(?a, ?b)  <=> gt(?b, ?a)                    -- oriented rewrites: `<=>`
    lte(?a, ?b) <=> gte(?b, ?a)
    gte(?a, ?b) <=> not(lt(?a, ?b))
    antisymmetric: ⊥ :- gt(?a, ?b), gt(?b, ?a)    -- constraint (a body test): stays `=`/`:-`
  }
end

-- Numeric: basic arithmetic (requires Ordered)
sort anthill.prelude.Numeric
  sort T = ?
  requires Ordered[T]

  operation {
    add(a: T, b: T) -> T           -- +
    sub(a: T, b: T) -> T           -- -
    mul(a: T, b: T) -> T           -- *
    div(a: T, b: T) -> T           -- /
    mod(a: T, b: T) -> T           -- %
    pow(a: T, b: T) -> T           -- ^
    zero-val() -> T                -- additive identity
  }

  rule {
    add_comm:  add(?a, ?b) <=> add(?b, ?a)                     -- laws are equational heads: `<=>`
    add_assoc: add(add(?a, ?b), ?c) <=> add(?a, add(?b, ?c))   -- symmetric; citable both ways via `using`
    add_identity: add(?a, zero-val) <=> ?a
  }
end
```

**Infix and prefix operators** are sugar for function application — `a + b` desugars to `add(a, b)`, `!a` to `not(a)`, etc. The full operator table is in §6.6. The prelude sorts above define the operations these operators desugar to; the operators are available when the corresponding sort is required (e.g. `requires Numeric[T = Money]`). One target is **position-directed**: `not(…)` is negation-as-failure (`anthill.reflect.not`, a resolver primitive over a `Term`) in a rule-body goal position, but boolean negation (`Bool.not`, a dispatched operation) as a value expression — see §6.6.

**Instantiation** — via inline type expressions (`Name[bindings]`):

```
entity Project(
  name   : String,
  tools  : List[T = String],
  modules: Option[T = Module]
)

operation lookup(key: String) -> Option[T = Account]
```

The inline form `List[T=Int64]` refers to the sort `List` with unspecified sort parameter `T` bound to `Int64`. This is the Maude view mechanism expressed as a type expression.

**Grammar:**

```
Type ::= Name                                        -- simple type reference
       | Name '[' SortBinding (',' SortBinding)* ']' -- inline instantiation
       | VariableTerm                                 -- logical variable: ?, ?T, ?T {< desc >}+ ?
       | TupleType                                    -- tuple type: (Int64, String), (a: Int64, b: String), ()
       | ArrowType                                    -- arrow type (function sort)

ArrowType ::= '(' ArrowParams ')' '->' Type              -- pure function
            | '(' ArrowParams ')' '->' Type '@' Type      -- effectful function

ArrowParams ::= (TupleTypeArg (',' TupleTypeArg)*)?       -- reuses TupleTypeArg: Type or Name ':' Type
```

**Arrow types** describe function-sorted values. `(A) -> B` is the sort of pure functions from `A` to `B`. The parameter list is always parenthesized, disambiguating `->` in type position from `->` in operation return type position. Parameters can be named (using the same syntax as named tuple elements):

```
(Int64) -> String                         -- unary function
(A, B) -> C                             -- binary function
() -> A                                 -- thunk (nullary)
(acc: A, elem: B) -> A                  -- named parameters
(A) -> B @ Modifies(S)                  -- effectful function
(A) -> B @ (Modifies(S), Errors(Err))   -- multiple effects
```

Arrow sorts associate to the right: `(A) -> (B) -> C` is `(A) -> ((B) -> C)`.

The `@` token annotates effects on the arrow, consistent with the term-level Pratt operator where `a -> b @ c` desugars to `arrow_effect(a, b, c)`. A pure arrow `(A) -> B` desugars to `arrow(params..., B)` in the KB; an effectful arrow `(A) -> B @ E` desugars to `arrow_effect(params..., B, E)`.

The braced annotation `@ {…}` admits the proposal-045 row algebra: bare labels (present), an explicit row variable (`?` anonymous, `?r` named, or a declared row binder `E` — an **open** row), and `-e` absence atoms (`lacks` constraints). `@ {}` is the explicit closed-empty (pure) row, identical to no annotation. An absence-only annotation (`@ -Modify[x]`) is a **closed** row carrying the lacks constraint; the co-finite "anything except `e`" is written with an explicit open base — `@ {?, -Modify[x]}` or `@ {Eff, -Modify[x]}` (WI-440 row-openness decision: an implicit fresh tail would be unnameable by the enclosing operation, which must declare the row it incurs when applying the callback). A callback parameter's row is checked at each call site against the argument operation's declared row, with the callback's binder places aligned positionally to the argument's own parameters (`Modify[c]` on the argument's param 0 matches `Modify[x]`/`-Modify[x]` on the callback's param 0); an unresolved place in a `-…` absence label is a load-blocking error (the constraint would be vacuous).

The arrow sort `(A) -> B` is equivalent to `Function[A, B]` from stdlib (with empty effect set). The effectful arrow `(A) -> B @ E` is equivalent to `Function[A, B, E]`. `Function` is the unified sort for all callable values — pure and effectful. Effect subtyping applies: a pure function can be passed where an effectful function is expected (`Function[A, B] <: Function[A, B, E]` for any `E`).

Import and instantiation are separate concepts: `import` makes names visible, inline `Name[bindings]` instantiates sort parameters. They are not bundled together.

**Instantiation as term:** The `Name[bindings]` syntax is valid both in type position and in term position. In term position, it represents a sort instantiation as a first-class value — used to assert that a type satisfies a parametric spec:

```
-- "Int64 satisfies Eq" — a fact in the KB
fact Eq[T = Int64]

-- "String satisfies Ordered" — scoped to the declaring namespace
fact Ordered[T = String]
```

This follows the "types are terms" principle: sort instantiations are knowledge, expressible as facts. Different namespaces can provide different instantiations (see §5.1 on namespace scoping).

**Entity instances and sort membership:** An entity constructor applied to arguments produces a term that inhabits the enclosing sort. For example, given `sort Modify { sort T = ? entity Modify(target: T) }`, the term `Modify(store)` is an instance of sort `Modify[T = typeof(store)]`. This means entity instances can appear in sort binding positions — `Modify[store]` is `Modify` instantiated with target `store`:

```
-- Sort-level: Modify parameterized with any target
fact Effect[T = Modify[?]]

-- Value-level: Modify applied to a specific parameter
operation persist(store: Store, fact: Term, meta: Meta) -> FactId
  effects {Modify[store], Error}   -- store will be mutated; operation can fail
```

Because types are terms, a type expression may contain logical variables and concrete value terms directly: the KB's unification machinery handles abstract bindings (`Modify[?]`) and concrete ones (`Modify[store]`) uniformly, with no separate type-variable mechanism. This is the precise content of "types are terms" — the type sublanguage (the `Type` grammar above) is the *normal-form* fragment of terms (names, parameterized applications, tuples, arrows) plus logical variables, over which sort membership and `refines` are decided structurally.

A type argument may also be a **value** rather than a sort — `Modify[store]` indexes the `Modify` effect type by the value `store` (proposal 027.1: `Modify[c]` on a parameter, `Modify[result]` on a return, `Modify[result.a]` per projection). This is *value-dependent* typing: the value is carried as `TypeExtractor.Denoted(value: <occurrence>)` so it is recognised as a value indexing the type, not a sort reference (WI-302; WI-361). The grammar already admits the surface forms (names and field projections in `[...]`); `Denoted` is the structural form that keeps the value distinct from a bare sort reference (`Ref(S)`).

This is distinct from *constructing* a `Type` by a computation. An operation call that returns a `Type` (e.g. building `List[T = apply_subst(env, t)]` — the term-backed `Fn{List, named}`, WI-361) is ordinary expression code that constructs the type term directly — it is not type-annotation syntax and does not use, or need, the `[...]` instantiation sugar.

Additional types are introduced via `sort` declarations (unspecified, type alias, or defined) in any namespace.

### 4.5 Tuples and Parenthesized Expressions

**Parenthesized expressions** `(a)` are grouping — `(a) = a`. They are valid wherever a term is expected.

**Tuple sorts** are structurally-typed anonymous products. There is one concept: **named tuples**. Every element has a name. Positional syntax is sugar for auto-generated names `_1`, `_2`, `_3`, ...

```
-- Tuple types (in type position)
TupleType ::= '(' ')'                                              -- unit
            | '(' TupleTypeArg ',' TupleTypeArg (',' TupleTypeArg)* ')'  -- 2+ elements

TupleTypeArg ::= Type | Name ':' Type

-- Tuple literals (in term position)
TupleLiteral ::= '(' ')'                                           -- unit value
               | '(' FnArg ',' FnArg (',' FnArg)* ')'              -- 2+ elements
```

**Disambiguation:** `(a)` with no comma is a parenthesized expression (grouping). `(a, b)` with a comma is a tuple. `Name(...)` preceded by a name is function application. No lookahead needed.

**All-or-nothing naming:** either all elements have explicit names or none do. Mixing `(a: Int64, String)` is an error.

**Desugaring:** Positional tuples desugar to named tuples with `_N` names:

| Surface syntax | Desugared form |
|---|---|
| `(A, B)` | `(_1: A, _2: B)` |
| `(1, "hello")` | `(_1: 1, _2: "hello")` |
| `()` | `()` (unit, no fields) |

**Representation:** Tuple literals are represented as `TupleLiteral(...)` terms with named args, analogous to `SetLiteral(...)` for sets. The `TupleLiteral` entity is defined in `anthill.reflect`.

**Examples:**

```
-- Multi-value return
operation divmod(a: Int64, b: Int64) -> (Int64, Int64)

-- Named multi-value return
operation divmod(a: Int64, b: Int64) -> (quotient: Int64, remainder: Int64)

-- Tuple in rules
rule swap((?x, ?y)) <=> (?y, ?x)

-- Unit
()
```

### 4.6 Collection Literals

**Collection literals** use bracket syntax for constructing ordered sequences.

```
-- Collection literals (in term position)
CollectionLiteral ::= '[' ']'                                           -- empty
                    | '[' Term (',' Term)* ']'                          -- elements
```

**Construction:** `[a, b, c]` is represented as `ListLiteral(a, b, c)` in the untyped term language. The typing process rewrites this to concrete constructors (`Collection.insert`/`Collection.empty`) based on the expected type.

**Destructuring:** there is **no** head-tail literal sugar. To destructure a list, match the `cons`/`nil` constructors directly (`cons(head: ?h, tail: ?t)` in a rule head, or `case cons(h, t) -> …` in a `match`). A first-class, type-directed collection *deconstruction* syntax (`[h | t]` desugaring to `Iteration.split` for any collection, in pattern position) is a planned extension, not yet in the language — see the collection-deconstruction work item. (An earlier `[h | t]` *literal* surface existed at parse level only, with no end-to-end semantics, and was removed.)

**Disambiguation:** Bare `[` starts a collection literal. `Name[` starts an instantiation term (`Eq[Int64]`) or parameterized type (`List[T = Int64]`). No lookahead needed — the presence of a leading `Name` disambiguates.

**Representation:** Collection literals are represented as `ListLiteral(...)` terms, analogous to `SetLiteral(...)` for sets and `TupleLiteral(...)` for tuples. The `ListLiteral` entity is defined in `anthill.reflect`.

**Examples:**

```
-- Empty collection
rule empty_list: []

-- Integer list
rule digits: [1, 2, 3]

-- List destructuring via the cons/nil constructors
rule first(cons(head: ?h, tail: ?_)) <=> ?h
```

### 4.7 Lambda

**Lambda expressions** construct anonymous functions — values of arrow sort `(P) -> R` (with effects `(P) -> R @ {E}` when the body is effectful).

```
LambdaExpr ::= 'lambda' Pattern '->' Expr
```

A lambda binds **exactly one** pattern. Multiple parameters are expressed by destructuring a tuple (`lambda (a, b) -> …`); a nullary thunk binds the empty tuple (`lambda () -> …`). This single-pattern rule is deliberate, not a limitation: it avoids comma ambiguity when a lambda is passed as a call argument (`map(lambda x -> f(x), xs)`) — the tuple parens delimit the parameter, so the enclosing call's commas separate arguments unambiguously.

The `lambda` keyword is **required**. A keyword-less `(x, acc) -> body` (or `x -> body`, or the effectful `x -> body @ E` form) is not a lambda — the infix `->` builds an arrow-*type* term, whose left-hand names would be read as value references, not binders. The loader diagnoses the typo by **provenance** (WI-605/WI-618): the parser marks each `->`/`@` operator term it desugars, so a desugared infix arrow is distinguished *exactly* from a written call to a functor the user happened to name `arrow` — the call keeps its meaning and its own diagnostics. In an operation/const-body expression position, any marked arrow is rejected with a targeted error suggesting the `lambda` keyword. In logic/data positions — rule heads and bodies, fact arguments, constraints, `requires`/`ensures` clauses — an arrow *type* is a legitimate term (types are terms), so a marked arrow is rejected only when it carries a binder-looking leaf (a lowercase or `_`-led name) that resolves to nothing in scope: a real arrow type's leaves (sorts, type parameters, rule type-variables, parameter/`result` places) resolve, and its logical variables are written `?x`, not bare names. Known accepted gap: a typo whose binder names all coincide with in-scope names (or are written uppercase) still loads as inert arrow data.

A lambda's type is the arrow sort `(P) -> R`: `P` is the parameter pattern's type, `R` the body's type, and any effects the body performs annotate the arrow (`@ {E}`). A lambda captures its enclosing bindings (a closure).

A lambda binder may carry an **optional `: Type` annotation**, written in parens: a single binder `lambda (x: T) -> …`, or per-element in a tuple `lambda (a: A, b: B) -> …` (WI-517). The parens are required — a bare `lambda x: T -> …` would clash with the `->` separator. The annotation pins the binder's type, so a lambda can be written **without** an expected-type context (e.g. `let f = lambda (x: Int64) -> add(x, 1)`, where no use site supplies the parameter type) and so foldLeft-style callbacks can document their parameters. When an expected arrow type is also available at the use site, the annotation must be consistent with it — a genuine contradiction is rejected (for a single binder, the lambda's arrow carries the annotation and is checked against the expected type; for tuple binders, the surrounding component type drives the binding, so a conflict surfaces through the body's use of the binder). A binder written without an annotation infers its type from the expected arrow at the use site (the HOF parameter's declared type, the operation's return type, etc.).

**Examples:**

```
lambda x -> x                              -- identity (type inferred at use site)
lambda x -> add(x, 1)                      -- single parameter
lambda (x) -> add(x, 1)                    -- same: parens are grouping, not a 1-tuple
lambda (a, b) -> add(a, b)                 -- tuple destructuring (two parameters)
lambda () -> compute()                     -- nullary thunk: type () -> R

lambda (x: Int64) -> add(x, 1)             -- annotated single binder (parens required)
lambda (acc: Int64, elem: Int64) -> add(acc, elem)   -- annotated tuple binders

-- annotation lets a lambda stand on its own, with no expected-type context:
let f = lambda (x: Int64) -> add(x, 1)

-- as a closure in an operation body:
operation make_adder(x: Int64) -> (Int64) -> Int64 = lambda y -> add(x, y)

-- as a call argument:
map(xs, lambda x -> add(x, 1))
```

The parameter pattern is a bare variable (`x`), a single parenthesized typed binder (`(x: T)`), a tuple destructuring (`(a, b)` or `(a: A, b: B)`, two or more binders), or the empty tuple (`()`) for a nullary thunk; the nullary form has arrow type `() -> R`. Parentheses around a single pattern are pure grouping — in **any** pattern position (lambda parameter, `match` case, `let`): `lambda (x) -> …` binds the same single variable as `lambda x -> …`, and `case (p) -> …` matches the same as `case p -> …`. A single parenthesized element is **not** a 1-tuple (WI-620).

## 5. Kernel Constructs

Four constructs the reasoning engine understands natively.

### 5.1 Namespace

The unit of encapsulation and independent evolution. A namespace scopes sorts, entities, operations, and rules. Namespaces can be nested.

**Dotted names desugar to nested namespaces.** When any declaration (`sort`, `namespace`, `entity`, `operation`) uses a dotted name, each dot-separated prefix segment becomes an implicit namespace if one does not already exist. The item itself is defined by its last segment (short name) in the innermost scope.

```
-- This declaration:
sort anthill.prelude.List { ... }

-- desugars to:
namespace anthill {              -- implicit, created if not present
  namespace prelude {            -- implicit, created if not present
    sort List { ... }            -- short_name = "List", qualified_name = "anthill.prelude.List"
  }
}
```

Implicit namespaces merge with explicit namespaces of the same qualified name. This means:
- Siblings share a scope: `sort ns.A` and `sort ns.B` in separate files both live in the implicit `ns` namespace and can reference each other without imports.
- Wildcard imports work naturally: `import anthill.prelude.*` imports all items defined in the `anthill.prelude` scope.
- Explicit `namespace anthill { ... }` and implicit `anthill` (from `sort anthill.prelude.X`) merge into one scope.

**Qualified names.** Every defined symbol has a `short_name` (last segment) and a `qualified_name` (full path from the global scope). Items nested inside a sort or namespace body have their qualified name constructed by prepending the enclosing scope's qualified path. For example, `operation eq` inside `sort anthill.prelude.Eq` gets `qualified_name = "anthill.prelude.Eq.eq"`. The `by_qualified_name` index serves as a global registry of fully-qualified paths, while scope-aware resolution (`resolve_in_scope`) uses short names and parent scope chains.

```
Namespace ::= DescriptionBlock*
              'namespace' Name
              Body[NamespaceContent*]

Import ::= 'import' ImportPath
ImportPath ::= Name                               -- import a specific name
             | Name '.' '{' NameList '}'           -- selective: specific names from a namespace
             | Name '.' '*'                        -- wildcard: everything from a namespace

NameList    ::= Name (',' Name)*
SortBinding ::= Name '=' Type                   -- named: binds a specific sort parameter to a type
              | Type                             -- positional: binds to the next unfilled sort parameter
              | VariableTerm                     -- anonymous/named variable: Modify[?], Modify[?r]
```

When a sort binding omits the `Name =` part, it is a **positional** binding — the value is bound to the next unfilled sort parameter in declaration order. Named (`Name = Type`) and positional bindings can be mixed, with positional bindings first:

```
-- Positional bindings (bound to sort parameters in declaration order):
List[Int64]                -- List[T = Int64] — Int64 binds to first param T
Map[String, Int64]         -- Map[K = String, V = Int64] — positional for both

-- Named bindings (explicit parameter name):
List[T = Int64]            -- explicit: T binds to Int64
Numeric[T = Money]       -- explicit: T binds to Money

-- Mixed: positional first, then named
Bifunctor[String, B = Int64]   -- A = String (positional), B = Int64 (named)

-- Positional with type variables (common in parametric sort bodies):
requires Eq[T]           -- Eq[T = T] — T positionally binds to first param
sort C = SPair[B, A]     -- SPair[A = B, B = A] — positional, swaps params
```

Note that `Eq[T]` inside a scope where `T` is a sort parameter works because `T` is positionally bound to `Eq`'s first parameter — which happens to be named `T`. This is a positional coincidence, not name-based punning.

A sort binding can also be a **logical variable** (`?` or `?name`). This is used to express existential quantification over type parameters — "for any instantiation":

```
-- Modify[?] means "Modify instantiated with any target type"
fact Effect[T = Modify[?]]       -- Modify is an effect kind, for any target

-- Named variable binds across the term:
rule CanModify[?r] :- Effect[T = Modify[?r]]   -- extract modifiable resources
```

Import makes names from another namespace visible in the current scope as local aliases. It does **not** add the imported sort's scope as a parent — importing `Eq` does not make `eq`/`neq` directly accessible. To access a sort's contents, use `requires Eq[T]` (sort composition) or wildcard import. Sort parameters remain unspecified — they are instantiated separately via inline type expressions (`Name[bindings]`), not at import time.

Three import forms:

```
-- Import a specific name from a namespace:
import anthill.prelude.List                   -- imports "List" from anthill.prelude

-- Import selected items from a namespace:
import anthill.prelude.{List, Option}         -- imports "List" and "Option" from anthill.prelude

-- Import everything from a namespace:
import anthill.prelude.*                      -- imports all visible names from anthill.prelude
```

**Visibility** is a prefix modifier on declarations. Names are **visible by
default**; the modifiers adjust that (full algorithm in §8.6):

```
Visibility ::= 'internal'    -- hidden from outside the declaring scope
             | 'public'      -- visible everywhere, even without import
```

A name is visible to importers and requirers unless marked `internal`. See §8.6
for the complete name-resolution algorithm. (The `export` statement and `export`
visibility prefix, formerly no-ops, were removed in WI-291.)

**Namespace content** — what can appear inside a namespace:

```
NamespaceContent ::= Import                        -- statements can appear anywhere in the body
                   | Sort | Rule | Operation      -- Sort: sorts-with-body or type aliases (not unspecified)
                   | RequiresDecl                -- sort-level constraint (see §5.2)
                   | Entity                      -- sugar (desugars to single-constructor Sort, see §6.3)
                   | Fact | Constraint           -- sugar (desugars to Rule, see §6.1, §6.2)
                   | OperationBlock | RuleBlock  -- sugar (desugars to individual declarations, see §6.4)
                   | Describe                    -- description block (see §4.1)
                   | Namespace                   -- nested namespaces
```

### 5.2 Sort

A type declaration. Sort has three forms — **unspecified** (declared, carrier unknown), **type alias** (equated to another type), and **sort with body** (inhabitants enumerated as a closed ADT, or algebra with operations/rules):

```
Sort ::= DescriptionBlock*
           [Visibility] 'sort' Name '=' VariableTerm              -- unspecified
           ['meta' ':' Meta]
       | DescriptionBlock*
           [Visibility] 'sort' Name '=' Type                   -- type alias
           ['meta' ':' Meta]
       | DescriptionBlock*
           [Visibility] 'sort' Name                            -- sort with body
           Body[SortContent*]
           ['meta' ':' Meta]

Constructor ::= 'entity' Name ['(' FieldList ')']            -- variant/constructor
FieldList   ::= Field (',' Field)*
Field       ::= Name ':' Type
```

`SortContent` mirrors `NamespaceContent`: imports are ordinary statements that can appear anywhere in the body, interleaved with sorts, entities, rules, operations, sugar forms, descriptions, or even nested namespaces.

**Unspecified sort** (`sort Name = ?`) — declares that a type exists without specifying its representation. Unspecified sorts appear inside sort bodies, where they serve as **type parameters** — their carrier is provided later by an implementation or by inline instantiation.

```
sort T = ?                           -- unspecified: type parameter (inside a sort body)
sort T = ?Name                       -- unspecified: named logical variable (shared within scope)
```

**Logical variables as types** — The `?` and `?name` syntax (logical variables) is valid in any type position, not just in `sort ... = ?` definitions. Named type variables share identity within their enclosing scope (operation, rule, entity), just like term variables:

```
operation identity(x: ?T) -> ?T           -- ?T is the same variable in param and return type
entity Pair(fst: ?A, snd: ?B)             -- two distinct type variables
operation transform(x: ?T {< input type >} ?) -> ?T  -- with inline description (trailing ? closes)
```

**Type alias** (`sort Name = Type`) — creates a name that is equivalent to an existing type. Useful for domain-specific naming:

```
sort Money = Int64                     -- Money is an alias for Int64
sort Velocity = Float                -- Velocity is an alias for Float
```

Unspecified properties are expressed as accessor operations within the enclosing sort body:

```
sort linear_algebra {
  sort Vector = ?                    -- unspecified: type parameter
  operation dim(v: Vector) -> Int64     -- accessor
}
```

**Sort with body** — a sort can have a body containing entities (constructors), sub-sorts (parameters, either unspecified or aliased), `requires` declarations (sort-level constraints), operations, rules, and other items. When a sort body contains entity declarations, they are constructors of that sort, making it a closed ADT:

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
rule length(nil) <=> 0
rule length(cons(?x, ?xs)) <=> add(1, length(?xs))
```

**Requires declaration** — a standalone `requires` in a sort or namespace body declares a sort-level constraint: the enclosing scope depends on another algebraic spec. This is distinct from operation-level `requires` clauses (preconditions on individual operations).

```
RequiresDecl ::= 'requires' Type
```

The `requires` declaration takes a type expression — either a simple sort name or a parameterized sort with bindings:

```
sort Ordered {
  sort T = ?
  requires Eq[T]                     -- this sort depends on Eq over T

  operation gt(a: T, b: T) -> Bool
}

sort banking {
  sort Money = ?
  requires Numeric[T = Money]         -- this sort (algebra) depends on Numeric over Money
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
Rule ::= DescriptionBlock*
           'rule' [Name ':'] (Heads ':-' RuleBody | RuleBody '-:' Heads | Heads)
           ['meta' ':' Meta]

Heads       ::= Term (',' Term)*           -- one or more heads (multi-head: conjunctive sugar)
              | '⊥'                        -- bottom (for denials; cannot mix with positive heads)

RuleBody    ::= Term (',' Term)*           -- premises (conjunction)
```

**Single arrow per rule.** `:-` and `-:` are mirror surface forms of the same implication operator (proposal 032). Exactly one of them appears per rule (or neither, for a bare-head fact). The dual-arrow form `head :- body -: conclusion` is **not** part of the grammar — under the unified design the head IS the rule's conclusion, so a separate `-:` slot would duplicate it. `:-` reads as "if" (head if body); `-:` reads as "then" (body therefore head). They produce the same internal Horn clause; choice is purely stylistic.

**Forms:**

```
-- Derivation rule (Horn), backward and forward forms:
rule ancestor(?X, ?Z) :- parent(?X, ?Y), ancestor(?Y, ?Z)
rule parent(?X, ?Y), ancestor(?Y, ?Z) -: ancestor(?X, ?Z)

-- Ground assertion (= fact): bodyless rule
rule parent("alice", "bob")

-- Denial / integrity constraint, backward and forward:
rule non_negative: ⊥ :- balance(?a, ?b), lt(?b, 0)
rule non_negative: balance(?a, ?b), lt(?b, 0) -: ⊥

-- Positive theorem — the head IS the conclusion:
rule lower_bound:
  reachable_real(?l, ?f), position_distance(?d, ?l, ?f),
  DistanceBounds(d_min: ?d_min, d_max: ?_)
  -: gte(?d, ?d_min)

-- Same theorem, backward form:
rule lower_bound: gte(?d, ?d_min)
  :- reachable_real(?l, ?f), position_distance(?d, ?l, ?f),
     DistanceBounds(d_min: ?d_min, d_max: ?_)
```

**Equational rules (`<=>`).** A bodyless rule whose single head is a `<=>` (unification) term — `rule LHS <=> RHS` — is an **equational rule**: an oriented rewrite / definitional equation the engine derives L→R. This is how the prelude defines derived operations (`rule neq(?a, ?b) <=> not(eq(?a, ?b))`, `rule length(nil) <=> 0`) and how a carrier defines an operation by cases (`rule eq(red, red) <=> true`). The head connective is `<=>`, **not** `=`: `=` (`Eq.eq`) is a semantic equality *test* that never binds, whereas an equational rule head *unifies* the redex with the rule's LHS and derives the RHS (binding the LHS variables) — see §8.3. The equation is **logically symmetric** and citable both ways via `using`; a `[simp]` / `[unfold]` attribute (proposal 043) picks the auto-normalizer's firing direction (only one orientation of e.g. `add(?x, 0) <=> ?x` terminates). Guards, contracts (`ensures eq(…)`), and constraints stay `=`/`:-` — they *test*, never bind.

**Bounded quantification over a collection (WI-027).** A rule-body goal may quantify over the elements of a list:

```
rule all_warm(?c)  :- coffees(?c), (forall ?x in ?c: warm(?x))
rule has_decaf(?c) :- coffees(?c), (some ?x in ?c: decaf(?x))
```

`(forall ?x in xs: P(?x))` is a finite **conjunction** — it holds iff `P` holds for every element of the list `xs` (an empty list holds vacuously). `(some ?x in xs: P(?x))` is a finite **disjunction** — it holds iff `P` holds for at least one element (an empty list fails: no witness). The binder `?x` is bound to each concrete element in turn; any other variables in the body are ordinary rule variables, shared with the surrounding clause (so `(forall ?x in xs: edge(?x, ?y))` constrains a single `?y` across all elements). This eliminates the hand-written recursive list-walking rule the same query would otherwise need.

The construct is parenthesised so its comma-separated body does not bleed into the enclosing rule-body conjunction. The collection is any term that evaluates to a ground `cons`/`nil` list (or list literal); a collection that is not yet ground when the goal is reached is carried as an undischarged residual (it is never silently decided). The binder is **not** separately scoped — it shares the enclosing clause's variable space — so it must be a **fresh** name not used elsewhere in the rule (reusing an enclosing variable as the binder captures it rather than shadowing). This is **distinct** from the unbounded hereditary-Harrop `(forall(?x), Q(?x) -: P(?x))` form (used by the auto-generated induction principles), which skolemises its binder rather than ranging over a collection.

**Multi-head (conjunctive sugar).** A rule may carry multiple comma-separated head terms — the conjunctive multi-head form. `H1, H2 :- B` (or its mirror `B -: H1, H2`) desugars at load time into N Horn clauses sharing body B; logically `body ⇒ (H1 ∧ ... ∧ Hn)`. The comma `,` always means logical conjunction in Anthill — both inside the head list and inside the body — a deliberate departure from classical CNF convention (where head-`,` would be disjunction). `;` and `|` are reserved in head position and rejected by the loader (a future proposal may introduce disjunctive heads under those tokens). `⊥` may not be mixed with positive heads.

**Z3 mapping** (rules with positive heads are *citable* via `using`; denial-shape rules with head `⊥` are not):

| Mode                         | SMT-LIB encoding                                            |
| ---------------------------- | ----------------------------------------------------------- |
| `proof X by z3(...)`         | `(assert <body>); (assert (not <head>)); (check-sat)` — `unsat` ⇒ theorem holds. For multi-head rules `head` becomes `(and H1 ... Hn)`. For denial-shape rules (head=⊥) the encoding collapses to "body unsat." |
| `proof Y using X by z3(...)` | `(assert (forall (<vars>) (=> (and <body>) <head>)))` injected into Y's preamble before Y's own assertions. |

The forall-quantification covers every free SMT variable of the lemma (the `var_<i>` synthetic names produced from the rule's de Bruijn indices). The encoding is deterministic by construction — the head is the conclusion, full stop.

**Citability.** Rules with positive heads are uniformly citable via `using`. Denial-shape rules (head = `⊥`) are **not citable**: their statement is "the body has no satisfying instance," which has no determinate conclusion to lift as `body ⇒ head`. Authors who want to cite a denial must rewrite it in positive form (state the conclusion explicitly).

**Other backends.** SLD resolution treats the head as the goal and chains through the body as in any Horn rule. The arrow direction (`:-` vs `-:`) is erased before resolution.

Rules can optionally be **named** (e.g., `non_negative:`) for reference in error messages, retractions, and documentation. Named rules with positive heads are also the citation handles for `using <Name>`.

**Rule head functors are scoped definitions.** The functor (predicate name) of a rule's head term is defined as a named symbol in the enclosing scope, just like sorts, entities, and operations. Multiple rules with the same head functor in the same scope share a single symbol. This means rule predicates participate in the namespace import system — they are visible by default and can be imported elsewhere. For example, `refines` defined inside `anthill.reflect.typing` has the qualified name `anthill.reflect.typing.refines` and is visible from other scopes via import.

### 5.4 Operation

A typed behavioral specification with contracts. Kernel-level because sorts + operations + laws = **algebra** — the foundation of the verification system. The kernel type-checks signatures and generates proof obligations from contracts.

```
Operation     ::= DescriptionBlock*
                    [Visibility] 'operation' Name [TypeParamList] '(' [ParamList] ')' '->' Type
                    ['requires' RuleBody]            -- precondition
                    ['ensures' RuleBody]             -- postcondition
                    ['effects' '(' Effect (',' Effect)* ')']
                    ['meta' MetaBlock]               -- attributes (WI-087); see §5.8, §7

TypeParamList ::= '[' TypeParam (',' TypeParam)* ']'
TypeParam     ::= Name                          -- per proposal 042
ParamList     ::= Param (',' Param)*
Param         ::= Name ':' Type
```

Parameters are **named bindings** — referenced by name (without `?`) in `requires`/`ensures` clauses. This distinguishes them from rule variables (`?x`), which are pattern-matching unification variables. `requires` clauses may reference parameter names only (precondition: checked before execution). `ensures` clauses may additionally reference `result`, which binds to the return value (postcondition: checked after execution). Using `result` in `requires` is a semantic error.

**Operation type parameters** (`[T1, T2, ...]`) declare per-call polymorphic slots scoped to a single operation invocation. They may appear in the parameter list, return type, requires/ensures, and effects positions. At a call site the bindings can be written positionally (`foo[Int64, String](args)`) or named (`foo[T1 = Int64, T2 = String](args)`), with the positional-first rule borrowed from `SortBinding` (see §5.2). Operation type parameters are **per-call** — each invocation binds them afresh — in contrast to sort-level type parameters which are pinned at sort instantiation. See `docs/proposals/042-explicit-type-parameters-on-operations.md` for the full design and `docs/design/operation-call-model.md` §"Operation type arguments" for the runtime threading through `frame.requirements`.

**Contracts** (`requires`/`ensures`) are scoped constraints — they generate denials over the operation's input/output bindings when an implementation is asserted:

```
operation deposit(a: Account, m: Money) -> Account
  requires gt(m, zero-val)
  ensures eq(balance(result), add(balance(a), m))
  effects Modify[Ledger]

operation balance(a: Account) -> Money           -- pure, no contract
```

An operation without an implementation is an **open obligation** — it emits a pheromone signal attracting implementing agents.

### 5.5 Effects

Effects are part of operation declarations, not standalone constructs. An effect declares **non-obvious behavior** — something the operation does that is not visible from its parameter list alone. Reading a parameter is not an effect; mutating it is.

Effect kinds are **open** — any `Name` or `Name[target]` pair is valid:

```
Effect ::= Name                          -- bare effect (e.g. Error)
         | Name '[' Name ']'             -- effect with target (e.g. Modify[store])
```

Currently implemented effect kinds:

| Effect kind | Meaning |
|-------------|---------|
| `Modify[target]` | Mutates a parameter — non-obvious from the signature |
| `Error` | Can fail with an untyped error |
| `Error[type]` | Can fail with a typed error |

Future effect kinds (not yet implemented in codegen):

| Effect kind | Meaning |
|-------------|---------|
| `Suspend` | May suspend and resume execution (async/coroutine) |
| `Branch` | May produce multiple results (nondeterminism, backtracking) |
| `Requires[capability]` | Needs a capability to execute |
| Concrete I/O effects | E.g. `Output[stdout]`, `Log[logger]` — ambient resources not in parameters |

**Design principle:** Effects declare what is NOT visible from parameters. If something can be passed as a parameter, it should be a parameter, not an effect. Effects exist for:
- **Mutation annotation** — `Modify[x]` tells the caller that parameter `x` will be mutated, which changes how it is passed in the host language.
- **Failure** — `Error` declares the operation can fail, which is not expressed in the parameter list or return type.
- **Control flow** — `Suspend` and `Branch` change how computation proceeds — suspension, nondeterminism.
- **Ambient resources** — operations that access state not in the parameter list, e.g. writing to stdout.

**Effect parameters on sorts.** A sort may declare an abstract effect parameter (`sort E = ?`) to express effect polymorphism. Concrete sorts bind `E` to specific effects. For example, `Stream[T, E]` declares that iterating the stream may have effect `E`; a file-backed stream would bind `E = Error`, while a pure in-memory stream leaves `E` unbound (no effects).

Users can define additional effect kinds; the kernel stores and propagates them but only interprets the well-known ones.

### 5.6 Effect Semantics (State-Passing Interpretation)

Effects give operations a precise execution semantics via a state-passing interpretation. An operation

```
operation op(x1: A1, ..., xm: Am) -> R
  effects {Modify[S], Error Err, Suspend, Branch}
```

is interpreted as a function that threads an **environment** and returns an **outcome**:

```
op_e : Env × A1 × ... × Am → Outcome(R, Env, Err)
```

The outcome type varies with the declared effects:

| Effects | Outcome type |
|---------|-------------|
| (none) — pure | `R × Env` where `Env_after = Env_before` |
| `Modify[S]` | `R × Env` (environment may change) |
| `Error Err` | `(R × Env) + Err` |
| `Branch` | `List(R × Env)` (zero or more results) |
| `Suspend` | `(R × Env) + Suspended(Env, Continuation)` |
| All combined | `List((R × Env) + Suspended(Env, K)) + Err` |

where:
- **`Env`** is a partial map from resource names (symbols) to terms representing their current state.
- **`Suspended(Env, K)`** is a paused computation — the current environment plus a continuation `K` that, when invoked, resumes execution.
- On `Branch`, the operation returns a list of results — each with its own updated environment. An empty list means failure (backtrack).
- On `Error`, the operation aborts with an error term. Errors are distinct from empty Branch (no results) — an error is an unexpected failure, empty results is a valid "no match."

An operation without effects is **pure**: it receives the environment unchanged and must return it unchanged. It cannot fail, branch, or suspend.

#### Environment and Resources

Each `Modify[target]` effect declares a **resource** — a named slot in the environment that the operation may update.

- `Modify[S]` — the operation may inspect and update `Env(S)`.
- `Error` / `Error[Err]` — the operation may abort, returning an error instead of a result.
- `Suspend` — the operation may return a suspension instead of a final result.
- `Branch` — the operation may return multiple alternative results.

#### Effect-Env Condition

An effectful operation **respects its effect-env condition** if it only modifies the resources declared in its `Modify` effects:

> For all resource names `s` not in the `Modify` set: `Env_after(s) = Env_before(s)`.

This is the fundamental correctness property: an operation's declared effects are an upper bound on what it may change. Pure operations (no effects) must preserve the entire environment.

#### Composition

Sequential composition of effectful operations threads the environment. For the basic case (Modify + Error):

```
(g ∘ f)(env, args) =
  case f(env, args) of
    Error err → Error err
    Ok (r1, env1) →
      case g(env1, [r1]) of
        Error err → Error err
        Ok (r2, env2) → Ok (r2, env2)
```

With `Branch`, composition distributes over alternatives — `g` is applied to each result of `f`, and the result lists are concatenated. With `Suspend`, composition chains the continuation — when resumed, the next operation runs on the resumed environment.

If `f` respects effects `E1` and `g` respects effects `E2`, then `g ∘ f` respects effects `E1 ∪ E2`.

#### Verification Obligations

When an `Implementation` fact links code to an operation with effects:

1. The implementation must **respect the effect-env condition** — it may only modify declared resources.
2. `requires` clauses are checked against input parameters and the pre-environment.
3. `ensures` clauses are checked against input parameters, the result, and the post-environment.

These generate proof obligations (see §8.4) that can be discharged at various trust levels.

### 5.7 Monadic Interpretation of Effects

The same effects admit an equivalent **monadic interpretation**. An operation

```
operation op(x1: A1, ..., xm: Am) -> R
  effects {Modify[S], Error Err, Suspend, Branch}
```

is interpreted as a computation in a combined monad `M_E`:

```
op_m : A1 → ... → Am → M_E(R)
```

where `M_E` layers monad transformers corresponding to declared effects:

| Effect | Monad layer | Purpose |
|--------|-------------|---------|
| `Modify[S]` | `StateT Env` | Thread mutable state |
| `Error[Err]` | `ExceptT Err` | Short-circuit on failure |
| `Suspend` | `ContT R IO` | Suspend and resume execution |
| `Branch` | `LogicT` | Produce multiple results (nondeterminism) |

The full monad is the composition: `M_E = StateT Env (ExceptT Err (LogicT (ContT R IO)))`. In practice, most operations use only a subset. An operation with only `Modify` and `Error` has `M_E(R) = Env → (R × Env) + Err`.

#### Monadic Operations

The monad provides primitive operations corresponding to each effect kind:

| Effect | Monadic primitive | Type |
|--------|-------------------|------|
| `Modify[S]` | `get_resource(S)` | `M_E(Term option)` |
| `Modify[S]` | `put_resource(S, v)` | `M_E(Unit)` |
| `Error[Err]` | `throw_error(err)` | `M_E(A)` for any `A` |
| `Suspend` | `suspend(k)` | `M_E(A)` — pause, resume via continuation `k` |
| `Branch` | `choice(a, b)` | `M_E(A)` — nondeterministic choice |
| `Branch` | `fail` | `M_E(A)` — no results (backtrack) |

Sequencing is monadic bind:

```
bind : M_E(A) → (A → M_E(B)) → M_E(B)
bind m f = λenv.
  case m env of
    Error err → Error err
    Ok (a, env') →
      case f a env' of
        Error err → Error err
        Ok (b, env'') → Ok (b, env'')
```

The monad laws hold: `bind (return x) f = f x`, `bind m return = m`, and `bind (bind m f) g = bind m (λx. bind (f x) g)`.

#### Effect Categories

Effects fall into two categories:

**State effects** — thread data through computation:
- `Modify[S]` — read and update a named resource in the environment.
- `Error[Err]` — abort with an error value. The caller can catch and handle the error.

**Control flow effects** — change how computation proceeds:
- `Suspend` — the operation may suspend and resume later. This is `async`/`await` in direct style, or the continuation monad. Enables cooperative multitasking and I/O without blocking.
- `Branch` — the operation may produce multiple results via nondeterministic choice. This is the list monad / `LogicT` in monadic style, or algebraic effect handlers with multi-shot continuations in direct style. LogicalStream encapsulates branching — consumers see a sequential stream interface.

These categories are orthogonal. An operation can be both suspending and fallible (`Suspend, Error`), or branching and stateful (`Branch, Modify[S]`). The monad stack composes the corresponding layers.

#### Equivalence of Interpretations

The state-passing interpretation (§5.6) and the monadic interpretation are **isomorphic** — conversion functions `to_monad` and `from_monad` form a round-trip in both directions. The effect-env condition is preserved by the correspondence.

The correspondence holds for all effect kinds:
- `Modify` ↔ `StateT Env`
- `Error` ↔ `ExceptT Err`
- `Branch` ↔ `LogicT` (list of alternatives ↔ nondeterminism monad)
- `Suspend` ↔ `ContT R IO` (suspended continuations ↔ continuation monad)

For the formal development of both interpretations and their equivalence proofs, see `isabelleland/kernel/Anthill_Kernel.thy`.

### 5.8 Operation Attributes (Metadata)

Operations carry structured metadata that downstream tools read — markers for
recurring codegen lowering patterns, profile/dispatch hints, and verbatim
host-language escape hatches. The vehicle is a `meta` clause carrying a
`MetaBlock` (the `[...]` shorthand from §7):

```
operation get_values(self: GPS) -> Vec3
  meta [Vec3FromConstDoublePtr3, Profile: "cpp20-stl"]

operation step(self: Robot) -> Unit
  effects Modify[self]
  meta [CppName: "step", CppBody: "self->step();"]
```

Each entry is either a **flag** (a bare `Marker`, value defaults to `⊥`) or a
**key/value** pair (`Key: term`), exactly as elsewhere a `MetaBlock` appears.
Three driving uses, all on this one mechanism:

1. **Named markers** for recurring lowering patterns (`Vec3FromConstDoublePtr3`)
   — codegen has one handler per marker, reusable across many operations.
2. **Verbatim host body** escape hatch (`CppBody: "..."`) for ad-hoc glue.
3. **Profile / dispatch hints** (`Profile: "cpp20-stl"`, `CppName: "..."`).

**Why the `meta` keyword.** Unlike facts and rules — which take a *bare* trailing
`[...]` — an operation needs the leading `meta` keyword. A bare `[...]` placed
right after the return type is otherwise grabbed as return-type application
arguments (`-> Vec3[...]`), which is exactly the clauseless getter shape that
most needs markers. The keyword disambiguates, and the clause composes with
`effects` / `requires` / `ensures` and works when no other clause is present.

**Representation.** The block lowers to a `meta(key: value, ...)` term (the same
shape as fact/rule metadata) carried as the `meta` field of the operation's
`OperationInfo` reflection fact. Consumers read it via the kernel helpers
`meta_has_flag` (flag presence) and `meta_value` (a key's value); an operation
with no `meta` clause carries an empty `meta()` (reported as "no attributes").

## 6. Syntactic Sugar

Readable shorthand that desugars to kernel constructs. The reasoning engine only sees rules and sorts.

### 6.1 Fact (bodyless rule)

A ground assertion — the most common way to add knowledge to the KB.

```
Fact ::= DescriptionBlock*
           'fact' Term
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
Constraint ::= DescriptionBlock*
                 'constraint' [Name ':'] Invariant [':-' Guard]
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
Entity ::= DescriptionBlock*
             [Visibility] 'entity' Name ['(' FieldList ')']
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
                     ['meta' MetaBlock]               -- attributes (WI-087); see §5.8

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
  add_comm:  add(?a, ?b) <=> add(?b, ?a)
  add_assoc: add(add(?a, ?b), ?c) <=> add(?a, add(?b, ?c))
}
→  rule add_comm:  add(?a, ?b) <=> add(?b, ?a)
   rule add_assoc: add(add(?a, ?b), ?c) <=> add(?a, add(?b, ?c))
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

### 6.6 Infix and Prefix Operators

Operators are sugar for `Fn` terms. The tree-sitter grammar parses them as flat chains; a Pratt resolver in the converter applies precedence and associativity to produce nested `Fn` calls. Adding a new symbolic operator requires only a dictionary entry — no grammar change.

**Operator tokens.** Any sequence of the characters `+`, `-`, `*`, `/`, `%`, `^`, `|`, `&`, `=`, `<`, `>`, `~` is a valid operator symbol. The character `!` is excluded from operator symbols and reserved as a prefix-only token; `!=` is an explicit two-character infix token. The unification operator `<=>` is a single token lexed **greedy-longest before `<=`** (proposal 049): `a <= b` is `lte`, `a <=> b` is `unify`. Likewise `===` (structural identity, proposal 051) is a single token lexed greedy-longest before `=`: `a = b` is the semantic `eq`, `a === b` is `struct_eq`.

**Infix operators** appear between terms:

| Operator | Priority | Assoc | Functor | Origin |
|----------|----------|-------|---------|--------|
| `\|` | 1 | Left | `or` | `Bool` |
| `or` | 1 | Left | `or` | `Bool` (word form) |
| `&` | 2 | Left | `and` | `Bool` |
| `and` | 2 | Left | `and` | `Bool` (word form) |
| `=` | 3 | None | `eq` | `Eq` (semantic equality **test**, dispatched) |
| `!=` | 3 | None | `neq` | `Eq` |
| `===` | 3 | None | `struct_eq` | `anthill.kernel` (structural identity **test**) |
| `<=>` | 3 | None | `unify` | `anthill.kernel` (structural **unification**) |
| `<` | 4 | None | `lt` | `Ordered` |
| `<=` | 4 | None | `lte` | `Ordered` |
| `>` | 4 | None | `gt` | `Ordered` |
| `>=` | 4 | None | `gte` | `Ordered` |
| `+` | 5 | Left | `add` | `Numeric` |
| `-` | 5 | Left | `sub` | `Numeric` |
| `*` | 6 | Left | `mul` | `Numeric` |
| `/` | 6 | Left | `div` | `Numeric` |
| `%` | 6 | Left | `mod` | `Numeric` |
| `mod` | 6 | Left | `mod` | `Numeric` (word form) |
| `div` | 6 | Left | `div` | `Numeric` (word form) |
| `^` | 7 | Right | `pow` | `Numeric` |
| `->` | 8 | Right | `arrow` | type arrows |
| `.` | 10 | Left | `field_access` | `anthill.reflect` |

Higher priority binds tighter: `a + b * c` desugars to `add(a, mul(b, c))`. Left-associative: `a + b + c` desugars to `add(add(a, b), c)`. Right-associative: `a ^ b ^ c` desugars to `pow(a, pow(b, c))`. None-associative: `a = b = c` is an error.

**Ternary operator.** The `->` operator has an optional continuation with `@` for effect annotation:

```
?a -> ?b               →  arrow(?a, ?b)
?a -> ?b @ ?c          →  arrow_effect(?a, ?b, ?c)
```

**Prefix operators** appear before a term:

| Operator | Priority | Functor | Origin |
|----------|----------|---------|--------|
| `!` | 9 | `not` | `Bool` (value) / `anthill.reflect` (NAF) |
| `not` | 9 | `not` | `Bool` (value) / `anthill.reflect` (NAF) |

Prefix binds tighter than all infix operators: `!?a + ?b` desugars to `add(not(?a), ?b)`.

**Boolean operators are position-directed** (WI-529). `not`, `or`, and `and` each name a dispatched **value** operation on `Bool` (`Bool.not` / `Bool.or` / `Bool.and`) inside an **operation body** (evaluated), but a **goal** form in a **rule body** (resolved): `not(goal)` is negation-as-failure (`anthill.reflect.not`), `or(g1, g2)` is disjunction (`anthill.kernel.or`), and goal conjunction is the comma (there is no `kernel.and`). Resolution is by syntactic position, not by a distinct glyph or operand type. Negation of a numeric value is written `neg(x)` → `Numeric.neg` (a defaulted spec op, `neg(?a) <=> sub(zero-val, ?a)`); negative literals (`-1`, `-0.45`) are lexed directly. A prefix `-` *operator* on non-literal expressions is not provided (it would collide with negative-literal lexing — WI-529).

**Desugaring examples:**

```
?a + ?b * ?c        →  add(?a, mul(?b, ?c))
!?a + ?b            →  add(not(?a), ?b)
?a | ?b & ?c        →  or(?a, and(?b, ?c))
?a != ?b            →  neq(?a, ?b)
?a -> ?b @ ?c       →  arrow_effect(?a, ?b, ?c)
?a ^ ?b ^ ?c        →  pow(?a, pow(?b, ?c))
```

**Extensibility.** The operator dictionary is currently hardcoded. A future phase will allow sorts to declare operators via meta annotations (e.g. `[infix: "+"]` on `Numeric.add`), extending the dictionary at load time.

### 6.7 Field Access (Dot Projection)

**Syntax:** `term.identifier` — dot projection for field/component access. Desugars to `field_access(term, identifier)`, a 2-arg `Fn` term, following the same pattern as `a + b` → `add(a, b)`.

```
?x.y             →  field_access(?x, y)
?x.y.z           →  field_access(field_access(?x, y), z)
f(?a.b, ?c)      →  f(field_access(?a, b), ?c)
```

**Precedence.** `.` has the highest precedence (10), above all other operators including prefix `!` (9). Left-associative: `a.b.c` desugars to `field_access(field_access(a, b), c)`.

**Three dispatch modes** (runtime):

1. **Entity field access:** if the object is a `Fn` term whose functor is a registered entity constructor, extract the named field from the entity's arguments. E.g., `env(fs: ?fs).fs` extracts `?fs`.

2. **Sort component access:** if the object is a `Fn` term whose functor is a sort symbol, look up the field identifier in the sort's scope. E.g., `Monoid().Carrier` resolves to the `Carrier` sub-sort.

3. **Named-tuple component access** (WI-638): if the object types as a **named tuple** (its functor is `named_tuple`, so the receiver sort is `None` and modes 1–2 never reach it), resolve the identifier against the tuple's `(name, type)` components — by short name (`t.x`) or by positional `_N` (`t._1`, 1-based, since positional tuples desugar to `_N` names). Access is name-keyed on both the type and the runtime `Value::Tuple`, hence **order-independent**. E.g., `(x: 10, y: 20).x` evaluates to `10`; `t.x` on a param typed `(x: Int64, y: Int64)` type-checks and evaluates.

**Disambiguation from qualified names.** At parse time, `a.b` in term position is parsed as `field_access(a, b)` — a variable or identifier followed by `.identifier`. Qualified names (`Namespace.Sort`) continue to be parsed as `name` nodes within `fn_term` and `instantiation_term`, which require `(...)` or `{...}` to follow the name. There is no ambiguity: `A.B(x)` parses as `fn_term(name: A.B, args: [x])`, while `A.B` alone in term position parses as `field_access(A, B)`.

**Well-formedness rules:**
- `t.f` requires `t` to have a known sort `S` with an entity that has field `f`
- Single-constructor sorts: field lookup is unambiguous
- Multi-constructor sorts: field `f` must appear in all constructors with the same sort
- Abstract sorts (`sort T = ?`): field access is ill-formed (no fields)
- Named tuples (mode 3): `t.f` requires `f` to be a component name of `t`'s named-tuple type, or a positional `_N` within its arity

## 7. Metadata

Every fact in the KB carries metadata. `Meta` is an **entity** in the `anthill.prelude` namespace — not a special grammar production. It is a regular Fn term with named arguments.

> **Canonical source:** `stdlib/anthill/prelude/meta.anthill`

```
namespace anthill.prelude.Meta
  import anthill.prelude.Option

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
    entity tested(n: Int64)                -- passed n test runs (Hypothesis, sbt-test)
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
| `iteration` | `Int64` | Tracks project evolution |
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

- **Unspecified sorts** (`sort T = ?` inside a sort body) introduce type parameters without representation. Can appear in operation signatures and fields within the enclosing sort, but have no constructors until a carrier binding is provided.
- **Type aliases** (`sort Money = Int64`) introduce a name equivalent to an existing type. The alias is interchangeable with the aliased type.
- **Sorts with constructors** (`sort S { entity C₁(...), entity C₂(...) }`) introduce closed algebraic data types. All constructors are enumerated; pattern matching in rules is exhaustive.
- **Operations** have typed signatures: `operation op(x: A, y: B) -> C`. Parameters are named bindings; the kernel type-checks that actual arguments match declared types.
- **Terms** are typed: `Const` carries its type, `Var` declares its type, `Fn` has the type of its sort's constructor, `Ref` refers to a named type.

**Expansion during unification.** A parametric sort referenced as a type with some or all of its declared parameters unbound unifies as that sort applied to a **fresh variable for each unbound parameter**. A bare reference is the all-unbound case — `Stream` ≡ `Stream[T = ?, E = ?]` — and a partial one fills the rest — `Stream[T = Int64]` ≡ `Stream[T = Int64, E = ?]`. The typer performs this expansion at **every sort application** — wherever a parametric sort appears as a type, including a bare reference unified against another bare reference — so the parameters participate even when the source writes no binding for them. The expansion covers **every** declared parameter: ordinary type parameters and effect-row parameters (`effects E`; proposal 045 §2) alike. It is the type-level counterpart of the partial-entity-pattern expansion (§8.3), and follows directly from "types are terms" (§4.4) — the same generalize-missing-arguments-to-fresh-variables mechanism, applied to the type sublanguage. Its effect is that a signature written against a bare sort still threads bindings: a parameter declared `s: Stream`, unified against an argument of type `Stream[T = Int64, E = {}]`, binds the expanded `T` and `E`, so both the element type and the access effect ground at the call instead of silently dropping. Without it, a bare `Ref(Stream)` carries no slots and unification binds nothing. In **type position** a bare parametric sort name is always an instantiation, so — unlike entity *data* terms, where bare `account` stays a reference and only `account()` expands — no parentheses are needed to trigger it. A *cross-sort* case, where the argument's sort merely *provides* the expected spec (a `List` used as a `Stream`), is the complementary mechanism: provider admissibility (§8.2) supplies the parameter bindings from the provider fact. See proposal 045 §5.1.1 for the effect-row instance and `docs/proposals/library/002` for the `Stream`/`iterator` walk.

### 8.2 Entity Subtyping

Constructors (entities) of a sort are subtypes of that sort. If `sort S { entity C₁(...), entity C₂(...) }`, then `C₁ <: S` and `C₂ <: S`. A term classified as sort `C₁` is also of sort `S`.

This relationship is **always 1-level** (entity → parent sort, non-transitive). When an entity is declared inside a sort body, the loader emits an `EntityOf(entity, parent)` fact in the KB. This is the only source of entity subtyping.

- Each constructor name is a sort in its own right.
- The `EntityOf` relationship is registered when a sort with entity constructors is declared.
- Entity subtyping is **1-level only**: if `C <: S`, that's because `C` is declared directly inside `S`. There are no multi-level entity chains.
- Querying by sort `S` returns facts of sort `S` and all entities of `S`.

```
sort Color {
  entity red
  entity green
  entity blue
}

-- This establishes (as EntityOf facts in the KB):
--   EntityOf(red, Color)
--   EntityOf(green, Color)
--   EntityOf(blue, Color)
-- A query for sort Color matches terms of sort red, green, and blue.
```

Entity subtyping does **not** arise from nesting. A sort `T` declared inside a namespace or sort body is a **parameter**, not an entity. Only the constructor-of relationship creates entity subtyping.

Spec refinement (`requires` chains) is a separate relationship handled by `refines()` rules in `stdlib/anthill/reflect/typing.anthill`. Provider admissibility — a value whose sort *provides* a spec (`fact S[carrier]`) is usable where that spec is expected — is the demand/supply twin of refinement, handled by the sibling `provides()` rule in the same file. (`requires X` and `fact X[Y]` are the two ends of one relation: a position demanding the spec is discharged by the supplying fact.)

### 8.3 Rule Evaluation

The kernel's reasoning engine supports:

**Forward chaining (bottom-up):** When a new fact is asserted, the engine checks all rules whose body might be newly satisfiable. If a rule's body is fully satisfied, its head is derived as a new fact.

**Backward chaining (top-down):** Given a query `?- goal`, the engine searches for rules whose head unifies with the goal, then recursively proves the body terms.

**Unification:** Standard first-order unification. `Var` terms unify with any term of the same type. `Fn` terms unify if their names match and all arguments unify pairwise. Its user-facing surface operator is `<=>` (see below).

**Equality: test vs. bind, structural vs. semantic** (proposals 049 + 051). Equality-shaped notions differ on two axes — *test* (compare, never bind) vs. *bind* (unify), and *structural* (raw term structure) vs. *semantic* (the carrier's `Eq` instance) — and the language gives each cell its own operator:

|                | test (no binding)  | bind (unify) |
|----------------|--------------------|--------------|
| **structural** | `===` (`struct_eq`) | `<=>` (`unify`) |
| **semantic**   | `=` / `eq`         | E-unification *(future engine)* |

- **`=` — the semantic equality *test*** (`Eq.eq`, a dispatched operation returning `Bool`). It reduces both operands and compares them **through the carrier's `Eq` instance** (WI-616): structurally identical operands are equal by reflexivity, and structurally distinct operands dispatch to the carrier sort's own `eq` override when it declares one — `Set` and `Map` are the first non-structural instances (`eq({1,2}, {2,1})` holds: membership equality, resolved against the carrier's rules by ordinary SLD). A carrier with no override keeps the structural compare — structural equality *is* its instance (`Int` stays a machine compare). `=` **never binds** a logical variable: `eq(7, ?p.x)` succeeds once `?p.x` reduces, but `eq(?v, ?p.x)` does **not** bind `?v` (a flex `=` that is never discharged is carried as an undischarged residual, not counted as a solution — WI-519). Use `=` for body-goal tests, operation contracts (`ensures eq(balance(result), …)`), and constraints — a postcondition must *test*, never bind. `neq` (`!=`) pairs with it: `neq(a,b) <=> not(eq(a,b))`, the negation of the *dispatched* equality.
- **`===` — the structural identity *test*** (`anthill.kernel.struct_eq`, a resolver builtin; WI-615). Total, carrier-agnostic, **never dispatches**, and needs **no `Eq` instance**: it answers "are these two values literally the same structure" for every value (opaque handles compare by identity). Two membership-equal sets in different spellings are `=` but not `===`. Use it for term/symbol/reflected-structure identity — comparisons that must not suddenly depend on a carrier's custom equality.
- **`<=>` — structural *unification*** (`anthill.kernel.unify`, a resolver primitive). It binds via a substitution effect on the resolver frame: `?v <=> ?p.x` binds `?v` to the projected value; `some(?x) <=> some(3)` binds `?x ↦ 3`. It is **occurs-checked** (`?v <=> f(?v)` is a loud failure, never a cyclic term), **symmetric** (either side may be the variable side), and **structural-only — it never dispatches**. It is the connective of equational rule heads (§5.3) and the substrate of `let`.

**Declaring a non-structural `Eq` instance.** A carrier declares the instance with `provides Eq[T = <Carrier>]` and supplies its own operation short-named `eq` (the same short-name override convention as every spec-op dispatch), backed by relational rules — see `Set.eq` / `Map.eq` in the prelude. Dispatch reads the operand's head at resolution and proves the carrier's `eq` in a closed sub-proof, three-way honest:

- Only **fully ground** operand pairs dispatch — `=` never binds, so a compare containing an unbound variable *suspends* (undecided) rather than proving-by-binding or deciding structurally.
- An overriding carrier **buried** inside non-overriding structure (`some({1,2})` vs `some({2,1})`) also suspends: a structural verdict would ignore the inner instance.
- The sub-proof is bounded; a compare too large for the budget degrades to *undecided*, never to a wrong verdict.
- Caveats: write relational base cases with a **body** or on a helper op — a bodyless 2-ary rule whose head is short-named `eq` is currently classified as an equational law and never fires at resolution (WI-627). Supply `eq` only: `neq`/`!=` is always derived as the negation of the dispatched `eq`, so an own `neq` member is never consulted. And the instance dispatches at **SLD resolution** — an *evaluated* operation body reaches it through the typeclass dispatch machinery, while the interpreter's raw `eq` fallback is still the structural compare pending the SLD→eval bridge (WI-625).

**`let ?v = expr`** is directed sugar for **`?v <=> expr`** — one primitive, two surfaces: `<=>` for symmetric equations, `let` for introducing a named binding in a goal sequence. (`:=` is *not* this — it is reserved for the mutable-cell `Cell.set`, `c := v`, which overwrites state rather than binding a logical variable once.)

**Negation.** Because `=` never binds, `not(eq(…))` is always safe. A `<=>` under `not` needs a **static allowedness** check: any variable occurring in a `<=>` under negation must be bound by an earlier positive goal, or the loader raises a load-time error (WI-525).

**Partial entity patterns:** When an entity term appears with fewer named arguments than the entity declares, the missing fields are automatically generalized to fresh anonymous variables. This means `account(owner: "Alice")` is equivalent to `account(id: ?, owner: "Alice", balance: ?)`, and `account()` is equivalent to `account(id: ?, owner: ?, balance: ?)`. The expansion applies whenever the functor is a registered entity — including the zero-argument case, where parentheses signal pattern-matching intent (bare `account` without parens remains a reference to the entity/sort). This convention avoids requiring the user to explicitly list unneeded fields with `?`. (Its type-level counterpart — fresh variables for the unbound *parameters* of a parametric sort used as a type — is **expansion during unification**, §8.1.)

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

### 8.6 Name Resolution and Visibility

This section is the canonical description of how a name resolves to a symbol.
Both implementations (`rustland`, `scaland`) follow this single algorithm. (See
[proposal 044](proposals/044-unified-name-resolution.md) for rationale and
migration. The registration of unlabeled-rule *head functors* as dispatchable
symbols is a separate, implementation-specific concern and is **not** part of
name resolution.)

**Symbols and scopes.** Every defined symbol has a `short_name` (last segment)
and a `qualified_name` (full path); the global `by_qualified_name` index maps
the latter to the unique symbol. Each scope holds:

- **locals** — names defined directly in the scope;
- **imports** — local aliases introduced by `import`;
- **exposed** — the scope's entity-variant names (see *variant exposure*);
- **parents** — included scopes, each flagged *enclosing* (the lexical
  sort/namespace body it sits in) or *non-enclosing* (`requires`, wildcard
  `import`, variant exposure);
- **type parameters** — `sort T = ?` names, which do not leak to parents.

**Visibility model.** A name is **visible by default**, across namespace and
sort boundaries, to importers and requirers. The modifiers adjust this:

- **`internal`** — hides the name from cross-scope resolution (it remains
  resolvable within its own scope). This is the only hide gate.
- **`public`** — visible everywhere, including without an `import`.

The former `export` statement and `export` visibility prefix (no-ops under this
model) were removed in WI-291.

**`resolve_in_scope(name, scope)`** — the resolution order:

1. a **local** of `scope` → resolved (a local shadows everything below);
2. an **imported alias** in `scope` → resolved;
3. otherwise recurse into the **parent** scopes. A *non-enclosing* parent is
   skipped when the name is (a) a type parameter of that parent, (b) marked
   `internal` there, or (c) absent from a non-empty **exposed** set of that
   parent (variant exposure, below). *Enclosing* parents are never filtered;
4. collect and de-duplicate by symbol: zero matches → unresolved, one →
   resolved, two or more distinct symbols → **ambiguous** (a load/query error).

**Import forms.** `import` introduces visibility into the current scope; it does
not by itself add a sort's contents (use `requires` or wildcard for that):

- `import a.b.C` — alias `C`, and include `a.b` as a non-enclosing parent.
- `import a.b.{C, D}` — alias each name, resolved by: direct `a.b.C`
  qualified lookup, then `resolve_in_scope(C, a.b)`, then a one-level nested
  lookup (`a.b.<segment>.C`, taken only if unique) so an entity declared inside
  a sort/enum of `a.b` is importable by its short name.
- `import a.b.*` — include `a.b` as a non-enclosing parent (every visible name).

**Variant exposure.** A sort that declares entity constructors exposes **only
those constructor (variant) names** to its enclosing scope, by linking its
scope as a non-enclosing parent whose `exposed` set is exactly the variant
names. So bare `Open` resolves to `WorkStatus.Open`, while the sort's
*operations* never leak as bare names (they are reached via `Sort.op`,
`requires`, or wildcard). Two sorts exposing the same variant name make that
bare name **ambiguous** rather than letting one silently win.

**Inherited operations.** When a sort gains an operation through `requires`
(spec auto-binding, §8.7), a derived rule it supplies for that operation binds
to the **inherited** operation symbol — it does not mint a new shadowing symbol.
So `Ordered`'s `eq` law contributes to `Eq.eq`, and a scope that reaches both
resolves `eq` to a single symbol, not an ambiguity.

Visibility is enforced during resolution (load/assert) and at query time.

### 8.7 Algebras

An algebra is not a separate syntactic construct — it is the **typing structure that emerges** from declarations within a sort body:

- **Unspecified sub-sorts** (`sort T = ?` inside a sort body) define the type parameters of the algebra.
- **Entity constructors** define concrete inhabitants (ADT variants).
- **Operations** define typed behaviors with contracts.
- **Rules** (including constraint sugar) express laws.

A sort-with-body that contains unspecified sub-sorts, operations, and laws IS an algebra. When an `Implementation` fact provides carrier bindings (`carrier: { Scalar = float, Vector = CudaDeviceBuffer[float] }`), it instantiates the algebra for a specific host language.

**Parametric structure:** Unspecified sorts inside a sort body serve as type parameters. A sort with unspecified sub-sort `T` is a parametric module — instantiated via inline type expressions `List[T = Int64]`. For example, `anthill.prelude.List` has unspecified sub-sort `T`; using `List[T = Int64]` inline produces a list-of-integers.

This also supports type class-like patterns: a sort declaring `sort A = ?` and `operation combine(x: A, y: A) -> A` with laws is a specification that any type with a `combine` operation must satisfy. Using `MyType` in place of `A` via inline binding instantiates the specification for a concrete type.

**Spec satisfaction:** To declare that a concrete type satisfies a parametric spec, assert the instantiation as a fact:

```
-- Int64 satisfies Eq, Ordered, and Numeric
fact Eq[T = Int64]
fact Ordered[T = Int64]
fact Numeric[T = Int64]
```

For built-in types, the operations are primitive (provided by the runtime). For user-defined types, rules define the operations:

```
fact Eq[T = Color]
rule eq(red, red) <=> true
rule eq(green, green) <=> true
rule eq(blue, blue) <=> true
rule eq(?_, ?_) <=> false
```

Since facts are scoped to namespaces, different namespaces can provide different instantiations of the same spec for the same type (e.g. different orderings). A consumer chooses which instantiation to use via `import`.

**Instance coherence.** Instance selection is scoped, not global. Within a single scope a spec has at most one provider for a given carrier — two is an ambiguity error (the coherence rule in `docs/design/spec-instance-dispatch.md`) — while different scopes may resolve the same `Spec[carrier]` to different providers, the per-`import` choice noted above. A sort's *embedded* requirements — the providers that fill its `requires` slots — are resolved in **that sort's** scope and captured when its instance is constructed, so `Spec[carrier]` behaves consistently within any one instance. Coherence is therefore lexical and per-scope: two routes to `A[X]` resolved in the same scope agree by construction, but a diamond whose arms captured providers from different scopes may observe different `A[X]` behavior. This is permitted — keeping `A[X]` canonical is a matter of resolving it in one scope (or using distinct carriers), not a guarantee the kernel enforces globally.

**Operation coherence across *different* specs.** The ambiguity rule above is about two providers of the *same* spec for one carrier. A distinct question is when a carrier provides several *different* specs that each define an operation of the same short name (e.g. a `List` provides both `FiniteCollection`, which defines a finite `map`, and — transitively — `Iterable`, which defines a lazy `map`). The kernel resolves this in two stages (`find_spec_op_for_provided_sort`):

1. **Provision-graph distance (primary).** It walks the carrier's provided specs breadth-first, *directly*-provided specs ahead of *transitively*-provided ones, and keeps the definers at the **nearest** distance. A `List` provides `FiniteCollection` directly (depth 1), so `FiniteCollection.map` beats `Iterable.map` (depth 2, via `Stream`) outright.

2. **`requires`-refinement (tie-break).** When two or more definers sit at the *same* nearest distance, the one that (transitively) `requires` all the others wins — a spec that requires another is its *refinement*, hence more specific. A `Map` provides `Iterable` **and** `FiniteCollection` *both directly* (a `Map` is not a `Stream`, so it cannot reach `Iterable` transitively the way a `List` does); the tie breaks toward `FiniteCollection` because `FiniteCollection requires Iterable`, so `Map.map`/`filter` are the finite ones too.

A tie with no single most-refined definer is a genuine ambiguity (resolution falls back to first-match and should be avoided — give one a distinct path or name). To deliberately invoke a non-winning op, qualify the call (`Iterable.map(xs, f)`).

**Operation auto-binding.** Operations in parametric sorts are implicitly parameterized — like type parameters (`sort T = ?`), they are logical variables bound at instantiation. When a sort satisfies a spec via `fact S[T]`, operations with matching names and compatible signatures are **automatically unified** — no explicit binding needed.

The binding gradient:

```
-- Full auto-binding: T=T and all same-named operations unified
fact Monoid

-- Explicit type, auto-bind operations (preferred style)
fact Monoid[T]

-- Explicit rename when names differ
fact Monoid[T, combine = add]
```

When `fact S[T]` appears inside a sort body, it means both spec satisfaction AND operation inheritance: the sort gains all operations defined in the spec. Derived operations (defined by rules in the spec) carry over automatically; the satisfying sort only provides the primitive operations. For example, if `Stream` defines `head` as a derived rule from `splitFirst`, a sort declaring `fact Stream[T]` inherits `head` without redeclaring it.

**Operation override.** A satisfying sort may **redefine** an operation the spec already supplies (a derived rule, or a defaulted operation); its own definition then wins for that carrier. Override is carrier-driven — a call resolves to the carrier's own operation when it has one, otherwise to the spec's. This is the `provides`/`fact` direction. A sort that merely `requires` a spec and happens to declare an operation of the same name is **not** overriding it: that operation is unrelated, and declaring it is reported as a warning that it shadows the required name. An overriding operation must **refine** the spec's contract — its effect row stays within the spec's, and its `requires`/`ensures` are no stronger / no weaker respectively (the effect check is described in `docs/design/spec-instance-dispatch.md`; the `requires`/`ensures` check is a planned follow-up).

Note: namespace-level `fact Eq[T = Int64]` (standalone, not inside a sort body) does NOT trigger auto-binding of operations — operations there are standalone rules associated with the fact.

**Namespaces** group sorts, operations, and rules for encapsulation and visibility control, but do not introduce type parameters. A namespace may contain sorts (both parametric and concrete) and type aliases, but unspecified sorts (`sort T = ?`) appear only inside sort bodies as type parameters — never directly in a namespace.

### 8.8 Persistence and Store-Aware Resolution

The KB is not purely in-memory. Facts can be backed by **persistent stores** — filesystem directories, SQL databases, or other external backends. The persistence model is defined as an abstract algebra in `anthill.persistence` (see [proposal 007](proposals/007-persistence-layer.md) for the full design).

**Store capabilities** determine how the reasoning engine interacts with each store:

- **`bulk`** stores (e.g., filesystem) — all facts are loaded into memory at startup via `pull()`. Backward chaining works entirely in-KB. The `.anthill/` directory with its `workitems/`, `tools/`, and `facts/` subdirectories is a bulk store.

- **`queryable`** stores (e.g., PostgreSQL) — patterns are translated to native queries on demand. During backward chaining, when the engine encounters a goal whose sort is routed to a queryable store, it calls `retrieve(store, pattern)` instead of searching in-memory facts. The store acts as an **external oracle** — a well-known pattern in logic programming (Datalog with external data sources, Prolog foreign predicates).

**Routing** maps fact sorts to stores via ordinary rules:

```
rule route(WorkItem(?))  <=> FileStore(".anthill", stage0)
rule route(AuditEntry(?)) <=> SqlStore("postgresql://...", "anthill", Postgresql)
rule route(?)             <=> FileStore(".anthill", stage0)   -- default
```

**Bootstrap.** Store configuration is itself expressed as KB facts, creating a chicken-and-egg problem. The solution: `project.anthill` at a well-known filesystem path is always loaded first (the bootstrap store). It declares other stores and routing rules. Those stores are then pulled or registered as oracles.

The reasoning engine is store-agnostic: it sees facts, some from memory (bulk stores), some fetched on demand (queryable stores). Rules, constraints, and backward chaining work uniformly across both.

## 9. Connections to Existing Systems

The kernel language connects to three traditions:

**ML-style modules.** A sort-with-body (containing unspecified sub-sorts and operations) ≈ signature (declares abstract types and operations), Implementation with carrier bindings ≈ structure (provides concrete types), inline `Name[bindings]` ≈ functor application. But anthill sorts are richer — they contain rules (logic) and contracts (requires/ensures), making them algebraic specifications rather than pure type signatures. Namespaces provide encapsulation and visibility control (like ML structures), but type parameters live in sort bodies, not namespaces.

**Maude / OBJ / CafeOBJ.** The closest match:

| Kernel language | Maude |
|----------------|-------|
| `namespace` | theory (`fth`) or module (`fmod`) |
| `sort T = ?` (unspecified) | `sort` |
| `sort S { entity ... }` | sort with constructor ops (`op ... : -> S [ctor]`) |
| `operation` | `op` (operator declaration) |
| `rule` (derivation) | equation (`eq`) or rewrite rule (`rl`) |
| `constraint` (denial) | membership axiom / conditional axiom |
| `Implementation.carrier` | view (maps theory sorts to module sorts) |
| `List[T = X]` (inline instantiation) | view instantiation (binds sort parameter) |
| sort with unspecified sub-sort | parameterized module (`fmod X{Y :: TRIV}`) |

The anthill adds: description blocks (partial formalization as KB facts), metadata (trust, provenance, agent), host-language embeddings (bidirectional mapping to Scala/Python/etc.), and the stigmergic agent layer.

**Proof assistants (Lean, Coq, Isabelle).** The kernel/tactic split: the kernel (small, trusted) checks proofs; tactics (large, untrusted) find proofs. In the anthill: the kernel grammar verifies, agents construct. The `trust` level on facts plays the role of Lean's `axiom` vs `theorem` distinction.

## 10. Examples

### 10.1 Banking Algebra

A complete algebra with type parameters, operations, contracts, and laws. Because the algebra is parametric over `Money` (an unspecified sort whose carrier is provided by an implementation), it uses `sort` — not `namespace` — as the enclosing construct:

```
sort banking
  sort Money = ?                                     -- type parameter (unspecified)
  requires Numeric[T = Money]                        -- gives us +, -, >, >=, = for Money

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
  sort Money = ?
  requires Numeric[T = Money]

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
  sort Scalar = ?                                    -- type parameter (unspecified)
  sort Vector = ?                                    -- type parameter (unspecified)

  operation {
    dim(v: Vector) -> Int64
    add(a: Vector, b: Vector) -> Vector
      requires dim(a) = dim(b)
      ensures dim(result) = dim(a)
    scale(s: Scalar, v: Vector) -> Vector
      ensures dim(result) = dim(v)
    dot(a: Vector, b: Vector) -> Scalar
      requires dim(a) = dim(b)
  }

  rule {
    add_comm: add(?a, ?b) <=> add(?b, ?a)
    add_assoc: add(add(?a, ?b), ?c) <=> add(?a, add(?b, ?c))
    scale_distrib: scale(?s, add(?a, ?b)) <=> add(scale(?s, ?a), scale(?s, ?b))
  }
end
```

Multiple implementations (in the `anthill.realization` standard namespace, see `stdlib/anthill/realization/`) can provide different carrier bindings. The `profile` field distinguishes them:

```
-- Rust std implementation:
fact Implementation("linear_algebra",
  artifact: "src/linalg/cpu.rs", language: "rust",
  profile: "std",
  description: "CPU-based linear algebra using std Vec",
  carrier: { Scalar: "f64", Vector: "Vec<f64>" },
  namespace_map: { "anthill.prelude.List": "std::vec::Vec" })
  [trust: proposed]

-- Rust no_std implementation (embedded):
fact Implementation("linear_algebra",
  artifact: "src/linalg/embedded.rs", language: "rust",
  profile: "no_std",
  description: "Fixed-size linear algebra for embedded targets",
  carrier: { Scalar: "f32", Vector: "heapless::Vec<f32, 64>" },
  namespace_map: { "anthill.prelude.List": "heapless::Vec" })
  [trust: proposed]

-- Python GPU implementation:
fact Implementation("linear_algebra",
  artifact: "src/linalg/cuda.py", language: "python",
  profile: "gpu",
  carrier: { Scalar: "float32", Vector: "CudaDeviceBuffer[float32]" })
  [trust: proposed]
```

**Profile compatibility:** When assembling a build, all selected implementations must share a compatible profile. For example, in Rust `no_std` targets, every component must use `no_std`-compatible implementations — mixing `std` and `no_std` profiles is an error. This is a build-time constraint analogous to feature unification in Cargo.

### 10.3 Namespace with Nested Sub-namespaces

```
namespace finance
  import banking.{Account, Money}

  namespace risk {
    sort RiskLevel {                              -- defined sort (not unspecified)
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
DurationLit      ::= IntLit ('ms' | 's' | 'm' | 'h' | 'd')            -- 5m → Duration(5, "m")
CollectionLit    ::= '[' ']'                                            -- [] → ListLiteral()
                   | '[' Term (',' Term)* ('|' Term)? ']'               -- [a,b] → ListLiteral(a,b)
SetLit           ::= '{' Term? (',' Term)* '}'                          -- {a,b} → SetLiteral(a,b)

Body[F]     ::= '{' F '}'  |  F 'end'

-- =================================================================
-- Terms
-- =================================================================

Term        ::= AtomTerm
              | InfixTerm

AtomTerm    ::= Const(type, value)
              | VariableTerm                 -- variable with optional description
              | Fn(name, args: [Term])
              | Ref(Name)
              | Instantiation(Name, SortBinding+)  -- Eq[T = Int64] in term position
              | CollectionLit                -- [a, b] → ListLiteral(a, b)
              | SetLit                       -- {a, b} → SetLiteral(a, b)
              | TupleLiteral                 -- (a, b) → TupleLiteral(_1: a, _2: b)
              | PrefixTerm
              | Quoted(language, source)

VariableTerm ::= Var                          -- bare variable: ? or ?name
               | Var DescriptionBlock+ '?'    -- with description(s): ?name {< text >}+ ?

-- Operators: flat parse → Pratt desugaring → nested Fn terms (see §6.6)
OperatorSym ::= [+\-*/%^|&=<>~]+            -- any sequence of operator chars (no !)
InfixOp     ::= OperatorSym | '!='
              | '@'
              | 'or' | 'and' | 'mod' | 'div'
PrefixOp    ::= '!' | 'not'

InfixTerm   ::= AtomTerm (InfixOp AtomTerm)+   -- desugars via Pratt to nested Fn
PrefixTerm  ::= PrefixOp AtomTerm               -- desugars to Fn(functor, [operand])

-- =================================================================
-- Kernel Constructs (4)
-- =================================================================

Namespace   ::= DescriptionBlock*
                'namespace' Name
                Body[NamespaceContent*]

Import      ::= 'import' ImportPath
ImportPath  ::= Name                                           -- import a name
              | Name '.' '{' NameList '}'                      -- selective import
              | Name '.' '*'                                   -- wildcard import
NameList    ::= Name (',' Name)*
SortBinding ::= Name ['=' Type]                 -- without '= Type': punning (Eq[T] = Eq[T = T])
              | Type                            -- positional: next unfilled param in declaration order (§5.2)
              | VariableTerm                    -- variable binding: Modify[?], Modify[?r]

NamespaceContent ::= Import
                   | Sort | Rule | Operation
                   | RequiresDecl                 -- sort-level constraint
                   | Entity                       -- sugar (§6.3)
                   | Fact | Constraint            -- sugar (§6.1, §6.2)
                   | OperationBlock | RuleBlock   -- sugar (§6.4)
                   | Describe                     -- description (§4.1)
                   | Namespace

Visibility  ::= 'internal' | 'public'

Sort        ::= DescriptionBlock*
                  [Visibility] 'sort' Name '=' VariableTerm        -- unspecified (only in SortContent)
                  ['meta' ':' Meta]
              | DescriptionBlock*
                  [Visibility] 'sort' Name '=' Type                -- type alias
                  ['meta' ':' Meta]
              | DescriptionBlock*
                  [Visibility] 'sort' Name                         -- sort with body
                  Body[SortContent*]
                  ['meta' ':' Meta]

-- Note: unspecified sorts (first form) may only appear inside a sort body
-- as type parameters. Type aliases (second form) may appear in sort or namespace bodies.
-- Namespaces contain sorts-with-body and type aliases (not unspecified sorts).

SortContent ::= Import
              | Sort | Entity | Operation | Rule
              | RequiresDecl
              | Fact | Constraint | OperationBlock | RuleBlock
              | Describe | Namespace

DescriptionBlock ::= '{<' Text '>}'               -- free-form text, preserved as KB facts
Describe    ::= 'describe' Name DescriptionBlock+  -- attach description(s) to named symbol; appends to existing

FieldList   ::= Field (',' Field)*
Field       ::= Name ':' Type

Type        ::= Name                                           -- simple: Account, Int64
              | Name '[' SortBinding (',' SortBinding)* ']'    -- inline instantiation: List[T=Int64]
              | VariableTerm                                    -- logical variable: ?, ?T, ?T {< desc >}+ ?
              | '(' ArrowParams ')' '->' Type                    -- arrow type: (A) -> B
              | '(' ArrowParams ')' '->' Type '@' Type          -- effectful arrow: (A) -> B @ E
ArrowParams ::= (TupleTypeArg (',' TupleTypeArg)*)?             -- Type or Name ':' Type

Rule        ::= DescriptionBlock*
                  'rule' [Name ':'] Head [':-' RuleBody]
                  ['meta' ':' Meta]
Head        ::= Term | '⊥'
RuleBody    ::= Term (',' Term)*

Operation   ::= DescriptionBlock*
                  [Visibility] 'operation' Name '(' [ParamList] ')' '->' Type
                  ['requires' RuleBody]
                  ['ensures' RuleBody]
                  ['effects' '(' Effect (',' Effect)* ')']
                  ['meta' MetaBlock]               -- attributes (WI-087); see §5.8
ParamList   ::= Param (',' Param)*
Param       ::= Name ':' Type

Effect      ::= Name                       -- bare effect (e.g. Error)
              | Name '[' Name ']'         -- effect with target (e.g. Modify[store])

RequiresDecl ::= 'requires' Type                -- sort-level constraint (in sort/namespace body)

-- =================================================================
-- Syntactic Sugar
-- =================================================================

Fact        ::= DescriptionBlock*
                  'fact' Term ['meta' ':' Meta]
              -- desugars to: rule Term

Constraint  ::= DescriptionBlock*
                  'constraint' [Name ':'] Invariant [':-' Guard]
                  ['meta' ':' Meta]
              -- desugars to: rule [Name ':'] ⊥ :- Guard, ¬Invariant

Entity      ::= DescriptionBlock*
                  [Visibility] 'entity' Name ['(' FieldList ')']
                  ['meta' ':' Meta]
              -- desugars to: sort Name { entity Name [( FieldList )] }

OperationBlock ::= 'operation' Body[OperationEntry*]
              -- desugars to: individual Operation declarations
OperationEntry ::= [Visibility] Name '(' [ParamList] ')' '->' Type
                     ['requires' RuleBody]
                     ['ensures' RuleBody]
                     ['effects' '(' Effect (',' Effect)* ')']
                     ['meta' MetaBlock]               -- attributes (WI-087); see §5.8

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

## 12. Open Questions

Design questions discovered during implementation that need decisions.

### 12.1 Effect semantics

Effect declarations are stored as-is — open `Name` or `Name[target]` pairs. Currently implemented: `Modify[target]` (mutation) and `Error` / `Error[type]` (fallibility). Open questions:

- **Effect checking**: Should declared effects be verified against implementations, or remain advisory?
- **Control flow effects**: `Suspend` and `Branch` are described in §5.7 but not yet implemented. How should they interact with codegen?
- **Effect polymorphism**: Sorts can declare abstract effect parameters (`sort E = ?`) — how should unbound effect parameters be propagated and resolved?
- **Ambient resource effects**: Effects for resources not in the parameter list (e.g. `Output{stdout}`, `Log{logger}`) need concrete use cases before design.

