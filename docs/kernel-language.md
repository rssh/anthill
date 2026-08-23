# Kernel Language Specification

The kernel language is the minimal formal language of the anthill knowledge base. It defines four constructs that the reasoning engine understands natively — everything else in the anthill is built on top of these as entity types in standard namespaces.

This specification is **self-contained**: it can be implemented without reference to the high-level design document ([metasystem-design-draft.md](../metasystem-design-draft.md)), which provides motivation and vision but is not formal.

## 1. Design Principles

1. **Minimal kernel.** Four constructs: `namespace`, `sort`, `rule`, `operation`. The kernel is deliberately small — analogous to the kernel of a proof assistant (Lean, Coq) that is small, trusted, and verifies proofs, while tactics (large, untrusted) find them. `entity` is syntactic sugar (see §6).

2. **Rule is THE knowledge primitive.** All knowledge in the KB is expressed as rules (Horn clauses). `fact` and `constraint` have a rule/denial logical reading. This unifies ground assertions, derived knowledge, and integrity constraints at the language-model level; the current execution boundary for constraints is narrower (§6.2, §8.4).

3. **Algebraic specification.** The kernel is in the tradition of algebraic specification languages (OBJ, CafeOBJ, Maude): a namespace declares sorts (unspecified, type aliases, or defined types), operations (typed behavioral specs with contracts), and rules (laws).

4. **Partial formalization.** Any named declaration can have one or more **description blocks** (`{< >}`) — free-form text preserved as KB facts. Each block is stored as its own indexed `anthill.reflect.DescriptionInfo` fact. Combined with anonymous variables (`?`), this allows a spectrum from fully informal to fully formal within the same language. A fact or an unlabeled rule/constraint has no stable declaration target, so a leading block on one is refused rather than dropped (§4.1).

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
Identifier   ::= (Letter | '_') (Letter | Digit | '-' | '_')*
               | '"' [^"]+ '"'                        -- quoted identifier (unimplemented)

Name         ::= Identifier                           -- simple: "transfer"
               | Name '.' Identifier                  -- qualified: banking.accounts.transfer

AbsoluteName ::= '..' Name                            -- absolute: ..banking.accounts.transfer
```

The first alternative is exactly what both implementations tokenize
(`[a-zA-Z_][a-zA-Z0-9_-]*` — `tree-sitter-anthill/grammar.js`'s
`_identifier_token`, scaland's `Tokens.identToken`); a **leading `_` is
admitted**, which is what makes §8.6's *The top-level scope* argument load-bearing.

Quoted identifiers would allow arbitrary strings as names: `"my weird name"`.
**Neither implementation parses one**, and adding one would re-open the
collision §8.6 closes — see that section before doing so.

A `Name` is resolved **relative** to where it is written; `..` asks for the
**root** instead, and is admitted only in *reference* positions — a term, a type,
a citation — never in a declaration (§8.6). `..` is a marker rather than an
identifier, so it names nothing and can itself never be shadowed.

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

Description blocks (`{< >}`) attach human-readable text to declarations. Unlike comments (`--`, `{- -}`), description blocks are **structural** — they are preserved as `anthill.reflect.DescriptionInfo` facts in the KB. Multiple description blocks can be attached to the same target; each block is stored as its own fact, ordered by an index argument.

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

1. **Before a named declaration keyword** (`sort`, `operation`, `const`, labeled `rule`, `entity`, labeled `constraint`, `namespace`) — describes the declaration that follows. For an `operation` this holds in BOTH spellings — the standalone `operation NAME(…)` and an entry of an `operation { … }` block — and the description attaches to the entry it precedes, not to the block. A fact, unlabeled rule, or unlabeled constraint has no declaration symbol/citation handle to put in `DescriptionInfo.target`; the grammar accepts a leading block so the converter can refuse it precisely, never silently discard it. Add a label where one is available, or move the text to a named declaration.
2. **After `describe Name`** — standalone, can reference any named symbol. Appends to existing descriptions.
3. **After a variable (`?` or `?name`), closed by trailing `?`** — describes what the variable represents in that rule, constraint, fact, or operation contract. The trailing `?` delimiter disambiguates variable descriptions from declaration descriptions.

Multiple `{< >}` blocks on the same target each emit a separate fact with an increasing index, preserving declaration order. The `describe` construct emits additional `DescriptionInfo` facts for its target, enabling incremental annotation across files (the index counter is per file, so declaration order is encoded within a file, not across files).

Descriptions are stored as `anthill.reflect.DescriptionInfo(target, content, index)` facts — one fact per block, with a 0-based per-target `index`. For variables, the target is the variable's term in the KB; for a declaration, it is the declaration's qualified symbol term. A labeled rule's target is its citation label, so a multi-head rule still emits once; a labeled constraint's label is likewise a `Constraint` symbol in its declaring scope.

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
| `[a, b, c]` | `ListLiteral(a, b, c)` — lowered to the `List` `cons`/`nil` spine unless a declared type names another collection (§4.6) |
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

  operation length(l: List) -> Int64 =
    match l
      case nil() -> 0
      case cons(_, xs) -> add(1, length(xs))
  -- WI-580: the operation BODY is the single source of truth. Its equational
  -- (`<=>`) and relational (Prolog-style) views are DERIVED from the body on
  -- demand — a ground call folds via the eval bridge; a non-ground occurrence
  -- (a relational `length(?l) <=> ?n` or a bare `member(?x, ?l)` goal) is served
  -- by the SLD one-step body-unfold, NOT by hand-written duplicate rules. See
  -- docs/design/abstract-interpreter-and-rules.md §3.3.
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

-- The ordering tower is THREE floors (library proposal 007, WI-1109), because
-- "total" and "antisymmetric" are two questions and `Ord` used to answer both:
--   PartialOrd  gt/lt/gte/lte; NO totality (a NaN operand answers false). Float.
--   WeakOrd     `compare`; TOTAL, and CONGRUENT w.r.t. Eq (eq(a,b) => compare=0).
--               Its kernel may be strictly COARSER than Eq, so it partitions the
--               carrier into classes — a comparator chosen by a key lives here.
--   Ord         adds ONLY the converse law (compare=0 => eq), so the kernel IS Eq.
--               No new operation, the way Eq adds only reflexivity over PartialEq.
-- One-to-one with C++20 <compare>: partial_ordering / weak_ordering / strong_ordering.
-- `Ord provides WeakOrd[T = T]` and that ONE clause is its whole content (WI-1110):
-- a carrier writes one provision, the lower floor is DERIVED, and the same clause
-- puts a WeakOrd dictionary inside an Ord one so an `Ord`-constrained body can reach
-- `compare`. `WeakOrd`'s own `requires Eq[T]` / `requires PartialOrd[T]` reach the
-- carrier through it, which is why `Ord` restates neither. See §5.1's
-- "`requires` and `provides` are both chain entries".
-- (ILLUSTRATIVE — the snippet keeps `gt`/`lt`/`gte`/`lte` inline for brevity. The
-- shipped `WeakOrd` declares `compare` and INHERITS those four from `PartialOrd`,
-- which is load-bearing rather than tidy: declaring them on both specs would give a
-- carrier providing both two `sort_ops` entries for one short name, and which wins
-- is HashMap-iteration order. See `stdlib/anthill/prelude/ordered.anthill`.)
sort anthill.prelude.WeakOrd
  sort T = ?
  requires Eq[T]
  requires PartialOrd[T]

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

-- Numeric: basic arithmetic (requires PartialOrd — IEEE Float is Numeric but only
-- partially ordered, so the requirement is the partial comparison surface)
sort anthill.prelude.Numeric
  sort T = ?
  requires PartialOrd[T]

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

**Infix and prefix operators** are sugar for function application — `a + b` desugars to `add(a, b)`, `!a` to `not(a)`, etc. The full operator table is in §6.6. The prelude sorts above define the operations these operators desugar to; the operators are available when the corresponding sort is required (e.g. `requires Numeric[T = Money]`). One target is **position-directed**: `not(…)` is negation-as-failure (`anthill.kernel.not`, a resolver primitive over a `Term`) in a rule-body goal position, but boolean negation (`Bool.not`, a dispatched operation) as a value expression — see §6.6.

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
Type ::= RefName                                        -- simple type reference (§2.3: Name or ::Name)
       | RefName '[' SortBinding (',' SortBinding)* ']' -- inline instantiation
       | VariableTerm                                 -- logical variable: ?, ?T, ?T {< desc >}+ ?
       | TupleType                                    -- tuple type: (Int64, String), (a: Int64, b: String), ()
       | ArrowType                                    -- arrow type (function sort)

ArrowType ::= TupleType '->' Type                        -- pure function
            | TupleType '->' Type '@' Type               -- effectful function

-- The parameter list IS a TupleType (WI-766) -- one production, so `->` never
-- has to be predicted at the closing paren.
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

**A UNIVERSALLY QUANTIFIED type has no production here, and that is deliberate** (WI-1083).
`∀A. (x: A) -> A` is a type the language *has* — it is what a type-parameterized operation's
name denotes when it is used as a function value — but nothing writes one: every binder in
anthill attaches to a **declaration** (`operation map[Dst, EffP](…)`, `sort [F] { … }`,
`sort T = ?`), never to a free-floating type. A bare `[A]` prefix could not be the spelling in
any case: types are terms, so a leading bare `[…]` is the collection literal of §4.6, and the
form would need a keyword like every other binder the language has. The quantified form is
therefore **inferred, never written**: it is minted where an operation first becomes a value
(§5.4, "as a FUNCTION VALUE") and eliminated at the reference that names it. Its structural
form is `TypeExtractor.PolyType(binders, body)` — `binders` a list of the bound **variables**
(so `id` links each to its occurrences in `body`, per §8.1's rule that a variable's identity is
its `id` and not its name), `body` the arrow they quantify. It is **∀ by construction** and
stores no quantifier: the polarity rule of §8.1 already makes the quantifier a function of
*position*, so a per-binder one could disagree with the position it sat in; and the existential
needs no binder node at all, being implied by the return position at a declaration and already
opened to a `Skolem` at a use.

**Parameter lists correspond slot by slot** (WI-782). A parameter list is
*applied positionally*, so one arrow conforms to another only when the two lists
have the **same arity** and their slots correspond by **position**. Binder names
are not *paired up* to build that correspondence — the zip is by index — but they
do decide whether the zip is **admissible** at all (see below): `(acc: A, x: B) ->
R` accepts a value typed `(_1: A, _2: B) -> R`, which is what lets a named-binder
callback take an operation's eta-expanded arrow. A permuted list is therefore compared
slot-for-slot rather than paired by name, so `(y: Bool, x: Int64) -> R` fails
against `(x: Int64, y: Bool) -> R` on the component types; and a two-parameter
value does not conform to a three-parameter one. A positionally consumed list
admits neither permutation nor width. **Data tuples are different**: every reader
of one is name-keyed — `t.x` access (§Field access, mode 3) and destructuring
alike (§"Destructuring binds by LABEL") — so **width and permutation are both
subtyping rules** for them, with components dropped from anywhere. See §4.5.

Because names are not matched up, the zip is admitted only when the two lists
agree on which slot is which — the names line up, or one side carries the
synthetic `_1.._n` convention. Two equal-arity lists with unrelated names do not
conform.

**An arrow records its parameter ARITY** (WI-791), and that count — not the shape
of the parameter type — decides which of the two relations applies:

* **arity ≠ 1** — the parameter position *is* the list, and the rules above hold:
  same arity, slot-by-slot, no permutation and no width.
* **arity 1** — the parameter position is the sole parameter's TYPE. A tuple there
  is *data*, so it is related as data: name-keyed, with width AND permutation
  (§4.5). A callback reading only `(a: A)` therefore accepts a wider
  `(a: A, b: B)`, and `(t: (x: A, y: B)) -> R` accepts a callback declared
  `(u: (y: B, x: A)) -> R`.

Arity is thus what tells `(t: (a: A, b: B))` — one tuple-typed parameter — from
`(a: A, b: B)` — two parameters. They are different types: neither conforms to the
other, and the mismatch is a **load error**, not a run-time trap. Write the
one-parameter form as `((a: A, b: B)) -> R` when there is no binder to name it;
that is also how it prints.

> An arity-1 parameter list still **drops its binder name** — `(v: A) -> R` and
> `(w: A) -> R` are the same type — so a named argument cannot be resolved
> against a single-parameter arrow. Arity is recorded; the arity-1 binder name is
> not.

**Applying a function value checks its arguments** (WI-792). The rules above
relate one arrow to another; this is the other half — which *arguments* fit an
arrow. Calling a value of arrow type `f(a₁, …, aₙ)` is checked exactly as calling
a named operation is:

* the argument **count** must equal the declared arity;
* argument `i` is checked against parameter slot `i`, and a **named** argument
  against the slot its label resolves to (§named arguments) — so a wrong-typed
  value in any position is a **load error**, not a run-time trap;
* the same call-side conversions apply as at any other argument position, notably
  the `Option` some-coercion (a bare `T` supplied for a declared `Option[T]` is
  wrapped).

A `Function[A, B, E]` states no arity (see the note below), so neither the count
nor the slot-wise check is stated over it — both `f(3, 10)` and `f((3, 10))`
remain legal at a `Function[(A, B), R]` parameter.

The same checks reach a callback argument whose declared type is still
**polymorphic** (`apply2[T](f: (x: T, y: T) -> R, …)`). A component type is
deferred only while it is *genuinely* polymorphic — a variable the call has already
pinned is **resolved and then decided**, including one pinned by a *sibling*
argument, so `both[X](f: (x: X) -> R, g: (x: X) -> R)` refuses a `g` that
contradicts the `X` its `f` fixed (WI-1084 for the result position, WI-1085 for the
parameter; the same rule that makes two `List[T = X]` arguments agree, WI-836).
**Arity** is decided regardless, since a parameter count is not something
instantiation can change.

The positional rule above relates two parameter *lists*, so it applies when both sides
are arrows — whether or not either was reached through a variable. It applies to a
`Function[A, B, E]` too, but only at the **spread** reading: when the callback's arity
is `A`'s component count (and not 1), `A`'s components *are* that callback's parameter
list, so they align positionally with the synthetic `_1.._n` escape (WI-1087). At the
**whole-`A`** reading — arity 1 — `A` is one argument's data type and is compared by
name, which is what keeps a permuted `(b, a)` conforming to `(a, b)` there.

That distinction is forced. An operation's eta arrow always spells its parameter list
`_1, _2, …` (an arrow drops its binder names), so a by-name comparison would refuse
*every* spread the arity rule admits, leaving the second reading reachable only for a
lambda — which adopts `A` as its parameter type and matches it by construction. It
would also make the verdict depend on how `A`'s components were *labelled*:
`Function[A = (Int64, Int64), B]` admitted a two-parameter operation and
`Function[A = (acc: Int64, x: Int64), B]` did not, though the runtime spreads either
and reads no label.

**The reader spreads by label.** Under the spread reading the callee's parameter `i` is
`A`'s component `i` positionally, while the *value* conforms to `A` by name and may
present its components in another order. So the components are handed over by `A`'s
labels, not in the value's source order — the same discipline destructuring follows
(§"Destructuring binds by LABEL"), and what makes an operation and a lambda
interchangeable in the slot.

**Two `Function` slots must agree on `A`'s order.** A `Function[A, B, E]` states no arity,
so *both* readings above stay open for any value standing in it — and the mapping a spread
uses is fixed where the value is **minted**, not where it is later re-typed. So when a
`Function`-typed value flows into another `Function` parameter, the two `A`s owe the
*intersection* of the two readings: by name, **and** in the same order. A pairing whose two
`A`s are permutations of each other is refused (WI-1088). Without it,
`inner(g: Function[A = (x, acc), B])` accepted an `f: Function[A = (acc, x), B]` and
`inner`'s declared `A` was silently not the mapping used — one program answering `7` called
directly and `-7` through the second slot, on a clean load. The refusal is on the **order**
axis alone; width and names are unchanged, and the whole-`A` reading still admits a
permuted argument at a single slot.

None of this relates a named tuple to a positional one as **data**: rule 4 stands, and
`A` in the spread reading is a parameter list rather than a data tuple.

The `@` token annotates effects on the arrow, consistent with the term-level Pratt operator where `a -> b @ c` desugars to `arrow_effect(a, b, c)`. A pure arrow `(A) -> B` desugars to `arrow(params..., B)` in the KB; an effectful arrow `(A) -> B @ E` desugars to `arrow_effect(params..., B, E)`.

The braced annotation `@ {…}` admits the proposal-045 row algebra: bare labels (present), an explicit row variable (`?` anonymous, `?r` named, or a declared row binder `E` — an **open** row), and `-e` absence atoms (`lacks` constraints). `@ {}` is the explicit closed-empty (pure) row, identical to no annotation. An absence-only annotation (`@ -Modify[x]`) is a **closed** row carrying the lacks constraint; the co-finite "anything except `e`" is written with an explicit open base — `@ {?, -Modify[x]}` or `@ {Eff, -Modify[x]}` (WI-440 row-openness decision: an implicit fresh tail would be unnameable by the enclosing operation, which must declare the row it incurs when applying the callback). A callback parameter's row is checked at each call site against the argument operation's declared row, with the callback's binder places aligned positionally to the argument's own parameters (`Modify[c]` on the argument's param 0 matches `Modify[x]`/`-Modify[x]` on the callback's param 0); an unresolved place in a `-…` absence label is a load-blocking error (the constraint would be vacuous).

The arrow sort `(A) -> B` is equivalent to `Function[A, B]` from stdlib (with empty effect set). The effectful arrow `(A) -> B @ E` is equivalent to `Function[A, B, E]`. `Function` is the unified sort for all callable values — pure and effectful. Effect subtyping applies: a pure function can be passed where an effectful function is expected (`Function[A, B] <: Function[A, B, E]` for any `E`).

> The equivalence is not exact in one remaining respect: **`Function` states no
> arity.** `A` is the one argument `apply(f, x: A)` passes, so `Function[(A, B),
> R]` denotes both a single-tuple-argument callback *and* — by the run-time
> convention that spreads one tuple argument across a multi-parameter operation —
> a two-parameter one. The arrow spelling now distinguishes those, so
> `((A, B)) -> R` accepts only the former while `Function[(A, B), R]` accepts
> either. (Before WI-791 the two disagreed the other way round, on permutation and
> width of a tuple parameter; that half is resolved — both relate a lone tuple
> parameter as data, slot-by-slot with names agreeing, per §4.5.)
>
> Stating no arity means no argument *count* can be **required** at a `Function`
> slot — but a count can be **observed** at the call, and the arguments **are**
> checked (WI-788): one argument is related to `A` itself, `n` arguments to `A`'s
> `n` components. A call that matches neither reading is a load error naming both
> admissible counts. This is not a special case for `Function` so much as the two
> spellings of application it genuinely permits.
>
> Symmetrically, the *callback's own* arity is checked against `A` (WI-801). Two
> readings are admitted and no others, so where `A` has `n` components a callback
> of arity `k ∉ {1, n}` is a **load error** — it fits neither `A -> B` nor `A`'s
> components spread, and no call form at the slot could reach it. Where `A` is a
> non-tuple the sole admissible arity is 1; where `A` is not yet known (a rigid
> type parameter) nothing is required, since a component count is exactly what
> instantiation supplies. This closes the dual of the paragraph above: the *call*
> was checked against `A` and the *callback* was not, so `Function[(X, Y), R]`
> given a three-binder lambda loaded clean and trapped at run time.
>
> The two admitted arities and the two admitted call forms compose freely — all
> four combinations evaluate. A spread call against a callback that takes the whole
> `A` is **normalized at load** into its whole-`A` form, which is the only place it
> can be: gathering `f(v₁, …, vₙ)` into `(l₁: v₁, …, lₙ: vₙ)` needs `A`'s component
> labels, and those are gone by run time.

Import and instantiation are separate concepts: `import` makes names visible, inline `Name[bindings]` instantiates sort parameters. They are not bundled together.

**Instantiation as term:** The `Name[bindings]` syntax is valid both in type position and in term position. In term position, it represents a sort instantiation as a first-class value — used to assert that a type satisfies a parametric spec:

```
-- "Int64 satisfies Eq" — a fact in the KB
fact Eq[T = Int64]

-- "String satisfies Ord" — scoped to the declaring namespace
fact Ord[T = String]
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

The auto-generated names are **one-based and canonical**: a component at source index `i` is named exactly `_<i+1>`, with no leading zeros. Every other `_`-prefixed identifier is an ordinary **user** label — `_0` (outside the range), `_01` (not the string `_1`), `_b`, and a `_2` written at a position other than the second. A user label keeps its position, is reachable only by that name, and is never re-slotted positionally; a synthetic one is erased when the tuple is printed back to surface syntax, since positional syntax is how it was written. (WI-786/WI-790.)

**Component ORDER is part of a tuple's type identity** (WI-788), *alongside*
component names. A component is identified by its **name and its position**
together: two tuple types are related **slot by slot**, with the names required to
agree at each slot. So a **permutation is never admitted**, at any position
(argument, return, parameter, component) — `(a: Int64, b: String)` and
`(b: String, a: Int64)` are different types because the positions disagree, and
`(a: Int64, b: String)` and `(Int64, String)` are different types because the
names disagree (proposal 004 rule 4 — no subtyping between named and positional).

Numbering a tuple's components `_1.._n` by definition order is a useful way to
*see* that position is part of identity, but it is **not a normalization** —
nothing rewrites a named tuple into positional form. Read literally it would erase
names and make `(a: A)` the same type as `(_1: A)`, which rule 4 refuses. Both
coordinates are checked; neither is discarded.

Order is identity because a tuple's components are read *positionally* wherever
names are unavailable or not what is being asked: an arrow's parameter list is
applied by position (§Arrow types), and unification asks whether two tuples are
the same type, which a reordering changes. Where a *consumer* reads by name, order
does not participate — that is `<:`, and the two must not be conflated.

Both of a tuple's readers are name-keyed. Component **access** always was
(§Field access, mode 3); **destructuring** became so in WI-803
(§"Destructuring binds by LABEL"). Before that it read by slot, and the
disagreement was the source of a whole family of silent wrong answers — a binder
bound to one component while the type checker had typed it from another. Note
that the read discipline could not have gated the *relation*: a value flows
through a `Function[A, B]` *parameter* to a consumer chosen at a different call
site than the one relating it to `A`, so the site admitting a permutation cannot
know which reader it will meet. Making every reader name-keyed is what removes
the question.

**Width subtyping is name-keyed**: `S <: T` requires every component `n : T_n` of
`T` to appear in `S` with `S_n <: T_n`, and `S`'s extra components — dropped from
*anywhere*, not only the end — are simply not observed. So `(A: TA, B: TB, C: TC)
<: (A: TA, C: TC)`. Order plays no part in `<:`; it belongs to *identity*, and the
two are different relations.

**Permutation is a subtyping rule too** (WI-803): `(b: String, a: Int64) <:
(a: Int64, b: String)`. Every consumer of a value typed `(a: Int64, b: String)`
asks for its components by *name*, and a value carrying both answers regardless of
the order it wrote them in. This is the same principle as width — `<:` is
name-keyed throughout — and it is *not* in tension with order being identity,
because they are different relations. Conflating them is the mistake to avoid: it
is what made an earlier rule refuse `(A, B, C) <: (A, C)`, a correct program.

This holds because **destructuring binds by label**, not by slot
(§"Destructuring binds by LABEL"). Until it did, a permutation admitted by `<:`
handed a destructuring binder a component the checker had typed from a different
field — an operation declared `-> Int64` returning a `String` with no error at
load or run time (WI-788) — and the rule was held back for that reason alone. The
defect was in the reader; the relation was right.

```
-- Tuple types (in type position)
TupleType ::= '(' ')'                                              -- unit
            | '(' TupleTypeArg ')'                                 -- 1 element (named, as a type)
            | '(' TupleTypeArg ',' TupleTypeArg (',' TupleTypeArg)* [','] ')'  -- 2+ elements

TupleTypeArg ::= Type | Name ':' Type | Name ':' Literal

-- Tuple literals (in term position)
TupleLiteral ::= '(' ')'                                           -- unit value
               | '(' Name ':' Term [','] ')'                       -- 1 element (NAMED only)
               | '(' FnArg ',' FnArg (',' FnArg)* [','] ')'        -- 2+ elements
```

**Disambiguation (term position):** `Name(...)` preceded by a name is function application. Otherwise the FIRST element decides. A leading `name :` makes `( … )` a tuple at any arity — `a: 1` is not a term, so `(a: 1)` has no parenthesized-expression reading to compete with. A leading *term* makes it a tuple only when a comma and another element follow: `(a)` is grouping, `(a, b)` is a tuple.

**Arity one is named-only** (WI-1131), and the asymmetry is forced, not an omission. `(1)` must stay grouping, so a lone *positional* component has no spelling and a trailing comma cannot conjure one: `(1,)` is refused, with a message naming this rule rather than a syntax error. A lone *named* component is a tuple literal, with or without the trailing comma.

The trailing comma is the one place a reader — and the parser — must look past the comma: `(a: 1,)` closes a one-element tuple while `(a: 1, b: 2)` continues a two-element one, and nothing at the comma itself separates them. Everything else here is decided by the token after `(`.

**Disambiguation (type position)** needs no lookahead either, because a parenthesized type list is *one* construct: `TupleType` is also an arrow's parameter list (WI-766). `( … )` is read as a tuple type unconditionally, and a following `->` simply makes it the parameter list of an arrow. Nothing has to be decided at the `)`.

Which readings are *valid* is then a separate question from how they parse, and two forms parse but are not types:

- A bare `(A)` is a parameter list (`(A) -> B`) but **not** a type. A single parenthesized type is neither grouping nor a 1-tuple; written where a type is expected it is an error.
- A denoted component is a tuple component but **not** a parameter: `(a: "x") -> B` is an error, since a parameter's declared type is a type and a literal is not one.

Both are reported where they occur, with the offending construct named — a located error rather than a syntax error, which is the reason the grammar admits them at all.

A one-component tuple type must therefore name its component: `(a: A)` is a 1-tuple, and the name is what carries the field label, so the named form is the only one that says something a bare `A` does not.

That type has an arity-matching literal: `(a: 1)` is a one-component tuple *value* and conforms to `(a: Int64)` directly, so a parameter declared `(a: A)` can be given an argument written at the call site. A one-component tuple type is thus inhabited two ways — by its own literal, and by width subtyping from a wider tuple (`(a: 1, b: 2)` conforms to `(a: Int64)` as well).

The surface is still not symmetric between types and terms, but only in the direction the disambiguation rule forces: a bare `(A)` parses in type position and is refused as a type, while a bare `(1)` in term position *is* a valid term — grouping — and so cannot also be a 1-tuple.

**Denoted components** (`Name ':' Literal`, WI-763) — a component may be a *constant standing in type position*, which lowers to a `denoted` exactly as a literal type **argument** does (`Vector[Int64, 3]`; see "value-in-type" below). This is what makes a projection's keep spec writable: `Project[T = (name: String, age: Int64), Keep = (person: "name", years: "age")]` maps each result key to its source column's *name*, and a name reaches type position only as a denoted, since there are no singleton types. One asymmetry follows from the surface grammar rather than from the type system, and is deliberate:

- A literal is **not** admissible where a component is always a type: an entity field declaration (`entity person(name: "foo")`) or an arrow parameter (`(a: "x") -> B`) is an error.

**All-or-nothing naming:** either all elements have explicit names or none do. Mixing `(a: Int64, String)` is an error.

**Distinct component names** (WI-805): a named tuple's component names must be
distinct. This is the same rule already stated for a projection's result keys
(§Distributive projection, "Distinct keys") and for a call's named arguments, for the
same reason: both of a tuple's readers resolve a name to its **first** match, so a
second component under an already-used name is reachable by neither its name nor its
position, and its declared type is never checked against anything. Measured before the
rule existed, on a clean load: `(a: 1, b: 2, a: 3)` conformed to `(b: Int64, a: Int64)`
with the `a: 3` column unreadable.

It is checked wherever a tuple is **built from names the author wrote** — three places,
each reporting a located error naming the repeated label:

- the **literal**, `(a: 1, b: 2, a: 3)`;
- the **type**, `(a: Int64, a: String)`;
- a **variadic capture**'s leftover named arguments, `cap(1, a: 2, a: "ess")`, which
  become a tuple without ever being written as one.

Note this is not the same guarantee as making every reader agree on *which*
occurrence to take (WI-803, which resolved a disagreement between the conformance
relation and `t.a`): agreeing on which component to read leaves the unread one still
unreadable. Refusing the duplicate where it is built is what makes the question
unreachable.

The rule is scoped to a **tuple**, not to every parenthesized name list. An arrow's
**parameter list** shares the surface production (`(a: Int64, a: Int64) -> Int64`) but
not the reading. A repeated binder name there does shadow — the body reads the *last*
such parameter, the opposite occurrence from the one a tuple reader takes — but every
parameter is still **applied positionally**, so the shadowed one's declared type is
checked against an argument at every call. Nothing is silently unchecked, which is what
this rule is about; whether to reject duplicate binder names is a separate question
about shadowing, and it would have to answer for entity fields too. Synthetic `_N`
labels are generated from each component's own index and cannot collide; a user
`_`-prefixed label (`_b`, `_0`, a `_2` off its slot) is an ordinary name and is
compared as one.

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

**Construction:** `[a, b, c]` is represented as `ListLiteral(a, b, c)` in the untyped term language. The typing process rewrites this to concrete constructors (`Collection.insert`/`Collection.empty`) based on the expected type. The loader performs the `List` case of that rewrite ahead of typing, so a rule can destructure a literal: `[a, b, c]` becomes the `cons`/`nil` spine, and `[]` becomes `nil`.

**`[…]` IS THE `List` LITERAL, AND A POSITION THAT NAMES NOTHING IS A `List` POSITION.** A declared type decides only when it *names* a different collection: in a position declared `Set[T = X]` (or any other concrete non-`List` collection type, including a collection *of* lists such as `Set[T = List[T = X]]`) the literal is left as written, for that type's own construction to consume. Everywhere else it is the `cons`/`nil` spine, and that covers three cases, not one:

- an entity field declared `List[T = X]`, or an `Option` around one — where the literal is the `Option`'s payload, desugared and then wrapped in `some(…)`;
- a position that declares **no type at all**: an operation-call argument, a rule head, a plain relation's fact head, a bare `?xs = [1, 2]`;
- a position whose declared type is a **type parameter** (`entity Box(v: T)`, and `Option.some(value: T)`, through which every bare `some([…])` passes). A `T` says the position is generic; that is the same information an absent declaration carries, and is not a rival collection.

The last two are the rule's default rather than gaps in it: those positions have no naming declaration to consult and never will. Reading their silence as "some other collection" made `contains([7], 9)` answer, `rule digits: [1, 2, 3]` undestructurable, and every such literal a silently wrong answer rather than a diagnostic.

**Only the bracket surface is this literal.** `[a, b]` and a `ListLiteral(a, b)` written by name build the identical term once the name resolves, so the rule above is keyed on the **surface the author wrote**, not on the functor: a `ListLiteral` written by name — positionally *or* with named arguments (`ListLiteral(elements: …)`) — is the reflect entity, and is never lowered, in any position. (The same shape, and the same remedy, as `Box[T = Int64]` vs `Box(value: 1)`: only the surface separates them, so the parser records it.) That by-name spelling is what a rule writes to match a list-literal occurrence's term twin through `occurrence_term`, and it is the only spelling that survives being written back to a file.

**Printed form.** A flat `ListLiteral` and a ground `cons`/`nil` spine both render as `[a, b]`, and deliberately so: the printed form is a *surface*, and the persistence layer's content-keyed retract matches an on-disk fact — parsed, not yet lowered — against a loaded head, so its key must be invariant under the lowering this section describes. Nothing can separate the two terms there in any case: a `[a, b]` left flat by a rival-collection declaration and a written `ListLiteral(a, b)` are one hash-consed term. Text *written back* to a file answers the other question — it must load to the term it came from — so a fact carrying a flat `ListLiteral` is persisted **by name**, which no position lowers.

**A declared type is in force for the whole load.** Where a declared type *does* decide, it decides alone — never by which file the declaration is in, where in that file it stands, or the order the files were handed to the loader. The same holds for every other decision the loader makes from a declared field type: the `some(…)` wrap of a bare value in an `Option`-typed field, and the `none()` fill of an omitted one. Enforced by lowering every entity's field types before any file's terms are converted (`Loader::declare_field_types`; the field NAMES are settled one phase earlier still, in the definition scan). The rule has to be stated because its violation is SILENT: a field type not yet known is indistinguishable from a position that declares nothing, so a `Set`-typed field whose declaration arrived late would take the `List` default and read as a decision.

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

**Applying a lambda** (WI-784). Binding one pattern does not mean a lambda is applied to one *argument*: an `n`-binder lambda is applied as `f(a₁, …, aₙ)`, the spelling the standard library's callbacks use (`foldLeft(t, f(init, h), f)`). The arguments are gathered into the tuple its binder list destructures, so a nullary thunk is forced as `t()` and a two-binder callback is called `f(3, 10)`. A **single** argument is always passed to the pattern unchanged, so a caller that builds the tuple itself (`f((3, 10))`) destructures exactly as before — both spellings of a two-binder call therefore work. Any *other* argument count must equal the binder count, else it is an arity error reported against that count. This is the mirror of the `Function[(A, B), R]` ⇒ `op(a, b)` eta convention for operation references, and it is what makes a lambda and a named operation **interchangeable as function values** — the same call site accepts either. The reverse adaptation — `n` arguments *gathered* into a callback that takes the whole tuple — is **not** performed here, and cannot be: it needs the component labels, which live in the static `A`. It is performed at load instead, by normalizing the call (WI-801, §`Function` states no arity); the run-time arity error above is what remains for a call whose slot type never said what those labels were.

A lambda binder may carry an **optional `: Type` annotation**, written in parens: a single binder `lambda (x: T) -> …`, or per-element in a tuple `lambda (a: A, b: B) -> …` (WI-517). The parens are required — a bare `lambda x: T -> …` would clash with the `->` separator. The annotation pins the binder's type, so a lambda can be written **without** an expected-type context (e.g. `let f = lambda (x: Int64) -> add(x, 1)`, where no use site supplies the parameter type) and so foldLeft-style callbacks can document their parameters. When an expected arrow type is also available at the use site, the annotation must be consistent with it — a genuine contradiction is rejected (for a single binder, the lambda's arrow carries the annotation and is checked against the expected type; for tuple binders, the surrounding component type drives the binding, so a conflict surfaces through the body's use of the binder). A binder written without an annotation infers its type from the expected arrow at the use site (the HOF parameter's declared type, the operation's return type, etc.).

A **`let` binding** may carry the same `: Type` annotation, and on **any** pattern — `let x: Int64 = …`, `let (a, b): (a: Int64, b: String) = …`, and `let _: T = …`, which asserts the value's type and binds nothing. The annotation supplies the expected type for the value and fixes the bound names' types for the continuation, so a later use can disambiguate against it. It is **one** annotation channel with the lambda binder's, not a parallel one: `let (x: T) = …` and `let x: T = …` write the same slot on the same pattern, so writing **both** (`let (x: T1): T2 = …`) is rejected — the two types name one slot and there is nowhere to put the loser (WI-819). A per-element binder annotation inside a destructuring is a different slot on a different (sub-)pattern, so `let (a: A, b): T = …` is fine.

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

### 4.8 Executable expression bodies

An operation or concrete `const` may carry an Anthill expression after `=`.  The
body may be written directly or enclosed in braces; the braces delimit the one
expression and do not introduce a second sequencing construct.  Sequencing is a
right-nested `let` chain.  This is the implemented surface of proposal 018.

```
BodyExpr   ::= Expr | '{' Expr '}'
Expr       ::= Term
             | MatchExpr
             | IfExpr
             | LetExpr
             | LambdaExpr
             | ProofStatement

MatchExpr  ::= 'match' Term MatchBranch+
MatchBranch ::= 'case' Pattern ['|' Term] '->' Expr
IfExpr     ::= 'if' Term 'then' Expr 'else' Expr
LetExpr    ::= 'let' Pattern [':' Type] '=' Expr Expr

Pattern    ::= Identifier                         -- binder
             | '_'                                -- wildcard
             | Literal
             | Name '(' [PatternArg (',' PatternArg)*] ')'
             | '(' ')'                            -- unit/empty-tuple pattern
             | '(' Pattern ')'                    -- grouping, not a 1-tuple
             | '(' PatternElem ',' PatternElem
                   (',' PatternElem)* ')'          -- tuple destructuring
             | '(' Identifier ':' Type ')'        -- typed single binder
PatternArg ::= Pattern | Identifier ':' Pattern   -- constructor field pattern
PatternElem ::= Pattern | Identifier ':' Type     -- typed tuple binder
```

There is no `end` belonging to `match`: each `case` arm's body is an `Expr`, and
the surrounding declaration/body delimiter ends the last arm.  A guard after
`|` is checked only for that arm.  Patterns bind lexically in their arm or
continuation; a repeated source name at a later binder is a distinct binding.

`let p: T = value continuation` gives `value` the expected type `T` and makes
the pattern's bindings available only in `continuation`.  The annotation is one
slot: a type on the whole pattern and a type on that same single binder may not
both be written.  Per-element annotations inside a tuple pattern are distinct
slots and may coexist with a whole-pattern annotation.

Operation bodies and const bodies use this same grammar.  A const adds the
purity and bounded-folding rules of §5.9; using the same expression syntax does
not make an effectful expression legal in a const.  In-body `ProofStatement` is
specified with the other proof forms in §5.10.

Design record: [proposal 018](proposals/018-expressions-and-operation-implementation.md).

## 5. Kernel Constructs

Four constructs the reasoning engine understands natively — §5.1–§5.4. The
sections after them cover what attaches to those four (effects and operation
attributes), followed by the `const`, proof, and realization declarations that
use the kernel but are neither additional native constructs nor §6 sugar.

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
- Wildcard imports work naturally: `import anthill.prelude.*` imports all items defined in the `anthill.prelude` scope — that scope's own items, not those of the `anthill` around it (§8.6, WI-1089).
- Explicit `namespace anthill { ... }` and implicit `anthill` (from `sort anthill.prelude.X`) merge into one scope.
- **Merging shares definitions, not imports (WI-995).** Two files writing one address contribute their declarations to one scope — that is what the first bullet says — but each file's `import` lines resolve names only in that file. See "An import is file-local" in §Namespaces and imports.

**Qualified names.** Every defined symbol has a `short_name` (last segment) and a `qualified_name` (full path from the global scope). Items nested inside a sort or namespace body have their qualified name constructed by prepending the enclosing scope's qualified path. For example, `operation eq` inside `sort anthill.prelude.Eq` gets `qualified_name = "anthill.prelude.Eq.eq"`. The `by_qualified_name` index serves as a global registry of fully-qualified paths, while scope-aware resolution (`resolve_in_scope`) uses short names and parent scope chains.

A diagnostic that reports which scope a name was resolved in names it by this
**qualified** name — see *How a diagnostic names a scope* in §8.6.

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

Binding across the term is *all* the name buys. In an operation signature it is what §8.1's return rule reads to tell a bound universal from an unbound existential (WI-1078): a variable a declaration uses in a parameter, an `[A]` binder or a `requires` bound is instantiated by the caller, while one used only in the return is opened at each use — the same verdict the anonymous `?` gets there.

Import makes names from another namespace visible in the current scope as local aliases. It does **not** add the imported sort's scope as a parent — importing `Eq` does not make `eq`/`neq` directly accessible (WI-1089; the resolution rule is §8.6, *Import forms*). To access a sort's contents, use `requires Eq[T]` (sort composition) or wildcard import. Sort parameters remain unspecified — they are instantiated separately via inline type expressions (`Name[bindings]`), not at import time.

Three import forms:

```
-- Import a specific name from a namespace:
import anthill.prelude.List                   -- imports "List" from anthill.prelude

-- Import selected items from a namespace:
import anthill.prelude.{List, Option}         -- imports "List" and "Option" from anthill.prelude

-- Import everything from a namespace:
import anthill.prelude.*                      -- imports all visible names from anthill.prelude
```

**Where an import may be written.** Anywhere a declaration may be: in a namespace
body, in a sort body, or at a file's **top level**, outside any namespace. The
import enters the scope it is written in, and a file's top level is the global
scope — the same one a top-level `sort` / `fact` / `rule` is defined in.

**An import is file-local (WI-995).** It resolves names only in the **file that
lists it**, at every scope including the global one. A scope is an *address*, and
two files may write one address (`namespace demo` in each, or the file top level);
before this rule they shared one import table, so a file could silently change what
a bare name meant in a file it had never seen — whole-program non-locality reachable
with two ordinary namespaces. Each file now imports what its own text names.

This is the one place an import differs from a **definition**, and the difference is
deliberate: a top-level `sort S` is still visible KB-wide, because a definition adds
a name to the *program*, while an import only chooses what one file's *text* may call
it. It follows that an import is **not a re-export** — `import a.b.{n}` requires `b`
to *declare* `n`, not merely to have imported it — so name the declaring scope
(`import anthill.prelude.Numeric.{sub}`, not `…Int64.{sub}`, which has `sub` only
because `int64.anthill` imported it there).

**A resolution with no file** — a query pattern, or a host-supplied name — reads only
imports that belong to no file: the implicit prelude, and those supplied by the
**invocation** (`anthill query -i <name>`). A program file's imports do not reach it,
having no file to be local to.

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
                   | Proof | ProvidesClause      -- see §7.3, §8.7; a ProvidesClause needs a sort at the address
                   | ProvidesBlock               -- host realization (see §10.2)
                   | Namespace                   -- nested namespaces
```

**A `namespace X` at the address of a sort `X` is a SECONDARY ENTRY to that
sort's scope** — not a separate module attached to it. `SymbolTable::define`
merges the two declarations onto one symbol (§8.6), so what the block declares
enters `X`'s own scope, is scoped by `X`'s type parameters, and may back `X`'s
spec claims. It is the only way to add a member to a type whose declaration one
does not own, and it is legal before, beside or after the type's declaration, in
the same file or another. The two are told apart by the **address**, never by the
text: the same `namespace X` block is an ordinary namespace wherever no sort
occupies `X`.

**What a secondary entry may contain — members and spec claims, never identity**
(proposal 059 R3; enforced by `SecondaryEntryPass`, `kb/load.rs`). The list is
DEFAULT-DENY, so an unclassified production is refused rather than silently
admitted:

| in a secondary entry | |
|---|---|
| an `operation`, or an `operation { … }` block | **allowed, and it must have a runnable Anthill body.** An entry adds a complete new member; a body-less declaration reserves an implementation slot for a builtin or a host `operation_map`, which is a main entry's to reserve. Asked of the declaration as written — a `[simp]` equation is not a body, and no `operation_map` or builtin makes one appear. A body-less operation in a MAIN entry stays legal, as the host carriers require |
| a `const` | allowed, **and it must have a defining value** — the same clause as the operation above, for the same reason: a value-less `const` reserves a host slot for a `const_map` entry (§10.2), the const-level peer of `operation_map`. A value-less `const` in a MAIN entry stays legal, as `Float.infinity` / `nan` require |
| a nested `sort` / `enum` with a body, or a type alias `sort A = T` | allowed: each declares a new type at its own address (`X.A`), so it is that type's main entry and the restrictions do not recurse into it |
| a nested `namespace` | allowed, and not recursed into: it is an ordinary namespace at `X.Inner` |
| `provides Spec[…]`, and a host `provides Spec language L … end` block | allowed. The block's INTERIOR is classified by this same table — realization clauses only |
| a `proof`, or a standalone `describe` | allowed **iff its target is declared in this same entry**. A proof writes its verdict back onto the target declaration and a `describe` writes a description onto it, so neither may reach a declaration another entry owns |
| an `entity`, or a type-parameter binder (`sort T = ?`, `sort ?T`, `sort [T]`, `sort [F] { … }`) | **refused** — a constructor and a type parameter are the type's identity, and identity is declared once (§5.2, §6.3) |
| a sort-level `requires` | **refused** — a requirement constrains every CALLER of the type's operations, and an entry may not add an obligation to a type's users. The qualified call `Spec.op(x)` needs no clause |
| a `rule`, a `rule { … }` block, any `fact`, any `constraint` | **refused** — the search over rules is not monotone, so a clause added here can falsify a statement already proved. Facts are rules, so the ban reaches them. Every spec claim an entry can make is written `provides Spec[…]` — including one whose carrier is some OTHER sort, which is a witness claim and so genuinely about this sort (it supplies the dictionary). What the ban costs is only the `fact` SPELLING of those claims, not the claims; `fact Spec[Carrier]` one level out remains available and is the only spelling at an address no type occupies |

An **entry** is individuated by file: all `namespace X` text at one address
within one file is ONE secondary entry, and the same text in a second file is a
second one. A `proof` / `describe` target may be written bare or qualified against
the entry's own address (`describe Rec.g` inside `namespace Rec`); a nested sort's
member is another entry's, that sort being the main entry of its own type.

**Only what the entry declares at its OWN address is classified.** A dotted
declaration name declares into the namespace its prefix names — `operation
Inner.helper` in a secondary entry to `Rec` declares `Rec.Inner.helper`, a member
of the ordinary namespace `Rec.Inner` — so nothing above reaches it, and the
dotted spelling and the nested-`namespace` spelling of one declaration get one
verdict. The exception is a dotted `sort <p>.T = ?`, which still registers `T` as
a type parameter of the enclosing sort and so stays refused.

The rule ban is wider than intended and deliberately so: a rule that *introduces*
a fresh head owned by one entry is sound, but deciding "introduces" needs a head
binding that does not depend on declaration order, which §5.3 does not yet
guarantee.

**A `provides` clause names its PROVIDER by WHERE it is written, and its CARRIER
by its bindings** — two questions, and the provision records both (WI-1069). The
provider is the enclosing sort, or a secondary entry at that sort's address; it
is whose member set becomes the dictionary. The carrier is the value bound to the
spec's **carrier parameter** (which parameter that is, the next paragraph
settles), and it is what the provision dispatches at. Where the two coincide the
clause is an ordinary
self-provision (`sort Set provides Eq[T = Set]`). Where they differ it is a
**witness** — `sort ListOrd provides Ord[T = List[T = E]]` says `ListOrd`
supplies the `Ord` dictionary *for* `List` — which is the shape proposal 058
§3.6's defaults, `DefaultProvider` and witness dispatch are all built on. One
owner decides this for every reader (`provision_carrier_binding` /
`witness_dispatch_carrier_value`), so the load checks, the coherence grouping and
dispatch cannot disagree about what a witness is.

**`requires` and `provides` are BOTH chain entries, and they differ only in where the
dictionary comes from** (WI-1110). `requires A[T]` says the `A` dictionary is **passed
in** — an inbound slot the caller fills. A **spec's** `provides A[T]` says it is **built
from self**: "hold one of me and you can obtain an `A`", which is what `B <: A` means
operationally. Both put a slot in the sort's dictionary chain, both lend the target's
names to the sort's scope (§8.6), and both are discharged by resolving the spec at the
goal's bindings; the difference is that a `provides` slot is answered by the provider's
own **derived** row rather than by the caller. So a spec that forwards writes ONE clause,
not a `requires` beside a `provides` — `Ord provides WeakOrd[T = T]` is the whole of
`Ord`, and `WeakOrd`'s requirements reach the carrier through it.

**A CARRIER's `provides` and a SPEC's are two clauses with one keyword.** A carrier's is
a fact about the world (`Int64 provides Ord[T = Int64]`, `Set provides Eq[T = Set]`,
`Stream provides Iterable[C = Stream, …]`) and belongs in the searchable provider
relation. A spec's is a **conversion** and belongs only in the chain: nothing has type
`Ord`, so offering `Ord` as a candidate answer to a `WeakOrd` goal can never resolve —
it merely adds a candidate that the cycle detector must reject, on every ordering goal in
every program, and closes a cycle if the same edge is also written `requires`. The two
are told apart by the row: a provision is a conversion when it is a **parameter
forwarding** — every binding sends a target parameter to one of the subject's own type
parameters — **and** the target is a constraint on something rather than a thing in its
own right **and** the subject supplies none of the target's operations. All three are
needed. A **parametric witness** (`sort AnyM { sort E = ?; provides Monoid[T = E];
operation combine(a: E, b: E) … }`) is a forwarding by shape and *is* a dictionary,
because it carries the operations. A **self-representing** target is a thing rather than
a constraint, so `LogicalStream provides Stream[T = T, E = E]` is the membership claim "a
LogicalStream is a Stream" and value-directed dispatch reaches `Stream.splitFirst` on a
`Relation` through it. And a target that *does* name a carrier parameter (the next
paragraph settles which) must have it among the forwarded ones — a row forwarding only
the element parameters says nothing about the carrier and converts nothing.

**The forwarding need not be name-for-name** (WI-1111). `provides Sp[X = A]` renames and
`provides Sp[X = B, Y = A]` permutes; both say exactly what `provides Sp[X = X]` says,
written with different letters, and the derived row **translates** the carrier's bindings
through the map rather than copying them. A binding to a **concrete** sort is not a
forwarding and translating nothing is what makes it a claim about the world.

**A derived row is a conversion when the edge it was derived through is one.** A tower
two conversions deep (`Top provides Mid[T = T]`, `Mid provides Low[T = T]`) materializes
`Top provides Low[T = T]`, whose carrier is itself a spec; it is not an answer to a `Low`
goal, because `Top` already holds a `Low` dictionary inside its `Mid` slot, and the
tower's real carriers get their own derived rows in the same pass.

**Which parameter is the carrier is read off the operations** (WI-1076), because
nothing in the surface language says: no keyword declares a sort to be a spec, or
a parameter to be its carrier. The rule as implemented is *the first declared type
parameter that some declared operation takes as a parameter* —
`Iterable.iterator(c: C)` makes `C` the carrier, and a provision's binding for it
is what that provision dispatches at. A spec **none** of whose operations takes any
of its type parameters has no carrier parameter, and its provisions record **the
provider** as their carrier: `Stream`'s operations all receive on `Stream` itself
and its `T` appears only in return and callback types, so `sort List provides
Stream[T, {}]` records `List`, and `List` `self_provides` `Stream`.

**"Takes" is the rule, not an approximation of one** (WI-1077). A narrower reading is
imaginable — whether an operation **receives on** a parameter rather than merely
**accepting** it — and the two part company in two shapes: a spec that takes its own
element somewhere (`Set.insert(s: Set, x: T)`, `Map.put(m: Map, key: K, value: V)`), and
a carrier-parameterized spec that declares its element *first* and accepts it
(`sort Holder { sort Element = ?; sort C = ?; operation has(c: C, e: Element) }`), where
the explicit `C = …` binding is discarded. In both, the earlier-declared *element*
answers and the provision is filed at it.

That is the language's answer and not a pending fix. Making it narrower requires the
surface to *say* which parameter is the carrier — a marker (`sort C = ? carrier`) or a
`spec` keyword — and neither is being added; inferring it from a wider operation shape
was tried and **refuses a program that loads**, because a spec may declare both a carrier
parameter and a self-receiving operation, and gating on self-representation throws its
explicit binding away. So where the reuse is *accidental*, the repair is the
**declaration**: `LogicalStream.pure` reused the sort's element for a value it merely
lifts and now takes its own (`pure[A](x: A) -> LogicalStream[A, {}]`). Where it is
*intended* — `insert` really does take the sort's element — the filing at the element is
what the rule says.

**An operation that lifts a value must relate its result to its ARGUMENT**, not to
the sort's parameter, and where one does not the repair is the declaration rather
than the inference. `LogicalStream.pure` read `pure(x: T) -> LogicalStream`,
reusing the sort's element parameter for a value it merely injects; written
`pure[A](x: A) -> LogicalStream[A, {}]` the ambiguity does not arise. The bare
return was losing information on its own account: by the expansion rule above it
means `LogicalStream[T = ?, E = ?]` with a *fresh* variable, so `pure(1)` produced
a stream whose element type was unconstrained and lifting an `Int64` into a
`String`-element stream was accepted (measured). Either spelling states the
relation — an operation type parameter (`pure[A](x: A)`) or a shared logical
variable (`pure(x: ?A) -> LogicalStream[?A, {}]`), the latter needing nothing
beyond §4.4.

**A NULLARY producer is the opposite case**: with no argument to relate to, a fresh
variable per use *is* the polymorphism and no parameter is wanted.
`List.empty() -> List` means `List[T = ?]`, and the same `empty()` serves
`List[T = Int64]` and `List[T = String]` in one program (measured). An operation
type parameter would be wrong here for the reason §5.6 gives — it is the caller's
to instantiate, and a call pinning it from nothing is the loud `got unconstrained`.
A bottom-typed result (`List[Nothing]`, leaning on `Covariant(sort: List, param:
T)`) would be the subsumption-based alternative; the kernel uses unification, which
needs no variance for this case.

Where a spec genuinely has no carrier parameter, **a witness for it cannot
exist**: dispatch is directed by the receiver value's own sort, there being no
parameter position that could name a carrier, so a sort claiming such a spec is
claiming to *be* one. Taking the first parameter unconditionally filed seven stdlib
provisions at the type variable `T` and left the defaults substrate (§3.6) with no
inferred row for any of them, while provider admissibility — which joins on
`SortProvidesInfo(sort_ref:)`, the provider, not the dispatch carrier — kept
working, which is why it stayed silent.

**Inside a sort body, `provides Spec[…]` and `fact Spec[…]` record the same
PROVISION** — both take the provider from the scope and the carrier from the
bindings, so neither can say something about a carrier the other cannot. They are
not the same *statement*, and the difference is what 058 §4's retirement of the
`fact` spelling actually costs. A fact is a rule with an empty body (§5.3), so it
also enters the rule index: the goal `Spec(T: ?q)` answers under the `fact`
spelling and not under `provides` (measured). One asymmetry runs the other way — a
conditional provision `provides Spec[…] :- goals` has no `fact` spelling. Outside a sort body the two
diverge on the provision as well: at an address no type occupies a `fact` still
derives its carrier from the bindings, while a `provides` clause has no provider
to be about and is refused. That is a divergence about the *provider*, not a
licence to omit the carrier — a `fact` at such an address that names **no carrier
the loader can read**, whether because nothing was written after the spec's name
or because what was written names no type, is refused too (WI-933/WI-1106, §6.3).
Both refusals are the same rule seen from two sides: a provision needs a provider
and a carrier, a namespace supplies neither, and what the text does not say the
loader will not guess.

**`provides` is the one spelling; the in-sort `fact` one is DEPRECATED and warns**
(WI-862, 058 §4). The loader raises a non-fatal `ProvisionFactSpelling` at each
remaining site, located, and the shipped tree carries none. The warning is scoped
to the arm above where the two spellings agree — a scope that NAMES A TYPE. At a
plain namespace or a file's root scope nothing is deprecated and nothing warns,
because `provides` is refused there: the namespace-level instance facts (058 §3.1)
keep the `fact` spelling permanently, and a deprecation there would advertise a
repair the next compile rejects. A `provides` clause is admitted inside a
proposal-038 `provides <Carrier> language <L> … end` binding block too, since that
block opens the carrier's scope and a spec claim in it is a provision of the
carrier; that is what gives the retirement a spelling to move the host bindings to.

*Migrating one is not always a pure rename, and the reason is the rule-index
asymmetry above.* Four readers keyed on the `fact` spelling alone — two of them the
pair of functions in the first bullet — each found by migrating the tree and measuring,
not by reading:

- `region_sorts` / `is_modifiable_sort` scanned raw `Modifiable[T = …]` facts, so
  `is_modifiable(Cell)` answered **false** — a wrong answer, not an error. Both now
  read either channel.
- Rust codegen rendered an in-sort claim as a supertrait bound from the `fact` arm
  only, silently dropping `trait NonMonotonicStore: Store`.
- A `requires` clause mixing a value precondition with a spec requirement
  (`requires neq(a, 0), lo: Ord[T = Int64]`) was classified by its `conjunction`
  head as wholly a value precondition and PROVED from Γ. It only ever passed because
  `fact Ord[T = Int64]` made the spec conjunct resolvable as an ordinary goal; the
  clause is split into conjuncts before classification now, which is what the
  paragraph above ("never proved from Γ") always said.

The standing rule for the remaining case: **if some rule resolves `Spec[…]` as a
GOAL, keep the fact and write the `provides` clause beside it** — the two are not
the same statement, and the deprecation is of the *spelling of a provision*, not of
the fact.

**A provision may mark itself the default: `default provides Spec[…]`** (WI-862,
058 §3.6/§4). One leading modifier, the `internal`/`public` pattern, desugaring in
the loader to the `DefaultProvider` row the defaults substrate already arbitrates —
so the inline mark and the by-reference `fact DefaultProvider(spec: …, provider: …)`
are ONE statement, deduplicated, and colliding marks are refused by the same
`one_default` check whichever spelling wrote them. The carrier is not written and
must not be: it is derived from this very provision, so a conditional provision's
mark lands at the carrier the provision wrote. `default` is a modifier in that one
position and stays an ordinary identifier everywhere else. The modifier set is
`default` alone — a modifier attaches where its relation's key lives, and `Coherent`
is keyed per SPEC, so its sugar belongs on the spec's own declaration and is not
admitted on a provision. This paragraph states the **spelling**; what a default
*means* at dispatch — at most one per carrier, `one_default`'s arbitration, and the
rung a bracket-less call takes — is §8.7 *Instance coherence*.

**A sort with constructors is a DATA sort, and both spellings read that**
(WI-407/WI-1106). Neither a `fact` nor a `provides` naming one records a provision:
nothing is-a a data sort. The rule holds of a **parametric** sort exactly as it
holds of a plain one, and the `provides` half asks it of the **provided spec**, not
of the enclosing provider — a provider with constructors is the ordinary concrete
carrier, so that is the one place the two predicates differ.

*What each does about it differs, and that is not an inconsistency.* A `fact` is
**classified**: `fact Colour[…]` naming a data sort asserts a data instance, a
second reading a `provides` clause does not have, so the provision is simply not
among its meanings. A `provides` clause is a provision claim and nothing else, so
one naming a data sort is **refused at load**, naming the spec, the provider it
would have let widen, and both repairs. The consequence is worth knowing: a
sort-body `fact <DataSort>` that the author meant as an is-a reports nothing at
its own line and fails at the use site, and reaching for `provides` is what says
why. Examples: `fact Polynom[Int64]` says the
instantiation is well-formed, not that `Int64` is a polynomial, and `fact
Box(value: Other)` constructs a box, not an is-a. Both filed a provider edge until
the rule was applied whole — the second one changing an upcast's verdict, since a
bogus edge admits the widening and the refusal that follows is then about
something else. The **written surface** does not decide this and cannot: `[…]`
applies types and `(…)` constructs, but a data `fact` is ordinarily written with
brackets, so brackets carry no claim of provision. What follows is worth stating,
because it is what makes a refusal possible rather than a heuristic: since a
constructor-less sort cannot be constructed, *every* `fact` that survives this
rule is a provision claim, and one whose carrier cannot be read is malformed
rather than ambiguous.

**A declaration may not capture a name it does not override** (proposal 059 R4
clause 3; `check_name_captures`, `kb/load.rs`). A name can already mean something
in a sort's scope without being a member of it, and a declaration taking that
name silently repoints every unedited body that was reading it: measured, a body
calling a bare `f(…)` that resolves through `import lib.f` answers `1`, and a
declaration of `f` in the sort's scope makes the same text answer `2`. The load
is refused, naming the capturing declaration's line and what the name meant.

- **Over the whole sort SCOPE**, main entry and secondary entries alike — the
  flip is identical for both spellings, so this is not a rule about entries.
  Nothing here reaches an *ordinary* namespace, one at an address no type
  occupies.
- **The captured name need not have been declared.** A predicate a **rule head**
  introduced (§8.6: a head functor is resolved, not declared) is a name a member
  of a sort in that namespace may capture through the enclosing parent, with no
  `import` anywhere — so `sort Vec3 { operation vec_add(a, b) }` beside a
  namespace-level `rule vec_add(?a, ?b, ?c)` is refused, in either text order.
  This is the rule that decides whether a namespace-level rule and a sort member
  may share one short name: they may not. Because the check is asked only of
  declarations in a **sort** scope, it is always the member that is named as the
  capturing side; the rule is named by one of its clauses.
- **Over every declaration category that can win lookup**: an `operation`, a
  `const`, and a nested type (a `sort`/`enum` with a body, or an alias
  `sort A = T`). A `const` captures without ever joining the dispatch surface,
  and a nested type captures the very type a receiver then dispatches against —
  so the rule is stated over *lookup*, not over membership. A binder and an
  entity variant are identity, not additions, and never capture.
- **Excluded when the declaring sort `provides` or `requires` the sort that owns
  the captured name** — a relation, never the route the name was reached by, and
  transitive on both legs. `provides` is how a sort implements what it provides.
  `requires` is excluded because the two operations may be genuine refinements
  (§8.7's `requires`-refinement tie-break) and because a requirement bound to a
  *type parameter* — `sort Polynom { requires Ring[R]; operation add(…) }` — is
  about the element type, not about the declaring sort. A requires-shadow that is
  merely suspicious is WI-346's advisory warning, not this refusal.
- **Not asked of a name reached only through §8.6's variant exposure**, nor of a
  captured **namespace**: see §8.6 and §8.7's *members and constructors are named
  per type*. An `import` anywhere along the path spends the first exemption — a
  name an import put in view is one the author asked for.
- **Asked once per file that has text at the address**, not over their union: an
  import resolves only in the file that wrote it (§8.6), so a name may have meant
  something else for one file and nothing at all for another. The union reading
  refuses programs no file could have misread.

### 5.2 Sort

A type declaration. Sort has three forms — **unspecified** (declared, carrier unknown), **type alias** (equated to another type), and **sort with body** (inhabitants enumerated as a closed ADT, or algebra with operations/rules):

Design records: [proposal 002](proposals/002-arrow-sorts.md) for the sort/arrow
parameter lineage and [proposal 045](proposals/045-effect-sets-and-expressions.md)
for effect-row binders.

```
Sort ::= DescriptionBlock*
           [Visibility] 'sort' Name '=' VariableTerm              -- unspecified
           [MetaBlock]
       | DescriptionBlock*
           [Visibility] 'sort' Name '=' Type                      -- type alias
           [MetaBlock]
       | DescriptionBlock*
           [Visibility] 'sort' Name [SortTypeParamList]            -- sort with body
           Body[SortContent*]
           [MetaBlock]
       | SortVarBinder | SortBracketBinder

SortTypeParamList ::= '[' SortTypeParam (',' SortTypeParam)* ']'
SortTypeParam     ::= Identifier [SortTypeParamList]               -- `A`, `F[T]`
SortVarBinder     ::= DescriptionBlock* [Visibility]
                      'sort' Var [SortBinderBody] [MetaBlock]
SortBracketBinder ::= DescriptionBlock* [Visibility]
                      'sort' '[' Identifier ']' [SortBinderBody] [MetaBlock]
SortBinderBody    ::= '{' (SortVarBinder | SortBracketBinder)+ '}'

EffectsSortItem ::= DescriptionBlock* [Visibility]
                    'effects' Name '=' Type [MetaBlock]

Enum ::= DescriptionBlock* [Visibility] 'enum' Name
         Body[EnumContent*] [MetaBlock]

Constructor ::= 'entity' Name ['(' FieldList ')']            -- variant/constructor
FieldList   ::= Field (',' Field)*
Field       ::= Name ':' Type
```

The enclosing-list form (`sort CpsMonad[F[T], A] { ... }`) and the
per-statement forms (`sort ?A`, `sort [A]`) declare the same non-rigid sort type
parameters (proposal 002, WI-451/WI-454).  A structured per-statement binder has
a brace-only, non-empty body containing binders only, recursively; it cannot
silently acquire operations, entities, or facts.  Sort type-parameter defaults
are not part of this surface.

`effects E = ?` is the effect-row-specific spelling of such a sort parameter;
`effects E = Row` binds it to a row.  It lowers to the corresponding sort
declaration plus the effects-runtime requirement described in §5.5 (proposal
045 / WI-320).

`enum` is the explicit closed-ADT-facing spelling implemented by the grammar.
Its contents are the constructor/specification subset admitted by
`EnumContent`; like a sort with constructors it records one sort identity and
the listed entity variants.  The spelling has no separately numbered proposal,
so its implementation provenance is the grammar and loader rather than a
proposal document.

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

These illustrate the `<=>` equational-rule *mechanism*. In the current prelude such per-constructor equations for an operation with a body (`length`, `append`, `contains`) are **not** hand-written: WI-580 makes the operation body the single source of truth and derives its equational and relational views from it on demand (the SLD one-step body-unfold; see docs/design/abstract-interpreter-and-rules.md §3.3). Hand-written `<=>` rules survive for genuine standalone equations (`neq(?a, ?b) <=> not(eq(?a, ?b))`, carrier `eq` overrides).

**A `Bool`-valued expression in goal position is a CONDITION** (WI-20260822-J38JE item 1): it evaluates, and the goal succeeds iff the value is `true`. The reading is **type-directed** — it follows from the term denoting a truth value, not from a list of admitted shapes — so every spelling of a boolean expression means the same thing wherever a goal is expected.

| in goal position | reads as |
|---|---|
| a name carrying clauses — rule, fact, entity | ordinary **resolution** |
| `not` / `or` | the resolver **primitives** (§6.6) — see below |
| a **`Bool`-valued expression**: `true` / `false`, a `Bool` operation at its declared arity, a `Bool` dot projection, a variable bound to one | an evaluated **condition**, `eq(expr, true)` |
| an **operation at arity + 1** | its **functional-relation** view (below) |
| a resolver **builtin** or scoping marker (`unify`, `find_dictionary`, `forall_impl`, …) | that builtin's own goal semantics |
| a **non-`Bool`** term that is not a relation — a non-`Bool` operation, a non-boolean constant | a **load error**: it denotes no truth, so it can never match |

`not` and `or` are not an exception to the condition reading, and §6.6 is not in tension with it. Those two names at a goal position resolve to the **resolver primitives** before anything is typed, so they never become `Bool` expressions there at all — the redirection is a rule about *names*, applied first. `and` has no primitive to be redirected to, which is why §6.6 names the comma; a genuine `Bool`-valued `and` of two `Bool` **values** is a condition like any other, and the refusal of `a & b` narrows to the case its measurement was about — operands that are **goals**, and so not values.

"A goal the resolver expects" means one it **proves**: the body's atoms, a `not` negand, an `or` / `push_choice` branch, a bounded quantifier's body, a discharge's **consequent**. A discharge's **antecedents** are not among them — a hypothesis *declares* the predicate the consequent proves against, so the slot binds rather than proves, and nothing above reads it.

**What the rule-body evaluator cannot yet reduce, it cannot yet condition on.** The reading above is the design; two `Bool` expressions do not get it *yet*, and for one reason — a rule body reduces a **bodied** operation and a resolver **builtin**, and nothing else. Both are load-time gaps, not readings, and both are measured:

* a **`const` reference** (`:- flag`) answers 0, and so does the spelled-out `:- flag = true` — with `const nn: Int64 = 5`, `:- Int64.gt(nn, 3)` answers 0 where `:- Int64.gt(5, 3)` answers 1, while the *same* reference inside an operation body folds (**WI-20260822-NDG34**).
* a **host-backed operation** — `Bool.and` / `Bool.or` / `Bool.not` are declared body-less and backed by a host builtin (`prelude/bool.anthill`), and their `<=>` laws are untagged, so they are inert in SLD. `Bool.and(true, true) = true` answers 0 in a rule body and 1 in an operation body (**WI-20260822-ZJZS7**). Until it reduces, `a & b` in a goal stays **refused** rather than silently answering nothing — a located error is the honest state of a reading the evaluator cannot yet deliver.

A **`Bool`-returning operation may be used directly as a rule-body goal** (WI-583): `:- valid(?x)` (with `valid: T -> Bool`) resolves as its relational view `eq(valid(?x), true)` — the operation reduces, `true` ⇒ the goal succeeds, `false` ⇒ it fails, an under-determined argument ⇒ it suspends as a residual (never NAF-decided). This is *position-directed*, like the boolean operators (§6.6): the gating applies only in **goal** position and at the operation's declared arity; the functional-relation form `f(args, result)` (one extra argument, the result column — e.g. `status(?fs, ?p, FileStatus(…))`) is the separate **arity+1** view described below, and a `Bool` operation in **value** position is just a value. A **non-`Bool`** operation in goal position has no such reading, so it is a **load error**, not a silently-failed relation lookup.

**The functional-relation view: `f(a₁…aₙ, ?r)` (WI-938).** A goal at **arity + 1** on a *rule-less bodied* operation of arity n is that operation's relational view, with the result as the last positional column. It resolves to **`unify(f(a₁…aₙ), ?r)`** — the call is reduced through the body (the SLD→eval bridge) and the result is **bound**. So the relation *generates*: `vec_add(a, b, ?c)` answers one definite solution with `?c = Vec3(11.0, 22.0, 33.0)`.

`unify`, **not `eq`** — this paragraph previously said `≡ eq(f(args), result)`, which described a form that could never answer. `eq` is a semantic equality *test* that never binds (§8.3), so an unbound `?r` can only delay; measured, such a goal residualized with `?r` free. The binding view is the useful one and is what the deleted `anthill.geometry.vec_add/3` clauses were a hand-written stand-in for.

Eligibility mirrors the `Bool` view above and each clause is load-bearing: not a builtin; **has a runnable body** (the view is derived from it — a body-less spec op dispatches instead, WI-573); **effect-free** (an effectful body is not a relation); and **rule-less** — a hand-written clause of the same functor WINS while both exist (design §3.3 precedence), the same rule that governs the `Bool` view and the WI-669 prover seam. Named arguments are not this shape: the result column is positional and last.

The routing fires only once the call actually **reduces**. `unify` is structural and never dispatches (proposal 049), so an unreduced call would bind `?r` to the call term itself — a definite-looking wrong answer. A call whose arguments are not ground therefore falls through to ordinary candidate selection (no answer) rather than binding; making that case *delay* instead is open follow-up work.

**Requires declaration** — a standalone `requires` in a sort or namespace body declares a sort-level constraint: the enclosing scope depends on another algebraic spec. This is distinct from an operation-level `requires` clause, which is scoped to the one operation — a *precondition* when it names a boolean condition, and an *op-scoped requirement* when it names a spec (see below).

```
RequiresDecl ::= 'requires' [Identifier ':'] Type
```

An optional binder names the requirement slot (`requires O: Ord[T]`, proposal
058 / WI-840).  A named slot is a type parameter of the enclosing sort and is
therefore addressable in type/selection position; an anonymous slot remains a
constraint that is solved rather than incorporated into the sort's identity.

Because a named slot is a type parameter, **omitting it means two different
things and they are decided per call site** (proposal 058 §3.4, WI-1094).  Where
nothing anywhere has bound it — a construction such as
`SortedSet.empty[T = Int64]()` — the dispatch ladder answers and the answer is
**bound into the parameter**, so it is part of the constructed value's type and
every later bracket-less call reads it back.  Where a *signature* omitted it
(`size(s: SortedSet[T = String])`), the slot is universally quantified: the
argument's provider was chosen elsewhere and no dictionary travels with a value,
so a call that dispatches through the slot is **refused**, regardless of how many
providers are in scope.  The repair is to name the slot on the enclosing
declaration and write that name in the parameter's type
(`first(s: SortedSet[T = E, O = OE])` under `requires OE: Ord[E]`), which is what
makes the forwarded dictionary the value's own.

A **default** (§8.7) reaches a named slot exactly where the ladder above does, and the
two readings split it the same way (WI-861, narrowed by WI-1094).  Where the binder is
*unbound anywhere* — the construction case — the ladder is consulted **in full**, a
default included, and its answer is written into the parameter: that is not a default
standing in for the slot, it is the slot being decided for the first time, by the one
mechanism that decides it.  Where a **signature** omitted it the call is refused before
any default is asked for, and a default would be the wrong answer in any case, for the
reason the refusal exists: a default fills *silence*, and this is not silence — the
value flowing in already chose, and its choice is part of its type, so answering here
would override a decision made elsewhere.  Measured, letting a default answer there
reads a `SortedSet[T = Int64, O = Descending]` back in **ascending** order.  One place
besides holds the rung back, and it is the only one left: *inside* a resolution tree,
at the chosen provider's **own** named slots (`LexFst requires OA: Ord[A]`), where
there is no call site to infer at and nothing has been said at any level.

The `requires` declaration takes a type expression — either a simple sort name or a parameterized sort with bindings:

```
sort Ord {
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

**Operation-level `requires` over a spec** is an *op-scoped requirement*, not a precondition: when the clause names an algebraic spec, it declares that **this operation** — and not its sort — depends on that spec (`List.contains requires Eq[T]`, so a `List[NonEq]` still dispatches `IndexedSeq.nth`). It may name the operation's **own** type parameters as well as its enclosing sort's — one list, as for a call-site bracket key (§5.2), and renaming them does not change what the clause means. Its effect is to **license** the spec's operations over those parameters in the operation's body: the call stays the spec op and its implementation is chosen at evaluation from the argument's own carrier (value-directed dispatch).

An op-scoped requirement **does** occupy frame slots of its own, placed after its parent sort's (WI-822). A call site fills them from the call's own substitution, exactly as it fills the sort's; the operation's slots are the *operation's*, so a sibling member of the same sort neither inherits them nor is inherited from. **A body reads them at the same point it reads its sort's** (WI-1091): where the call it writes is licensed by a `requires` clause in scope, the dictionary that clause names is what answers it — and which declaration carries the clause, the sort or the operation, changes nothing an author can observe. Moving a `requires` from a sort to an operation narrows *who* is obliged to supply it, never how the body is served.

That reading is what makes a call-site `[Spec = Witness]` decide on either spelling: the supply honours the bracket, and the body reads the supply. It was not always so — while an op-scoped call was served by value-directed dispatch, which never sees a selection, such a bracket had to be refused rather than accepted and silently dropped (a program that loaded and computed the answer of the provider the author had not named). Two spellings of one program disagreeing is what identified the placement as the defect rather than the refusal.

Value-directed dispatch still serves every call no `requires` in scope licenses — an abstract-spec receiver, a carrier only the runtime value names — and that is the ordinary case for a spec op called without such a clause. What it no longer does is answer a call whose licence names a dictionary.

A slot the call site could not fill is simply **absent**, and a body that reads an absent slot fails at the read naming the running operation and the slots its frame does hold — never on a dictionary that could not be justified. "Has an unpinnable chain" and "needs it" are different questions and only the body answers the second, so a body that ignores such a slot runs unchanged. **A tie is the one absence that is a verdict rather than a gap**: two providers coexist by design (§4.3's nameability rule), so no earlier pass will report one, and the route that finds it must. Where a call site pins the element, that is a load refusal naming the requirement and both providers; where there is none — a host entry, a rule body — it is raised when the dictionary is built. Both spellings of the program are refused the same way and at the same moment.

**Requirement supply at a call site is checked at load** (WI-828). A cross-sort call to (or function-value use of) an operation whose parent sort carries `requires` must be able to supply each requirement: either *constructed* from a provider fact at the call's instantiation, or *forwarded* from a covering `requires` of the enclosing scope whose element denotes the **same** type parameter under the call-site substitution (σ-class agreement, WI-821 — a wildcard cover over a *different* parameter is no cover). A cover must answer for **every** element the requirement names, so an enclosing entry that names *fewer* elements covers nothing (WI-826): the bracket-less `requires Desc` form binds no element at all, and therefore never forwards a dictionary to a requirement that has one — the call constructs instead. The converse is *not* symmetric, and deliberately so: a **requirement** that names no element (the callee's own bracket-less `requires Desc`) is the callee's wildcard — it says nothing about which instantiation it wants, so any enclosing `requires` of that spec supplies it. Naming fewer elements weakens a *supply* and widens a *demand*. (Bracket-less `requires` remains the ordinary spelling for a spec with no parameters, where there is nothing to name.) Omitting *some* bindings of a parameterized spec is not a middle ground: `requires Pair[P = T]` fills the unwritten `Q` with the spec's own parameter, an element nothing constrains, which is the load error below. A requirement element left **genuinely unconstrained** at the call (nothing in the call pins it — e.g. an element appearing only in the callee's return type, called with nothing that determines it) is a **load-time error** naming the requirement, the unconstrained element, any σ-refused covering entry, and the construction outcome. There is no fallback semantics: silently instantiating the element from the caller's (different) parameter was the pre-WI-821 unsoundness, and deferring the failure to evaluation would be a clean load that crashes at run time. The sort-level spelling (`sort F = ?` plus `requires Spec[…, F]` on the enclosing sort) carries this verdict too, and until WI-945 it carried none — it loaded clean and raised at evaluation, the one outcome this paragraph forbids. It is not the *same* check as the operation-level one, and the difference is real rather than an implementation accident: an operation's own undetermined type parameter is rejected outright — the caller cannot recover the return type, which is the loud `expected a type for 'F', got unconstrained` (WI-270; §8.1 reads the same asymmetry at a return position) — whereas a sort parameter left open is rejected only where the requirement it feeds is actually owed. **The error is owed where the call's compile-built dictionary is its only supply** (WI-945). That excludes two calls, neither by granting them a fallback: a goal in a *rule body*, whose dictionaries SLD resolution builds from the concrete argument values at resolve time and suspends over when it cannot — an element unpinned at load is the ordinary case there, every goal argument being a variable; and a call whose callee never reads the slot, because "has an unsuppliable requirement" and "needs it" are different questions and only the body answers the second (the same distinction §5.3's op-scoped slots draw). "Reads the slot" counts **five** ways, and the check enforces all five (**WI-1095**): the body **defers** to it; it **inherits** — a same-sort call the typer built no dictionary for takes the caller's frame whole, so delegating to a sibling that reads the slot does not evade the refusal; it **forwards** through the callee's parent-bundle dictionary, or through an **op-scoped** one, a call the typer *did* build a dictionary for having one of its slots be a read of this frame rather than a construction; or it **etas** — a bare reference lifted to a function value, whose dictionary is captured in this frame at the mint and travels with the value. A dictionary is not self-contained, so "this call got one" does not mean "it needs nothing from me"; and an eta never inherits however same-sort it is, since the function value escapes to a foreign apply frame. The count is stated because it has twice been short — each time by a channel that loaded clean and raised at evaluation, the outcome this paragraph forbids — so the enumeration is now the call classification's own, form for form, and a new call form is a decision to make rather than an omission to discover.

**A requirement whose carrier the call names, and which that carrier does not provide, is a load error** (WI-1102, proposal 058 §3.10 — the *use-site discharge*). Where the call site pins **every** type parameter of the requirement to a concrete type, the requirement is a question with an answer: the goal `Spec[T = Carrier]` either resolves — against a provision row, an instance fact, or the enclosing scope's own `requires` read as an assumption — or it does not, and *providing nothing at all is not an accepting state*. The refusal names the call, the carrier sort, and the provision it lacks, so the repair is the line the author must write. This is the same verdict on either spelling of the requirement (its parent sort's or the operation's own), for the reason §5.3 gives.

It is **not** owed where the requirement is not that question, and the exclusions are the ones the paragraph above already draws, plus one of its own: a type parameter left **abstract** at the call (the caller's chain or a later instantiation may still supply it); a goal in a **rule body** (dictionaries are built from the concrete argument values at resolve time); a callee that never **reads** the slot; and a spec operation that resolves **structurally** — a comparison or equality registered as a resolver builtin never consults an instance, so no provision would change its outcome and its absence is not a defect. A refusal withheld here leaves the program exactly the behaviour it had, the evaluation-time raise included.

**Standalone `entity`** is syntactic sugar for a single-constructor sort (see §6.3):

```
entity Account(id: AccountId, balance: Money)
-- desugars to: sort Account { entity Account(id: AccountId, balance: Money) }
```

### 5.3 Rule

**THE knowledge primitive.** A Horn clause. All knowledge in the KB is expressed as rules. Two important special cases are given syntactic sugar (see §6):

Relevant design records: [proposal 032](proposals/032-symmetric-rule-arrows.md),
[proposal 033.1](proposals/033.1-cut-and-the-barrier-mechanism.md), and
[proposal 060](proposals/060-clause-level-requirements-and-typed-heads.md).

- `fact X` = a clause with the empty body — `X :- true` (§6.1)
- `constraint I :- G` = integrity-declaration sugar (the current executable
  subset and ordinary-denial boundary are in §6.2)

**No body ⇒ DECLARES; a body ⇒ asserts (proposal 061).** A rule with no body
**declares** its head's predicate and asserts nothing; it has no clauses. This removes
`rule`'s exception: `operation f(…) -> R` declares and `= body` defines, `const N: T`
declares and `= expr` defines, and `rule` was the sole construct whose body-less form
*asserted* — only because §6.1's desugaring had spent that form on `fact`. Moving one
`:- true` into that desugaring gives all four constructs one reading.

| written | reads as |
|---|---|
| `rule p(?x, ?y)` | **DECLARES** `p` — asserts nothing, has no clauses |
| `rule p(?x, ?y) :- G` | a **clause** of `p` |
| `rule p(?x, ?y) :- true` | a **clause** of `p` with the empty body — what `fact` desugars to |
| `fact p("a", "b")` | an **assertion** (§6.1) |
| `rule lhs <=> rhs` | a **defining equation** — untouched (below, WI-881) |

The arguments carry no part of the distinction: `rule p(?x, ?y)` and `rule p(1, 2)` are
read the same way, because it is the **body** that says whether the rule asserts. `true`
is the **empty conjunction**, so `:- true` is the explicit spelling of the empty body and
produces exactly the clause `fact` produces — which is what a site needs when it wants an
assertion *and* a citation label, since `fact` has no label form (§6.1).

**A boolean constant in GOAL position is a search: `true` succeeds, `false` fails**
(WI-20260822-J38JE). `rule p(1) :- false` is legal and its clause is **dead** — a
deliberate way to disable one — and the reading holds at *every* goal position, not only
at the top of a body: `not(true)` fails and `q | true` succeeds even where `q` does not.
This is §6.6's own rule for the boolean operators ("at every GOAL position: the body's
atoms, and the goal slots of the connectives above them") applied to their constants.
Both readings agree at the top of a body, where the `:- true` above has already been
erased at load — that erasure is what keeps the body EMPTY, which is what makes `fact H`
and `rule H :- true` one clause rather than two with equal answers. Every OTHER
constant in goal position is a **load error** (item 4): `:- 42`, `:- "hello"` and `:- 1.5` name no
predicate, so the clause can never fire — and before the refusal they loaded with no word
said, indistinguishable from a deliberate `:- false`, while `:- not(42)` answered *one*.
WI-1034's "goal names nothing" refusal cannot reach them, because it tests a goal's
FUNCTOR and a constant has none; the refusal therefore sits with WI-583's non-`Bool`
operation error, which answers the same question — *is this term readable as a goal at
all?* — and the error names the constant, its position, and both repairs (an argument
`p(42)` or a comparison `?x = 42`; `false` if the clause is meant to be dead).

**Equations are not this construct.** An equational rule (`lhs <=> rhs`) extends
unification; its clauses are indexed under the connective, not under its subject, so the
subject owns no clauses and there is no predicate to declare (§8.7, WI-898). A body-less
equational head therefore keeps defining, and `[simp]`'s enablement is untouched. The two
shapes are told apart by the head's functor — a minted equality-family connective is an
equation, anything else is a predicate head — which is the reader §8.3's own refusals
already run.

**A body-less rule that can declare nothing is refused.** A `⊥` denial names no
predicate, a multi-head rule names several, and a **qualified** or desugared head
introduces no name at all (§8.6). Two more shapes declare nothing for a different reason:
a name **another construct already declares in that scope** (an `operation`, a `sort`, an
entity) — the declaration merges into it and adds nothing, which is the no-op 059 R4
clause 3 refuses everywhere else — and a head in a position the defining pass does not
reach, which today is the interior of a `provides … language … end` block. Each would
assert nothing and declare nothing, so each is a located load error rather than a silent
drop; write a body (`:- true` asserts it, and against an operation that is a lemma about
it — §8.6) or spell it as a `fact`. A **label, a description block, a `[…]` tag, a `[t]`
type-variable introducer or a typed column `?x: T`** on a declaration is refused for the
same reason: a declaration stores no clause, so there is nothing for a citation handle to
cite, nothing for a tag to govern, no body goal to bound a `[t]` (§5.3's `:- Spec[t]`),
and no rewrite for a typed-pattern bound to be enforced on. 060's reading of a body-less
head's `?x: T` as the **column's type** is the intended future of that last one
(WI-742); it is not delivered, so the ascription is refused rather than accepted and
ignored.

**A declaration carries no arity claim.** Clauses of one predicate may still differ in
arity, exactly as today; whether they should is a separate question
(WI-20260821-6WVJB / proposal 061 §"One arity per predicate"), and a declaration states
its head's arity without enforcing it.

```
Rule ::= DescriptionBlock*
           'rule' [Name ':'] RuleShape
           [MetaBlock]

RuleShape   ::= Heads ':-' RuleBody
              | RuleBody '-:' Heads
              | Heads
Heads       ::= Goal (',' Goal)*           -- one or more heads (multi-head: conjunctive sugar)
              | '⊥'                        -- bottom (for denials; cannot mix with positive heads)
RuleBody    ::= Goal (',' Goal)*           -- premises (conjunction)
Goal        ::= Cut | LetBinding | Term
Cut         ::= '!'
LetBinding  ::= 'let' VariableTerm '=' Term
RestArg     ::= '...' VariableTerm         -- variadic capture (§11 CallArg); legal ONLY as
                                           --   the last positional argument of a [simp]
                                           --   equation head's LHS — see below
```

A leading `DescriptionBlock` requires the optional `Name` label to be present. The
grammar retains the unlabeled combination only to produce the precise §4.1 refusal.
The label is the description target (and, for a multi-head rule, remains one target
regardless of how many stored clauses the sugar produces).

**Single arrow per rule.** `:-` and `-:` are mirror surface forms of the same implication operator (proposal 032). Exactly one of them appears per rule (or neither, for a bare-head fact). The dual-arrow form `head :- body -: conclusion` is **not** part of the grammar — under the unified design the head IS the rule's conclusion, so a separate `-:` slot would duplicate it. `:-` reads as "if" (head if body); `-:` reads as "then" (body therefore head). They produce the same internal Horn clause; choice is purely stylistic.

The grammar deliberately shares `Goal` between heads and bodies so the two
comma lists do not form competing parses.  `let` and cut are nevertheless
body-only constructs: conversion rejects either in a head, as well as an
outermost literal (§4.1), with a located diagnostic.

**Cut (`!`, proposal 033.1 / WI-568).** A standalone `!` body goal commits the
current rule invocation: once reached, alternatives created since that
invocation's choice-point barrier are pruned, while choice points belonging to
its callers remain available.  It is distinct from prefix negation (`!atom` or
`not atom`): the standalone token is control, the token with an operand builds a
negated goal.

**Clause-level requirement binding (`require[X]`, delivered subset of proposal
060 / WI-1040).** Two and only two source positions are interpreted:

```
rule p(?x, ?y) :- require[Eq[T]], eq(?x, ?y)
rule q(?x, ?d) :- ?d = require[Eq[T]], consume(?x, ?d)
```

The bare form brings the resolved dictionary into the clause for covered body
calls; the direct `?d = require[X]` form also exposes that same structural
dictionary as a clause variable.  The latter is a converter-recognized binding
form at the top level of a body goal—not a change to ordinary `=`, which remains
a semantic equality test (§8.3).  A nested occurrence such as
`consume(require[Eq[T]])` is refused rather than lifted or silently ignored.
Both forms lower before resolution to the existing `find_dictionary` relation
with an output slot, and the dictionary is an ordinary structural value in the
clause substitution.

This is deliberately only the delivered requirement-binding half of proposal
060. Typed head syntax is **partially** implemented: the typed-pattern form on
a `[simp]`/`[unfold]` equation is implemented below, while accepting the same
annotation on a plain relational rule (including the parameter spelling
`p(x: T)`) is not. WI-742 owns that relational `domain(x, T)` lowering, and
WI-743 owns finite/user-defined domain generation. Do not confuse proposal 060
with the unrelated work item WI-060.

**Forms:**

```
-- Derivation rule (Horn), backward and forward forms:
rule ancestor(?X, ?Z) :- parent(?X, ?Y), ancestor(?Y, ?Z)
rule parent(?X, ?Y), ancestor(?Y, ?Z) -: ancestor(?X, ?Z)

-- Ground assertion: a clause with the EMPTY BODY. `fact` is its short spelling;
-- a body-less `rule parent("alice", "bob")` DECLARES the predicate instead (§5.3).
rule parent("alice", "bob") :- true
fact parent("alice", "bob")

-- Predicate declaration (proposal 061): no body, asserts nothing
rule ancestor(?X, ?Z)

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

**A head is an atom.** Each head in a `rule`'s head list is a *conclusion* — an application, a name, or a connective term (`<=>`, `:-`-free relational forms) — or the denial `⊥`. A bare **literal** (`42`, `"s"`, `true`, `[…]`, `{…}`, `(…)`) is refused **when the file is converted** (parse time, not load — `convert_rule_heads`): it denotes a **value**, and a value is not a proposition. The same holds for a `fact`'s term, a fact being a rule with an empty body. Literals are legal *inside* a conclusion (`p(42)`, `f(?x) <=> 42`); only its own outermost shape is constrained. A `let` binding and a cut `!` are refused for the same reason — they are body goals, and heads and bodies share one grammar.

**A rule-introduced functor is scoped where it is written (WI-894).** A rule head that names something no enclosing scope defines *introduces* that name, and the name belongs to the scope the rule is **written in** — the sort when written inside a sort, the namespace when written at namespace level. This is the rule `operation`, `entity` and `const` already follow; a rule functor is not an exception to it. Consequently two sorts may each define a `pick` by their own laws, and each sort's calls reach its own; there is no global rule namespace for them to collapse into. The name a rule introduces is the **conclusion's own** functor, except for an equation (`lhs = rhs` / `lhs <=> rhs`), where the head functor is the *connective* and the introduced name is the **LHS head** — `rule ite(true, ?t, ?_) = ?t` introduces `ite`, never `eq`. An **equation is bodyless** (§8.3), so `f(?x) = ?y :- guard` is a predicate rule whose head names the connective, not a definition of `f`. A head is an equation because the **infix operator wrote it**, never because of how its functor is spelled (WI-948): `eq` and `unify` are the names the `=` / `<=>` desugar mints, but they are also ordinary identifiers, so a head written as a *call* — `rule eq(?a, ?b)` — is a 2-ary predicate head whose subject is itself. (`===`/`struct_eq` is *not* on that list at all — it is a test, not a defining connective, and a `===` head with no body goals is refused; WI-1090, above. It is still an infix connective for every question about the head's **shape**: a `[T]` introducer rides on its LHS operand exactly as on an equation's.) Reading a connective head as an equation when it is a written call instead makes its first **argument** the subject, which is both a wrong name to introduce and the wrong place to look for a head's `[T]` introducer. This settles *what the loader reads*, not whether such a rule runs: every connective spelling is reserved vocabulary, so the head **resolves** rather than declares (below), its clause joins the connective's own symbol, and it is inert at SLD — the silence WI-899 owns. Three shapes introduce nothing. A conclusion whose outermost form the parser *desugared* — `?x.m(?y)`, `?x.f`, `?a + ?b`, in either an equational or a predicate head — carries the desugar's functor, not the rule's. A **qualified** subject (`rule String.isEmpty(?s) <=> …`) *references* an existing name rather than introducing one. And a name that **already denotes something at that scope** is never captured, in an equational *or* a predicate head: `rule cons(?h, ?t) <=> ?h` states a law about `List.cons`, and minting a scope-local `cons` would silently repoint every bare `cons` in that scope at a different function (the same reason an `eq`/`unify` connective head never mints `<ns>.eq` — WI-530).

**What an introduced name denotes (WI-898).** The two head shapes introduce two different *kinds* of name, and only one of them is a relation. A **predicate** head's functor owns its clauses — they are indexed under it — so the name denotes a relation, and the citation forms run it. An **equation**'s subject owns none: the stored clause is headed by the `eq`/`unify` *connective*, so the name denotes a function *defined by rewriting*, with neither a relational nor a value reading of its own. A citation of it is answered by a `[simp]` clause firing before dispatch (§5.3) or it is **refused** — and the refusal names which failure it was, because they call for different repairs: defining equations that carry no `[simp]` tag and so can never fire, tagged clauses none of whose left-hand patterns matched the citation, or no live clause at all. Before WI-898 the two shapes shared one kind, so the relation reader answered for both: it found zero clauses under an equation functor and reported a name that resolved perfectly well as *unresolved*. Whether a name denotes a relation is decided by the **clause index**, not by the head shape alone — so a name a scope writes in **both** shapes is a relation whichever rule comes first: a predicate clause is indexed under it, and which rule sits higher in the file does not enter into it.

**A rule head functor is resolved, not declared (WI-896).** Whether a head *defines* a new predicate or *concludes about* an existing one is decided by **name resolution**, exactly as in any other position: the functor runs the ordinary ladder — enclosing scope, imports, then the implicit prelude / reserved kernel vocab — and the rule contributes a clause to whatever it lands on. Only when the ladder finds **nothing** does the rule introduce the name, scoped where it is written (above). So `rule bound: gte(?x, 3.0) :- gte(?x, 5.0)` is a lemma about `PartialOrd.gte` because `gte` *resolves*, and its unlabeled twin is the same lemma for the same reason. To introduce a name that already resolves, **declare** it — a local `operation gte(…)` is found before the fallback tier, and the rule then binds to that declaration.

**And an undeclared head declares AT THE SCOPE IT IS WRITTEN IN (WI-20260822-845G7).** "Only when the ladder finds nothing" once needed a *when*, because this was the one position whose own answers changed the table it reads: every other name is defined before any name is resolved (the WI-321 cross-file invariant), while a rule head was *introduced* during the same pass that decided it. Asked against the scanned prefix, textual order decided the program — measured, `rule p(1)` beside `sort Rec { rule p(2) }` loaded as **one** predicate with two clauses when the namespace-level rule was written first and as **two** predicates when it was written second, and the same pair across two files split on whichever file the loader reached first. WI-980 closed that by asking whether some scope this one can *see* already introduces the name, resolved through a non-monotone fixpoint over the finished program. 061 then made a predicate **declared** rather than discovered, and 845G7 measured what was left for the fixpoint to do: over the whole corpus and every test fixture, **234,078** head decisions, of which **233,917** were "introduce here", **161** were "join another scope's head" — every one of those in a fixture written to exercise the fixpoint — and **zero** in the shipped corpus. It computed a constant, so it is gone, and the *when* dissolves with it:

> A rule head whose functor **resolves** is a clause of what it resolves to. One that resolves to **nothing** declares its predicate at the scope it is **written in** — never anywhere else. Nothing is asked about any other head, so no order can enter.

This reaches **every** head shape, an equation's subject included. 061 puts equations outside the *declaration* rule — their clauses index under the connective, so the subject owns none — but not outside this one: measured, exempting them silently split `zeq { rule f(true) <=> 1 [simp]; sort Rec { rule f(false) <=> 2 [simp] } }` into two symbols where it had been one, which is the hazard the refusal below exists for, permitted for half the shapes.

**Two scopes that can see each other may not both introduce one name (845G7).** The rule above is total and order-free, but it makes a second scope's same-named head a **shadow** rather than a clause — a scope's own name beats what it imports or inherits, because `resolve_in_scope` reads `locals` and returns before consulting any import or parent. Measured with a paired control: `mA { import mB.*; rule p(1) :- true; rule usesp(?x) :- p(?x) }` beside `mB { import mA.*; rule p(2) :- true }` answers `usesp(1)`=1 and `usesp(2)`=**0**, while the same `mA` with no `p` of its own answers 0 and **1** — so the import works, and the local is what killed it. The **shadow itself is not the defect; inventing it is.** An author who *writes* `rule p(?x)` in `mA` gets exactly this and should. So a name introduced at two scopes either of which can reach the other is a **load error**, naming them and naming both repairs: one body-less `rule p(…)` in the scope that owns it makes the others' heads its clauses, or one in **each** scope says they are separate predicates. Where one place collects every head the message names it; where none does it says so and prescribes the per-scope declaration instead. Which place that is, and why the obvious reading of it is wrong, is below.

It is stated over **visibility**, not over files, and that is a deliberate departure from 059 §Definitions' file unit. The file boundary answers *"a predicate assembled by two parties that never agreed on it"*; this is a different hazard, and one author writing `demo { rule p(1) :- true; sort Rec { rule p(2) :- true } }` in one file is not two parties — they are one party who would otherwise silently get two predicates where the language used to give one. Corpus cost of the wider rule, measured: **zero**, the same as the narrow one. Two scopes that *cannot* reach each other are untouched: unrelated namespaces sharing a short name are two ordinary predicates, which is the overwhelmingly common case and what the rule must not disturb.

**A predicate is DECLARED, not discovered ([proposal 061](proposals/061-rule-declarations.md)).** A rule with no body **declares** its head's predicate (§5.3) and asserts nothing, and its name is minted in the pass that defines every other name — so a head has something to land on, put there like every `sort`, `operation` and `const`, and the WI-321 invariant covers predicates too. Nothing about resolution changes: the head runs the ordinary ladder and contributes a clause to whatever it lands on. This is also the form §WI-896's own remedy always assumed — before it, the only way to declare a predicate name was a body-less `operation`, which drags in a signature and membership of the dispatch surface ([059](proposals/059-secondary-entries.md) §Definitions: the dispatch surface of `X` is exactly the operations). A declaration is **not** on the dispatch surface and has no return type; whether the name it declares is citable as a `Relation[T]` value is decided at the reader, from the clause index, exactly as it is for a rule-introduced name today (§8.7, [052](proposals/052-rules-as-stream-valued-operations.md) OQ2).

**Auto-declaration, and where it stops (061, narrowed by 845G7).** Requiring a declaration for every predicate would be a migration for no gain in the common case, so:

> A predicate whose heads are all written at **one scope** in **one file** is auto-declared there. Heads at more than one scope are the visibility error above; heads in more than one file must be declared explicitly, and without a declaration are a load error naming the files.

The **file** is the unit for the second half for 059 §Definitions' own reason: what that rule guards against is a predicate "assembled by two parties that never agreed on it", and two blocks in one file are one author making one edit — a file boundary is the smallest place where *two parties* is real. It is also the unit `import` already uses, since an import resolves only in the file it is written in (WI-995). Corpus census over stdlib + `anthill-stl` + `examples/github-todo`: **102** predicates carry rule heads, every one has its heads in exactly one file, and none spans two scopes — so neither half refuses anything that exists.

What the file rule removes is every **cross-file absorption**: a sibling file's head moving another file's clause, a mutual-import cycle picking an owner by file order, one pair at one address giving two different programs. Under 845G7 none of those is even representable — a head never moves — and what remains of them is the two refusals above.

It is a **whole-program property**, and that is a real cost rather than an oversight: a predicate becomes "multi-file" when someone adds a second file, so an edit in one place can require a declaration somewhere else. This is the same discomfort 059 records for secondary entries — a namespace becomes a secondary entry because someone else declared a sort at its address — and it is recorded here rather than discovered.

**A declaration is what joins scopes, and that is the point of it.** `demo { rule p(?x); rule p(1) :- true; sort Rec { rule p(2) :- true } }` is **one** predicate with two clauses, because `Rec`'s head resolves `p` through its enclosing scope to the declaration. Naming a scope is how you opt into its names; wanting your own instead is §WI-896's case — declare it there too, or write it somewhere else. Without any declaration the pair is the visibility error, because nothing in the text says which of the two readings was meant. With the declaration present the join is the same whoever wrote each clause — a program that opens a namespace and adds a clause to a predicate **declared** there extends it, and the declaration is what makes that an agreement rather than an accident. The **file** rule still applies on top: two files' clauses at one declared predicate are fine; two files' clauses at an *undeclared* one are not.

The difference between an **absent** predicate and an **empty** one matters to anyone reading the KB: an empty predicate answers a goal with zero solutions, while an absent one is a name nothing resolves. A declaration produces exactly the first — `anthill.logic.Constructive`'s axioms are declarations, so they are named symbols with no clauses (their file says so: they exist so a `proof … :- modus_ponens, …` hint block can reference them, and the `-:` pass will read them as schemas rather than facts).

**`<global>` is not a party to any of it** (WI-980, kept by 845G7). It is the one scope nobody opts into — a namespace-less file's heads land there without naming it — so it takes the one exception in this section. Such a head **introduces** its name there, exactly as the `**Forms:**` block above and `examples/classic-mini/ancestor` are written; but a head written *inside* a namespace never collides with it, so a name at `<global>` can neither absorb one nor refuse one. Fusing the two questions fails either way round, both measured — treat `<global>` as a party and a one-line `rule modus_ponens(7, 8)` in a file with no `namespace` makes `anthill.logic.Constructive.Constructive.modus_ponens` cease to exist, on a program that loads clean; refuse the pair instead and the language's own documented first form stops loading. It is excluded from the **candidate set**, not merely from the overlay a head resolves through: the group is the *undirected* closure of reach, so excluding it one way round still pulls a namespace into a group with `<global>` when the namespace-less file itself writes `import ns.*` — measured, and the repair that refusal named deleted the `<global>` head's predicate. **What that costs is a named silence**: a namespace-less file importing a namespace and writing its head name does shadow it, and nothing says so. That is the trade this scope has always taken, recorded here rather than discovered.

**A named owner must be reachable from every other member.** When the refusal names a scope it promises that declaring there makes every other member's head a clause of it, so the scope it picks is the one *every* other member reaches **from every file that member writes a head in** — not the one that reaches nothing, and not one merely reached from some file. The two differ wherever reach is not transitive, which a wildcard import always is: it is never re-exported. Measured on `zzA → zzB → zzC`, the reaches-nothing reading named `zzC`, and **following that advice made the program load clean with `zzA`'s predicate still split off and no error at all** — the refusal defeated by taking its own suggestion. In a mutual cycle every member qualifies and the first in display order is named; where no scope qualifies the message says so and offers the per-scope declaration instead. The per-file half is the same defect one coordinate over, measured the same way: with reach unioned per scope, a namespace reopened in two files where only one carries the import named the imported scope, and declaring there left the import-carrying head on the local predicate with nothing reported.

**The refusal does not reach a PAREN-LESS nullary head** (`rule holds :- base(1)`). Such a head introduces nothing anywhere — a bare identifier is not an application, so it carries no functor for §"A rule-introduced functor is scoped where it is written" to scope, and it falls to the one global intern that section exists to prevent. Two scopes writing the same nullary name therefore still share one uncitable predicate, measured, while the parenthesised twin `rule holds()` is scoped: two spellings of one nullary predicate, two behaviours. This predates the rule above and is not repaired by it, and it is not the only such shape: a **fact** head, and each functor of a **multi-head** rule, are likewise unscoped and likewise collapse two scopes onto one name — both measured, each against a `rule`-shaped control that scopes correctly — as is a head inside a `provides … language … end` block. Which head shapes introduce a name is an enumeration nothing states as a decision, and the shapes outside it fall through in silence. Corpus census of the paren-less spelling, at every depth rather than only at `<global>`: **four** — `anthill-cli/tests/fixtures/wi754/props.anthill:11,12`, `multi-query.anthill:8` (`fact holds`), and `examples/webots-modelling/lf1/safety_gps.anthill:82`, which is the nested shape this paragraph calls harmful, in a shipped example. Proposal 061 narrows the silence rather than closing it: a **body-less** paren-less head now DECLARES, and since it names no functor to declare it is a located refusal (§5.3, "a body-less rule that can declare nothing") — as are a body-less multi-head rule and a body-less qualified head. All four corpus sites carry bodies, so none is reached; what stays silent is exactly the BODIED spellings, which is WI-20260821-P85Z7 and WI-20260821-RDGQC's enumeration.

It is the **same ladder**, to the rung (WI-900), which settles the two edges. A name that is **ambiguous** at that scope resolves — to several things, which is still resolving — so the head concludes about it and the ambiguity is reported at the reference; introducing instead would put a scope-local ahead of the candidates and decide the conflict silently. And the implicit-prelude / reserved-kernel tier answers only when its **target is loaded**: in a knowledge base that does not load the declaring file, `and` resolves to nothing, so the head introduces it in its own scope — rather than falling to one shared global that a sibling scope's same-spelled head would collapse onto.

**But a clause may not occupy a bodied operation's GRAPH slot** (WI-939 item 4; `check_operation_body_and_clauses`, `kb/load.rs`). A rule's operation name is its label else its head functor ([proposal 052](proposals/052-rules-as-stream-valued-operations.md) §"Naming the relation"), so a clause written at the operation's **arity + 1** — the slot WI-938's derived relational view answers — is a second **definition** of it, not a second view, and the pair is a **loss, not a trade**. Measured: with the body alone the arity+1 goal answers a definite value through the derived relational view (WI-938); add one clause and design §3.3's precedence suppresses that view, and the goal answers a **residual**. The clause takes the working reading away and computes nothing in its place, which is what WI-580 found when it retired `List.contains`'s twins (then spelled `member`) (they branched on structural unification while the body used the declared `Eq`, so the two could disagree). The load is refused, naming the operation, its declaration and every clause.

One operation, **one definition** — and either form may be the one. Three neighbouring shapes are **not** this and stay legal, each for its own reason:

- a clause at the operation's **own arity** is a **lemma** about it *when the operation is builtin-backed* — `rule bound: gte(?x, 3.0) :- gte(?x, 5.0)` against the bodied `PartialOrd.gte`. A builtin decides its goal before any clause is consulted, so such a clause suppresses nothing; it states something about the operation rather than defining it, and the SMT backend cites it. **Arity alone does not separate the two**, and it is the Bool case that shows why: a Bool-returning operation's derived view sits at its **own** arity (`eq(op(args), true)`), not at arity + 1 — so a same-arity clause on a bodied Bool operation with no builtin behind it is refused, exactly as an arity + 1 clause is. Measured: `operation isbig(b) -> Bool = true` beside `rule isbig(box(n: 0))` loaded clean and made the goal answer *nothing* while the body says `true`;
- a **body-less** operation carrying clauses is one definition written relationally — `anthill.prelude.Set.contains` / `.subset` / `.eq`;
- an **equation** (`<=>`; `=` at a bodyless head is a load error, WI-888) is a law about the operation and loads under the connective's functor, so it is not a clause of it at all — §5.3 owns when an equation instead *backs* a body-less operation.

Corpus census of the refused shape: **zero**.

A **label plays no part** in what the head is about: it names the *clause*, so it can no more decide that than a variable's name can. `bool.anthill`'s `ite_true:` / `ite_false:` are two labeled clauses of one `ite`. (Until WI-896 a label did suppress a *predicate* head's introduction — proposal 032's "a labeled rule already has an identity". That stood in for the missing fallback tier and was right only by coincidence: it saved the labeled `gte` lemma while the unlabeled twin was captured, and it made a genuinely-new labeled head travel to the global namespace.)

One consequence is deliberate and **not yet diagnosed**: once the head resolves, a clause on a **builtin-backed** name is inert at SLD, because the builtin decides the goal before any clause is consulted. The `gte` lemma above has always been such a clause — cited by the SMT backend, never fired by resolution — and a user's `rule or(?a, ?b) :- …` joins it. Off the builtin's own arity the clause is reachable; at it, the builtin wins silently. A refusal is WI-899.

**Naming one from elsewhere.** Because the functor is scoped, it has a qualified name, and both ways of writing that name work: a selective import (`import anthill.prelude.Bool.{ite}`, which is how `ordered.anthill` and `int64.anthill` reach `bool.anthill`'s `ite` laws) or the qualified spelling at the use site (`Bool.ite(c, t, e)`). Without one of those, a bare use is **refused** in an operation body (unknown functor). In a rule body it is refused in **goal** position too (WI-1034): a body goal whose functor names nothing — no clause indexes it, no declaration of any kind carries it — can never match, so the rule silently answers the empty set, and the loader names the goal and its `line:col`. Three positions are exempt and each for its own reason: a resolver **scoping marker** (`forall_impl` at arity 3, …) carries no clause by design; a functor this rule **assumes**, as the antecedent of a `(forall(?x), P(?x) -: Q(?x))` discharge, is declared by that antecedent; and a **bare `or` / `push_choice` branch or bounded-quantifier body** is left to resolution, since such a branch may fail while its sibling succeeds — the same tolerance a query pattern gets, for the same reason. The ARGUMENT position is refused too (WI-1058), by a separate check with its own exemptions and its own sentence ("rule-body **term** … names nothing"): a rule body's data slots also carry things the KB deliberately declares nothing under — a discharge's binder tuple, a binding pattern, and the interior of a **type** — so the check skips those and reads every other compound term. Both positions ask one question of one authority, so they cannot disagree about which names exist. A **contract clause** is the third position and the last to arrive (WI-20260822-59CDQ): a `requires` / `ensures` goal is written on a *declaration* rather than in a body, so neither walk above saw it, and an invented predicate there loaded byte-identically to a real one. It is now refused by the same authority, over the clause's conjuncts (the loader lowers several comma-separated goals as one `conjunction(…)`, which names nothing itself and is split, never tested). The consequence stated is its own: such a clause is silent as a *condition* — a `requires` conjunct no clause can match can never be proved, an `ensures` conjunct is assumed about a name nothing else can query — and it is **not** inert, because the override-refinement check of §8.7 compares contract clauses structurally, so an undeclared name matches another undeclared name of the same spelling and mismatches every declared one, deciding whether a provider is accepted on a name that denotes nothing.

**What types a rule's variables** (WI-741 / WI-20260819-9C2PZ). A rule body declares nothing, so its variables take their types from the *positions* they occupy — an operation-parameter slot and an entity-field slot each say what the value there must be — unified across every position a variable appears in. Those types are what a rule read as a `Relation` publishes as its free **columns**, and what a rule-body **dot** resolves its receiver on. A callee's own **type parameters are instantiated per call**: `eq(?x, ?y)` puts *these two* variables on one type, a second `eq` in the same body puts *its* two on another, and neither speaks for the other. So `rule twoeq(?x, ?n) :- gen(?x, ?n), eq(?x, "a"), eq(?n, 1)` publishes `(x: String, n: Int64)` — two independent columns, and `twoeq("a", 1)` runs while `twoeq(1, "a")` is a load error — whereas `rule pair_eq(?x, ?y) :- eq(?x, ?y)` publishes two columns of *one* type, refusing `pair_eq(5, "s")`. A **literal** argument types the parameter it fills, which is where the two concrete columns above come from; a variable a call forces equal to a concretely-typed one **inherits** that type, transitively (`eq(?x, ?y)` beside `gt(?y, ?z)` puts all three on one type); and a **subgoal on another rule** types nothing — its columns are not read back — so a variable only a subgoal binds stays open, which is the ordinary case and not an error. None of this was per-call before WI-20260819-9C2PZ: every call to one spec operation anywhere in the knowledge base recorded that spec's own parameter symbol, so unrelated variables were treated as one type and the correct citation above was refused.

**Equational rules (`<=>`).** A bodyless rule whose single head is a `<=>` (unification) term — `rule LHS <=> RHS` — is an **equational rule**: an oriented rewrite / definitional equation the engine derives L→R. It is a **law**, and — with `[simp]` — a rewrite the normalizer fires (below); it is **not** how an operation acquires a definition, and that holds for the `eq` family too, including where the right-hand side is the literal `true`/`false` (WI-1092, measured). An equation's clause is indexed under the **connective**, not under its subject (WI-898, above), so `rule eq(red, red) <=> true` leaves `eq` owning no clause: SLD has nothing to try, and neither the `eq` bridge nor a dictionary dispatch can run it. A carrier defines its own `eq` by cases with **predicate heads** — `rule ceq(red, red)`, the shape `set.anthill`'s `rule eq(?a, ?b) :- subset(?a, ?b), subset(?b, ?a)` uses — whose clauses ARE indexed under the operation and which the eval→SLD `eq` bridge (WI-625) proves; §8.7 has the whole declaration. There is no catch-all `<=> false` case to write beside them: absence is falsity, since the sub-proof is a closed test over a complete search. The prelude's `rule neq(?a, ?b) <=> not(eq(?a, ?b))` is likewise a law stated beside a builtin rather than `neq`'s definition — `PartialEq.neq` is a registered resolver builtin, and a builtin decides its goal before any clause is consulted (below). For any other operation on a provided spec an equational rule is a law and not executable backing either; see "Backing is executable", §8.7 / WI-818. (An operation that has a *body* — `length`, `append`, `contains` — is **not** given hand-written `<=>` twins: WI-580 derives its equational and relational views from the body on demand; see docs/design/abstract-interpreter-and-rules.md §3.3.) The head connective is `<=>`, **not** `=`, and this is **enforced at load** (WI-888): a bodyless rule or fact head written with `=` is a **load error** naming the subject and the substitute spelling. `=` (`PartialEq.eq`) is a semantic equality *test* that dispatches to a carrier's own equality and never binds, whereas an equational rule head *unifies* the redex with the rule's LHS and derives the RHS (binding the LHS variables) — see §8.3. It is the same rule the spec's equality table already states and that `===` was held to (WI-1090): `=` and `===` are the **test** column, `<=>` is the **bind** column alone, and only a connective that binds can head an equation. The equation is **logically symmetric** and citable both ways via `using`; a `[simp]` / `[unfold]` attribute (proposal 043) picks the auto-normalizer's firing direction (only one orientation of e.g. `add(?x, 0) <=> ?x` terminates). Guards, contracts (`ensures eq(…)`), and constraints stay `=`/`:-` — they *test*, never bind, and that position is untouched by the refusal.

The refusal is **not** a repair of a silence, and knowing that is what keeps its message honest: an `=`-spelled head **worked**. Driven across all four (connective × attribute) combinations (WI-884, measured), the answer tracked the `[simp]` **attribute** alone — `=` fired and an untagged `<=>` was dead. What the refusal finishes is proposal 049's migration (build step 6, WI-526), which relabelled 40 heads and left 44 in the stdlib, and it retires the affordance that made both spellings classify alike "while the relabel is in flight". So `[simp]` is still the enablement (WI-881) — the connective now decides only whether the rule **loads**, and the attribute alone decides whether it **fires**.

Two boundaries are deliberate. A **guarded** equation — `lhs = rhs :- guard` — keeps its `=` spelling, because proposal 049 draws the migration line at the **empty body** and `map.anthill` writes one directly beneath its `<=>` siblings; emptiness is judged **after guard folding**, so a rule whose only body goal was a folded `Spec[T]` bound is a definition and is refused. And a `<=>` head **never** binds to a same-named symbol in scope: `<=>` is structural-only and never dispatches (§8.3's Invariant), so a namespace that declares its own `unify` — `anthill.reflect` does, for proposal 049's term-level face — does not capture the connective. Only a *written* `unify(a, b, kb)` call reaches such a declaration. `=` is deliberately the opposite, since a carrier's own `eq` **is** meant to override it (§8.7).

**`[simp]` is what makes an equation run (WI-881).** The attribute does not merely pick a *direction* — it is the *enablement*. An **untagged** equational rule is inert: the normalizer never fires it, so a body-less operation whose only definition is an untagged equation dies `OperationBodyMissing` at eval. That verdict is now uniform across the routes to such an operation (WI-1092), which it was not: a carrier's `eq` member reached through the eval→SLD bridge — by a requirement **dictionary**, or from the `eq` builtin's carrier dispatch — used to be handed to the resolver anyway, exhaust an EMPTY candidate set, and come back *refuted*, so the program silently computed with "not equal" wherever that carrier's equality was consulted and raised nothing. An absent definition is not a false one: a **declared** operation with no clause, no body, no host mapping and no builtin is unrunnable and says so, while an *undeclared* predicate symbol with no clauses stays the empty relation and refutes, which is ordinary closed-world SLD. Inside resolution the same target leaves the goal **undecided** — the resolver has no error channel, and an undecided goal is the one answer that is not wrong. Tag the same equation `[simp]` and the operation runs, because the typer rewrites LHS→RHS in operation bodies before any dispatch. That is **inlining, not dispatch**, and the distinction is load-bearing: the §8.7 backing check does not count a `[simp]` equation, so one cannot discharge a *spec* operation's obligation (a rule is not backing — WI-818); what it can do is give a sort's **own** operation a meaning — but **not** as a third way beside a body and a host mapping, and WI-885 is deciding whether it is a backing kind at all. `[simp]` needs two things a *dispatched* call does not have: a syntactic **redex**, and a **statically known carrier** (`set.anthill` states the second — its laws fire "once the redex's carrier is known to provide `Set`"). Dispatch through a requirement **dictionary** has neither: `dispatch_via_sort_ops_table` resolves an operation *symbol* out of the dict and invokes it, and the invocation path is builtin → body → value-directed impl. There is no slot a rewrite rule could occupy, so **no dictionary entry can be built from a `[simp]` equation** — which is why `carrier_override_op` reading such a member as absent is the correct answer, not a bug. Treat `[simp]` as proposal 043's directional-rewrite attribute; write a definition as a body (WI-580: the equational, relational and proof views are *derived* from it — WI-669) or as a host mapping. Two spellings are traps, both measured: a **nullary head must carry its parentheses** — `rule tau <=> …` never fires, because the bare identifier is not an application and no redex matches it, while `rule tau() <=> …` does — and a bare-identifier RHS immediately before the attribute parses as an instantiation (`<=> none [simp]` is `none[simp]`), so write `none()`. The parenthesized head has a **reach** the dispatched forms do not: it matches an application, so it rewrites `tau()` and **not** a bare `tau` call site (a `var_ref`). A nullary operation callable both ways therefore wants a body or a host mapping, not an equation.

**Variadic capture in a rule head (`...?args`, proposal 056 §2.3 / WI-1129).** The last positional argument of a `[simp]` equation's **left-hand side** may be written `...?name`. It **collects every named argument of the redex that the head does not name** into a single record and binds `?name` to it, so `rule fix(?r, ...?args) <=> fix_of(?r, ?args) [simp]` fires on `fix(r, x: 1, z: 2)` with `?args ↦ (x: 1, z: 2)`. Everything else about the rule is unchanged: the capture variable is an ordinary positional slot of the stored head, so matching, variable numbering and clause indexing are exactly what they would be without the marker.

This is the **second face** of the same capture the operation declaration has (`...name: R`, §5.4), and the two are not interchangeable — which face a construct wants is the macro-vs-typer-direct choice of proposal 052:

- The **operation** face hands the callee a *record value* whose type is built from each argument's type. A captured `"name"` therefore arrives as `String`: a name reaches type position only as a *denoted*, there being **no singleton types** (§4.5). It is the face for a construct whose return type is a function of the captured **types** — `fix`'s `Without[Drop = R]`.
- The **rule-head** face binds the residue as a record **occurrence** — the argument *syntax*, labels and sub-expressions intact — which is what a compile-time macro (proposal 043.1) reads, through `sub_occurrences` and its peer `sub_occurrence_labels` (`anthill.reflect`). It is the only way a variadic construct can get a **name** to the type level: the macro reads the label and splices it.

Because the reader is a macro, and a macro is expanded at compile time by the `[simp]` engine alone, the capture is admitted in exactly that one position. Written anywhere else it is a **located refusal**, not a marker quietly read as an ordinary argument: on a rule head with no `[simp]` tag, as a second `...`, before another positional argument, on a rule body goal or an operation body call, on an equation's right-hand side, nested inside an argument, or on a **dot-form** rule head (`rule ?r.rename(...?cols) <=> …` — a `dot_apply`-headed `[simp]` rule is fired by a different engine, which has no fold step; write the head applicatively). That last one is about the HEAD only: a dot **call site** reaches the capture normally, since the method fallback synthesizes the applicative call and re-visits it, which is what makes `r.rename(who: r.name)` — the driving surface — work. Correspondingly, the capture is a *typer*-side lowering only: the resolver's own `[simp]` firing skips a capture-bearing rule, since a runtime goal is not a syntax bracket (043.1 §5).

The head's arity is **not** checked against the operation's declaration — `[simp]` matching is structural, and a head that matches nothing simply never fires. In practice the two faces appear **together**: the operation declares `...args: R` so that `r.rename(who: r.name)` is a well-formed call at all, and its `[simp]` rule captures the same residue as syntax **first** — the typer fires `[simp]` at an application before it matches arguments to parameters, so the two captures cannot both run on one call. An **empty** capture is a record with no components, not a failure (056 §3 OQ #6).

**Typed rule patterns (`?x: T`) are currently a directional-rewrite feature
(WI-582, WI-903).** A variable in a rule's LHS pattern may carry a type bound —
`rule keep_id: keep(?x: Summable, ?y) <=> ?x [simp]` — read as the guard "the
matched value's carried type conforms to `T`". The annotation is **stripped from
the head**, so the indexed pattern is the untyped one, and the bound is
three-valued: it fires where the carried type conforms, and neither fires nor
refutes where that type is under-determined. This bound-mode meaning is the
compatibility contract for proposal 060's plain-relational form: WI-742's
generated `domain(?x, T)` goal must make the same carried-type decision when
`?x` is bound. Its body-goal placement, column typing, and future output mode
are different execution duties, not a different meaning for the annotation.

The equivalent **introducer** spelling binds the type variable in the head and
states the bound as a guard — `keep[T](?x: T, ?y) = ?x :- Summable[T] [simp]`
— which the loader **folds out of the body**, so the rule is still an equation.
It is enforced at exactly **one** site — the resolver, firing a directional
rewrite — so it is legal today only on a `[simp]`/`[unfold]` equational rule (an
equation being bodyless, §8.3) and **refused at load** anywhere else, naming the
rule. A body goal that is *not* a folded `Spec[T]` guard therefore disqualifies
it: the rule is no longer an equation, nothing fires it as a rewrite, and the
bound would have no reader. That refusal includes a `[simp]` **dot rule** — a
sort-scoped law written against the method-call form, `rule dr:
dot_apply(?receiver, member, ?x) = … [simp]`: such a rule is fired by the typer,
which enforces typed bounds nowhere, so the bound could only be ignored — write
the law as an operation-headed equation instead. The refusal is exactly as wide
as that firing: an `[unfold]` dot rule, which only the resolver fires, keeps its
bound.

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

Relevant design records: [proposal 018](proposals/018-expressions-and-operation-implementation.md),
[proposal 041](proposals/041-operation-result-naming.md), [proposal
042](proposals/042-explicit-type-parameters-on-operations.md), and [proposal
058](proposals/058-modular-instances.md).

```
Operation     ::= DescriptionBlock*
                    [Visibility] 'operation' Name [TypeParamList] '(' [ParamList] ')' '->' Type
                    OperationClause*
                    ['=' BodyExpr]
                    [MetaBlock]

OperationClause ::= 'requires' RequiresBody
                  | 'ensures' RuleBody
                  | 'effects' EffectSet
                  | 'meta' MetaBlock                -- attributes (WI-087); see §5.8, §7
RequiresBody ::= RequiresItem (',' RequiresItem)*
RequiresItem ::= RequiresBinder | Goal
RequiresBinder ::= Identifier ':' Type

TypeParamList ::= '[' TypeParam (',' TypeParam)* ']'
TypeParam     ::= Identifier                    -- per proposal 042; BARE name only (WI-850)
ParamList     ::= Param (',' Param)*
Param         ::= ['...'] Identifier ':' Type    -- leading '...' = variadic capture (056)
```

The optional body uses §4.8's expression grammar, either directly or inside a
single pair of braces (proposal 018).  A body-less operation is an abstract or
host-backed obligation; an operation with `=` has an Anthill implementation.

Parameters are **named bindings** — referenced by name (without `?`) in
`requires`, `ensures`, effects, and the body. This distinguishes them from rule
variables (`?x`), which are pattern-matching unification variables. A
`RequiresBinder` (`requires plus: Monoid[T]`) names an operation-local
requirement slot; like its sort-level peer in §5.2, it is a type parameter and
can be selected by its binder (proposal 058 / WI-840). Other items in the same
comma list are ordinary spec requirements or value preconditions.

**An operation's `requires` list holds two kinds of item, and different machinery
checks them** (proposal 058 §8's split; WI-539 and WI-448 respectively).

- A **value precondition** names a boolean condition over the parameters —
  `requires neq(b, zero-val)`. It is *proved*, at the call site, from what the caller
  knows: in an operation body any unproved precondition is a load error, and in a rule
  body only a ground **refutation** is one — an under-determined condition legitimately
  floats rather than raising, since a rule-body goal's arguments are variables and a
  precondition over a symbolic one is undecided rather than violated (WI-557/WI-602:
  act on a decided obligation, never on an undetermined one). It is also what §8.5
  turns into a proof obligation.

  **What the caller knows includes the argument's TYPE** (WI-9PGCM). A value
  precondition may name a variable bound in a *parameter type* rather than among the
  value parameters — `send(body: Text[L = ?l]) requires flows_to(?l, Public)`, where
  `?l` is a label the sort carries as a type parameter. Such a variable is decided by
  the call's **type unification**, not by the substitution of arguments for parameters:
  `send(fetch())` with `fetch() -> Text[L = Untrusted]` binds `?l := Untrusted`, and the
  obligation the call must discharge is `flows_to(Untrusted, Public)`. So the clause is
  walked through the call's type substitution before it is proved, exactly as the
  operation's declared effects are. The three-state rule above then applies unchanged,
  and its middle state is what makes this sound: a variable that **survives** the walk
  leaves the obligation *undetermined*, and an undetermined obligation must not be handed
  to the resolver at all. A free variable in a goal is witnessed **existentially**, so
  `flows_to(?l, Public)` would prove itself off an unrelated fact about some other
  label and the contract would gate nothing.

  **Surviving is not the same as being undetermined, and the difference is the
  quantifier** (WI-K88TN). Read the surviving variable's *kind*. A **flexible** one — an
  inference variable no caller has bound and no later pass has solved — is genuinely
  undetermined and floats. A variable the enclosing operation's **own signature binds**
  is not, and this section states no new rule about it — §"Expansion during unification"
  already settles the quantifier: "Inside a body, then, an unwritten parameter is
  **rigid** … At a *call* it is flexible again, and binds from the argument. Same
  variable, two positions". A variable the author *writes* in a parameter type is that
  same family, spelled out there under WI-1FKR2 (`via(b: Box[?t])`), so `?m` in
  `relay(t: Text[L = ?m])` is rigid in the body exactly as `?t` is. What WI-K88TN
  changed is only that the `requires` check now reads that kind instead of treating
  every surviving variable alike. So in `relay(t: Text[L = ?m]) -> Unit = send(t)` the
  obligation is `∀m. flows_to(m, Public)` — **decided**, and false, since only `Public`
  flows to `Public`. It is refused, and the diagnostic names the clause and the repair.

  **The repair is to declare it**, and a declared clause is then an *assumption* inside
  the body it guards — proposal 050's Hoare reading, so an operation's own value
  preconditions seed its body's Γ₀. `relay` writing `requires flows_to(?m, Public)`
  discharges its `send(t)` obligation from Γ and propagates the contract to its own
  callers, where `?m` is flexible again and each call decides it: `relay(banner())`
  loads and `relay(fetch())` is refused naming `flows_to(Untrusted, Public)`. The
  obligation is restated in the vocabulary of whichever signature owes it, so a wrapper
  of a wrapper owes the same declaration — no pass reads a callee's body to discover
  this, and each operation is checked against its signature alone.

  This is **declare-or-refuse**, the same discipline `effects` obeys on the other half of
  this clause list: a body incurring an effect its signature does not declare is a load
  error, not an inferred addition to the signature. The alternative — inferring the
  floated clause onto the enclosing contract — was weighed and rejected: it leaves a
  contract no reader can see in the source (the objection this section makes to invisible
  slots), it needs a call-graph fixpoint to stay modular, and it still cannot place a
  clause naming a variable *no* signature binds, which `f() = send(pick())` over a
  polymorphic `pick() -> Text[L = ?k]` produces and which is refused under either regime.
  A wrapper whose obligation holds for **every** instantiation needs no declaration: the
  clause is decided by proof and not by membership in the declared set, so a goal a rule
  proves for all labels discharges it where a fact about one label does not.

  **A variable no signature binds is a third case, and it has no repair.** The rule above
  reads the surviving variable's kind, and a rigid one has two sources: a signature's own
  parameter, universally quantified and *declarable* — and an **opaque witness** opened
  from a callee's return, which §"In a RETURN the quantifier flips to ∃" mints fresh per
  use. `f() = send(pick())` over `pick() -> Text[L = ?k]` raises an obligation about that
  witness, and no `requires` on `f` can name it: a `?k` written there is `f`'s own new
  variable and never meets the opened one. Such a call is refused and the diagnostic says
  so rather than prescribing a declaration — the value's label is unknowable here, and the
  program must give it a type whose parameter is known or take it as a parameter so a
  caller's label flows in. Nothing may be assumed about an opaque witness; that is what
  makes the opening sound in the first place.
- A **type precondition** names a spec — `requires Ord[T]`, or the named form
  `requires lo: Ord[T]`. It is *never* proved from the caller's Γ. It declares a
  **requirement slot**, which the call fills with a dictionary: its rules are the
  op-scoped requirement in §5.2 (what it licenses, whose frame slots it takes, and the
  supply check that must be able to fill it) and the selection surface below.

The implementation draws exactly this line, which is what makes the split observable
rather than editorial: the call-site contract check splits each clause into its
conjuncts and keeps only the value goals (`is_value_precondition_clause`), leaving the
spec goals to dispatch. The split is per **conjunct** and not per clause because one
comma list may mix the two — `requires neq(a, 0), lo: Ord[T = Int64]` lowers as a
single `conjunction(…)`, and classifying that whole clause once proved the spec half
from Γ, which is precisely what a type precondition must never be (WI-862).

A **named** op-level slot is a type parameter of the *operation*, not of any sort, so
§5.2's named-vs-anonymous rule reaches it only halfway: naming it makes it addressable
in a bracket (`biFold[plus = AddM, times = MulM](xs)`) and distinguishes two slots of
one spec, but there is no value whose type could carry the choice — an op-scoped
requirement is evidence about *this call of this operation* and belongs to no instance
(proposal 058 §3.9). §5.2's inference for an omitted named slot therefore stops at the
sort level and does not run here.

`requires` is checked before execution and therefore cannot reference
`result`. `ensures` and `effects` may reference the reserved `result`, which
denotes the return value; a named-tuple return can be addressed through normal
field access (`result.a`, `result.b`). A parameter named `result` is refused.
Inside an operation body, `result` has no reserved output meaning and follows
ordinary lexical binding rules. This delivered widening is proposal 041 /
WI-261.

**Operation type parameters** (`[T1, T2, ...]`) declare per-call polymorphic slots scoped to a single operation invocation. They may appear in the parameter list, return type, requires/ensures, and effects positions. At a call site the bindings can be written positionally (`foo[Int64, String](args)`) or named (`foo[T1 = Int64, T2 = String](args)`), with the positional-first rule borrowed from `SortBinding` (see §5.2). Operation type parameters are **per-call** — each invocation binds them afresh — in contrast to sort-level type parameters which are pinned at sort instantiation. See `docs/proposals/042-explicit-type-parameters-on-operations.md` for the full design and `docs/design/operation-call-model.md` §"Operation type arguments" for the runtime threading through `frame.requirements`.

**A type-parameterized operation as a FUNCTION VALUE** (WI-1083). A bare operation name in a
function-typed slot denotes the operation as a value — its eta expansion, `inc(n: Int64) ->
Int64` becoming `(Int64) -> Int64` (§4.4 "Arrow types"). When the operation declares type
parameters, or its signature otherwise binds a logical variable, the value's type is the **∀**
over them: `idp[A](x: A) -> A` denotes `∀A. (x: A) -> A`, whose structural form is
`TypeExtractor.PolyType(binders, body)` (§4.4). The **reference** is where the ∀ is eliminated,
which is §5.6's rule read at a value rather than at a call — a type parameter is the caller's
to instantiate — so two references to one operation are instantiated separately and share no
variable, and the operation may serve two element types in one program.

**Which variables the ∀ quantifies** is the same set §8.1 uses to decide which *return*
variables are existential, read positively: a variable named in a **parameter** type, in a
**`requires`** clause, by the operation's own **`[A]`**, or by its declaring sort's parameter.
So an operation that writes no brackets at all still generalizes — `mplus(a: LogicalStream[?A],
b: LogicalStream[?A]) -> LogicalStream[?A]` binds `?A` for exactly the reason §8.1 does not open
it — and the two rules partition a signature's variables between them rather than competing for
one. The quantification happens at the lift; nothing about it is stored on the declaration. The
same set is what the **body** is checked under, skolemized (§"Expansion during unification",
WI-1FKR2): a variable this list quantifies is the caller's to instantiate, so the body may use it
and never constrain it.

**A declared type parameter is a BARE name** (WI-850). A *default* on the declaration — `operation foo[T = Int64](x: T) -> T` — is **refused**, with a diagnostic naming the operation, the parameter and the type written. The grammar parses the `= Type` form precisely so the diagnostic can name it; the refusal is taken when the source is converted, before load, so every consumer of a parsed file (including the parse-only Rust codegen) is covered by the one rule. Nothing read it: a declared parameter becomes one fresh logical variable minted from its **name**, so `[T = Int64]` meant exactly `[T]` and the default was dropped in silence — and then a call that left `T` otherwise unconstrained reported "unconstrained type parameter", advising the author to pin `T` at the call when they had written that pin on the *declaration*. A type parameter is bound at the **call**: from the argument types, from the expected type, or explicitly (`foo[T = Int64](…)`). Proposal 042 OQ3 admitted the form grammatically and left its semantics unadopted for want of a driver; *honouring* a default — consulting it at exactly the point the unconstrained-parameter error is raised — remains available, and would need the default carried beside the minted variable through the operation's record plus an explicit verdict on whether a default may mention an earlier parameter (`[T, U = List[T]]`).

**Every call-site binding must land, and only an operation body may carry one** (WI-839). Within one bracket, each binding must reach a **distinct** target of the callee. Four ways it can fail, all **load errors**: a named key naming no target; the **same key twice**; a positional with no parameter **left** to bind (those a named key already took do not count as available); and a callee that is not an operation at all — a function value, an applied rule citation, an entity constructor — which has no type-parameter list for a bracket to bind.

**What a key may name — two rungs, in order** (WI-841, proposal 058 §4.2). (1) A declared **type parameter**: the operation's own, **or its enclosing sort's**. Both scopes, one list — an operation may not declare a parameter whose name collides with its sort's, so no key has two targets, and that collision is refused at the *declaration*. (2) A requirement's **spec short name**, when it picks out exactly **one** *anonymous* requirement slot of the callee — its own `requires`, its enclosing sort's, or, for a body-less spec op, the spec being dispatched (`Monoid.combine[Monoid = AddM](a, b)` selects the dictionary backing that very call). The value there names a **witness sort**, and the binding *selects* that provider for the slot: explicit selection outranks both the search for a unique provider and a deferral to the enclosing frame's dictionary. A slot the author **named** (`requires m: Monoid[T]` — WI-840; proposal 058 §4.7) is reached by its binder under rung (1) — which both pins the parameter and selects — and is no longer answered by its spec's short name, so one bracket cannot bind one slot twice. A **positional** binding is rung (1) only: a requirement slot has no position a call site could count to.

Three refusals belong to rung (2), all **load errors**: a **qualified** key (`fold[algebra.Monoid = AddM]`) is refused rather than resolved — resolving it would make selection depend on the *caller's* imports, while the supply path consults no scope at all, and every selection a short name cannot express is written by naming the slot; a short name matching **two or more** anonymous slots (the gate that makes matching by short name sound at all); and two keys selecting **different** witnesses for one spec.

**A selected witness is validated at the call site** (proposal 058 §4.4): it must provide the spec **at the call's own bindings** — a witness that provides it at other bindings is as loud as one that provides it not at all — and it may not be a **concrete** provider, a sort with constructors, whose values carry their own sort and therefore already direct the dispatch. There the value decides, and an explicit witness is refused rather than preferred. A selection applies to the call's **own** goal and not to the sub-goals a conditional witness resolves: those search, as they always did. To steer one, name the witness's own slot in the key's value position (`fold[Monoid = ListM[O = MyEq]]`), where the selection happens at the witness's boundary as a callee slot again.

The bracket is read in exactly **two** positions: on a call **in an operation body**, and as a rule **head's** type-variable introducer, where only the *bare* form is accepted (`keep[T](…) = …`, §8 — a concrete binding such as `r[A = Int64](…)` is an error). Written **anywhere else** it is a load error naming the callee — a rule-body goal, a `fact` head, a `constraint`, an operation's `requires` / `ensures` contract expression, an entity-constructor call, and any other position: the rule is *"read or refused"*, enforced by checking that some lowering consumed the bracket rather than by a list of positions, so an unlisted position refuses too. Selection of an instance inside a rule body is *deferred*, not ignored: a rule body that needs a chosen provider calls an operation whose body carries the bracket (proposal 058 §4.2). This is distinct from a parameterized **type** written in term position (`is_modifiable(Cell[V = Int64])`, §5.2), which is a different production and remains valid wherever a type may be written.

**Variadic capture parameter** (`...name: R`, proposal 056 / WI-727) — a leading `...` marks the one **trailing** parameter that **collects every named argument not matched to a declared parameter** into a single **named-tuple record** value. Its type is an ordinary explicit type parameter (`R`, inferred from the call, exactly as `join[L, R]` infers its schemas). This lets an operation whose "arguments" are a **variadic set of names** — not a fixed parameter list — resolve through the ordinary call path: the leftover `(x: 1, z: 2)` binds `R = (x: Int64, z: Int64)` and reaches the body/runtime as a plain named tuple (a `Value::Tuple`), with no macro and nothing keyed on the operation's identity. At most one, trailing (a second `...`, or a non-trailing one, is a load error). **The slot is a position too** (WI-1130): a **positional** leftover binds the capture parameter **directly**, `R` taking that argument's own type rather than a record wrapping it — so `cap(5)` and `cap(rest: 5)` denote the same thing. The two channels are **exclusive**: one positional leftover *or* any number of named ones, never both. Mixing them is a load error naming the **named argument the author wrote** and saying a positional argument already fills the slot; a *second* positional leftover is the ordinary arity error below. A positional residue is therefore **not collected** — `...name: R` is variadic in the **named** direction only. The record is consumed by an ordinary type constructor — e.g. `Without[T, Drop]` (the dual of `Concat`) drops from a schema every column named in the captured record: `fix[R](p: Relation, ...args: R) -> Relation[T = Without[T = p.T, Drop = R]]`, the driving client. Its **peer** is the rule-head rest pattern `...?args` (§5.3), the same capture surfaced as *syntax* for a compile-time macro rather than as a value — reach for that one when the construct must lift a captured **name** to the type level, which this face cannot (a captured argument arrives as its TYPE, and §4.5 has no singleton types). See proposal 056.

**A call must fill the parameter list exactly** (WI-1100). Every declared parameter takes exactly one argument, and no argument may occupy a slot the declaration has not got. This is the rule §4.4 states of an arrow application — "the argument **count** must equal the declared arity" — written there as what a named operation's call is *already* checked by; until WI-1100 it was checked at neither. With **named** arguments it is a coverage question rather than a count: `pair(b: 2, a: 1)` fills both slots and `pair(a: 1, bogus: 2)` fills one, though both write two arguments. A **variadic capture** slot may be filled by the capture rewrite rather than by the caller, so `r.fix()` is complete — or **positionally by the caller** (see the **variadic capture parameter** paragraph above), in which case it counts as an ordinary argument — so a capture-bearing operation admits **one more** positional argument than its fixed list holds, and one beyond that is this error. Anything else is a **load error** naming the operation, its declared arity and the count given — there is no partial application in this language, and an under-applied call denotes nothing. One position admits one more count: a rule-body **goal** may be written at arity **+ 1**, which is the functional-relation view of §5.3 (`vec_add(a, b, ?c)`), the extra positional column receiving the result. **It is a position, not a rule body** (WI-1104): the same call written as a *value* inside a goal — `?y = concat("a", "b", "c")` — is refused exactly as it is in an operation body, and the extra column is itself **checked against the operation's declared return type**, since that is what it receives (`Desc.describe(leaf(), "s")` against `-> Int64` is a load error, while an unbound `?r` is left to resolution). What the check replaces is a run-time `ArityMismatch` on the first execution to reach the call — and, on the resolution path, nothing at all: the goal answered *no solutions*, indistinguishable from one that legitimately has none.

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

Design records: [proposal 013](proposals/013-abstract-effects.md), [proposal
045](proposals/045-effect-sets-and-expressions.md), and [proposal
048](proposals/048-conditional-effects.md).

Effect labels are **open** and effect rows have the implemented algebra from
proposals 013/045/048:

```
EffectSet  ::= EffectExpr
             | '{' [EffectExpr (',' EffectExpr)*] '}'
EffectExpr ::= SimpleEffect                         -- presence is the default
             | '+' SimpleEffect                    -- explicit presence
             | '-' SimpleEffect                    -- absence/lacks constraint
             | 'merge' '(' EffectExpr (',' EffectExpr)* ')'
             | SimpleEffect ':-' Term              -- one-goal guard
             | '(' SimpleEffect ':-' RuleBody ')'  -- conjunctive guard
SimpleEffect ::= Name
               | Name '[' SortBinding (',' SortBinding)* ']'
               | VariableTerm
```

`{}` is the closed empty row and therefore the explicit pure row. A single
effect needs no braces. `merge(E1, ..., En)` is row union and may nest; a bare
label and `+label` both assert presence, while `-label` records a lacks
constraint. These spellings are accepted both after an operation's `effects`
keyword and after an arrow type's `@`.

**Guarded effects** (proposal 048, WI-478/WI-067) qualify one row element, not
the whole row. The bare spelling admits one guard term so an outer comma still
separates row elements; parentheses delimit a conjunctive `RuleBody`:

```
effects {Modify[s], Error[DivisionByZero] :- eq(b, 0)}
effects {(Error[BadInput] :- malformed(x), unsupported(x))}
```

At a call site the parameters are substituted into the guard. The label is
dropped only when the local logical context **constructively proves the guard's
negation**; a proven guard or an undecided/floundered guard conservatively keeps
the effect. Thus guarded effects are optional precision, not preconditions or
proof debts. A guard over an enclosing parameter can propagate with that
parameter substituted. The same effect label may also occur unconditionally;
refuting one guarded occurrence never removes the unconditional occurrence.

**An `eq`/`neq` guard is refuted by the carrier's OWN equality** (WI-755), because
the refutation is an ordinary resolution of the negated goal and `=` is the
dispatched semantic test of §8.3 — so `{ Boom :- eq(c, Red) }` at `risky(Green)`
drops `Boom` exactly when that carrier's `eq(Green, Red)` is *false*, and keeps it
when the carrier calls them equal even though they are structurally distinct. A
carrier with no override is decided structurally, since structural equality *is*
its instance. The undecided cases keep the effect on the general rule above, and
they are the ones a *structural* answer would get wrong: an operand still ranging
over a runtime parameter; an **override reachable inside** an operand whose own
carrier declares none (`eq(some(Green), some(Red))` over `Option[Color]`) — there is
no instance at the head to dispatch, and recursing structurally would ignore
`Color`'s; and — until WI-1125 — a carrier supplying a **`neq`**, which *nothing
dispatches*: equality dispatch keys `PartialEq.eq` suppliers, and every evaluator
computes `neq` as the negation of the dispatched `eq` (the §8.3 law). WI-755 held
that case as a narrowed typer gate on this route alone; **WI-1125 decided `neq` is
not an override point and refuses the declaration at load** (§8.3, and §8.7 for the
binding forms), so no program
reaching a guard discharge can carry an equality the resolver cannot see, and the
gate is gone. Where the carrier supplies **both**, that is refused too and for the
second half of the same reason: its `eq` decides — `neq` is defined as that `eq`'s
negation, so dispatching the `eq` *is* consulting the carrier's own equality — which
leaves the written `neq` able only to disagree with it, a coherence question no load
can settle.
This replaces WI-573's earlier floor, which kept the effect whenever an override of
*either* member was merely reachable: sound, but it suspended the `eq` dispatch it
was waiting for — including on carriers that spelled both members consistently.

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

**Effect targets that name a binder are alpha-equivalent.** A `Modify[x]` target naming a **callback's own arrow parameter** is a binder reference, and its identity is its **position** among that callback's parameters, not its spelling. So

```
(a) -> R @ Modify[a]
(c) -> R @ Modify[c]
```

are the same type: unifying the two arrows aligns the *i*-th parameter of each, so the binders compare equal by position. A target naming anything else — an operation parameter, the result — is a **free** reference and compares by symbol identity; it is never alpha-equated.

**Effect parameters on sorts.** A sort may declare an abstract effect parameter
with the dedicated `effects E = ?` item (proposal 045 / WI-320) to express row
polymorphism; `effects E = Row` binds it. The item lowers to the corresponding
sort parameter plus its effects-runtime requirement. For example, `Stream[T,
E]` declares that iterating the stream may have effect `E`; a file-backed stream
can bind `E = Error`, while a pure in-memory stream binds the closed empty row
`E = {}`.

**Handler discharge — a row minus a handled label.** A handler is an ordinary
operation, not new syntax. It discharges effect `K` by **sharing a row tail** `ρ`
between its body parameter and its result, with `K` present on the body side and
absent from the result:

```
operation handle_K[Rho](body: () -> X @ {K[...], Rho}) -> X @ {Rho}
```

Checking `handle_K(lambda () -> e)` is then the ordinary call-site row machinery
(proposal 045 §5.6, WI-329): `ρ` binds to the **residual** — everything in `e`'s
row other than `K` — and the call's row *is* `ρ`. A body of `{Error[Int64],
Modify[c]}` under `handle_Error` yields `{Modify[c]}`. Because the discharge is
carried entirely by the handler's **type**, it composes: nested handlers drop
their labels successively in either order, and every unhandled label propagates.
The dropped label is decided by the **result** row alone — a handler whose result
row keeps `K` discharges nothing, at the same call.

**A body that does not perform the handled label is admitted**, and `ρ` is then
the body's whole row: `handle_Error(lambda () -> pure())` has row `{}` and
`handle_Error(lambda () -> modifies())` has row `{Modify[...]}`. A callback
argument's row conforms by **subset**, not by equality, so a declared label the
argument never performs is not an error — the handler simply has nothing to
catch. Writing the tail out (`handle_Error[Rho = {Modify[c]}](...)`) yields the
row inference derives, and a wrong explicit tail is refused.

This is the **static** half only: it asserts that the program is well-typed, not
that a handler is installed. The runtime handler — installation, `HandlerAction`,
continuations — is [proposal
027](proposals/027-effect-handlers-and-standard-effects.md)'s. Consequently a
handler that actually *ran* its body would incur `{K, ρ}` against its own
declared `{ρ}`; the type above describes the contract, and 027 supplies the
machinery that realises it.

Users can define additional effect kinds; the kernel stores and propagates them but only interprets the well-known ones.

### 5.6 Effect Semantics (State-Passing Interpretation)

Effects give operations a precise execution semantics via a state-passing interpretation. An operation

```
operation op(x1: A1, ..., xm: Am) -> R
  effects {Modify[S], Error[Err], Suspend, Branch}
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
| `Error[Err]` | `(R × Env) + Err` |
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

**A `Modify` target is a PLACE, never a type.** `Env` maps resource *names*, so the
argument of `Modify[…]` must **denote a value** — a parameter (`Modify[c]`), the result
binder (`Modify[result]`, §5.5), a field path off one (`Modify[c.contents]`), a
value-producing zero-arg operation (`Modify[kb]`, the ambient-resource accessor), or a
**nullary constructor** (`Modify[counter]`, the *ambient resource*). The rule is
*denotation*, not a closed list of spellings. A **type** in that slot — a sort
(`Modify[Cell]`), a sort parameter (`Modify[T]`), or a type projection (`Modify[s.T]`) —
names no slot, and is a **load error**; so is a bare `Modify` with no target.

The **ambient resource** is the nullary constructor read as what it is: a *constant* of
its sort, hence a value, hence a name for the slot `Env(counter)`. A constructor that
takes fields is a *function* and names no slot until applied, so `Modify[wrap]` is a type
error like any other; and an **eponymous** constructor is its own sort (§6.3), so
`Modify[Slot]` where `sort Slot { entity Slot }` cannot be read as the constructor without
also reading it as the type, and stays refused. This is the one slot in the language where
a bare entity name is *not* a type — every other type-argument position reads it as one
(`Text[L = Untrusted]`, a label carried as a type parameter), which is exactly what §5.6's
resource-name reading of this bracket says it should be.

The rule is not a restriction but a consequence: a type target is unsatisfiable by
construction, because a provision binds a type parameter to a *type*
(`provides ModifyRuntime[T = Cell]` binds `T` to the sort), never to a place — so no
instantiation of `Modify[T]` ever becomes a resource name. Two places of the same type
are two resources, which is why granting `Modify[a]` does not grant `Modify[b]`; a
target naming the type they share would erase exactly that distinction.

A place's *type* still matters, and separately: it is what a `Modifiable[T = …]`
requirement is asked about, and what the ordinary parameter-conformance check (§8.7)
compares against a provision's binding.

Enforced by `check_modify_targets` (`kb/typing.rs`) on an operation's own effect row. A
**computed** region — an application in the target slot, `Modify[glob(pattern)]` — is
refused earlier still, by the type grammar. Inside a *parameter's* arrow type
(`handle(body: () -> X @ {Modify[…], ρ})`) the target is the arrow's own binder, not the
enclosing operation's parameter; that position is not yet checked.

**At a call, the target is re-keyed onto the argument** — `Cell.set` declares
`effects Modify[c]`, so `Cell.set(k, 1)` incurs `Modify[k]`. The argument must therefore
name a place by the same rule: a variable, a field path off one (which coarsens to its
head — `Modify[c.rep]` is covered by `Modify[c]`), or a nullary constructor
(`set(counter(), n)`, with or without the parentheses). An argument that names none — an
application, whose result is a fresh value per call — is a **load error at the call**,
naming the caller's own expression: there is no slot for the effect to be re-keyed onto,
and the repair is to give the value a name (`let x = mk()`, then pass `x`).

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

These generate proof obligations (see §8.5) that can be discharged at various trust levels.

### 5.7 Monadic Interpretation of Effects

The same effects admit an equivalent **monadic interpretation**. An operation

```
operation op(x1: A1, ..., xm: Am) -> R
  effects {Modify[S], Error[Err], Suspend, Branch}
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

### 5.9 Const (term-level named constant)

A name that **is** a value at every term position — `BROADCAST_CHANNEL` denoting the
integer `-1` rather than standing for a nullary operation that computes it. Not one of
the four native constructs, and not sugar either: a `const` does not desugar, it is its
own declaration with its own loader path. See proposal 039.

```
Const       ::= DescriptionBlock*
                  [Visibility] 'const' Name ':' Type ['=' BodyExpr]
                  [MetaBlock]
```

It slots into the same positions as an operation — a namespace body and a sort body —
and accepts the inline `Visibility` prefix. **Monomorphic and carrier-independent by
design**: no parameters, no type parameters, and the grammar admits no `effects`
clause.

**The declared type is mandatory, the body optional.** `: Type` is part of the name's
contract, not an inference target. A body-less `const` is **host-supplied** — its value
comes from the host language, bound by the `const_map` clause of a `provides` block,
which is the const-level peer of `operation_map` (a const is not an operation, so
`operation_map` refuses it).

**The empty effect row is the purity gate.** Because no `effects` clause can be
written, a const's anthill body must be pure, which is what makes it referentially
transparent and safe to memoize. This excludes allocators — `Cell.new` and friends
carry `Modify[result]` — so `const COUNTER: Cell[Int64] = Cell.new(0)` is a load-time
error rather than a load-time singleton. Folding is lazy (first value-demand, then
cached) and bounded by the evaluator's step cap; a host-supplied value waives the fold
check, the kernel having no body to inspect.

**Description blocks are admitted, identically to operations** — §4.1 position 1.

### 5.10 Proof declarations, in-body proofs, and provides blocks

Proof syntax names an existing rule/obligation and records how it is to be
discharged (proposals 025, 025.1, 030, and 031). The parser admits a single
tactic/query form and a structured sequence of tactic-checked rule steps:

Design records: [proposal 025](proposals/025-proof-constructs.md), [proposal
025.1](proposals/025.1-z3-tactic-dsl.md), [proposal
030](proposals/030-theorem-registry.md), and [proposal
031](proposals/031-structured-proofs.md).

```
Proof ::= DescriptionBlock* 'proof' Name
          (SingleProof | StructuredProof) 'end' [Name]

SingleProof ::= ['using' NameList] ['by' ProofStrategy] [ProofBody]
ProofBody ::= ':-' RuleBody
            | 'query' StringLit ['mapping' MappingBlock]
ProofStrategy ::= Identifier
                | Identifier '(' FnArg (',' FnArg)* ')'

StructuredProof ::= ProofStep+ [ProofConclusion]
ProofStep ::= 'rule' [Name ':'] RuleShape [MetaBlock]
              ['using' NameList] 'by' ProofStrategy
ProofConclusion ::= ['using' NameList] 'by' ProofStrategy

MappingBlock ::= '{' MappingEntry (',' MappingEntry)* [','] '}'
MappingEntry ::= Name '->' (Name | StringLit)
```

The strategy name is an open syntactic dispatch key; parsing a strategy does
not imply that a given proof executor implements it. `using` cites previously
discharged positive rules through the theorem/ProofRecord registry. A denial
headed by `⊥` has no conclusion to lift and is not citable (§5.3). Structured
proofs accumulate the checked step rules and optionally use a final tactic to
discharge the enclosing target.

An operation/const body may put a proof in control flow (proposal 025, WI-538):

```
ProofStatement ::= 'proof' Name ['using' NameList]
                   ['by' ProofStrategy] ['conclude' Term]
                   'end' Expr
```

The proof is checked in the body's local logical context and scopes over the
continuation expression after `end`. `conclude` supplies a local proposition
when no named rule supplies the goal; successful derivation feeds the conclusion
back into that continuation's context.

`provides` has two surfaces. A clause on a sort claims a spec, optionally under
per-provision spec conditions (proposal 058 / WI-869). A standalone host block
records realization artifacts and name mappings (proposal 025):

```
ProvidesClause ::= 'provides' SpecInstantiation
                   [':-' SpecInstantiation (',' SpecInstantiation)*]

ProvidesBlock ::= DescriptionBlock* 'provides' Type
                  'language' Identifier ProvidesItem* 'end' [Name]
ProvidesItem ::= 'artifact' StringLit
               | 'carrier' Bindings
               | 'namespace_map' Bindings
               | 'operation_map' Bindings
               | 'const_map' Bindings
               | Rule | RuleBlock | Fact | Proof
```

The conditional tail accepts spec instantiations, not arbitrary rule goals: it
describes dictionary dependencies of this one provision. `const_map` is the
value-level peer of `operation_map` (§5.9). Provides blocks are namespace/file
realization declarations and are not admitted inside a sort body; a
`ProvidesClause` instead takes its provider from the sort address where it is
written (§5.1, §8.7, §10.2).

## 6. Syntactic Sugar

Readable shorthand that desugars to kernel constructs. The reasoning engine only sees rules and sorts.

### 6.1 Fact (bodyless rule)

A ground assertion — the most common way to add knowledge to the KB.

```
Fact ::= DescriptionBlock*
           'fact' Term
           [MetaBlock]
```

`DescriptionBlock*` is accepted for a precise diagnostic, but a fact has no declaration
name or citation handle and therefore no stable `DescriptionInfo.target`; a non-empty
prefix is refused (§4.1). Describe the named relation/sort declaration instead.

**Desugars to:**

```
fact parent("alice", "bob")
→  rule parent("alice", "bob") :- true
```

The `:- true` is load-bearing (proposal 061): since a rule with **no body declares** its
predicate (§5.3), an assertion must say so with a body, and `true` is the empty
conjunction. `fact` is therefore the body-less *assertion*'s spelling and the only one
whose head may be ground-and-silent about it.

**A `fact` head introduces no scoped name**, and that is a known gap rather than a
consequence of this desugaring: the head reaches the bare global intern, so two scopes
writing one fact name share one uncitable predicate — measured, with a `rule`-shaped
control that scopes correctly (WI-20260821-RDGQC, which owns the enumeration of which
head shapes introduce a name; §8.6). Until it closes, `fact p(…)` and `rule p(…) :- true`
are **not** the same program: only the second gives its predicate a name its own scope
can cite.

### 6.2 Constraint (headless rule / denial)

An integrity-invariant declaration. The quantified subset is enforced by the
KB guard engine; the current boundary for ordinary denials is stated below.

Design record: [proposal 023](proposals/023-kb-guards.md).

```
Constraint ::= DescriptionBlock*
                 'constraint' [Name ':'] ConstraintBody
                 [MetaBlock]

ConstraintBody ::= RuleBody [':-' RuleBody]
                 | QuantifiedConstraint
                 | AggregationConstraint
QuantifiedConstraint ::= Quantifier '(' Variable ':' Term ')' '-:' ConstraintBody
                       | Quantifier Variable ':' RuleBody '-:' ConstraintBody
                       | Quantifier Variable '-:' ConstraintBody
Quantifier ::= 'forall' | 'some' | 'one' | 'lone' | 'no'
AggregationConstraint ::= Aggregate '(' Variable ':' RuleBody '-:' RuleBody ')'
                          Comparison Term
Aggregate ::= 'count' | 'sum' | 'min' | 'max'
Comparison ::= '<=' | '>=' | '<' | '>' | '=' | '!='
```

A leading description requires the optional label. The label is defined as a
`Constraint` symbol in the declaring scope and is the `DescriptionInfo.target`; the
unlabeled combination is parsed only to produce the precise §4.1 refusal.

The invariant (head) states what must be true; the guard (body after `:-`)
states when it would apply. This is the logical reading and the desugaring
below. **Current execution boundary:** an ordinary denial/invariant constraint
is stored but not registered with the guard engine, so it is inert today. Only
the quantified forms described next are enforced. WI-882 owns removal of the
misleading stdlib denials and correction of this surface; do not rely on a
plain constraint as an operation precondition—use an operation `requires`
clause or guarded effect.

The quantified forms from proposal 023 are enforced through KB guards. The
condition selects bindings for the variable; `some`, `one`, `lone`, and `no`
require respectively at least one, exactly one, at most one, or zero satisfying
bindings. `forall` requires the body for every selected binding. A typed binder
`forall (?x: T) -: body` supplies the type/domain condition directly.

The delivered `forall` guard can negate a single body atom. A multi-atom
`forall` body is currently refused as an unsupported constraint form because
negating a conjunction atom-by-atom would be unsound. Likewise, the grammar
recognizes `count`/`sum`/`min`/`max` aggregation constraints, but the loader
refuses them explicitly: aggregate enforcement remains future work alongside
the aggregation design in WI-712. These
parse-only forms are not executable language capabilities, and the refusal is
part of the current contract rather than a silent no-op.

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
             [MetaBlock]
```

**Desugars to:**

```
entity Account(id: AccountId, balance: Money)
→  sort Account { entity Account(id: AccountId, balance: Money) }

entity Marker
→  sort Marker { entity Marker }
```

**An eponymous constructor IS its sort** (WI-926). A constructor that carries its
enclosing sort's own name declares no second name: `sort Project { entity
Project(…) }` writes `Project` once and defines **one** symbol — there is no
nested `Project.Project`. The field schema, the `EntityInfo`, and the head functor
of a `Project(…)` fact are all that one name, so a reader that resolves `Project`
finds the declaration a writer wrote. This is what makes the desugaring above an
*equivalence* rather than a rename: the sugar and the long form denote the same
thing, and a `.toml`/`.json` store, a codegen backend, or a reflect query naming
`Project` gets the same answer either way.

A constructor named *differently* from its sort is unaffected — `sort Status {
entity Open, entity Closed }` and `sort Person { entity mk(…) }` keep their nested
`Status.Open` / `Person.mk` symbols. The rule is keyed on the name matching, not
on being a sole variant. Only a **sort** body collapses; `namespace Project {
entity Project(…) }` does not, since a namespace is not a single-constructor sort.

Consequences worth stating, because they are what the rule buys:

- Such a sort **is its own constructor**, not the parent of a separate one — one
  name fills both places. What answers "is this constructible" is the declared
  **field schema**, the same question for both spellings.
- **Every entity belongs to a sort, and that is what the wrapping is for**
  (WI-925). Since `entity E` *is* `sort E { entity E }`, the belongs-to relation
  must answer for the wrapped case too, or the wrapping buys nothing. It does: the
  sort of a wrapped entity is **itself**, so the relation is **total** and, for
  this shape, reflexive. A fact whose head is a free-standing entity is therefore
  filed under that entity. (Reading the relation as a chain to *climb* — a variant
  to its enclosing sort — one takes the strict step, which is simply absent here;
  a name that is its own sort has nowhere further to go.)
- **A name carries a SET of categories, not one** (WI-925). Such a name plainly
  *is* a sort and *does* construct, so it records both: `{Sort, Entity}`, from
  either spelling. A single category could not say that — it kept whichever
  keyword was declared first, which made the answer depend on source order rather
  than on meaning. Ask whether a name **plays** a role. The set's *order* is the
  one further fact it carries: the head is the keyword actually written, which is
  what a diagnostic and reflect's `kind` report.
- A **bare** `Project` still denotes the *type* (it is passable where a `Type` is
  expected); an **applied** `Project(name: …, language: …)` constructs. Position
  decides, as it already did for a free-standing entity.
- The **written surface** decides which reading an *applied* eponymous name gets
  (WI-927): `Box[T = Int64]` is a type application whose arguments bind the sort's
  declared **type parameters**, `Box(value: 1)` is a construction whose arguments
  fill the entity's **fields**. Both lower to the same `Term::Fn`, so only the
  brackets-vs-parens distinction separates them — the functor's *kind* cannot,
  since an eponymous sort is one symbol that is both. Each surface keeps its own
  error: a stray `Box[W = …]` reports `no type parameter named 'W'`, a misspelled
  `Box(valu: 1)` reports `'Box' has no field 'valu'`, and neither is reported
  twice. This holds in every position — a rule body, a fact, an operation body, and
  a type annotation.
- **The declaration record is one record** (WI-928), and this is what makes the
  equivalence hold at LOAD time rather than only at run time. Both spellings emit
  the same `SortInfo` — one constructor, itself — so both are reached by the
  load-time passes that walk declared sorts. The consequence that matters:
  **a fact of a free-standing entity is type-checked against its declared field
  types**, exactly as one of a `sort`-written entity is. `entity Thing(count:
  Int64)` followed by `fact Thing(count: "hello")` is a located type error, and was
  silently accepted while the two spellings emitted different records. The
  single-constructor **induction principle** is emitted for both, likewise.

  The one field that differs is `SortInfo.kind`, which reports the keyword actually
  written — `entity` here, `sort`/`enum` for the long form — the same rule the
  category set's head follows above. It is a record of the surface, not of a
  difference in meaning: `name`, `definition` and `constructors` agree, and no
  reader may branch on it to decide what a declaration *is*.

- **Every reader of the belongs-to relation answers for both spellings**
  (WI-946). WI-928 made the *record* reachable; this is the same equivalence for
  the checks that then read it, and each was a place where the two spellings had
  disagreed on whether a program is accepted. A value of a free-standing or
  eponymous carrier in a field declared some *other* sort is a type error, as the
  nested spelling's is (it was silently accepted); an eponymous *parametric*
  sort's destructure binds `T` from the scrutinee, and its construction builds
  `Box[T = …]` rather than a bare `Box`, so a wrong declared binding is caught
  (`case Box(v)` was falsely rejected, and `-> Box[T = String] = Box(x)` on an
  `Int64` field was accepted); an eponymous variant is a *sibling* of the other
  variants of its sort, so a `match` arm naming it is a definite non-match.
  Reading the relation as a chain to CLIMB stays the strict step — that is what
  §4's subtype walk and provider search want, and it is genuinely absent here.

- **A field declared `anthill.reflect.Term` holds a QUOTED term, so any value
  conforms.** Reflection (value → Term) is total, so `entity Holder(pat: Term)`
  accepts `Holder(pat: Thing(id: "z"))` whatever sort `Thing` belongs to.
  Reification (Term → value) stays partial and explicit (`term_as_entity`), so the
  reverse is *not* accepted, and `Term` is therefore **not** a top type.

- **A free-standing entity is a CONCRETE carrier, so its provisions are checked**
  (WI-931). `entity EulerAngles(roll: Float, pitch: Float, yaw: Float)` is as instantiable as the
  `sort` spelling, so `fact Spec[Vec3]` carries the same obligation any other
  concrete carrier's does: every operation `Spec` declares must be backed for it by
  something the evaluator can dispatch to (§5.3 / WI-818 — a rule is *not* backing).
  Before the records agreed, such a carrier emitted none and read as abstract, so
  the obligation was skipped by omission.

  It follows that **a satisfaction fact belongs in the closure where its backing
  exists** (proposal 038): if a spec's operations are host primitives, `fact
  Spec[Carrier]` is declared in that host's binding layer, not beside the carrier
  in the language-agnostic library, where nothing backs them. A host implementation
  named for a **spec** op says that operation has an implementation; it never says
  a given **carrier** is realized — that is a separate declaration, and conflating
  the two lets any carrier claim the spec (WI-876, WI-931).

  **The obligation follows the claim, not where it is written or which declaration
  came first** (WI-978). `fact Spec[X]` carries it identically in `X`'s body, beside
  `X` in its namespace, at a file's top level, and inside a `namespace X` block at
  `X`'s address. The loader files the provision by asking whether the enclosing
  scope **names a type** — a category *membership* question, since a name carries a
  SET of categories (the rule above, WI-925/WI-956) — never by reading whichever
  category was registered first. That made a claim beside a free-standing `entity X(…)`
  record no provision at all, so it loaded clean with nothing backing it, while
  moving the same text one line out refused it.

  **But a claim still needs a carrier to attach the obligation to, and only one
  position supplies one without brackets** (WI-933). A `fact` is writable in three of
  the four positions above — the fourth, a `namespace X` block at a sort's address, is
  a **secondary entry**, where `fact` is refused outright and the spelling is `provides
  Spec[…]` (§6.3's secondary-entry rule; a fact is a rule, and in that position a
  spec claim cannot be told from an ordinary fact over a parameterized data sort).
  Of the three, only *inside `X`'s own body* is the enclosing type the carrier — which
  is what `sort QueryableStore { fact Store }` says and how the store hierarchy is
  built. The other two, beside `X` in its namespace and at a file's top level, name it
  in brackets, because neither address names a type. A **bracket-less `fact Spec` at
  either of those** is therefore about nothing, and is a **load error** naming the
  spec, the scope, and both repairs — not a silent no-op, which is what it was: two
  such lines shipped in the stdlib and neither produced a provision, while their
  bracketed neighbours on the next line did (measured, WI-931). It is the `fact` twin
  of the refusal §5.1 states for a `provides` clause at an address no type occupies,
  and refused for the same reason — a provision needs a provider and a carrier, and a
  namespace supplies neither. The tempting alternative, reading the carrier off the
  enclosing namespace's entity declaration, is rejected on the same ground WI-978
  states above: a namespace may declare more than one, so proximity would put
  declaration *order* back in charge of what a claim is about.

  A **constructor** of the named sort is what puts a `fact` outside this rule
  altogether (WI-1106, §5.1) — `fact Box` where `sort Box` has an `entity Box`
  constructs rather than claims, whether or not `Box` takes parameters. Everything that
  reaches the refusal therefore *is* a provision claim, so it is refused whenever no
  carrier can be read: with nothing after the spec's name, and equally with brackets
  whose contents name no type (`fact Spec[T = ?]`, or brackets binding only
  operations). The two get different sentences, since only the first can be repaired by
  adding brackets.

- **Operations move a free-standing entity to the long form.** The sugar has no body
  in which to write one, so `sort Box { entity Box(v: Int64); operation unwrap(…) = … }`
  is how a free-standing entity gains members — still one symbol, per the rule above,
  and the fields and operations therefore belong to one type in every backend
  (a C++ backend emits one `struct`, not a data struct beside a traits struct).

  What every backend owes is that the **type is one declaration**; where the members
  go is the host language's to answer (WI-940). C++ can put them in the same
  `struct` because a member declaration needs no definition there. Scala cannot: a
  `case class` admits no abstract member, so a signature-only backend emits the one
  `case class` and leaves the members on the separate `<Sort>Ops` contract it
  already uses for every sort with constructors — which is not the forbidden
  shape, since that contract does not bear the type's name. The defect the rule
  names is a **second declaration of the sort's own name** — `Vec3.Vec3`, or two
  `struct Vec3` — not the existence of a companion.

  Mind the **short name** when doing this in a namespace that already has a
  rule or operation of that name: the new member is a second binding for it, and an
  `import ns.{f}` elsewhere may bind to the member rather than to the namespace-level
  `f` — silently, since both are legal (measured; WI-935).

**Distinct field names** (WI-808): an entity's field names must be distinct —
`entity mk(a: Int64, a: Int64)` is a located error naming the repeated field. A field
name is how the field is *addressed* — `x.f`, a named argument, a rule pattern — and
all of those resolve a name to its **first** match, so a second field under an
already-used name can never be read by name.

This is the same principle as §4.5's distinct tuple component names, and deliberately
*not* the same harm. A tuple component under a repeated name is unreachable entirely,
so its declared type is never checked against anything. An entity's second field is
still constructed and read **positionally** (`mk(1, 2)` type-checks both fields,
`case mk(p, q)` reads the second), so what it loses is its access path, not its type
check. It is refused anyway, because a field name is the field's public interface and
a name identifying two fields addresses neither.

> **Omitted optional fields (surface semantics, WI-716).** Omitting an
> `Option[…]`-typed field is position-dependent: in a **value position** (a
> `fact`, or the head of an entity-deriving rule) the absent field denotes
> `none()`; in a **pattern position** (a query, or a rule-body atom) it denotes
> "matches anything". A reflect `Term`-typed field holds a *quoted pattern*, so
> its content is pattern position even inside a fact — an entity omitted-field
> there stays a wildcard (e.g. `fact FactHolds(pattern: E(id: ?x))`). So a rule
> that matches an optional field structurally (`some(?x)`, `nil()`, `cons(…)`)
> does NOT match a fact that omits the field — add a `none()` case when the
> domain intends omitted to mean empty/absent (see WI-717).
>
> **See also — runtime representation.** How an entity value crosses between the
> interpreter's `Value::Entity` and the hash-consed `Term::Fn` at runtime (fact
> load, materialization, optional-field defaulting, 0-ary constructor storage) is
> an internal-representation concern, documented in
> [`docs/design/entity-term-mapping.md`](design/entity-term-mapping.md).

### 6.4 Operation and Rule Blocks

Multiple operations or rules can be grouped under a single keyword using block syntax. Each entry inside the block has the same grammar as the standalone form minus the leading keyword, and desugars to an individual `operation` or `rule`.

```
OperationBlock ::= 'operation' Body[OperationEntry*]
OperationEntry ::= DescriptionBlock*
                     [Visibility] Name [TypeParamList]
                     '(' [ParamList] ')' '->' Type
                     OperationClause* ['=' BodyExpr] [MetaBlock]

RuleBlock      ::= 'rule' Body[RuleEntry*]
RuleEntry      ::= [Name ':'] RuleShape [MetaBlock]
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

This is the obligation-generation half only. **§5.4 is canonical for what a `requires` clause means and which machinery checks it** — the per-conjunct split into a call-site-proved value precondition and a dispatch-filled type precondition — and §8.5 for what an implementation must then discharge.

### 6.6 Infix and Prefix Operators

Operators are sugar for `Fn` terms. The tree-sitter grammar parses them as flat chains; a Pratt resolver in the converter applies precedence and associativity to produce nested `Fn` calls. Adding a new symbolic operator requires only a dictionary entry — no grammar change.

**Operator tokens.** Any sequence of the characters `+`, `-`, `*`, `/`, `%`, `^`, `|`, `&`, `=`, `<`, `>`, `~` is a valid operator symbol. The character `!` is excluded from operator symbols and reserved as a prefix-only token; `!=` is an explicit two-character infix token. The unification operator `<=>` is a single token lexed **greedy-longest before `<=`** (proposal 049): `a <= b` is `lte`, `a <=> b` is `unify`. Likewise `===` (structural identity, proposal 051) is a single token lexed greedy-longest before `=`: `a = b` is the semantic `eq`, `a === b` is `struct_eq`.

**Infix operators** appear between terms:

| Operator | Priority | Assoc | Functor | Origin |
|----------|----------|-------|---------|--------|
| `\|` | 1 | Left | `or` | `Bool` |
| `or` | 1 | Left | `or` | `Bool` (word form) |
| `&` | 2 | Left | `and` | `Bool` (value) / `anthill.kernel` (goal) |
| `and` | 2 | Left | `and` | `Bool` (word form) |
| `=` | 3 | None | `eq` | `PartialEq` (semantic equality **test**, dispatched) |
| `!=` | 3 | None | `neq` | `PartialEq` |
| `===` | 3 | None | `struct_eq` | `anthill.kernel` (structural identity **test**) |
| `<=>` | 3 | None | `unify` | `anthill.kernel` (structural **unification**) |
| `<` | 4 | None | `lt` | `PartialOrd` |
| `<=` | 4 | None | `lte` | `PartialOrd` |
| `>` | 4 | None | `gt` | `PartialOrd` |
| `>=` | 4 | None | `gte` | `PartialOrd` |
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

**Boolean operators are position-directed** (WI-529). `not`, `or`, and `and` each name a dispatched **value** operation on `Bool` (`Bool.not` / `Bool.or` / `Bool.and`) inside an **operation body** (evaluated), but a **goal** form in a **rule body** (resolved): `not(goal)` is negation-as-failure (`anthill.kernel.not`), `or(g1, g2)` is disjunction (`anthill.kernel.or`), and `and(g1, g2)` is conjunction (`anthill.kernel.and`, over the `push_and` primitive). Resolution is by syntactic position, not by a distinct glyph or operand type — in BOTH directions (WI-1046). For `not` the pair are two SYMBOLS and not two readings of one, because they are two different functions: `Bool.not` takes a Bool **value** and returns one, while `kernel.not` takes a reified **goal** and is three-valued (succeed / fail / DELAY on an unbound variable), and a failed goal is not the value `false`. `sort Bool`'s own laws measure the gap — `not(true) <=> false`, `not(not(?a)) <=> ?a` and de Morgan are each false of negation-as-failure — which is also why proposal 052's uniform `eq(op(args), true)` routing for a bare Bool goal is not available for it (052 §Open questions 7). An operation body redirects the primitives to the `Bool` ops; a rule body redirects the `Bool` ops to the primitives, at every GOAL position (the body's atoms, and the goal slots of the connectives above them — a goal's ARGUMENT is a value expression and keeps the `Bool` reading). Position-directedness cannot rest on the implicit-prelude fallback alone, which sits below scope resolution: before WI-1046 an ordinary `import anthill.prelude.Bool` captured `not` and `|` in that namespace's rule bodies, and every negated or disjunctive rule silently stopped answering — a wrong answer for `not`, whose whole job is to succeed where its goal fails.

`a & b` in a goal position **is** goal conjunction, and the comma stays its other spelling: `a, b` and `a & b` are the same conjunction, refuse the same dead conjunct, and answer the same. Watch the precedence, since `&` binds looser than `=` and `?r = ?a & ?b` is `and(eq(?r, ?a), ?b)`. Until WI-20260822-J38JE this was **refused at load** on the ground that "there is no `kernel.and`" — which was a missing primitive, not a rule about the language: `not` and `or` each had one to be redirected to and `and` did not. Adding `push_and` (§ the kernel primitives) made the three symmetric and retired the refusal; a statement elsewhere that `kernel.and` does not exist predates it. The conjunction reading also **subsumes** the boolean-value one wherever both apply: a `Bool` expression in goal position is a condition (§5.3), so "`?a` succeeds" is "`?a` is true", and `true & false` fails as a conjunction exactly as it is false as a value — with the unground case resolved as a goal rather than required to evaluate. Unlike `not`, `and` needs no separate account of the two functions: goal conjunction and value conjunction agree wherever both are defined, so one symbol chosen by position is enough. Negation of a numeric value is written `neg(x)` → `Numeric.neg` (a defaulted spec op, `neg(?a) <=> sub(zero-val, ?a)`); negative literals (`-1`, `-0.45`) are lexed directly. A prefix `-` *operator* on non-literal expressions is not provided (it would collide with negative-literal lexing — WI-529).

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

3. **Named-tuple component access** (WI-638): if the object types as a **named tuple** (its functor is `named_tuple`, so the receiver sort is `None` and modes 1–2 never reach it), resolve the identifier against the tuple's `(name, type)` components — by short name (`t.x`) or by positional `_N` (`t._1`, 1-based, since positional tuples desugar to `_N` names). Access is name-keyed on both the type and the runtime `Value::Tuple`, hence independent of the order **the value** wrote its components in — a value conforms to its type BY NAME and may present them in any order (permutation is a `<:` rule, §4.5), and nothing reads that order. This does **not** say the TYPE has no order: a positional reading takes its order from the type's label list, which is also what `_1.._n` numbers — see "Destructuring binds by LABEL" below, where position selects *which label*, never which value. (Measured: two operations declared `-> (a: Int64, b: String)`, one written `(a: …, b: …)` and one `(b: …, a: …)`, return `Value::Tuple`s in their two written orders — the value is not normalized — while `.a`, a positional `let (p, q) = …`, and `eq` read both identically.) E.g., `(x: 10, y: 20).x` evaluates to `10`; `t.x` on a param typed `(x: Int64, y: Int64)` type-checks and evaluates.

**Destructuring binds by LABEL, like access** (WI-803). `lambda (p, q) -> …` and
`case (p, q) ->` bind `p` to the component named **first in the binder list's
expected tuple type** and `q` to the second — by *name*, so whatever slot the
value put that component in is where it is fetched from. `lambda (p, q) -> p - q`
applied to a value typed `(x: Int64, acc: Int64)` computes `x - acc` whether the
value was written `(x: 3, acc: 10)` or `(acc: 10, x: 3)`.

The label comes from the **type**, never from the binder's name: a tuple pattern
has no way to *spell* a label (its elements are patterns or `name: Type` typed
binders), so a binder name is a fresh binder rather than a selector — matching
binder names against labels would leave `lambda (a, b)` no meaning at all over a
named tuple. Position still selects *which label*; it no longer selects which
value.

Two consequences:

- A **wider** value destructures fine. Width subtyping (§4.5) lets an
  `(a: A, b: B, c: C)` value meet a binder list typed `(a: A, b: B)`; a by-label
  fetch ignores the component it was not asked for, exactly as an `.a`/`.b` reader
  would.
- Where no tuple type is known for the pattern, the binder list falls back to the
  value's own component order, which is then the only reading available. The same
  applies to a **positional** tuple, whose labels are the synthetic `_1.._n` — for
  it the two readings coincide by construction.

A binder list whose length differs from its expected tuple's component count is a
**mismatch**, reported where it occurs; it is not silently narrowed to the
components that do line up.

This reader is what lets `<:` be name-keyed at all (§4.5). While it read by
**slot**, a permuted value conforming by name bound a binder to one component
while the checker had typed it from another, and an operation declared `-> Int64`
could return a `String` on a clean load (WI-788).

An arrow's parameter list is likewise applied positionally, but its binder names
are not free: they gate whether two lists may be zipped at all (§Arrow types,
"Parameter lists correspond slot by slot"), so an arrow spelled `(p: A, q: B) ->
R` does *not* currently conform to one spelled `(x: A, y: B) -> R`.

**Disambiguation from qualified names.** At parse time, `a.b` in term position is parsed as `field_access(a, b)` — a variable or identifier followed by `.identifier`. Qualified names (`Namespace.Sort`) continue to be parsed as `name` nodes within `fn_term` and `instantiation_term`, which require `(...)` or `{...}` to follow the name. There is no ambiguity: `A.B(x)` parses as `fn_term(name: A.B, args: [x])`, while `A.B` alone in term position parses as `field_access(A, B)`.

**Well-formedness rules:**
- `t.f` requires `t` to have a known sort `S` with an entity that has field `f`
- Single-constructor sorts: field lookup is unambiguous
- Multi-constructor sorts: field `f` must appear in all constructors with the same sort
- Abstract sorts (`sort T = ?`): field access is ill-formed (no fields)
- Named tuples (mode 3): `t.f` requires `f` to be a component name of `t`'s named-tuple type, or a positional `_N` within its arity

### 6.8 Distributive Dot Projection (member list)

**Syntax:** `x.(m1, …, mn)` — a member LIST after the dot, generalizing the
single-field `x.f` of §6.7. It **distributes** the receiver `x` over the members
and desugars (at parse/convert time) to the **ordered/named tuple**
`(m1: x.m1, …, mn: x.mn)`. Each `x.mi` is an ordinary §6.7 dot access (any member,
not only a field), so no new typer/eval machinery is involved.

```
x.(f1, f2)        →  (f1: x.f1, f2: x.f2)       -- bare: member is BOTH key and dot-member
x.(a: f1, b: f2)  →  (a: x.f1, b: x.f2)         -- rename: `a:`/`b:` are the result keys
x.(f)             →  (f: x.f)                    -- one member is still the named tuple
x.(a: f)          →  (a: x.f)                    -- and a single rename still keys by `a`
```

Two properties are load-bearing:

1. **The result is the ordered/named tuple, never positional.** Labels are
   preserved from the member names (or the rename), never auto-named `_1/_2` —
   this is what lets a projected relation keep its column schema and re-join by
   name. The member ORDER is the source order.
2. **Members resolve at TYPING, not at name-resolution.** Each `mi` lands in the
   §6.7 `field_access(x, mi)` dot position, resolved against `x`'s type at the
   typer — so a member is never a value-position scope symbol. Both keep
   (`x.(f1, f2)`) and rename (`x.(a: f1)`) are therefore free of any
   free-identifier hazard.

**No arity-one special case (revised: 052 OQ5, option A).** `.( )` builds the named tuple at
every arity, one member included, so a projection's result type is always the tuple of its
keys and a computed one-column result is `(a: A)` rather than the bare `A`. `Concat` and
`Without` are therefore inverses at every arity, and a relation SCHEMA is the named tuple of
its columns at every arity too (§4.5): `Relation[(board: Board)]`, whose rows are
`(board: …)` and whose column reads as `row.board`.

This **replaces** the earlier 1-collapse, under which a single member yielded the scalar
`x.m` — arity-based, so a single *rename* `x.(a: f)` collapsed as well and dropped its label.
That was a paired **type-and-value** convention: the term half here, the schema half in the
typer, and the row half in materialization. This section recorded the cost of revising it as
"moving both halves together", and that is what was done — the term desugaring above, the
schema (`relation_schema_type`) and the materialized row all changed in one step, so no two
of them can disagree at arity one.

**What the collapse cost, and why it was dropped.** It erased the schema's *arity*, not
merely a name. A collapsed schema no longer said how many columns it came from, so three
readings became indistinguishable at the type level:

- **one column** — its name was gone, so a derived schema could not name it: `Concat`,
  `Without` and `Project` each *refused* a one-column operand, and `Concat`/`Without` were
  not inverses at arity one ("nothing downstream can supply the lost `a`");
- **zero columns vs one `Unit`-typed column** — both spelled `Unit`, so `Membership` accepted
  a relation that still had a column and only the drain refused it;
- **n columns vs one column whose type is an n-field tuple** — both spelled that tuple.

The third was the one that decided it, because it was a **silent wrong answer** rather than a
refusal. The collapsed reading is spelled identically to an ordinary working one, so the two
schemas were the *same type* and no checker could tell them apart; refusing one would refuse
the other. A construct needing the arity had only two options — recognise and refuse the
shapes it *could* name, or carry its own check against a relation value's column list, the
one place the arity survived. `Concat` had neither: merging is name-free, so there was no
runtime question to ask, and a `join` over a tuple-typed column type-checked against a merged
schema with more columns than the row it materialized. The other three members survived the
same ambiguity only because each asks the value "is there a column of this name?".

What the collapse bought was one line — `queens.head : Board` instead of `(board: Board)` —
and no shipped source used it. That is a measurement, not a survey: dropping the collapse
changed the type, the row and the term all at once, so any source draining a one-column
relation as a *value* would have failed to load. None did — every `.anthill` file under
`stdlib/`, `examples/` and the project's own program still loads and runs unchanged, and the
only edits the change forced were in per-feature test fixtures. (A static count agrees:
of the ~49 rule names with exactly one head variable, the citations are all rule-body goals,
where the schema type never arises.)

**What did not change.** A one-component named tuple type was never a broken spelling of its
component: per §4.5 its inhabitants arrive both from the one-component literal `(a: v)` and by
width subtyping from a wider tuple, in any position — `operation narrow() -> (a: Int64) =
(a: 1)` and `operation narrow() -> (a: Int64) = wide()` over `wide() -> (a: Int64, b: String)`
are each well-typed. Under the collapse that type was simply never what a *computed*
one-column result had.

**Consequences elsewhere in the surface**, each stated where it lives:

- a bare row binder in a `where` / `join` condition is a **loud error**. The row is a named
  tuple at every arity, so `c` names no column variable and `eq(c, 30)` becomes
  `eq(c.age, 30)`; joining a one-column relation reads `q.who`, not `q`.
- a **membership** (`Unit`) operand merges as zero columns, because `Unit` now means zero
  columns and nothing else. Joining one is a filter, and types as one.
- `stdlib/anthill/prelude/relation.anthill` records the per-operation surface.

**Grammar note.** The opener is a single fused `.(` token (a `.` immediately
followed by `(`, no interior space). `.(` is otherwise-free syntax, so the
receiver may be any atom **including a bare/dotted `name`** (`t.(x, y)`,
`a.b.(x, y)`) — unlike single-field `x.f`, whose bare-name receiver rides the
`name` rule — with no grammar conflict against qualified names (`Ring.one` uses
a plain `.`).

**Well-formedness (loud errors, checked at convert):**
- **Named-only.** A projection key may not be `_`-prefixed (the positional-tuple
  convention): `x.(_1, _2)` is rejected — positional selection is written out as
  `(x.f1, x.f2)`. Renaming a positional member is fine: `x.(a: _1)`. This applies at
  **every arity**, one member included: `x.(_1)` builds `(_1: x._1)` and is rejected with
  the rest (before the arity-one case was unified it desugared to the plain access `x._1`
  and was exempt).
- **Distinct keys.** Duplicate result keys are rejected: `x.(a, a)` and the
  rename collision `x.(k: f1, k: f2)` are errors (a duplicate-key tuple would
  silently drop the later column). This is one instance of the general rule that a
  named tuple's component names are distinct (§4.5, "Distinct component names"),
  kept here as its own check because a projection builds its result tuple from keys
  the surface never writes as a tuple literal.

Expression/call members (`x.(count(), y)`) and a positional projection variant
are deferred (see proposal 052).

**The desugaring is MARKED, and the mark is what "is a projection" means.** The
tuple built above is structurally identical to the same tuple written by hand —
`x.(f1, f2)` and `(f1: x.f1, f2: x.f2)` are the same term — so the desugaring
records its own provenance and downstream passes read that mark rather than
re-deriving projection-hood from the shape (WI-762). This is observable, and
deliberately so: **only a written `.( )` projects.** Over a relation, `r.(f1, f2)`
is the projection `Relation[T = (f1: …, f2: …)]`, while a hand-written
`(f1: r.f1, f2: r.f2)` is what it says — an ordinary named tuple whose two
components are two independent single-column relations, evaluated separately.

**A projection that names no column is reported as a projection.** Over a relation, a member
that resolves to *nothing* — neither a column nor any member reachable on the receiver, as in
`r.(nosuch)` — fails, and the failure names the projection and lists the schema's columns.
Both readings are live at that surface at once (select a column; access any member, above),
and reporting only the missing *member* answers the one the author is least likely to have
meant. The rule is narrow on purpose: it applies to a **member lookup that found nothing**,
never to a member that exists and whose *use* is wrong — `r.(takeN)` is missing an argument,
not missing a column, and keeps its own error. A hand-written tuple and a non-relation
receiver likewise keep the ordinary member message, which is the accurate one for each.

That is the same distinction §4.5 draws elsewhere: a projection is an *operation
on* a relation that happens to yield a tuple-shaped schema; a tuple literal *is* a
tuple. Per-row computation is not projection at all (a computed column is out of
the distribute-dot, above) — it is written functionally with `.map`, which yields a
`Stream` rather than a `Relation`. Proposal 052 originally had the typer recognize
a name-keyed row tuple as `projected` directly, stated there as the stopgap "until
`.( )` lands"; `.( )` is §6.8, so that reading is retired.

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

**Expansion during unification.** A parametric sort referenced as a type with some or all of its declared parameters unbound unifies as that sort applied to a **fresh variable for each unbound parameter**. The four ways of leaving a parameter unwritten — a bare reference, a partial application, an explicit `?`, and an operation type parameter — all mean the same thing and are checked alike (WI-1056). A bare reference is the all-unbound case — `Stream` ≡ `Stream[T = ?, E = ?]` — and a partial one fills the rest — `Stream[T = Int64]` ≡ `Stream[T = Int64, E = ?]`. The typer performs this expansion at **every sort application** — wherever a parametric sort appears as a type, including a bare reference unified against another bare reference — so the parameters participate even when the source writes no binding for them. The expansion covers **every** declared parameter: ordinary type parameters and effect-row parameters (`effects E`; proposal 045 §2) alike. It is the type-level counterpart of the partial-entity-pattern expansion (§8.3), and follows directly from "types are terms" (§4.4) — the same generalize-missing-arguments-to-fresh-variables mechanism, applied to the type sublanguage. Its effect is that a signature written against a bare sort still threads bindings: a parameter declared `s: Stream`, unified against an argument of type `Stream[T = Int64, E = {}]`, binds the expanded `T` and `E`, so both the element type and the access effect ground at the call instead of silently dropping. Without it, a bare `Ref(Stream)` carries no slots and unification binds nothing. In **type position** a bare parametric sort name is always an instantiation, so — unlike entity *data* terms, where bare `account` stays a reference and only `account()` expands — no parentheses are needed to trigger it. A *cross-sort* case, where the argument's sort merely *provides* the expected spec (a `List` used as a `Stream`), is the complementary mechanism: provider admissibility (§8.2) supplies the parameter bindings from the provider fact. See proposal 045 §5.1.1 for the effect-row instance and `docs/proposals/library/002` for the `Stream`/`iterator` walk.

**A variable frees its own SLOT, not the head above it (WI-RKMD4).** A parameter type carrying a type variable is checked at a call like any other; the variable makes free only the *slot it occupies*. `sum(m: Text[Trust = ?t]) -> Text[Trust = ?t]` applied to a `Message[Trust = Untrusted]` is refused at `Message`/`Text`, because no instantiation of `?t` could repair a disagreement at the **head constructor**. The refusal descends through the parameters two instances of one sort share, so `List[T = Message[…]]` against `List[T = Text[Trust = ?t]]` is refused one level beneath a `List` both sides agree on, and it reaches a **callback's parameter** — `f: (m: Text[Trust = ?t]) -> Int64` given a `Message`-taking arrow — by the same rule. Heads are compared by the ordinary nominal relation, so entity subtyping, `refines`, an alias's shape and provider admissibility all still accept — a carrier is usable where a bare spec it *provides* is declared, exactly as it is anywhere else (§8.2), and the head rule adds no second opinion about when two sort identities are one. What is *not* decided is a pair that is not a nominal head on both sides — an arrow, a tuple, an effect row, a neutral projection, a variable, or a head that is itself a parameter (`sort Spec[F[T]]`'s `F`, which unification FILLS) — and, at the ARGUMENT position only, a declared `Option[T]` or a reflect `Term`, since a bare `T` at the first is the some-coercion and the second takes a value of any sort. Those two are conversions the argument position performs, so they excuse a head disagreement *there* and nowhere deeper: a wrong sort against a nested `Option` slot is refused like any other.

This is stated as a rule rather than left to the checker because accepting such a mismatch is not a neutral outcome. The variable it fails to reject stays **unbound**, and an unbound variable is the *maximally permissive* value, since the consumer instantiates it to whatever it wants. Where the variable carries an information-flow label the effect is laundering: measured on `examples/guardians`, a `Text[Trust = ?t]` summarizer handed a `Message` left `?t` free, the sink bound it to `Public`, and the exfiltration was accepted. A wrong program being admitted is the smaller half; the constraint the variable existed to carry being discarded is the larger one.

**An unwritten parameter is fresh at each call, so the BODY must hold for every instantiation of it.** The expansion above says what an unwritten parameter means at a call — a fresh variable, bound there from the argument. That is also what it means for the declaration: `s: Stream[T = Int64]` is `s: Stream[T = Int64, E = ?]`, and `?` is a *new* variable per instantiation, so the operation is universally quantified over it. A body may therefore only do what holds for **every** `E`:

```anthill
operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64   -- demands NO effects

operation feed(s: Stream[T = Int64]) -> Int64 = takes_pure(s) -- REFUSED: E is any row, not {}
```

`feed` is refused at its own declaration, not at its callers: it claims to accept a stream at any row and then hands it to something that accepts only the empty one. The two spellings that say the same thing are refused the same way — `feed[E](s: Stream[T = Int64, E = E])` names the quantification explicitly, and a bare `feed(s: Stream)` leaves both parameters unwritten. An author who means the empty row writes it:

```anthill
operation feed(s: Stream[T = Int64, E = {}]) -> Int64 = takes_pure(s)   -- accepted
```

Inside a body, then, an unwritten parameter is **rigid** — a skolem that unifies with nothing but itself — exactly as an operation's own `[T]` and its enclosing sort's parameters already are. At a *call* it is flexible again, and binds from the argument. Same variable, two positions, and confusing them is what the rule exists to prevent.

**A variable the author WRITES in a parameter type is the same rule, spelled out (WI-1FKR2).** `operation via(b: Box[?t]) -> Box[?t] = id(b)` names its quantified parameter instead of leaving the slot open, and §5.4's *"Which variables the ∀ quantifies"* is what says `?t` is quantified: a variable named in a parameter type binds, exactly as an omitted slot does. So it is rigid in the body and flexible at a call like every other family above — and the tie the author wrote is what carries the caller's variable through, so `via` returns *its own* `?t` rather than something derived from `b`. This is what lets a generic operation be implemented in terms of another one, which is otherwise impossible: every generic operation would have to be a primitive. While the body left such a variable flexible, the unwritten-slot filler (§"How the slot is named", just below) reached it — that filler reads *any* still-flexible variable as an omitted slot — and rewrote the parameter to `Box[T = b.T]` while the return still said `Box[T = ?t]`, so the two stopped naming one thing. The **anonymous** spelling `?` is not this case and keeps the filler: it names nothing and ties nothing, which is exactly what makes it the omitted slot rather than a variable.

The same rigidity is what refuses a body that *pins* such a variable. `operation leaky(x: ?t) -> Int64 = sink(x)` with `sink(n: Int64)` is refused at `sink.n`, for the reason `feed` above is refused: `leaky` claims to accept every `?t` and then hands it to a slot that accepts one. It refuses a body that pins it through a **`requires`** for the same reason and with the same words (WI-K88TN): `relay(t: Text[L = ?m]) = send(t)`, where `send` demands `flows_to(?l, Public)`, claims to accept every `?m` and then hands it to a sink that accepts one — decided by §5.4's value-precondition rule rather than by type unification, but the same quantifier deciding it. The repair there is to declare the clause, which passes the obligation to the callers who choose `?m`.

**How the slot is named (WI-1059).** The skolem an unwritten slot takes is the *projection off the value that carries it* — `s: Stream[T = Int64]` is checked as `s: Stream[T = Int64, E = s.E]` — and not a fresh anonymous variable. `s.E` is already rigid by §"path-dependent types" (a neutral equals only an identical neutral, never a concrete type), and it is the name a signature can already write: `operation collect(s: Stream) -> List[T = s.T]` says `s.T` in its own return, and the body must resolve the parameter to the *same* thing that return does. A *self*-sort reference is the exception, and §3 of `docs/design/type-parameter-scoping.md` is what decides it: within a sort's own definition a bare self reference participates in the parametricity tie, so `append(xs: List, ys: List)` declared inside `sort List` ties both to *this* sort's `T` rather than giving each its own projection.

**Enforced throughout a parameter's type (WI-1059 at its top level; WI-1061 nested inside a binding).** Each program below is refused at its own declaration, naming the row it may not assume — never at the caller that exploits it, since refusing there would make every legitimately row-polymorphic signature unusable:

```anthill
-- top level (WI-1059): the row is missing from `s`'s own type
operation feed(s: Stream[T = Int64]) -> Int64 = takes_pure(s)
--                                              ^ refused: expected E = {}, got E = s.E
operation caller(s: Stream[T = Int64, E = {Error}]) -> Int64 = feed(s)   -- not refused here

-- nested (WI-1061): the row is missing one level down, inside a written binding
operation feed(l: List[T = Stream[T = Int64]]) -> Int64 = takes_pure(l)
--                                                        ^ refused: expected E = {}, got E = ?E
operation caller(l: List[T = Stream[T = Int64, E = {Error}]]) -> Int64 = feed(l)
```

Note that a *bare* reference says strictly less than a partial one: `Stream` leaves `T` unwritten too, so `feed(s: Stream)` may no more hand its stream to an `Int64`-element slot than it may assume a row. The four spellings are one type only in the parameters they all leave unwritten.

**Which skolem, by depth (WI-1061).** Only the *filler* differs. At the top level the slot takes the projection above, because the language already spells that name. A nested slot has no name at all — nothing spells the inner row of `List[T = Stream]` — so it takes a *fresh* rigid, one per slot. The *self*-sort exception overrides both depths, since the parametricity tie is the sort's: a self reference nested in a binding takes this instance's parameter exactly as a top-level one does.

Depth means the parameter type's whole structure, not only its sort-application bindings: a callback's **result** (`f: (x: Int64) -> Stream[T = Int64]`) and a **tuple component** (`p: (s: Stream[T = Int64], n: Int64)`) each carry unwritten slots too, and each is rigid in the body. Two children are excluded, each for its own reason. An **effect-row** binding or an arrow's **effects** (`Stream[T = Solution, E = Error]`) is a row whose labels are compared by structural identity against the effects a body incurs, so materializing a label's own parameters would make two spellings of one effect unequal. A callback's own **parameter** is excluded because the quantification faces the other way there: an unwritten slot in `f: (a: Cell) -> Unit` says `f` accepts *every* instantiation, so the body may hand it whatever it has — rigidifying it would say `f` accepts one fixed unknown instead.

The `effects` clause is likewise **not** a position for this rule. An effect atom is a row, a projection, a value-in-type denotation or a concrete label, and where a parametric sort is written there the effects check already refuses a body that incurs a *more* specific instance than the declaration names (`effects Box` against an incurred `Box[T = Int64]`) — strict in the safe direction, so the laundering this rule prevents cannot be built through it.

**In a RETURN the quantifier flips to ∃ (WI-1063).** Read the quantifier off the arrow's polarity. A parameter's unwritten slot stands in *negative* position and is **universal**: the caller instantiates it, which is the same fact the paragraphs above state from the two ends — flexible at a call, rigid in the body. A return's unwritten slot stands in *positive* position and is **existential**: `-> Stream[T = Int64]` declares `∃E. Stream[T = Int64, E]`. So the two halves are

- the **body packs** — it exhibits a witness, and that is all an existential asks. A body whose inferred type is *more specific* than the declared return is doing existential introduction, not making a mistake;

- **each use opens** — it mints a **fresh** skolem per opening, so the result of `widen(s)` is `Stream[T = Int64, E = ρ]` with `ρ` rigid. Freshness per opening is load-bearing: two calls may legitimately return different rows. *Use*, not *call*, is exact: a nullary operation named without parentheses is a use, and so is naming an operation where a function is expected — the eta arrow's result opens as well. That last one opens once per lift rather than once per application, because an arrow type has nowhere to write `∃`; it is why an operation with type parameters has no function-value form either.

```anthill
operation widen(s: Stream[T = Int64, E = {Error}]) -> Stream[T = Int64] = s
--                                                                        ^ correct: packs E := {Error}
operation exploit(s: Stream[T = Int64, E = {Error}]) -> Int64 = takes_pure(widen(s))
--                                                                        ^ WRONG: ρ is not {}
```

Where the skolem is minted is the whole design. It is minted **at the call**, so `widen` is left alone and `exploit` is refused at `takes_pure`'s parameter. Minting it in the *body check* instead demands the body be good for every instantiation — universal quantification in a positive position, the wrong quantifier — which refuses `widen` itself and costs 40 tests across thirteen delivered tickets; that reading was built, measured and rejected.

Three of the four spellings are existential here — a bare reference, a partial application and an explicit `?` all leave the slot for the body to witness. The fourth is not: an **operation type parameter** in a return (`mk[E]() -> Stream[T = Int64, E = E]`) is the *caller's* to instantiate, and a call that pins it from nothing is already the loud `expected a type for 'E', got unconstrained`. That is the same asymmetry the whole section rests on, read at one more position.

**A named variable is existential unless the SIGNATURE binds it (WI-1078).** `?name` is the fifth spelling, and it opens like the other three: `-> Stream[T = Int64, E = ?E]` launders exactly what the omitted and `?` spellings do. What the name buys is what §"Sort composition" says it buys — it **binds across the term** — and that is a question about the whole signature, not about the return:

- a variable the declaration *also* uses where the caller supplies or instantiates it is **bound**, an ordinary universal, and nothing opens it — this call's arguments are what pin it. Three binders count: a **parameter** type (`mplus(a: LogicalStream[?A], b: LogicalStream[?A]) -> LogicalStream[?A]`), the operation's own **`[A]`**, and a **`requires`** bound, since `-> List[T = ?C] requires Eq[T = ?C]` is a universal *with* a bound;
- a variable used **only in the return** is **unbound** — the existential the polarity rule describes — and opens at each use.

The declared `effects` are not a fourth binder: a row the operation incurs stands on the same side of the arrow as the return, so it relates two positive positions and binds neither. The **enclosing sort's** parameters need no entry either, though a foreign return may name one without any parameter type mentioning it (`toPair(h: Holder) -> Pair[A = T, B = T]` writes `Holder` bare): a sort parameter *written* in a type is a reference to its own symbol, not a logical variable, so it is not something this rule can open. Only a variable **written in the declared return** is a candidate at all — one that reaches a call's result by eliminating a projection (`takeN(s: Stream, n: Int64) -> List[T = s.T]` against a receiver whose element type is a variable) belongs to the receiver, not to the callee's signature.

**What opens is a sort-parameter SLOT**, here as throughout this section — a binding inside a sort application, an arrow's result, a tuple component. A return that *is* a bare variable (`-> ?A`, with no sort applied around it) is not a slot and is not opened; that is the same scope the omitted and `?` spellings have always had, not a carve-out for names.

**Sharing survives the opening**, which is the half of the spelling that was real. `?` is fresh at each occurrence and takes a rigid per *slot*; a named variable is opened once per use and shared by every slot it appears in, so `mk_same() -> Pair[A = ?t, B = ?t]` opens to `Pair[A = ρ, B = ρ]` and still says its two components agree. A consumer may rely on the agreement and on nothing else: `needs_same(p: Pair[A = ?u, B = ?u])` is accepted, `needs_ints(p: Pair[A = Int64, B = Int64])` is refused.

A slot on a reference to the **callee's own sort** is not existential: it is the §3 parametricity tie of `docs/design/type-parameter-scoping.md`, naming this instance's parameter, which rides the canonical channel rather than being opened. Only a *foreign* sort's unwritten slot is opened — the same scope the parameter-side expansion uses. Both spellings agree there, and that is what carries the `empty` of a parametric container: `List.empty()` and `LogicalStream.empty() -> LogicalStream[?A]` are members of the sort their return names, so neither is opened — the named variable was never what was holding the second one up.

**The tie is WRITTEN, not left as an absence (WI-1082).** Saying a self slot "rides the canonical channel" was not enough on its own: a slot nobody writes is width-**ignored** at the consumer, so nothing was claimed about it and nothing could refute a demand. `operation widen(s: MyStream[T = Int64, E = {Error}]) -> MyStream[T = Int64] = s` declared *inside* `sort MyStream` therefore loaded and its result satisfied a parameter declaring `E = {}` — §8.1's headline exploit surviving on the self side, in **both** spellings alike. So a declaration inside a sort's own body that names that sort and elides a slot is rewritten to name **that sort's own parameter**, once, before any body check or call site reads the signature. §3 names three positions and all three are rewritten: `insert(c: List, elem: T) -> List` means `-> List[T = T]` (which is what `SortedSet.insert(s: SortedSet[T = T, O = O], x: T) -> SortedSet[T = T, O = O]` already writes by hand); a **parameter** that partially writes the sort — `widen(s: MyStream[T = Int64])` — means `s: MyStream[T = Int64, E = E]`; and an **entity field**, §3's own example, means `entity cons(head: T, tail: List)` ⇒ `tail: List[T = T]`, so a `case cons(x, rest)` binds `rest` at this instance's element instead of at nothing.

The parameter position is what makes the rule hold for a member with **no body**: with only the return rewritten, a self parameter that elides a slot still claims nothing, the argument never reaches the sort's parameter, and the return's copy of it stays a variable that unifies with anything — so a body-less `operation widen(s: MyStream[T = Int64]) -> MyStream` laundered exactly as before. A **bare** self parameter is the one case left alone: `unify_parameterized_with_sort_ref` already binds the sort's parameters when one side is a bare reference, and writing the tie in makes that binding strict enough to refuse a sibling member called at a different element (`List.mapElems` calls `reverse` at `Dst`, not at the enclosing `T`).

Two consequences are worth stating outright. First, **for a member with a body the refusal moves to the declaration.** Within a member body the sort's parameters are rigid — the tie read as parametricity — so `widen`'s body must hold for *every* `E`, and `= s`, pinned to `{Error}` by its own parameter, does not. The error names `widen.return`. (A body-less member has nothing to check, so its refusal stays at the consumer, where the argument's row now reaches it.) The rule: *a member may not pin its own sort's parameter to a constant and still elide it in the return*; writing the return out (`-> MyStream[T = Int64, E = {}]`) is unaffected, since a **written** slot is never rewritten. Second, **all the spellings still agree**: `-> S[E = ?E]` is rewritten exactly when WI-1078's classification calls `?E` unbound, so the named and omitted spellings remain one type — the self case answers with the tie where the foreign case answers with a fresh ρ.

An operation with **no parameter naming its own sort** is left alone: `List.empty() -> List` has nothing at a call that could bind the sort's parameter, so writing it there would put an unbindable variable in the result. Its slot stays open and the caller's expected type determines it — right for `empty`, whose body holds for every `T`, and not expressible-otherwise. `PolyType` (WI-1083) does **not** change that: it is inferred where an operation becomes a **value** (§5.4) and there is still no way to *write* a ∀ in a return, so `empty[T]() -> List[T = T]` — which loads today — remains the only spelling of the universal here, and it says it with a **declaration's** binder rather than with a quantified type.

Opening is what erasure *is*. A consumer may rely only on what the type carries, so a value whose element type the signature never wrote cannot have it recovered downstream, not even by an annotation: `makeList() -> List` is `∃T. List[T]`, and `let l : List[T = Int64] = makeList()` is refused.

**How the opened slot is REPRESENTED (WI-1079).** The ρ an opening mints is a logical variable of the *rigid* kind, and reflect names it: `anthill.reflect.extract` reports it as `TypeExtractor.Skolem(name, id)`, beside `FlexVar(name, id)` for a still-flexible one. The two are separate forms because they answer opposite questions — a skolem unifies with **nothing but itself** (it is the opaque constant a consumer may assume nothing about, which is what makes the opening sound), while a flex variable unifies with **anything** (an instantiated `∀`, the type `empty()` has before its context pins it). `id` is the identity and `name` is only what a diagnostic prints: two skolems minted for one parameter name render alike (`?E` vs `?E`) and are different types, so a consumer comparing them must compare `id`. Distinguish all three from `TypeVar(name)`, which is neither — it is the *placeholder* for a type the extractor could not name (an un-annotated lambda binder), carries no identity, and is not a variable at all. The **bound** variable of a `∀` arrived with WI-1083's binder: it is an element of a `TypeExtractor.PolyType`'s `binders` list (§4.4, §5.4), which is a list of variables precisely so that `id` says which occurrences of the quantified body it binds. Instantiating a `PolyType` turns each binder into a fresh `FlexVar`; opening an existential turns a slot into a `Skolem`. The three forms are one lifecycle.

The language already implements this rule for the *carrier* of an existential return, explicitly spelled: `ensures Spec[C]` (§"path-dependent types", WI-402) has the body witness `C` while the caller sees only the spec. The **members** are opened by the same rule as a bare return's, and had to be: the loader rewrites `-> C ensures Spec[C]` to a bare `-> Spec`, so before WI-1063 the same `openOne(m) -> C ensures KVStore[C]` whose witness binds `K = String` satisfied a demand for `K = Int64`. Writing `ensures` bought nothing there — it was one gap in two spellings, not a bare-return quirk. `docs/design/type-parameter-scoping.md` §5's informal "erased" is this existential said without the word.

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

**A query yields ANSWERS; a relation yields PROOFS** (WI-FFPGD). Backward chaining enumerates *proofs*, and one answer can have many: a body variable written `?` is **existential**, so `rule tagged(?t) :- check(t: ?t, witness: ?)` over three `check` rows two of which agree on `t` is proved three ways and answers **twice**. A query's result is therefore projected onto the query's own goals — two proofs agreeing on every query variable are ONE solution, however differently they were derived, and two disagreeing anywhere in the query are two, however much of the proof they share. The projection is over the whole goal **vector**, not any one goal: `a(?x), b(?y)` over two facts each still has four answers. A **query** variable is part of the answer however it is spelled, `?` included — the caller can read its binding, so it distinguishes.

Two cases deliberately do **not** collapse, both fail-open (a duplicate answer, never a lost one): a solution whose substitution *bears an opaque* anywhere — a closure, a stream, a `Map`/`Cell` handle, or one nested inside a tuple or entity — since such a value has no structural fingerprint and two genuinely distinct external rows would key alike; and a goal with an opaque spliced into it directly, which no scan of the substitution can see.

The other face is the **relation** (proposal 052): `Relation[T]` is an unordered **bag** whose multiplicity is the number of proofs — `union(r, r)` yields each row twice, a zero-column membership relation counts its derivations, and `Relation.set` is the explicit operator that collapses them. Relation consumption takes the resolver's stream as-is and is not projected. The two faces ask different questions of one engine, and each says which at its entry point.

**Unification:** Standard first-order unification. `Var` terms unify with any term of the same type. `Fn` terms unify if their names match and all arguments unify pairwise. Its user-facing surface operator is `<=>` (see below).

**Equality: test vs. bind, structural vs. semantic** (proposals 049 + 051). Equality-shaped notions differ on two axes — *test* (compare, never bind) vs. *bind* (unify), and *structural* (raw term structure) vs. *semantic* (the carrier's `Eq` instance) — and the language gives each cell its own operator:

|                | test (no binding)  | bind (unify) |
|----------------|--------------------|--------------|
| **structural** | `===` (`struct_eq`) | `<=>` (`unify`) |
| **semantic**   | `=` / `eq`         | E-unification *(future engine)* |

- **`=` — the semantic equality *test*** (`PartialEq.eq`, a dispatched operation returning `Bool`). It reduces both operands and compares them **through the carrier's `PartialEq` instance** (WI-616): structurally identical operands are equal by reflexivity, and structurally distinct operands dispatch to the carrier sort's own `eq` override when it declares one — `Set` and `Map` are the first non-structural instances (`eq({1,2}, {2,1})` holds: membership equality, resolved against the carrier's rules by ordinary SLD). A carrier with no override keeps the structural compare — structural equality *is* its instance (`Int` stays a machine compare). **Partial vs. total (proposal library/004, WI-644):** `eq`/`neq` live on the base **`PartialEq`** spec — a plain `Bool` test with *no* reflexivity law. **`Eq`** `provides PartialEq[T = T]` — a conversion, so it is a chain entry AND a derivation (WI-1110: it was `requires PartialEq` until the two clauses were told apart, and a carrier writing `provides Eq[X]` now gets `provides PartialEq[X]` derived rather than writing it) — and adds the checked law `eq_refl: eq(?a,?a) <=> true`; requiring `Eq[T]` (what `Set`/`Map` keys, dedup and sort demand) means "a *lawful*, reflexive equality." IEEE **`Float` provides only `PartialEq`** (plus the witnessed `NonEq`) — `eq(nan, nan)` is *false* (IEEE), and `Float` cannot discharge `eq_refl`; the wrapper `TotalFloat` provides the lawful `Eq` (it is **not** `Ord` — a functional total float order needs host support). So the interpreter, resolver, and C++ codegen all agree on `Float` (IEEE), while `nan === nan` (`struct_eq`) stays structurally true. **That requirement is enforced where a container type is written** (WI-644/WI-835): instantiating a sort that `requires Eq` at a parameter with a carrier that provides `NonEq` is a **load error** — `Map[K = Float]` / `Set[T = Float]` are refused *wherever the type is written* (an entity field, an operation parameter or return type, a `const`'s type, a sort alias, a body `let` annotation, a typed lambda binder, a binding value inside a `requires`/`provides` clause, and nested inside any of those), naming the sort, the parameter, the carrier and the required spec; `Map[K = TotalFloat]` / `Map[K = Int64]` load. The refusal is negative — it fires on a *witnessed* `NonEq` carrier, not on the absence of an `Eq` provision, so an abstract type-parameter binding stays accepted. It reads the key's *own* provisions, so a key whose unlawfulness is in its **argument** (`Map[K = List[T = Float]]`, `Map[K = (a: Float)]`) is a known remaining gap, not a guarantee. **A composite DERIVES its classification, both ways** (WI-664 / WI-1098): an entity or named tuple whose fields are all lawful is a `Total` composite and the loader asserts `provides PartialEq` + `provides Eq` for it, so `List.contains(colours, red)` discharges its `requires Eq[T]` with no provision line written — before this, such a program loaded clean and died inside the evaluator at the first requirement it reached. One whose field reaches an IEEE `Float` is `Partial` and gets `provides PartialEq` + `provides NonEq` instead, which is what makes a user `provides Eq[Point]` over a `Float` composite a load error (`Eq` ⊥ `NonEq`). The two are one fixpoint over the field-reference graph, so a *recursive* composite (`node(l: Tree, r: Tree)`) is classified too, and a lawful-`Eq` **boundary** — a carrier whose `eq` is dispatched, `TotalFloat` being the shipped one — is neither classified nor overwritten: its `eq` is the author's. Nothing is derived for a **parametric** sort or for a composite with a parametric field (`hold(p: Pair[A, B])`): their lawful equality is *conditional* on their arguments' (`provides Eq[Pair] :- Eq[A], Eq[B]`), and an unconditional claim would make `List[Float]` lawful. Writing the provision by hand stays legal and is not duplicated — the derivation skips a carrier that already provides. `=` **never binds** a logical variable: `eq(7, ?p.x)` succeeds once `?p.x` reduces, but `eq(?v, ?p.x)` does **not** bind `?v` (a flex `=` that is never discharged is carried as an undischarged residual, not counted as a solution — WI-519). Use `=` for body-goal tests, operation contracts (`ensures eq(balance(result), …)`), and constraints — a postcondition must *test*, never bind. `neq` (`!=`) pairs with it: `neq(a,b) <=> not(eq(a,b))`, the negation of the *dispatched* equality. (Ordering mirrors this, and since **WI-1109** it has THREE floors rather than two — `gt`/`lt`/`gte`/`lte` are the base **`PartialOrd`** surface, IEEE-partial for `Float`; `compare` and the order laws live on **`WeakOrd`**, which `requires Eq, PartialOrd` and is TOTAL but whose kernel may be strictly *coarser* than `Eq`, so it partitions a carrier into equivalence classes; and **`Ord`** adds only the converse law — `compare(a,b) = 0` implies `eq(a,b)` — making the kernel exactly `Eq`. `Ord provides WeakOrd`, so a carrier writes one provision and the loader derives the floor below; since **WI-1110** that clause is `Ord`'s *whole* content — a spec's `provides` is a chain entry as well as a derivation, so `WeakOrd`'s `requires Eq, PartialOrd` reach the carrier through it and `Ord` restates neither (§5.1). The practical consequence is stated at `sortedset.anthill`: a `SortedSet` keyed by a `WeakOrd` that is not an `Ord` stores CLASSES — it collapses members that compare equal, and its `union` keeps the left operand's representative, so it is not commutative. Requiring `Ord` is what buys a set of elements.)
- **`===` — the structural identity *test*** (`anthill.kernel.struct_eq`, a resolver builtin; WI-615). Total, carrier-agnostic, **never dispatches**, and needs **no `Eq` instance**: it answers "are these two values literally the same structure" for every value (opaque handles compare by identity). Two membership-equal sets in different spellings are `=` but not `===`. Use it for term/symbol/reflected-structure identity — comparisons that must not suddenly depend on a carrier's custom equality. Being a *test*, it is **not a defining connective**, and a **`lhs === rhs` rule with no body goals is refused at load** (WI-1090) naming `<=>` as the substitute — a `fact lhs === rhs` too, a fact being a bodyless rule (§6.1), and a rule whose only goal was a folded `Spec[T]` bound, that guard being a bound rather than a goal: the builtin answers every `===` goal itself, so no clause of it is ever consulted, `[simp]` never fires it (the normalizer reads the `<=>` equations), and its subject would be left naming no callable. A rule with a real **body goal** is untouched — that is not an equation (§8.3) but an ordinary law about the operator, and `totalfloat.anthill` writes one (`rule eq(?a, ?b) :- ?a === ?b`). Being carrier-agnostic, `===` is also **not shadowable**, on the same rule and for the same reason as `<=>` below: a namespace declaring its own `struct_eq` does not capture the operator, and only a *written* `struct_eq(a, b)` call reaches such a declaration. **`=` is held to the defining rule too** (WI-888): it is the other half of the test column, so a bodyless `=` head is refused too, and for the same reason rather than a second one. The two refusals *replace* different things and their messages differ accordingly — a `===` head was silently useless, an `=` head fired — so the `=` message names the substitute spelling and withholds the "give it a body goal" remedy, a guarded `=` equation being read by no firing site.
- **`<=>` — structural *unification*** (`anthill.kernel.unify`, a resolver primitive). It binds via a substitution effect on the resolver frame: `?v <=> ?p.x` binds `?v` to the projected value; `some(?x) <=> some(3)` binds `?x ↦ 3`. It is **occurs-checked** (`?v <=> f(?v)` is a loud failure, never a cyclic term), **symmetric** (either side may be the variable side), and **structural-only — it never dispatches**. It is the connective of equational rule heads — the **only** one, §5.3 — and the substrate of `let`. Because it never dispatches, it is also **not shadowable**: a namespace that declares its own `unify` does not capture the operator, so a `<=>` written there still means this primitive (WI-888; `anthill.reflect` declares one, for the term-level face below). Only a *written* `unify(a, b, kb)` call reaches such a declaration. `=` is deliberately the opposite — a carrier's own `eq` **is** meant to override it.

**Declaring a non-structural `Eq` instance.** A carrier declares the instance with `provides Eq[T = <Carrier>]` and supplies its own operation short-named `eq` (the same short-name override convention as every spec-op dispatch), backed by relational rules — see `Set.eq` / `Map.eq` in the prelude. Dispatch reads the operand's head at resolution and proves the carrier's `eq` in a closed sub-proof, three-way honest:

- Only **fully ground** operand pairs dispatch — `=` never binds, so a compare containing an unbound variable *suspends* (undecided) rather than proving-by-binding or deciding structurally.
- An overriding carrier **buried** inside non-overriding structure (`some({1,2})` vs `some({2,1})`) also suspends: a structural verdict would ignore the inner instance.
- The sub-proof is bounded; a compare too large for the budget degrades to *undecided*, never to a wrong verdict.
- Caveats: write relational base cases with a **body** or on a helper op — a bodyless 2-ary rule whose head is short-named `eq` is currently classified as an equational law and never fires at resolution (WI-627). Supply `eq` only: `neq`/`!=` is always derived as the negation of the dispatched `eq`, so an own `neq` member is never consulted — and since **WI-1125** a carrier that supplies one is a **load error** (`CarrierSuppliesNeq`), through any of the three supply routes (own member, `fact PartialEq[T = C, neq = …]`, witness sort) and whether or not it also supplies an `eq`. It was accepted and ignored before: with no `eq` beside it the equality answered *structurally*, against the very inequality the carrier had written, at all four `prove_from_gamma` consumers and in the interpreter; with an `eq` beside it the `eq` decided (correctly — it is the authority the law names) and the `neq` was dead text that could only disagree, which nothing checked and nothing can, since `∀a,b. neq(a,b) = not(eq(a,b))` is not decidable at load. Refusing the member makes that disagreement unrepresentable rather than partially checked. The repair is the same equality one member over: `operation neq(a, b) = false` is `operation eq(a, b) = true`. A **spec** declaring the family for its own type parameter (`sort MyEq { sort T = ?; operation neq(a: T, b: T) -> Bool }`) is a declaration, not a carrier override, and is untouched. And the instance dispatches at **SLD resolution** — an *evaluated* operation body reaches it through the typeclass dispatch machinery, while the interpreter's raw `eq` fallback is still the structural compare pending the SLD→eval bridge (WI-625).

**`let ?v = expr`** is directed sugar for **`?v <=> expr`** — one primitive, two surfaces: `<=>` for symmetric equations, `let` for introducing a named binding in a goal sequence. (`:=` is *not* this — it is reserved for the mutable-cell `Cell.set`, `c := v`, which overwrites state rather than binding a logical variable once.)

**Negation.** Because `=` never binds, `not(eq(…))` is always safe. A `<=>` under `not` needs a **static allowedness** check: any variable occurring in a `<=>` under negation must be bound by an earlier positive goal, or the loader raises a load-time error (WI-525).

**Partial entity patterns:** When an entity term appears with fewer named arguments than the entity declares, the missing fields are automatically generalized to fresh anonymous variables. This means `account(owner: "Alice")` is equivalent to `account(id: ?, owner: "Alice", balance: ?)`, and `account()` is equivalent to `account(id: ?, owner: ?, balance: ?)`. The expansion applies whenever the functor is a registered entity — including the zero-argument case, where parentheses signal pattern-matching intent (bare `account` without parens remains a reference to the entity/sort). This convention avoids requiring the user to explicitly list unneeded fields with `?`. (Its type-level counterpart — fresh variables for the unbound *parameters* of a parametric sort used as a type — is **expansion during unification**, §8.1.)

**Termination:** The kernel uses stratification and loop detection to ensure rule evaluation terminates. Recursive rules must be stratifiable (no negation through recursion in the basic mode; stratified negation is supported for constrained cases).

### 8.4 Constraint Enforcement

Only **registered quantified guards** are currently enforced. Each such guard is
checked once after the complete source set has loaded and again when a fact that
matches one of its trigger sorts is asserted:

1. The post-load check blocks the load when the guard is violated, cannot be
   lowered, or cannot be decided within the resolver budget.
2. The per-assert check retracts and rejects a newly inserted fact when the guard
   is violated or undecidable.
3. A labeled violation identifies the source constraint in its diagnostic.

An ordinary denial/invariant constraint is currently stored as reflected
structure but is **not** registered as a guard and therefore does not reject a
load or assertion. Aggregation constraints and unsupported quantified shapes are
refused loudly instead of being accepted without enforcement. See §6.2 for the
exact surface boundary; WI-882 tracks the misleading legacy plain-denial uses.

### 8.5 Operation Contracts and Obligations

**This section is about the IMPLEMENTATION side of a contract, and it is not the
whole story of `requires`.** §5.4 splits an operation's `requires` list per conjunct
into a **value precondition** — proved at the *call site* from what the caller knows,
an unproved one being a load error — and a **type precondition**, which names a spec
and is never proved from the caller's Γ. Read §5.4 first for which clause is which
and what checks it; what follows is what the kernel does with a contract once an
implementation claims to satisfy it. (This section predates that split and used to be
cited as though it covered the call site too.)

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
- **exposed** — the scope's entity-variant names, filtering its *variant
  exposure* link alone (see below);
- **parents** — included scopes, each carrying the CLAUSE THAT WROTE IT:
  *enclosing* (the lexical sort/namespace body it sits in), a `requires` /
  `provides`, a wildcard `import`, or a *variant exposure*. The three
  non-enclosing kinds resolve differently, so the kind is recorded rather than
  inferred from the shape (WI-M460D); a link two clauses justify carries both,
  and the more permissive one governs;
- **type parameters** — `sort T = ?` names, which do not leak to parents.

**The top-level scope.** A file's top-level declarations land in one synthetic
scope, shared by every file and by the host-supplied and command-line names that
read at the top level. It is not a declaration, so it has no qualified name; a
diagnostic calls it by the name it is interned under, `<global>`. That spelling
is deliberately **outside the identifier token** (§2.3): were it inside, as
`_global` was, `namespace <that name>` would *define a second scope* — a
declaration is registered by qualified name and does not consult the interned
one — and the two would then be indistinguishable in every message that names a
scope. The angle brackets make the second scope unrepresentable rather than
merely refused, which is the same argument `..` rests on (§2.3). Declaring
`namespace _global` is therefore ordinary and means nothing special.

The guarantee is exactly as wide as the identifier token, which is why it is
stated here rather than left to the implementations. §2.3's **quoted
identifier** (`"my weird name"`) admits arbitrary text and would readmit the
collision; neither implementation parses one today, and whichever adds one must
either exclude this name from it or move the sentinel out of its reach.

**How a diagnostic names a scope (WI-977).** Wherever a message reports the scope a
name was resolved in — `unresolved name`, `unresolved type name`, `ambiguous
symbol`, the duplicate-declaration refusal of §5.1, the forbidden-internal
refusals below — it spells that scope by its **qualified** name:
`in scope 'demo.User'`, never `in scope 'User'`. A short name does not say *which*
scope among siblings, and the reader chasing the diagnostic has only the name to go
on: the two `sort User` bodies of a two-namespace program otherwise produce
byte-identical refusals. Qualification also keeps a nested scope's rendering
distinct from its parent's, a child's qualified name strictly extending the
enclosing one. The top-level scope, having no qualified name, renders `<global>`
as described above.

The scope named is the one the offending code is **written in** — for code in an
operation body, that operation's own scope, not its enclosing sort. Diagnostics
raised by different subsystems (name resolution, type checking) must agree here;
naming the sort in one and the operation in the other reports two scopes for one
line of code.

This is a single rule with a single implementation per port rather than a
convention re-applied at each raise site: rustland answers it at
`KnowledgeBase::scope_display_name`, scaland at `KnowledgeBase.scopeDisplayName`.
It is **total** — a scope is identified by a scope id, whose owner projection
cannot fail — so no message needs a placeholder for a value that names no scope,
and none may invent one.

**Visibility model.** A name is **visible by default**, across namespace and
sort boundaries, to importers and requirers. The modifiers adjust this:

- **`internal`** — hides the name from cross-scope resolution (it remains
  resolvable within its own scope, and within scopes that reach it by *enclosing*
  links — a nested sort or namespace body, and an operation's own scope inside
  it). This is the only hide gate.
- **`public`** — visible everywhere, including without an `import`.

**Top-level code is outside every declaring scope but the global one (WI-977).**
The top-level scope encloses nothing, so an `internal` name declared in any
`namespace` or `sort` is hidden from a top-level declaration exactly as it is from
a sibling namespace — there is no "no scope, so no gate" case. This applies to
field projection as much as to construction: a top-level operation reading `b.v`,
where `v` belongs to an `internal` constructor of another sort, is the same
forbidden-internal access as naming that constructor directly. An `internal`
name declared *at* the top level is unaffected, the global scope being its own
declaring scope.

The former `export` statement and `export` visibility prefix (no-ops under this
model) were removed in WI-291.

**`resolve_in_scope(name, scope)`** — the resolution order:

1. a **local** of `scope` → resolved (a local shadows everything below);
2. an **imported alias** in `scope` → resolved, **if the asking file wrote it**
   (WI-995): an alias written by another file is not there at all, and resolution
   continues to the parents as if the import had never been written. Aliases
   belonging to no file — the implicit prelude, and `-i` invocation flags — are
   read by every asker;
3. otherwise recurse into the **parent** scopes. A *non-enclosing* parent is
   skipped when the name is (a) a type parameter of that parent, (b) marked
   `internal` there, or (c) absent from a non-empty **exposed** set of that
   parent **across a variant-exposure link, and only there** (below).
   *Enclosing* parents are never filtered;

   (c) is a property of the **link**, not of the scope at its far end. A
   `requires`, a `provides` and a wildcard import are non-enclosing links too,
   and they see the target whole — so a spec that acquires an entity constructor
   does not thereby hide its operations from the clauses that reach in for them.
   Where one link is justified both ways — a `requires` on a nested sort that
   also exposes variants — the reaching clause wins and nothing is filtered;
4. collect and de-duplicate by symbol: zero matches → unresolved, one →
   resolved, two or more distinct symbols → **ambiguous** (a load/query error).

**Dotted names — the fallback ladder.** When `resolve_in_scope` leaves a name
unresolved and it is a *path* — it contains a `.`, or carries the `..` marker —
which reading applies is decided by **how the path is spelled** (Rust; `scaland`
implements neither reading yet):

- `a.b.c` — **relative**, and only relative (**head-qualification**): resolve the
  *first* segment in scope, append the remaining segments to its
  `qualified_name`, look that up in `by_qualified_name`. This is what makes
  `Map.empty` work for an imported `Map`. A hit whose kind is **`Field`** is
  refused: entity fields are indexed under their constructor's path, and a field
  is reached by dot dispatch on a value, never by a path. A **miss** under the
  head the path bound is **loud**; the path is never re-anchored elsewhere.
- `..a.b.c` — **absolute**, always: the name *is* some symbol's own
  `qualified_name`, looked up directly — the same channel `import` uses, so
  nothing can shadow it. `..` is a marker, not an identifier, so it burns no name
  and cannot itself be shadowed (unlike Scala's `_root_`). A single segment
  counts: `..top` asks for the top-level `top`. The `internal` gate still
  applies — `..` escapes **shadowing**, not visibility.

The relative reading is not reached when the head resolves **ambiguously**: the
ladder answers with that ambiguity instead (below). An absolute path has no head
to contest. The relative reading admits no name without a dot — a short name is
not a path, and resolving one that way would reinstate the global short-name scan
removed in WI-476; the marker is what lifts that for `..top`, which is an exact
lookup of the name written rather than a search.

**A relative path still reaches the root**, which is why `..` is rarely needed:
the scope walk goes out to the top-level scope, where a top-level namespace is
an ordinary local, so with nothing shadowing `outer` the head of `outer.inner.g` binds the
top-level `outer` and the whole path resolves relatively. `..` is needed **only**
where something shadows the head.

**Why the absolute reading needed its own spelling (WI-1075).** Until then both
readings shared one, as an unconditional second rung under head-qualification,
and that rung's two jobs were indistinguishable at the point of decision — head
resolves locally, rung 1 misses, rung 2 hits. Measured: with both `outer` and
`inner` shadowed by members of the enclosing sort, `outer.inner.g(…)` still bound
`outer.inner.g` (the capability — an FQN needed no `import` and survived
shadowing of even its outermost segment); but a *relative* `inner.g` in that same
body, where a top-level `inner.g` also existed, bound the **top-level** one, and
with the two returning the same type nothing complained. The only difference is
whether the author meant the path absolutely, which is not in the text — a
relative path can *coincide* with some other symbol's fully-qualified name — so
every rule keyed on the old syntax picks one side and loses the other. Two
spellings, one meaning each, is the separation.

The marker **replaces** the implicit absolute reading rather than joining it:
leaving an unmarked path absolute-when-it-has-to-be would give one meaning two
spellings differing only in a rare corner, and the safe one is the one nobody
writes, because the unmarked one appears to work — the defect proposal 059 R4
refuses for `fact Spec[X]` vs `provides Spec[X]`. Migration was **zero**,
measured: an instrumented rung 2 over stdlib, `anthill-stl`, the examples and
`anthill-todo` fired **zero** times, and the count is kept executable.

**One implicit-absolute route survives, and only one:** a head-qualified hit
**hidden by `internal`**. Such a hit has not *bound* the path — the citing scope
may not see it — so the descent continues to the absolute reading, which is a
different question from a miss (WI-752). It is stood down under a **namespace**
head, which owns every path beneath it: an `internal` member there is a member
the citing scope is forbidden, reported as such, not a licence to bind a
same-spelled top-level path instead.

**An ambiguity ends the ladder.** The rungs below `resolve_in_scope` — the dotted
readings, then the implicit prelude / reserved kernel vocab — are for a name that
means *nothing* at this scope. A name that means *several* things has an answer
already, so no lower rung may be consulted: descending past a conflict picks a
symbol that is not even among the candidates, and picking one candidate decides
in the author's favour a conflict the author has to see. A position that only
asks *whether* a name denotes, such as the rule-head mint guard, counts an
ambiguity as denoting for the same reason.

A **dotted path** ends the ladder the same way, on its **head segment** (WI-917):
the head is the only part resolved in scope — the tail is appended to whatever it
denotes and is never looked up on its own — so a contested head is a contested
path, and the candidates reported are the head's. The relative reading would
stand down under one anyway; what the ambiguity adds is that standing down is no
longer silent. (An **absolute** path has no head to contest: it is resolved by
qualified name, with no scope walk.)

The ambiguity is then **reported wherever the name is written**: as a load error
at a reference, as a refused mount for a host-supplied name, and as a refused
query naming the candidates at a pattern. A query pattern is refused *anywhere* in
the pattern, including the positions that tolerate an **unresolvable** name (a
bare disjunction branch, a quantifier body, a data slot). That tolerance does not
transfer, and its own reason is why: it holds because an absent name's branch has
no solutions to lose, whereas a contested name's branch answers under either
reading — so tolerating one silently *drops* solutions, the corruption the
tolerance exists to avoid.

**The `internal` gate applies to the ladder, not to a rung.** The qualified index
bypasses step 3's filter, so visibility is checked explicitly on each hit — but a
hit hidden by `internal` **skips to the next reading** rather than ending the
descent. A path therefore keeps whatever reading it has: a shadowing declaration
carrying a hidden member of the right name does not break an otherwise-valid
`..` path. Only when *nothing* has a visible answer is the hidden one reported,
as the (load-blocking) forbidden-internal access — a precise diagnostic that
outranks the generic unresolved-name error it replaces.

**The ladder is position-independent.** The same readings, decided the same way,
resolve a dotted name wherever one is written — a term functor, a type or sort
reference, a rule citation, a proof target, and a query pattern all consult one
definition (WI-752). The *spelling* is admitted per position by the grammar, and
every position that can write a path admits both: a position given only the
relative one would have no way to say what `..` says. A name supplied by the
**host** rather than by source text reads the same way, at the top-level scope
(WI-908): the functor an extent mount owns is the one that spelling would name in
a program written outside any namespace, so a short host name must be *in scope*
(or in the implicit tier), an `internal` member is no more mountable than it is
citable — and a host that means the root regardless of what is in scope there
spells it `..a.b.c`, as source does. A name a **running program** supplies as a
`String` value — `reflect.lookup_symbol`, `reflect.make_fn` / `make_apply`,
`persistence.Store.monotonicity` — reads the same way, at the same scope (WI-913):
the string is data, with no source occurrence and so no enclosing namespace to be
relative to, which is what the top-level reading means. It follows that the
loader's qualified-only kernel registrations (`Sort`, `Fact`, `Member`, `meta`, …)
answer to `..Member` and not to `Member`: they are delocalized precisely so that
name resolution cannot surface them, this is name resolution, and `..` is the
spelling that says otherwise. A **command-line**
name reads the same way, at the same scope (WI-914): `anthill query --mode functor`
and `--mode domain` name what the same text names in `--mode pattern`, and `-i`
therefore bears on all three — every mode `query` has, since WI-921 removed the
one whose argument was not a name. (One reserved ARGUMENT still is not: `--mode
domain '<global>'`, the loader's raw-interned tag for the top-level domain, which
no declaration owns and the ladder can never return. Its spelling is deliberately
not an identifier, so no declaration can contest it — see *The top-level scope*
above. WI-923.) A name that denotes
something in one position denotes the same thing in every other; before this was
unified, `util.f()` resolved by head-qualification while `util.T` in the same
scope reported an unresolved type name, and `anthill query` could bind a dotted
text to a different symbol than the program it queried.

There is one deviation, and it is a different *question* rather than a different
*answer*:

- The **dot-call re-route** asks *"does this path have an answer?"* — not *"which
  symbol does it denote?"* — before deciding whether to peel a name apart into a
  member chain. It therefore counts a hidden-`internal` hit, and an ambiguity, as
  resolving: both are real findings with precise diagnostics, and decomposing the
  name would bury them under an invented member miss.

Any future deviation belongs in this list, with its reason stated at the
deviating site.

**Import forms.** `import` introduces visibility into the current scope; it does
not by itself add a sort's contents (use `requires` or wildcard for that):

Every form is scoped to the file that writes it (WI-995), on **both** of the things
an import writes: the alias, and — for the wildcard form — the parent link. A parent
link a `requires`, an enclosing body or variant exposure also justifies stays
visible, since those belong to a declaration at the address rather than to one
file's text.

- `import a.b.C` — alias `C`, and **nothing else** (WI-1089). Not `a.b`, and not
  `C`'s members: the line binds the one name it writes, exactly as it does in
  Scala, Java and Rust. `C.member` reaches through the bound name; `import
  a.b.C.*` or `requires` brings `C`'s contents in.
- `import a.b.{C, D}` — alias each name, resolved by: direct `a.b.C`
  qualified lookup, then `resolve_in_scope(C, a.b)`, then a one-level nested
  lookup (`a.b.<segment>.C`, taken only if unique) so an entity declared inside
  a sort/enum of `a.b` is importable by its short name.
- `import a.b.*` — include `a.b` as a non-enclosing parent (every visible name).

**An import opens what it names, and not the module around it** (WI-1089). The
parent walk of step 3 above does not leave an import-contributed parent through
that scope's *enclosing* links, and stays stopped for the rest of the path. So
`import a.b.*` brings `a.b`'s names and not `a`'s, and `import a.b.C.*` brings
`C`'s and not `a.b`'s. The other links out of an imported scope — a `requires`,
a variant exposure, the scope's own imports — are contents of the thing imported
and stay reachable. Without this stop every import also delivered the whole
declaration chain above its target, which is what made the plain form *look*
like "include `a.b`": the reach was an artifact of the walk, and it disappeared
whenever the imported name had no scope of its own (WI-993).

**A parent link needs a scope to link.** The wildcard form's path must name a
**namespace** (§5.1) or a **sort** (§5.2) — the two declarations that *can have*
contents — and a `requires` must name a **sort**, since it names a spec and a
namespace declares no operations to dispatch against. A path naming anything
else (an operation, a const, an entity declared *inside* a sort) is **refused,
naming the kind it turned out to name** (WI-988, WI-993), because neither thing
it would otherwise do is what the author asked for: the link either resolves
nothing at all, or — where the named declaration's own scope is enclosed by the
sort that declared it — brings in every name of that sort and of the namespace
above it, none of which the author wrote. "This line did nothing" is not a
diagnosis a reader can act on, so the kind is part of the message.

The test is on the **kind**, not on whether the scope currently holds anything:
an empty namespace, a spec with no operations, and §6.3's eponymous constructor
(`entity Point(…)` at top level, which *is* a sort, so it passes on either of
the two roles its one name plays) are all admitted. Refusing on emptiness would
make the same program load or not depending on declaration order — a sort's
rule-introduced members are registered *after* imports are wired, and a
`namespace X … end` secondary entry may add members from another file entirely.

Since WI-1089 the plain form links no parent at all, so this refusal is the
wildcard form's and the `requires` clause's.

**Variant exposure.** A sort that declares entity constructors exposes **only
those constructor (variant) names** to its enclosing scope, by linking its
scope as a non-enclosing parent whose `exposed` set is exactly the variant
names. So bare `Open` resolves to `WorkStatus.Open`, while the sort's
*operations* never leak as bare names (they are reached via `Sort.op`,
`requires`, or wildcard). Two sorts exposing the same variant name make that
bare name **ambiguous** rather than letting one silently win.

`exposed` filters **this link and no other**. It says what a sort leaks
*outward* to the namespace around it, which is a different question from what a
`requires` clause or a wildcard import reaches *inward* — and the two are told
apart by which clause wrote the link, since all three are non-enclosing. Read as
a property of the far scope instead, adding one unrelated `entity` to a spec
made its `exposed` set non-empty and hid every one of its operations from every
`requires` caller, one line apart, and made the last clause of the paragraph
above false (WI-M460D). Invisible until then only because no stdlib spec
declares a constructor.

**Exposure reaches the enclosing scope, not the types inside it.** A constructor
leaked this way is written unqualified *in that namespace*; it does not reserve
its short name against the **members** of the other types declared there. Two
types in one namespace may name their operations, consts and constructors freely
against one another — see §8.7, *members and constructors are named per type*.
This is why 059 R4's capture rule does not follow the exposure link: the leak is
automatic, so the presence of an exposed `merge` says nothing about whether any
body inside a sibling sort reads a bare `merge` (WI-999).

An **import** spends that exemption. `import a.Colour.*` or `import a.*` is the
author asking for those bare names at this address, so a declaration taking one
*is* a capture and is refused. The PLAIN `import a.Colour` is not: since WI-1089
it binds the name `Colour` and brings no variant into view, so nothing at this
address was asking for a bare `Red`. This holds along the whole path, not just at the
imported hop: `import a.*` brings in the namespace, and the constructor arrives
one exposure hop further on — it is still a name the import put in view.

A `requires` or `provides` link is not the exposure link at all, so the capture
walk follows it like any other — and every name it reaches is then excused by
the relation itself, a sort being free to name its own members beside the spec
it requires (§8.7). It therefore yields no refusal either way. Said as a rule
rather than as a case, so the two questions stay apart: what a link filters is
decided by which clause WROTE it, and never by whether the scope it lands on
happens to declare a constructor (WI-M460D).

**Constructor patterns resolve against the scrutinee, not the scope.** A
constructor name in a `match` case (`case Red`, `case some(?x)`, `case nil()`) is
**not** resolved through the general scope order above. It is resolved
**type-directedly against the scrutinee's own constructors**, by short name:
`match c case Red` with `c: Color` binds `Red` to `Color.Red` because `Red` is one
of `Color`'s constructors. A `case`-name that matches **none** of the scrutinee's
constructors is instead a plain **variable binding** (`case x`) — so `case` on a
bare name is inherently ambiguous between "nullary constructor" and "binder", and
only the scrutinee's constructor set decides. Because that set is known only from
the scrutinee's *type*, this resolution happens during **type-checking**, not at
load; the loader carries the pattern name unresolved (as a fresh binder symbol) and
the typer binds it. It is a name **lookup** scoped to the scrutinee's constructors —
distinct from the general `resolve_in_scope` above (which ignores the scrutinee and
could pick a different sort's same-named constructor) and from sort *identity*
comparison. No ambiguity arises within one match: a sort's constructors have
distinct short names, and the constructors compared for exhaustiveness are the
resolved scrutinee symbols, compared by identity.

**Named-argument labels and field selectors resolve by short name, too.** The same
lookup-not-identity principle governs other *written names matched against a known
set*. A **named argument** (`op(label: v)`) resolves its `label` against the callee
operation's parameter names; a **record/tuple field selector** (`t.field`, or a
destructuring `let (field, _) = …`) resolves `field` against the aggregate's declared
field names. Both match by short name, because the written label is a bare source
identifier while the parameter or field it names is registered under a *qualified*
name (`Iterable.find.pred`, `Point.x`). Within one candidate set the members have
distinct short names, so the lookup is unambiguous. This scoped **name lookup** is
legitimate exactly as constructor-pattern resolution is — and categorically distinct
from **sort identity** comparison, which is always by the resolved (canonical) symbol
and *never* by last segment: a top-level `sort Ring` and `anthill.prelude.algebra.Ring`
are different sorts even though they share a short name. Short-name matching in the
kernel therefore survives only for name resolution against a scoped set, never as a
test of whether two sorts are the same.

**The subtype relation's nominal leg is inside that rule** (WI-872). "Is this type that
type" is a sort-identity question wherever it is asked — at an argument, a field, a
return, or when deciding whether a provision is *about* a carrier — so it is answered by
the resolved symbol. A user sort may therefore be named for a library sort freely: a
local `sort Pair` beside `anthill.prelude.Pair` is a different sort, and neither shadows
nor reserves the other. Reading identity by last segment here is not a locally-wrong
answer but two opposite ones at once, which is how such a violation shows itself: at a
*value* position it **accepts** a foreign sort of the same short name (a silent wrong
value), while at a *dispatch* it **refuses**, the foreign sort's provision being offered
and its condition then failing at that sort's own parameter — reported as an
implementation mismatch rather than as the name collision it is. Because both sides of a
type mismatch render by short name, such a pair prints as `expected T, got T`; the
diagnostic names the two qualified sorts, since those are the repair.

**Distinct labels within one argument list** (WI-809). A named-argument list may not
repeat a label, whatever the callee is: an operation, an entity constructor, a
function value, a `fact`, or a rule-body atom. The second occurrence names a slot the
first already bound, so it cannot be read back by name and the slot it displaces is
left unbound — measured, `mk(a: 1, a: 2)` against `entity mk(a: Int64, b: Int64)` used
to build a value with two `a` fields and no `b`, with `.b` failing only at run time.

This is checked as **syntax**, since whether one list repeats a label needs no type
information; one rule therefore covers every callee shape at once, and it is the same
distinctness principle as §4.5's tuple components and §6.3's entity fields. Two
related checks remain *semantic*, because neither is decidable from the argument list
alone: an **unknown** label (it must be matched against the callee's parameters), and
a label that re-binds a parameter already filled **positionally** (`f(3, acc: 10)`).

**Named arguments to a function value.** Where the callee is not a named operation
but a **variable of arrow type**, the label resolves against that *arrow type's*
declared binder names: with `f: (acc: Int64, x: Int64) -> Int64`, both `f(x: 10,
acc: 3)` and `f(acc: 3, x: 10)` bind `acc` to the first parameter and `x` to the
second. The **declared** names govern, not those of whichever function is finally
passed — an arrow's parameter list is applied positionally, so an operation whose
own binders read `(a, b)` remains a legal argument for `(acc, x)` (§ arrow
conformance) and declared slot *i* is that callee's slot *i*. An unknown label is a
load error, as for an operation call; a duplicated one is refused earlier still, by
the syntactic rule above.

Two arrow types record **no** binder names, and a label there is rejected with a
located error rather than resolved: a **one-parameter** arrow, whose binder name the
type does not retain (`(v: Int64) -> Int64` is `Int64 -> Int64`), and
`Function[A, B]`, whose `A` is one tuple-typed *argument* rather than a parameter
list. Both take positional arguments.

**Inherited operations.** When a sort gains an operation through `requires`
(spec auto-binding, §8.7), a derived rule it supplies for that operation binds
to the **inherited** operation symbol — it does not mint a new shadowing symbol.
So `Ord`'s `eq` law contributes to `Eq.eq`, and a scope that reaches both
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
-- Int64 satisfies Eq, Ord, and Numeric
fact Eq[T = Int64]
fact Ord[T = Int64]
fact Numeric[T = Int64]
```

For built-in types, the operations are primitive (provided by the runtime). For user-defined types, the `eq` family may be given by rules — as **predicate heads on a member the carrier binds as its equality**:

```
sort Color
  entity red
  entity green
  entity blue
  operation ceq(a: Color, b: Color) -> Bool
  rule ceq(red, red)
  rule ceq(green, green)
  rule ceq(blue, blue)
  provides PartialEq[T = Color, eq = ceq]
  provides Eq[T = Color]
end
```

Every part of that is load-bearing, and each was measured (WI-1092). The clauses are **predicate heads**, so they are indexed under `ceq` and the eval→SLD `eq` bridge (WI-625) can prove them; written as equations (`rule ceq(red, red) <=> true`) they index under the connective instead, `ceq` owns nothing, and the operation is unrunnable — §5.3. There is no `rule ceq(?_, ?_) <=> false` catch-all beside them: the sub-proof is a closed test over a complete search, so an unmatched pair is unequal by absence. And the **binding** is what points the carrier's equality at those clauses: the same rules under a bare `fact Eq[T = Color]`, with no member bound as `eq`, are never consulted — nothing dispatches to them and structural equality answers instead. The binding may also be written from outside the sort, as `fact PartialEq[T = Color, eq = Color.ceq]`.

**Only `eq` may be bound (WI-1125).** Every binding form on this page — a member of the carrier, `provides PartialEq[T = Color, eq = ceq]`, a witness sort's member, `fact PartialEq[T = Color, eq = Color.ceq]` — supplies `eq` and only `eq`. Supplying the carrier's **`neq`** through any of them is a **load error** (`CarrierSuppliesNeq`), because `neq(a, b) <=> not(eq(a, b))` makes it derived and equality dispatch keys `eq` suppliers alone: such a binding is honoured nowhere, and beside an `eq` it can only contradict the equality that decides. §8.3 states the rule and the two shapes it covers; write the `eq` and `neq` follows. A member merely *named* `neq` that does not compare the carrier's own values — an abstract spec's `neq(a: T, b: T)` for its own parameter, or an unrelated helper on a witness sort — supplies nothing and is untouched.

This rule-given shape is specific to the **predicate-shaped** `eq`/`neq` family. It does **not** generalize to value-returning operations: under WI-818 ("Backing is executable", §8.7) a rule is a law, not backing — a concrete carrier providing a spec must back every other declared operation with a runnable body or a builtin, or the load is rejected.

Different namespaces may declare different providers of the same spec for the same type (e.g. different orderings). An `import` governs **visibility** — which names one file's text may write — and nothing else: it does not choose among providers, and it does not gate the rule below, which is **global**. Whether a second provider is admitted is decided at load from what every loaded file declares, not from what one file imports; and among the providers so admitted, the **call** selects, by binding the requirement slot (§5.4). That is the subject of *Instance coherence*, immediately below.

**Instance coherence.** Selection is **explicit and per-call**, not per-scope (proposal 058 §8; design notes in `docs/design/spec-instance-dispatch.md` and `docs/design/058-implementation.md`).

*At most one default per carrier.* A spec has at most one **default** provider for a given carrier: the carrier's own provision where one exists — inferred, so the existing library needs no marks — or the provider a `DefaultProvider` row names, written either as the `default provides Spec[…]` modifier on the provision or as a by-reference `fact DefaultProvider(spec: …, provider: …)` (§5.1; which of a spec's parameters is the *carrier* is settled there too). Two default rows for one carrier are a **load error naming both**, each by its provider, its carrier, and whether it was *declared* or *inferred* — the inferred row has to be named because the author never wrote it, and would otherwise read the error as firing on a single declaration. That is `AmbiguousDefaultProvider`, raised by the `one_default` check, which compares rows at carriers that **overlap** rather than at carriers that are equal, so a ground row beside a parametric one for the same family collides while two disjoint ground rows coexist. Nothing *displaces* a default; a rival only collides with one, because a self-providing carrier already holds the inferred row: **fill silence, never overwrite speech.**

*A second provider is permitted, gated on nameability.* Two providers of one spec for one carrier may coexist — if and only if **every** candidate can be *named*, since the repair for an unselected call is to write a name. A witness sort has one, its declared sort name; an instance fact has none — its identity *is* the bindings it asserts — so a group containing one keeps the load-time refusal (`MixedProviderKinds`, or `AmbiguousInstanceFact` for two facts). Missing names are deliberately not generated: a fingerprint breaks every written selection when the fact is edited, and an ordinal one silently swaps their meaning when two declarations are reordered. Two *texts* naming **one** provider are one candidate rather than a group of two — see *One carrier declaring one spec twice* below. Nameability buys coexistence only where a **call site** exists to spend the name at. Semantic equality has none — `eq` dispatches from **unification** (§8.3), so no written call could carry a bracket — and it is therefore coherent permanently: two `eq` suppliers for one carrier are a load error (`AmbiguousEqDispatch`, `build_eq_dispatch_index`) however nameable each is, and the same holds of the `neq` beside it (§8.3, WI-1125). The general form of that rule: a read asking whether a provider **exists** stays boolean, while a read that **selects** one goes loud on the second candidate — at load where it has no later site to complain from, at the use site where it has one, and never by first match.

*Which one a call gets.* Against a carrier with two candidates a dispatch says **which**, by binding the requirement slot at the call — `fold[Monoid = AddM](xs)`, §5.4, whose validation rules are stated there. An **unselected** dispatch takes the **default** when exactly one of the *tied most-specific* candidates is it. Specificity ranks first, where the candidates are *provisions* and one head can be strictly more specific than another: such a candidate wins outright, so a default is a fallback and never a competitor. Where they are supply **routes** rather than provisions — a carrier's own member, an instance fact's binding, a witness sort's member — there is no specificity relation between them to rank by, so all of them are tied and the default arbitrates directly. And *exactly* one, never the first — two tied candidates naming one provider leave the tie standing, since a default names a **provider** and does not arbitrate between two of that provider's own texts. Otherwise the dispatch is an error naming **every** candidate. Which *repair* the message offers depends on the route the tie was reached by, and only the dispatch routes offer the bracket: a tie raised while a requirement **dictionary** is being constructed names its providers and asks for the element to be pinned, since that is what its own site can act on — the bracket is still the fix, but that message does not spell it. *Where the ambiguity error is raised* below says at which phase each route refuses, and by which route each rival is named.

*Embedded requirements: named or anonymous, not scoped.* A sort's own `requires` slots are decided by whether the slot is **named** (§5.2), not by the scope the sort was written in. A **named** slot is an ordinary type parameter, so the chosen provider is part of the sort's **type identity** and every value of that type carries it: `SortedSet[T = String, O = ByLength]` and `SortedSet[T = String, O = Alphabetical]` are *different types*, and merging them is a type error before it is a wrong answer. An **anonymous** slot is a **constraint** — solved, not recorded — so it fixes nothing about the type and is re-answered at each dispatch, which is why two `Map[K = Int64]`s cannot differ by which `Eq` satisfied them, and why a container's key requirement stays outside its type's identity — the `Map[K = Float]` repair is the **newtype** `TotalFloat`, which changes the *type*, where selection changes only the *witness* (§8.3).

*Consequence.* Two routes to `A[X]` agree unless a call site deliberately says otherwise — the coherence a diamond needs is a property of the calls, not of the importing scopes. Implicit scope-directed selection — a nearer provider silently winning, or providers ranked by the caller's imports — is deliberately **not** the rule (proposal 058 §7). It cannot express the need at all (`fold[Monoid = AddM](xs)` beside `fold[Monoid = MulM](ys)` wants both providers in one body, and a `SortedSet` chooses its order per *construction site*), and it would let an added `import` change what a program computes.

*Where the ambiguity error is raised.* A tie reaching this paragraph is one the default rung did not arbitrate — no default row names any candidate, or two of the tied candidates name the same provider. Most such ties are refused at **load**, before anything runs; a carrier that provides a spec *itself*, beside a second sort providing the same spec for it, is not — that pair reaches the runtime. Such a tie is refused at the point a dictionary for it is actually **built**: when dispatch resolves an impl's `requires` slot and finds two providers, it raises an ambiguity error naming the requirement and both providers, rather than proceeding without the dictionary. Choosing which impl runs for a spec-op call is a separate step, and it is refused the same way (WI-842): when the receiver's carrier has two suppliers of the operation — its own member, an instance fact's binding, a witness sort's member — the refusal names the operation, the carrier, and each candidate *by its supply route*, since the three are written in three different syntaxes and the author must know which text to delete. Which repair the message offers depends on whether any rival can be *named*: a `[Spec = Witness]` bracket binds a **body-less** spec op's dispatch slot to a provider, so it separates rivals only when one is a witness sort and the operation has such a slot — a defaulted operation has none, and a carrier's own member and an instance fact have no name (*A second provider is permitted, gated on nameability*, above). When nothing is nameable the message says to keep exactly one text rather than suggest a spelling that would be refused. **Where** the tie is raised is a separate question, and it is answered before anything runs wherever the type checker can see it: when the carrier is pinned *statically*, the refusal is a **load** error, since the span, the carrier and the candidate list are all in hand at the moment dispatch declines to select (WI-1012 for a **defaulted** operation, WI-1027 for a **body-less** one). What still waits for the call is what no static carrier names: an abstract-spec receiver, and a call whose carrier is a type parameter. The two halves refuse *different* counts, and the difference is not an inconsistency. A defaulted operation has no dispatch slot, so nothing at any call site could ever choose between its suppliers — the type checker does not even attempt a dispatch resolution for one — and two suppliers are always a tie. A body-less operation does have one, so a call site *can* choose — with a `[Spec = Witness]` bracket, or by one provision being strictly more specific than another — and those choices are made by the dispatch resolution before any tie is counted. What that resolution cannot weigh is a supplier which is not a provision at all (the carrier's own member), or one whose operation binding a same-named member of the carrier overrides (an instance fact's). Two suppliers with one of those among them were never chosen between, and that is what the load refusal on this half names. One limit is worth stating, since it is not a general "ambiguity is always caught": inside SLD resolution a tie that reaches the runtime *delays* the bridged evaluation instead of aborting the enclosing rule, so a rule reports it by not answering. A **top-level query** is the one runtime call site that does have a moment to be loud at — its own, the moment the pattern is converted — and it uses it: a query naming a spec-op call whose carrier has two suppliers is refused before it runs, in the same wording and naming each rival by the same supply route (WI-1044). A query has no enclosing rule to protect, and belonging to none is also why no load pass sees it. A rule body that names the spec operation *directly* is type-checked through the same call path on **both** halves — defaulted (WI-1026) and body-less (WI-1043) — so the load refusal and the override rule reach it there, wherever the call names the operation. Such an atom is then type-checked in full (WI-1056), so an ordinary type error inside one — a `String` argument where `Int64` is declared — is a load error wherever it is written, rule body and operation body alike; the one failure deliberately not reported there is a dot whose receiver has no static sort, which an untyped rule-head variable always is (WI-282). The general rule-body call is decided too (WI-1058), and what decides it is the **position** it is written in rather than its functor alone: at *goal* position an atom is a connective, a resolver builtin, a fact pattern, an instance claim, or a **subgoal** — and a subgoal is checked against the clauses its functor heads (a goal no clause can match by shape, e.g. the wrong arity, is refused naming the rule and both shapes) rather than against a signature it has not got. At *data* position a term is not type-checked at all, deliberately and by measurement: the call ladder is expectation-directed and scope-sensitive (a sort name denotes a `Type` only in a slot that expects one; a node under a `lambda` needs its binder), and type-checking a data slot also *rewrites* it, which changes what the rule means. A data slot gets the one context-free check it can have — that its functor names something — described under §5.3 "Naming one from elsewhere". One supply route also stays out of reach from a rule body: an implementation supplied **only** by an instance fact's binding has no static pin (the dispatch resolution does not read those bindings), so an operation body reaches it by value and a rule body answers nothing — WI-1057. A call written as a **dot on the receiver** (`x.describe(?r)`) resolves the member on the receiver's sort by name, before any spec is consulted — but that resolution is now asked the same question the named spellings are asked (WI-1035): where the member it finds backs a spec the receiver provides, and that operation has a second supplier for this carrier, the dot is refused too. This holds on both halves and in an operation body and a rule body alike. On a *concrete* carrier the call is still dispatched to the member, and what a rival changes is only that route order no longer decides silently. On an *abstract-spec* receiver there is no static carrier to count for, so the dot instead hands the call to the spec operation and the value decides it — the same reader the qualified spelling reaches, refusing at the call when two texts supply one implementation (WI-1038). A receiver typed as a **`requires`-constrained type parameter** is the third case and reads the same way (WI-1119): the parameter names no sort whose members could be searched, so the dot resolves the member against the specs that **constrain that parameter** — the clauses on the enclosing operation and on its sort alike, transitively through their `requires` graphs — and hands the call to the spec operation for the value to decide, exactly as the named spelling `Spec.member(x)` does under the same clause (§5.4). A clause lends its spec's members only where it constrains *this* parameter: `probe[A, B](x: A, y: B) requires Desc[B]` does not resolve `x.describe()`, and refusing it is the same rule that stops the clause from licensing the named spelling there. Two constraining specs declaring one member name are refused naming both, rather than settled by the order the clauses are written — the requires-*refinement* rule below already settles the orderable case, and unlike the two ladders above there is no distance between a clause on an operation and a clause on its sort for a first-match to mean anything. They are rivals only where the *call* cannot tell them apart: a candidate the dot's own argument list could not reach is not counted, on the same ground the shadowing rule below starts from (equal arity), and for the same reason a tie must not be reported by suggesting a spelling that is itself refused. A member no constraining spec declares is refused as an unresolved member, naming the parameter and *every* spec that constrains it — including one whose operations receive on nothing, since the author wrote that clause and must not be told to add it. A requirement that is merely *unpinnable* at the argument types is a different case and is not an error at all — the call proceeds, and only a body that actually reads the missing slot fails (WI-822/WI-855).

*One carrier declaring one spec twice.* A carrier may provide a spec many times at **different applications** — `sort Console` provides `Effect` for each of `ConsoleOutput` / `ConsoleError` / `ConsoleInput`. What is refused, at **load**, is two provisions of one spec that agree on the spec's carrier parameter (the same application) and disagree about another parameter: every reader of a carrier's provider view takes the first match, so admitting the pair would let the *order the provisions are written* decide the program's meaning. Provisions that agree are merged into one view, so a parameter bound by a later provision and omitted by an earlier one is still read. The dispatch side follows the same rule (WI-1032): two provisions that agree in everything dispatch consults — the carrier and the spec's *type*-parameter bindings — are **one candidate**, not a tie. A carrier writing `provides Spec[…]` in its own body beside a namespace-level `fact Spec[…]` for itself has said one thing twice, and a call on it resolves rather than being refused. An *operation* binding is not a type-parameter binding and so does not make two provisions differ here; when such a binding rivals an implementation the carrier already supplies, the conflict is reported as the supplier tie above — naming each by its supply route — rather than as two providers.

**One name, one operation (WI-1049).** An operation name is declared at most once per scope, and the loader refuses a second declaration, naming both. Anthill has no signature-keyed overloading: a scope maps a name to one symbol, so a second `operation` of that name does not introduce a second operation — it merges into the first and its signature is lost, leaving *which* signature the kernel reports to depend on which was written first. Same-named operations on **different** sorts are not overloading and stay legal: they are distinct symbols chosen by carrier, per the ladder below. A `rule` whose head names an operation is not a second declaration either — for an operation with a body the equational and relational views are *derived* from that body (WI-580), and for a body-less one the rules are what give it meaning (WI-818, WI-881).

**Members and constructors are named per type (WI-999).** *Per scope* above means per **type**, and a namespace is not one flat name space for every member of every sort in it. Two types declared in one namespace may name their operations, consts and constructors freely against one another — `sort SortedSet` may declare `merge` while a sibling `enum EffectExpression` declares an `entity merge`, and those are different declarations, chosen by carrier at the call site. §8.6's *variant exposure* does not change this: it leaks a constructor's short name to the **enclosing** namespace so it can be written unqualified there, and reserves nothing inside the sibling types declared alongside. The alternative would make every constructor name in a namespace a reserved word for every sort in it, which is why proposal 059 R4's capture rule stops at the exposure link.

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

When `fact S[T]` appears inside a sort body, it means both spec satisfaction AND operation inheritance: the sort gains all operations defined in the spec. Defaulted operations (a spec-level `operation … = body`) carry over automatically; the satisfying sort only provides the primitive operations. For example, `Stream` defines `head` by a default body over `splitFirst`, so a sort declaring `fact Stream[T]` inherits `head` without redeclaring it.

**A NAMESPACE-level operation is not backing (WI-935).** Backing must be reachable *through the carrier* — the carrier's own member or an inherited spec default (see the next paragraph for the full list). A free operation declared at **namespace** level, with the same name and signature and sitting beside the carrier, is none of those and backs nothing: `check_provider_operations` reports one `… no own <op> on <carrier>` per declared member (measured). The refusal is not incidental. A spec member is dispatched *through* its carrier, so with two carriers of one spec there are two `vec_add`s and the carrier is the only thing that distinguishes them; a namespace-level name has no carrier dimension to distinguish by. The implementation therefore goes in the carrier's sort body. Writing it there means writing the long form `sort E { entity E(…); operation … }` where `entity E(…)` stood — the same declaration (§6.3), now with somewhere to put members, but **not** a no-op edit: it changes the parse-IR item kind, and a codegen backend reached the two spellings by different paths — scaland's `Bootstrap` emitted a `case class` for the sugar and `enum Vec3: case Vec3(…)` for the long form, which is the `Vec3.Vec3` §6.3 rules out. Fixed and pinned by byte-equality of the two emissions (WI-940).

**Backing conformance: the member must fit where it is the only backing (WI-20260822-1MAGR).** `op_backed` matches a declared member by **short name only**, and until this rule nothing compared the two declarations: `fact VectorSpace[BadVec, Float]` loaded clean when `vec_add` took one argument, when `vec_sub` returned `Float`, or when `vec_scale`'s parameters were swapped, and each then mis-dispatched or died at the call (WI-935, measured). `check_override_refinement` now compares **arity**, the **parameter types** — and so their **order** — and the **return type**, with the provision's bindings substituted into the spec's declaration, **exactly where the spec operation has no implementation of its own that would back this carrier** — no default body and no resolver builtin. A host `operation_map` naming the spec's own member is deliberately not counted: that index has no carrier dimension, so it says an implementation exists somewhere and never that *this* carrier is realized (WI-876), which is the same reason `op_backed` does not count it either. The refusal names both shapes, the spec's written at this provision's bindings.

That gate is the line between two different programs, and it is not a cost dodge. Where the spec supplies nothing, the member is the only thing that can back the operation — there is nothing for it to be *distinct from* — so a mismatch makes the provision's claim simply false, and no other pass would ever say so. Where the spec supplies its own implementation, a same-named member of a different signature is a **distinct operation** and the default is what backs the provision; that is the reading §8.7 already gives the `requires` direction (WI-1048 — different arity, a provably different parameter or return type ⇒ distinct by construction), under which a call that expected the spec's shape is already a loud type error naming both types. So `operation neq() -> Bool` beside `provides PartialEq[T = Color]` still loads: `PartialEq.neq` is a builtin, and a 0-ary member is not it (WI-1125).

Three things are **not** compared, and each is undecidable here rather than excused:

- **The self-receiver parameter.** A spec that types a parameter as *itself* (`splitFirst(s: Stream)`) is naming the dispatch receiver, and an override narrows it to the carrier (`splitFirst(xs: List)`) — which contravariance would refuse and which dispatch makes sound, since the receiver *is* the carrier by construction. Recognised structurally (the spec side's sort functor is the spec, the member's is the carrier), never by position: `holds(x: T, b: Bag)` puts it second.
- **A type carrying an expression projection** (`s.T`, WI-376). The provision's bindings substitute the spec's *type parameters*; they cannot ground a projection off the operation's own parameter, and the two operations' receivers are different parameters, so `Stream.splitFirst`'s `s.T` and `List.splitFirst`'s `xs.T` are two distinct neutrals that no substitution over type parameters relates.
- **A non-ground pair**, which fails open here as everywhere else.

**Parameter order is a partial check and says so.** It is decidable only where the types differ: `f(a: Int64, b: Int64)` written in either order is the same signature, so a swap there is invisible and nothing claims otherwise. Where the types do differ, a permutation that *would* fit is reported as an order mistake rather than as N unrelated parameter mismatches, because that is the repair.

MEASURED before enforcing, report-only over the whole corpus and fixture suite — 1152 distinct (carrier, spec, operation) pairs across 999 carriers. The comparison run raw flagged 67 of them; the two structural exemptions above account for 56 (42 self-receiver parameters across 32 carriers, 14 projection-carrying return types), and every one of those 56 is an ordinary stdlib or fixture declaration. The gate then splits the remaining 11 exactly: the 3 beside an executable spec operation are the three programs the language had already decided must load (WI-1125's nullary `neq` and its witness twin, WI-1042's non-parametric `provides`), and the 8 beside a body-less one are all deliberate mismatch fixtures — six in `wi347_override_refinement_test` and the two probes in `docs/measurements/guardians/` that recorded this very gap.

The **return type** is now read by two rules, and they ask different questions. This one asks whether the member fits at all, and applies only where the member is the sole backing. WI-20260822-59CDQ's asks whether a contract clause's `result` binder may be **discharged** across the two — a question about a *clause*, which stands whether or not the spec supplies an implementation. Neither subsumes the other; see *Operation override* below for the second.

**Backing is executable (WI-818).** Providing a spec obliges the carrier, per declared operation, to an implementation the *evaluator* can dispatch to: a runnable body (the carrier's own, or an inherited spec default), a registered builtin, or a **host mapping** (WI-876 — an `operation_map` entry in a `provides … language <host>` block; §10.2). A spec-level `rule` mentioning the operation is a **law** — specification the SLD world resolves against — not an implementation; it does not discharge the obligation. The loader rejects a provision whose operation has no executable backing (`… backs no operation …`), rather than certify a program whose call fails only at run time. (Before WI-818 a rule counted, per WI-363; that reading let a spec-level `rule head(?s) <=> …` satisfy the check while `head(cons(7, nil))` died at eval with `UnknownOperation`.) The `Eq` family's relational instances (§ above: `Set.eq`/`Map.eq` given by rules) remain sound under this reading, for two independent reasons: the check's scope covers only provisions whose carrier is CONCRETE (has constructors), and `Set`/`Map` are abstract carriers, so their provisions are not gated at all today; and at eval, dispatch proves a carrier's `eq` rules through the eval→SLD `eq` bridge (WI-625) — the predicate-shaped exception, where "no proof = false" is a sound answer in a way no value-returning operation has. (A concrete carrier's own `eq` would additionally pass the check through the builtin `PartialEq.eq` spec op.)

**Conditional provisions (WI-869; proposal 058 §3.8, §4).** A provision may carry a `:- goals` tail that scopes its conditions to **that provision**:

```anthill
provides PartialEq[Pair] :- PartialEq[A], PartialEq[B]
provides Eq[Pair]        :- Eq[A], Eq[B]
```

Each goal is a spec instantiation over the declaring sort's own parameters (never an arrow, a tuple, or a value goal). The provision holds only where its goals resolve, so `Pair[Float, Int64]` has `PartialEq` and not `Eq`. Conditions do the same double duty a sort-level `requires` does: they *condition* the provision and they *are* the evidence that provision's member bodies dispatch through — `Pair.compare` reads `Ord[A]` from a slot only `provides Ord[Pair] :- Ord[A], Ord[B]` puts there.

A sort-level `requires` keeps its meaning (it conditions **every** provision, and supplies every body's evidence) and the two compose. The dictionary a carrier is laid out by is therefore its `requires` chain followed by its provisions' conditions, deduplicated — **one** slot set per sort, since a body is owned by the sort and not by a provision. Strictness is what varies: a slot is demanded at a dispatch when it is a sort-level `requires` or a condition of the provision being dispatched, and is otherwise left unfilled. Reading an unfilled slot is refused at the read, not silently answered — so a body may name evidence its provision did not earn, and finds out.

A condition **admits, it never ranks**: it shrinks where a provision applies, and provisions still applicable after their conditions resolve are settled by the ordinary dispatch ladder. A provider's conditions do not discharge the *spec's* own `requires`.

Conditions are recorded as `anthill.reflect.ProvidesConditionInfo(sort_ref, provided, condition)` facts — one per goal, joined to the provision by the view `SortProvidesInfo` carries — so they are observable to the same fact layer that reads the provision. One rule is checked over them (WI-1033): where a conditional provision is certified by the carrier's own conditional provision of a spec it requires, the outer conditions must **entail** the inner ones — a condition entails another when its spec is, or transitively requires, the other's at the same bindings. So `provides Ord[C] :- Ord[E]` may lean on `provides Eq[C] :- Eq[E]` (`Ord requires Eq`), while `provides Ord[C] :- PartialOrd[E]` may not: it would claim `Ord[C]` where the `Eq[C]` that `Ord` requires does not hold.

**Operation override.** A satisfying sort may **redefine** an operation the spec already supplies (a defaulted operation); its own definition then wins for that carrier. Override is carrier-driven — a call resolves to the implementation supplied *for the carrier* when there is one, otherwise to the spec's default. This is the `provides`/`fact` direction. **A default fills a gap; it never shadows a written implementation, whichever of the three supply routes writes it** (WI-1010): the carrier's own member, an instance fact's op-valued binding (`fact Desc[T = Leaf, describe = leafDescribe]`), or a witness sort's member all beat the default, and they are the same three routes the ambiguity rule above (§"Where the ambiguity error is raised") counts — so whether a spec operation happens to carry a default body changes *what runs when nothing is supplied*, and nothing else. Two suppliers are that same tie, refused rather than settled by route order — at load when the carrier is statically known, at the call when only the runtime value names it. The rule holds wherever the call **names the operation** — in an operation body, in a rule body, and in a **top-level query** alike, on both halves (WI-1026 defaulted, WI-1043 body-less): a rule body's `Desc.describe(leaf(), ?r)` reaches the supplied implementation, and two suppliers refuse it at load. It holds equally where *nothing static* names the carrier — a rule-body receiver bound only by the caller, or a query, which no load pass sees at all (WI-1044): the implementation is then chosen from the argument's own carrier at the moment the call reduces, exactly as an operation body has always chosen it, and two suppliers refuse the query and leave the rule without an answer. One route is the exception, and it is a route and not a half: an implementation supplied **only** by an instance fact's op-valued binding is discoverable by the runtime value alone, so an operation body reaches it and a rule body answers nothing (WI-1057). What a rule body does *not* reach is a goal whose functor names nothing at all — that fails to resolve before dispatch is a question — and a call spelled as a **dot** reaches the same rule (WI-1035): it still takes the receiver sort's own member where there is one and the carrier is concrete, but a rival supplier for that carrier now refuses the load rather than losing silently, and on an abstract-spec receiver — or on a receiver typed as a `requires`-constrained **type parameter**, where the constraining clause is what names the spec (WI-1119) — the dot dispatches by the value like the named spelling does (§"Where the ambiguity error is raised"). A sort that merely `requires` a spec and happens to declare an operation of the same name is **not** overriding it: that operation is unrelated. Declaring one is reported as a warning that it shadows the required name — but **only where the two are not confidently distinguishable at a call site** (WI-1048): equal arity, and no parameter or return type provably different once the `requires Spec[…]` bindings are substituted into the spec's. A type parameter on either side is a **wildcard**, not a difference — an unbound spec parameter (`requires Pingable`, binding nothing) is an unknown type, which is why the plainest collision still warns. A shadow that genuinely **refines** the signature is a distinct operation by construction, is chosen by the ladder above, and is not warned about: `FiniteCollection.map` returns a `FiniteCollection` where `Iterable.map` returns a `Stream`, so a call expecting the other is already a type error naming both. An overriding operation must **refine** the spec's contract — its effect row stays within the spec's, and its `requires`/`ensures` are no stronger / no weaker respectively. All three are checked at load by `check_override_refinement` (the effect leg is described in `docs/design/spec-instance-dispatch.md`). The **effect leg is decided per atom**, and fails open only on the atoms it cannot decide (WI-20260822-1TKN0): an override effect still carrying a type parameter may yet instantiate to something the spec covers, and a `Modify` whose target is a **place** — a parameter, or `result` — is not related to a spec `Modify` over a resource **type**. That last one is left undecided rather than resolved conservatively, because *this* section and `prelude/effects.anthill` do not yet agree on what the bracket denotes: §5.6 reads `Modify[X]` as a resource **name** (`Env` mapping names to states), under which a place refines nothing, and the prelude reads it as the resource-identity **type**, under which `Cell.set`'s `Modify[c]` refines `ModifyRuntime.set`'s `Modify[T = Cell]`. The stdlib is written to the second reading. Settling it is **WI-20260823-39AD2**, which also owns the `Modifiable[target]` obligation — stated in `prelude/effects.anthill` and proposal 037, and enforced by no pass at all — since both want the same first step: the type a place denotes. Everything else is compared, a `Modify` **target** included, and that is what makes §5.6's frame condition survive a provision: a spec row carrying no `Modify` asserts `Env_after = Env_before` for *every* resource, so an override acquiring one is refused; and granting `Modify[a]` is not granting `Modify[b]`, the condition being per resource rather than per label — two parameters of the same type are two resources. Per **atom** is the load-bearing word rather than a detail of phrasing: while the gate was one verdict over the whole row, a single undecidable atom suppressed the check for every effect beside it, so any widening at all could be hidden behind one `Modify[c]`. Targets are compared in the spec operation's own parameter vocabulary — the same positional alignment the contract legs use, `result` included, `result` being declared per operation — so an override that renames a parameter, or restates the spec's `Modify[result]`, is not thereby naming a different resource. The contract legs compare clauses **structurally**, in the spec's own vocabulary: the override's parameters are aligned to the spec's positionally, and its `result` binder to the spec's — `result` is declared per operation as `<op>.result` (proposal 041), so without that alignment no clause mentioning it could ever match and a spec operation carrying any `ensures` would have **no possible provider**. A logically equivalent but differently spelled refinement is not yet recognised. Aligning the two `result` binders is a claim about the values they denote, so it holds only where the two **return types** agree, and where it does not the override is refused naming both types rather than reported as a weakened postcondition. The condition is that the alignment is what **discharges** a clause — there is a clause pair that matches with the binders aligned and does not match without — and not merely that some clause mentions `result`. The three cases separate only under that reading and each wants a different answer: a spec and an override that both promise `P(result)` are matched by the alignment alone, so the return types decide; a spec and an override that both promise `P(x)` match either way, so a differing return type there is the general signature question *Backing conformance* above asks and this one does not; and a spec promising `P(x)` against an override promising `P(result)` matches under neither, so it is a weakened postcondition and naming the return types would send the author to a line whose repair would not load. The comparison is **covariant** — a subtype return is a refinement, and a predicate about a value of the subtype is the same proposition — and it is made only when both types are **ground**, so a return type the provision's bindings do not ground fails open. Grounding is what makes the ordinary parametric case decidable at all: a spec declaring `-> T` is compared as the carrier the provision binds `T` to, not as `T`. This rule and the *Backing conformance* rule above are the two places the return type is read, and they are not redundant: this one applies wherever a clause is discharged across the two binders — including where the spec operation carries its own default body, which the other rule's gate excludes — while the other applies with no clause in sight. A program can trip either alone.

Note: namespace-level `fact Eq[T = Int64]` (standalone, not inside a sort body) does NOT trigger auto-binding of operations — operations there are standalone rules associated with the fact.

**Namespaces** group sorts, operations, and rules for encapsulation and visibility control, but do not introduce type parameters. A namespace may contain sorts (both parametric and concrete) and type aliases, but unspecified sorts (`sort T = ?`) appear only inside sort bodies as type parameters — never directly in a namespace.

### 8.8 Persistence and Store-Aware Resolution

The KB is not purely in-memory. Facts can be backed by **persistent stores** — filesystem directories, SQL databases, or other external backends. The persistence model is defined as an abstract algebra in `anthill.persistence` (see [proposal 007](proposals/007-persistence-layer.md) for the full design).

**Store capabilities** determine how the reasoning engine interacts with each store:

- **`bulk`** stores (e.g., filesystem) — all facts are loaded into memory at startup via `pull()`. Backward chaining works entirely in-KB. The `.anthill/` directory with its `workitems/`, `tools/`, and `facts/` subdirectories is a bulk store.

- **`queryable`** stores (e.g., PostgreSQL) — patterns are translated to native queries on demand. During backward chaining, when the engine encounters a goal whose sort is routed to a queryable store, it calls `retrieve(store, pattern)` instead of searching in-memory facts. The store acts as an **external oracle** — a well-known pattern in logic programming (Datalog with external data sources, Prolog foreign predicates).

**Routing** maps fact sorts to stores via ordinary rules:

```
rule route(WorkItem(?))   <=> IndexedFileStore(".anthill", stage0)
rule route(AuditEntry(?)) <=> FileStore(".anthill/audit", by_namespace)
rule route(?)             <=> FileStore(".anthill", stage0)   -- default
```

The stores named here are the ones the stdlib actually ships. A queryable SQL store
would be routed the same way; its shape is sketched at `examples/sql-store/`, which is
where it lives because no host realizes it (proposal 038, "What the stdlib carries").

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

**Host implementations are keyed per carrier and per operation (WI-876).** A binding block maps two kinds of thing into the host: `carrier { … }` says which host **type** realizes a sort, and `operation_map { … }` says which host **function** realizes one of that carrier's operations.

```
namespace anthill.prelude
  provides Int64 language rust
    artifact "rustland/anthill-stl/src/prelude/int.rs"
    carrier { Int64: "i64" }
    operation_map { compare: "ordered_compare", gt: "ordered_gt" }
    fact Ord[T = Int64]
  end
end
```

The key on the left is the **short name of an operation the carrier declares**; the string on the right is a key into the host runtime's own registry of exposed functions. The clause says what *backs* an operation — it does not bring one into existence, so the carrier must still declare it (body-less, its body being the host artifact's). Two failures are refusals rather than silent no-ops: a `host_fn` the runtime does not provide, and a `<carrier>.<operation>` that is not declared. Mappings for another host language are ignored by a given runtime.

A mapping counts as *executable* backing for §8.7's check, **and only for the carrier that wrote it** — though nothing exercises that today, because the check skips a host-realized carrier wholesale (retiring that coarser exemption, now that backing is knowable per operation, is follow-up work). That per-carrier keying is the point of the clause: without it a host implementation has nowhere to live but the **spec** operation, where one implementation serves every carrier that never wrote its own — including carriers it cannot handle. The ordering surface was exactly that: `Ord.compare` and `PartialOrd.gt`/`gte`/`lt`/`lte` compared host scalars only, yet backed every provider, so a structural `Ord` carrier loaded clean and died at eval. Keyed per carrier, the spec's own default bodies are no longer shadowed and a structural carrier needs only `compare` — `PartialOrd` derives the four comparisons from it and `Ord` derives `max`/`min`. It also lets one spec operation have genuinely different host implementations per carrier: `Float`'s comparisons are IEEE (a `NaN` operand answers false), the other scalars' are total, and each names its own function in its own binding.

Each entry reaches the KB as an `anthill.realization.OperationMapping` fact (`carrier`, `operation`, `host_fn`, `lang`) — the flat, queryable form the realization tables use, so the runtime's registry reads facts rather than a hardcoded list.

**What `host_fn` denotes is the host's to say (WI-886).** For a language whose runtime *interprets* the program, it is a key into a closed registry of functions that runtime is willing to expose — the host code already exists and the binding only selects it, so an unknown key is a refusal — raised when an interpreter is built over the program, not by the loader. The split is deliberate: whether the operation exists is the loader's question and it answers it, but which functions a runtime exposes is only that runtime's to know, and a mapping for a *different* host language must not be judged by it at all. Closed means *a key must be registered*, not *fixed when the runtime was compiled*: an embedder may add its own entries to that registry (WI-1122), which is what lets a host bind a carrier of its own. The refusal, the arity check against the declaration, and the requirement that the carrier still declare the operation apply identically to an embedder's entry, and a key may name only one function — a collision with the runtime's own entries is itself a refusal. For a language the toolchain *generates*, there is no registry, because the backend writes the host code; what it needs from the binding is the **spelling**. The C++ backend therefore reads `host_fn` as an expression template, with `$1`, `$2`, … standing for the operation's arguments:

```
namespace anthill.prelude
  provides Float language cpp
    operation_map { sqrt: "std::sqrt($1)", neg: "(-$1)", pi: "3.141592653589793" }
  end
end
```

A bare function name would not do: a host language's primitive operations are not all functions (`neg` is an operator, `pi` a literal), and a template also lets the mapping state a conversion its anthill signature requires (`Float.floor` returns `Int64`, `std::floor` a `double`). Neither reading resolves the string by reflection, and neither can check it: whether `std::sqrt` exists is the C++ compiler's question. What *is* checked, in both, is agreement with the declaration — the interpreter compares its registry's arity, the generator requires the template's placeholders to be exactly `$1`..`$n` for the operation's `n` parameters.

The mapping is also what a generating backend must have: an operation with no body and no host realization for the target language cannot be lowered at all, and is a codegen error naming the operation and the carrier rather than a call emitted into the output for a function that does not exist.

**Host-supplied constants use `const_map`, the const-level peer (WI-889).** A carrier may declare a body-less `const` whose value comes from the host — the `Float` IEEE specials `infinity` / `negativeInfinity` / `nan` have no anthill surface literal. A `const` is not an operation, so it cannot ride `operation_map`, whose reader refuses a non-operation by design (the kind check that stops an `operation_map` over an entity from registering a comparison as the constructor). `const_map` is its channel, and it draws the **mirror** kind check — the target must resolve and be a `const` — so together the two clauses keep the guarantee that a host implementation attaches only to an operation or a const, never to an entity constructor or a sort.

```
namespace anthill.prelude
  provides Float language rust
    const_map { infinity: "float_infinity", nan: "float_nan" }        -- runtime value-source keys
  end
  provides Float language cpp
    const_map { infinity: "std::numeric_limits<double>::infinity()" } -- verbatim C++ expression
  end
end
```

Each entry reaches the KB as an `anthill.realization.ConstMapping` fact (`carrier`, `const_name`, `host_fn`, `lang`). `host_fn` is read exactly as it is for an operation, per host: a key into the interpreting runtime's registry (an unknown key is refused when an interpreter is built, as for an operation; the value source must be nullary), and a verbatim expression for a generating backend (a const takes no arguments, so there are no `$1` slots). Like `operation_map`, the clause says what *backs* a const — the carrier must still declare it — and writing one in a `language anthill` block is a refusal, since an anthill implementation is a body, not a host binding.

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
AbsName     ::= '::' Name                    -- absolute path; REFERENCE positions only
RefName     ::= Name | AbsName               -- what a term / type / citation may write
StringLit   ::= '"' [^"]* '"'
IntLit      ::= '-'? Digit+
FloatLit    ::= '-'? Digit+ '.' Digit+
BoolLit     ::= 'true' | 'false'

-- Literal sugar for compound types (desugars to Fn terms):
DurationLit      ::= IntLit ('ms' | 's' | 'm' | 'h' | 'd')            -- 5m → Duration(5, "m")
CollectionLit    ::= '[' ']'                                            -- [] → ListLiteral()
                   | '[' Term (',' Term)* ']'                            -- [a,b] → ListLiteral(a,b)
SetLit           ::= '{' Term? (',' Term)* '}'                          -- {a,b} → SetLiteral(a,b)

Body[F]     ::= '{' F '}'  |  F 'end'

-- =================================================================
-- Terms
-- =================================================================

Term        ::= AtomTerm
              | InfixTerm

AtomTerm    ::= Const(type, value)
              | VariableTerm                 -- variable with optional description
              | Fn(RefName, args: [CallArg])
              | Ref(RefName)
              | Instantiation(RefName, SortBinding+)  -- Eq[T = Int64] in term position
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

-- Executable bodies (§4.8). `BodyExpr` admits optional braces only at the
-- operation/const boundary; nested expressions use `Expr`.
BodyExpr    ::= Expr | '{' Expr '}'
Expr        ::= Term | MatchExpr | IfExpr | LetExpr | LambdaExpr | ProofStatement
MatchExpr   ::= 'match' Term MatchBranch+
MatchBranch ::= 'case' Pattern ['|' Term] '->' Expr
IfExpr      ::= 'if' Term 'then' Expr 'else' Expr
LetExpr     ::= 'let' Pattern [':' Type] '=' Expr Expr
LambdaExpr  ::= 'lambda' Pattern '->' Expr
Pattern     ::= Identifier | '_' | Literal
              | Name '(' [PatternArg (',' PatternArg)*] ')'
              | '(' ')' | '(' Pattern ')'
              | '(' PatternElem ',' PatternElem (',' PatternElem)* ')'
              | '(' Identifier ':' Type ')'
PatternArg  ::= Pattern | Identifier ':' Pattern
PatternElem ::= Pattern | Identifier ':' Type
FnArg       ::= Term | Identifier ':' Term | VariableTerm ':' Type | LambdaExpr

-- A CALL's argument list admits one more form than a tuple literal's does: the
-- variadic-capture rest pattern (proposal 056 §2.3 / WI-1129). The grammar allows
-- it in any call, because a rule head and an operation-body call are the same
-- production; WHERE it is legal — the last positional argument of a `[simp]`
-- equation head's left-hand side, and nowhere else — is a located refusal at
-- conversion (§5.3). Not admitted on the dot form (`x.m(...)`, §6.7).
CallArg     ::= FnArg | RestArg
RestArg     ::= '...' VariableTerm

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

File             ::= (NamespaceContent - ProvidesClause)*
                                                 -- a file's top level: the same content,
                                                 -- scoped to the GLOBAL scope (§5.1); see
                                                 -- the note below for the one exclusion

NamespaceContent ::= Import
                   | Sort | Enum | Rule | Operation | Const
                   | RequiresDecl                 -- sort-level constraint
                   | Entity                       -- sugar (§6.3)
                   | Fact | Constraint            -- sugar (§6.1, §6.2)
                   | OperationBlock | RuleBlock   -- sugar (§6.4)
                   | Describe                     -- description (§4.1)
                   | Proof                        -- §7.3
                   | ProvidesClause               -- §8.7; needs a sort at the address (§5.1)
                   | ProvidesBlock                -- host realization (§10.2)
                   | Namespace

-- A namespace at the address of a sort is a SECONDARY ENTRY to that sort's scope,
-- and §5.1 bounds what it may contain. `File` above reuses this production with ONE
-- exception: a ProvidesClause takes its subject from the scope it is written in, and
-- a file's top level is the global scope, which is no sort — so it is not admitted
-- there at all. Proof and ProvidesBlock are.

Visibility  ::= 'internal' | 'public'

Sort        ::= DescriptionBlock*
                  [Visibility] 'sort' Name '=' VariableTerm        -- unspecified (only in SortContent)
                  [MetaBlock]
              | DescriptionBlock*
                  [Visibility] 'sort' Name '=' Type                -- type alias
                  [MetaBlock]
              | DescriptionBlock*
                  [Visibility] 'sort' Name [SortTypeParamList]     -- sort with body
                  Body[SortContent*]
                  [MetaBlock]
              | SortVarBinder | SortBracketBinder

SortTypeParamList ::= '[' SortTypeParam (',' SortTypeParam)* ']'
SortTypeParam ::= Identifier [SortTypeParamList]
SortVarBinder ::= DescriptionBlock* [Visibility]
                    'sort' Var [SortBinderBody] [MetaBlock]
SortBracketBinder ::= DescriptionBlock* [Visibility]
                        'sort' '[' Identifier ']' [SortBinderBody] [MetaBlock]
SortBinderBody ::= '{' (SortVarBinder | SortBracketBinder)+ '}'
EffectsSortItem ::= DescriptionBlock* [Visibility]
                      'effects' Name '=' Type [MetaBlock]
Enum ::= DescriptionBlock* [Visibility] 'enum' Name
           Body[EnumContent*] [MetaBlock]
SortAlias ::= DescriptionBlock* [Visibility]
                'sort' Name '=' Type [MetaBlock]
EnumContent ::= Import | SortAlias | EffectsSortItem | RequiresDecl
              | Entity | Operation | Rule | Fact | Constraint
              | OperationBlock | RuleBlock | Describe | Proof | ProvidesClause

-- Note: unspecified sorts (first form) may only appear inside a sort body
-- as type parameters. Type aliases (second form) may appear in sort or namespace bodies.
-- Namespaces contain sorts-with-body and type aliases (not unspecified sorts).

SortContent ::= Import
              | Sort | Enum | EffectsSortItem | Entity | Operation | Const | Rule
              | RequiresDecl
              | Fact | Constraint | OperationBlock | RuleBlock
              | Describe | Namespace
              | Proof | ProvidesClause
              -- NOT ProvidesBlock: a host realization block is admitted in a
              -- namespace body and at a file's top level, never in a sort body.

-- Proof / provides (§5.10).
Proof ::= DescriptionBlock* 'proof' Name
           (SingleProof | StructuredProof) 'end' [Name]
SingleProof ::= ['using' NameList] ['by' ProofStrategy] [ProofBody]
ProofBody ::= ':-' RuleBody
            | 'query' StringLit ['mapping' MappingBlock]
ProofStrategy ::= Identifier | Identifier '(' FnArg (',' FnArg)* ')'
StructuredProof ::= ProofStep+ [ProofConclusion]
ProofStep ::= 'rule' [Name ':'] RuleShape [MetaBlock]
               ['using' NameList] 'by' ProofStrategy
ProofConclusion ::= ['using' NameList] 'by' ProofStrategy
ProofStatement ::= 'proof' Name ['using' NameList] ['by' ProofStrategy]
                     ['conclude' Term] 'end' Expr

ProvidesClause ::= 'provides' SpecInstantiation
                    [':-' SpecInstantiation (',' SpecInstantiation)*]
ProvidesBlock  ::= DescriptionBlock* 'provides' Type 'language' Identifier
                     ProvidesItem* 'end' [Name]
ProvidesItem   ::= 'artifact' StringLit
                 | 'carrier' Bindings                         -- anthill type  -> host type
                 | 'operation_map' Bindings                   -- operation     -> host fn
                 | 'const_map' Bindings                       -- const         -> host value
                 | 'namespace_map' Bindings                   -- namespace     -> host module
                 | Rule | RuleBlock | Fact | Proof           -- admitted; see §5.1 in an entry
Bindings       ::= '{' Identifier ':' Term (',' Identifier ':' Term)* '}'
MappingBlock   ::= '{' MappingEntry (',' MappingEntry)* [','] '}'
MappingEntry   ::= Name '->' (Name | StringLit)

DescriptionBlock ::= '{<' Text '>}'               -- free-form text, preserved as KB facts
Describe    ::= 'describe' Name DescriptionBlock+  -- attach description(s) to named symbol; appends to existing

FieldList   ::= Field (',' Field)*
Field       ::= Name ':' Type

Type        ::= RefName                                        -- simple: Account, Int64, ..a.b.T
              | RefName '[' SortBinding (',' SortBinding)* ']' -- inline instantiation: List[T=Int64]
              | VariableTerm                                    -- logical variable: ?, ?T, ?T {< desc >}+ ?
              | TupleType                                        -- tuple type: (), (a: A), (A, B)
              | TupleType '->' Type                              -- arrow type: (A) -> B
              | TupleType '->' Type '@' EffectSet                -- effectful arrow: (A) -> B @ E
TupleType   ::= '(' ')'                                          -- unit
              | '(' TupleTypeArg ')'                             -- 1 element
              | '(' TupleTypeArg ',' TupleTypeArg (',' TupleTypeArg)* [','] ')'  -- 2+ elements
TupleTypeArg ::= Type | Name ':' Type | Name ':' Literal
SpecInstantiation ::= Name
                    | Name '[' SortBinding (',' SortBinding)* ']'
-- An arrow's parameter list IS a TupleType (WI-766); there is no separate
-- ArrowParams production. A lone positional element `(A)` parses, but is a
-- parameter list only -- as a TYPE it is an error.

Rule        ::= DescriptionBlock*
                  'rule' [Name ':'] RuleShape [MetaBlock]
RuleShape   ::= Heads ':-' RuleBody | RuleBody '-:' Heads | Heads
Heads       ::= Goal (',' Goal)* | '⊥'   -- a [simp] equation head's LHS may end in a RestArg (§5.3)
RuleBody    ::= Goal (',' Goal)*
Goal        ::= Cut | LetBinding | Term
Cut         ::= '!'
LetBinding  ::= 'let' VariableTerm '=' Term

Operation   ::= DescriptionBlock*
                  [Visibility] 'operation' Name [TypeParamList]
                  '(' [ParamList] ')' '->' Type
                  OperationClause* ['=' BodyExpr] [MetaBlock]
TypeParamList ::= '[' TypeParam (',' TypeParam)* ']'
TypeParam    ::= Identifier                        -- legal form; `= Type` parses only for refusal
OperationClause ::= 'requires' RequiresBody
                  | 'ensures' RuleBody
                  | 'effects' EffectSet
                  | 'meta' MetaBlock
RequiresBody ::= RequiresItem (',' RequiresItem)*
RequiresItem ::= RequiresBinder | Goal
RequiresBinder ::= Identifier ':' Type
ParamList   ::= Param (',' Param)*
Param       ::= ['...'] Identifier ':' Type

EffectSet   ::= EffectExpr | '{' [EffectExpr (',' EffectExpr)*] '}'
EffectExpr  ::= SimpleEffect | '+' SimpleEffect | '-' SimpleEffect
              | 'merge' '(' EffectExpr (',' EffectExpr)* ')'
              | SimpleEffect ':-' Term
              | '(' SimpleEffect ':-' RuleBody ')'
SimpleEffect ::= Name
               | Name '[' SortBinding (',' SortBinding)* ']'
               | VariableTerm

Const       ::= DescriptionBlock*                 -- term-level constant; see §5.9
                  [Visibility] 'const' Name ':' Type ['=' BodyExpr]
                  [MetaBlock]
              -- type MANDATORY, body OPTIONAL (body-less = host-supplied via const_map)
              -- no params, no type params, no effects clause

RequiresDecl ::= 'requires' [Identifier ':'] Type
                  -- optional binder = named requirement slot (proposal 058)

-- =================================================================
-- Syntactic Sugar
-- =================================================================

Fact        ::= DescriptionBlock*
                  'fact' Term [MetaBlock]
              -- desugars to: rule Term

Constraint  ::= DescriptionBlock*
                  'constraint' [Name ':'] ConstraintBody
                  [MetaBlock]
ConstraintBody ::= RuleBody [':-' RuleBody]
                 | QuantifiedConstraint | AggregationConstraint
QuantifiedConstraint ::= Quantifier '(' VariableTerm ':' Term ')' '-:' ConstraintBody
                       | Quantifier VariableTerm ':' RuleBody '-:' ConstraintBody
                       | Quantifier VariableTerm '-:' ConstraintBody
Quantifier ::= 'forall' | 'some' | 'one' | 'lone' | 'no'
AggregationConstraint ::= Aggregate '(' VariableTerm ':' RuleBody '-:' RuleBody ')'
                            Comparison Term
Aggregate ::= 'count' | 'sum' | 'min' | 'max'
Comparison ::= '<=' | '>=' | '<' | '>' | '=' | '!='
              -- aggregates parse but are refused as unsupported (§6.2)

Entity      ::= DescriptionBlock*
                  [Visibility] 'entity' Name ['(' FieldList ')']
                  [MetaBlock]
              -- desugars to: sort Name { entity Name [( FieldList )] }

OperationBlock ::= 'operation' Body[OperationEntry*]
              -- desugars to: individual Operation declarations
OperationEntry ::= DescriptionBlock*
                     [Visibility] Name [TypeParamList]
                     '(' [ParamList] ')' '->' Type
                     OperationClause* ['=' BodyExpr] [MetaBlock]

RuleBlock   ::= 'rule' Body[RuleEntry*]
              -- desugars to: individual Rule declarations
RuleEntry   ::= [Name ':'] RuleShape [MetaBlock]

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
MetaEntry   ::= Name [':' Term]                 -- flag or any key-value pair
```

## 12. Open Questions

Design questions discovered during implementation that need decisions.

### 12.1 Effect semantics

Effect declarations use §5.5's row algebra and guarded elements. Row parsing,
canonicalization, propagation, lacks constraints, and guarded discharge are
implemented; executing every possible effect label is a separate runtime
question. Open questions:

- **Effect checking**: Should declared effects be verified against implementations, or remain advisory?
- **Control flow effects**: `Suspend` and `Branch` are valid row labels, but their
  continuation/nondeterminism runtime behavior remains open in WI-069/WI-070.
- **Effect polymorphism**: Sorts declare row parameters as `effects E = ?`; the
  row typer propagates them, while host/codegen representation remains backend
  specific.
- **Ambient resource effects**: Effects for resources not in the parameter list
  (e.g. `Output[stdout]`, `Log[logger]`) need concrete use cases before design.
