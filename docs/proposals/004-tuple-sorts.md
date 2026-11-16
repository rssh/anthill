# Proposal 004: Tuple Sorts

**Status:** Implemented. Extended 2026-11-16, draft: a tuple is a `NamedTuple`, a sort that carries derived provisions (§"Extension (2026-11-16)").
**Depends on:** None
**Affects:** Kernel Language Specification §4, §11

## Motivation

The kernel language has no anonymous product types. To group values, users must define named entities:

```
entity Pair(fst: A, snd: B)
```

This is adequate for domain-specific types where field names carry meaning (`entity Point(x: Int64, y: Int64)`), but verbose for transient groupings — intermediate results, multi-value returns, or generic specifications where named fields add no information.

Moreover, operation parameter lists are already named tuples in disguise:

```
operation divmod(a: Int64, b: Int64) -> (Int64, Int64)
--               ^^^^^^^^^^^^^^     ^^^^^^^^^^
--               named tuple        unnamed tuple
```

Tuple sorts make this implicit concept explicit.

## Core Idea: One Concept

There is only one construct: **named tuples**. Every tuple element has a name.

Positional syntax `(A, B, C)` is sugar for `(_1: A, _2: B, _3: C)` — elements get auto-generated positional names `_1`, `_2`, `_3`, etc. This follows Scala's approach where `Tuple2` has fields `._1` and `._2`.

This means:

- `(Int64, String)` and `(_1: Int64, _2: String)` are the **same sort**
- `(a: Int64, b: String)` is a **different sort** (different field names)
- No subtyping between named and positional — they are simply tuples with different names
- Pattern matching `(?x, ?y)` is sugar for `(_1: ?x, _2: ?y)`

## Grammar

```
Type ::= ...
       | '(' NamedField ',' NamedField (',' NamedField)* ')'   -- named tuple (2+)
       | '(' Type ',' Type (',' Type)* ')'                     -- positional sugar (2+)
       | '(' ')'                                                -- unit

NamedField ::= Name ':' Type

Term ::= ...
       | '(' NamedArg ',' NamedArg (',' NamedArg)* ')'         -- named tuple value (2+)
       | '(' Term ',' Term (',' Term)* ')'                     -- positional sugar (2+)
       | '(' ')'                                                -- unit value

NamedArg ::= Name ':' Term
```

A single-element form `(A)` is just parenthesization for grouping, not a tuple. Tuples require two or more elements.

**All-or-nothing naming:** either all elements have explicit names or none do (in which case `_1`, `_2`, ... are inferred). Mixing `(a: Int64, String)` is not allowed.

## Desugaring

Positional tuples desugar to named tuples with `_N` names:

| Surface syntax | Desugared form |
|---|---|
| `(A, B)` | `(_1: A, _2: B)` |
| `(Int64, String, Bool)` | `(_1: Int64, _2: String, _3: Bool)` |
| `(?x, ?y)` | `(_1: ?x, _2: ?y)` |
| `(1, "hello")` | `(_1: 1, _2: "hello")` |
| `()` | `()` (unit, no fields) |

## Examples

### Named tuples

```
(a: Int64, b: String)                     -- named pair
(x: Int64, y: Int64, z: Int64)               -- named triple
(name: String, age: Int64)               -- record-like

(a: 1, b: "hello")                     -- named tuple value
rule swap((a: ?x, b: ?y)) = (a: ?y, b: ?x)
```

### Positional tuples (sugar for `_1`, `_2`, ...)

```
(Int64, String)                           -- same as (_1: Int64, _2: String)
(A, B, C)                              -- same as (_1: A, _2: B, _3: C)

(?x, ?y)                               -- same as (_1: ?x, _2: ?y)
rule swap((?x, ?y)) = (?y, ?x)         -- same as swap((_1: ?x, _2: ?y)) = (_1: ?y, _2: ?x)
```

### Unit

```
()                                      -- zero-element tuple, the unit value/sort
```

## Relationship to Existing Constructs

Named tuples unify several existing concepts:

| Current concept | With named tuples |
|---|---|
| `operation f(a: Int64, b: String) -> R` | parameter list = `(a: Int64, b: String)` |
| `entity Point(x: Int64, y: Int64)` | nominal wrapper around `(x: Int64, y: Int64)` |
| `Pair(fst: A, snd: B)` | nominal wrapper around `(fst: A, snd: B)` |

An `entity` declaration adds a **nominal** type around a named tuple — the distinction is that `entity Point(x: Int64, y: Int64)` creates a new sort, while `(x: Int64, y: Int64)` is structural:

```
(x: Int64, y: Int64)                        -- structural: any (x: Int64, y: Int64) matches
entity Point(x: Int64, y: Int64)            -- nominal: only Point values match
```

### Named tuples and Operation

Operation parameter lists are named tuples. This means `Operation[A, B, E]` can use a named tuple for `A`:

```
-- operation deposit(account: Account, amount: Money) -> Account
-- is an Operation[A = (account: Account, amount: Money), B = Account, E = ...]

rule apply(?op, (account: ?a, amount: ?m)) = ...
```

This preserves parameter names through the `Operation` abstraction.

## Disambiguation

Tuples use parentheses `(A, B)`. The only existing parenthesized forms are:

- `Name(args)` — function application (preceded by a name)
- `(expr)` — grouping (single element, no comma)

Neither conflicts: `Name(` is function application, `(A, B)` with a comma is a tuple, `(A)` is grouping. No lookahead needed.

Named tuples `(a: Int64, b: String)` are distinguished from positional tuples by `name :` after `(`. This uses the same `name : Type` pattern as existing `field_decl` in entity/param declarations.

Arrow types like `(A, B) -> C` are not a special case — `->` is a regular infix operator (Proposal 016), so this parses as `arrow((A, B), C)`: a tuple as the left operand of `->`. No disambiguation needed.

## Semantics

Tuple sorts are **structurally typed** anonymous products. Two tuples with the same field names and types are the same sort, regardless of where they appear.

### Unit

The unit sort `()` has exactly one value, also written `()`. It is the identity for products:

```
(A, ())  ≡  A
((), B)  ≡  B
```

Unit is useful as a placeholder return type for side-effecting operations and as the zero-element product.

Note: the prelude already defines `sort Unit = ?`. With tuples, `Unit` becomes an alias for `()`.

## Representation

Tuple literals are represented as `TupleLiteral(...)` in the term layer, analogous to `SetLiteral(...)` for set literals. Named elements use named args: `TupleLiteral(a: elem1, b: elem2)`. Positional elements desugar to `TupleLiteral(_1: elem1, _2: elem2)`. The `TupleLiteral` entity is defined in `anthill.reflect`.

In type position, tuples are represented as parameterized types (structural encoding — the exact form is an implementation detail).

## Use Cases

### Multi-value returns

```
operation divmod(a: Int64, b: Int64) -> (Int64, Int64)
  requires neq(b, 0)

rule divmod(?a, ?b) = (div(?a, ?b), mod(?a, ?b))
```

### Named multi-value returns

```
operation divmod(a: Int64, b: Int64) -> (quotient: Int64, remainder: Int64)
  requires neq(b, 0)

rule divmod(?a, ?b) = (quotient: div(?a, ?b), remainder: mod(?a, ?b))
```

### Operation as first-class sort

With tuples, `Operation[A = (Int64, String), B = Bool, E = ...]` naturally represents multi-argument operations:

```
rule apply(?op, (?x, ?y)) = ...
```

With named tuples, parameter names are preserved:

```
rule apply(?op, (account: ?a, amount: ?m)) = ...
```

### State-passing (connection to §5.6)

The state-passing interpretation of effectful operations (§5.6) uses products internally:

```
-- op_e : Env × A → (R × Env × Event list) + Error

-- With tuple sorts:
operation op_e(env: Env, a: A) -> (R, Env, List[T = Event])
  effects (Error)
```

## Semantic Rules

1. There is one tuple construct: named tuples. Positional syntax is sugar for `_1`, `_2`, ... names.
2. Tuple sorts are structurally typed — identity is determined by field names, types, **and order**.
3. `(A, B)` and `(_1: A, _2: B)` are the same sort.
4. `(a: Int64, b: String)` and `(Int64, String)` are different sorts (different names).
4a. `(a: Int64, b: String)` and `(b: String, a: Int64)` are different sorts (different **order**).
    Order is part of a tuple's IDENTITY. It is NOT part of `<:`, which is a different relation:
    subtyping is name-keyed, so BOTH width and permutation hold —
    `(A: TA, B: TB, C: TC) <: (A: TA, C: TC)` with the drop from anywhere, and
    `(b: String, a: Int64) <: (a: Int64, b: String)`. Every reader of a data tuple is name-keyed
    (`t.x` access and destructuring alike), which is what makes that sound; do not carry the
    order rule across from identity into `<:`. See `kernel-language.md` §4.5
    (WI-788, WI-804, WI-803).
5. `()` is the unit sort with a single value `()`.
6. Tuple values are constructed and destructured via pattern matching.
7. All-or-nothing naming: either all elements have explicit names or none do.
8. Component names are **distinct**, checked at every producer that builds a tuple from
   names the author wrote: the literal `(a: 1, b: 2, a: 3)`, the type
   `(a: Int64, a: String)`, and a variadic capture's leftover named arguments
   `cap(1, a: 2, a: "ess")` (WI-805). Every reader resolves a name to its FIRST match
   (rule 4a), so a repeated name makes the later component reachable by neither its name
   nor its position and leaves its declared type unchecked. This is rule 2 read to its
   conclusion: if identity is determined by field names and order, a name that
   identifies two components identifies neither. Scoped to a tuple — an arrow's
   parameter list shares the surface but is applied positionally, so a shadowed
   parameter's type is still checked against an argument at every call.

## Backwards Compatibility

No existing syntax is affected. Parenthesized expressions in the current grammar are either:

- `Name(args)` — function application (preceded by a name)
- `(expr)` — grouping (single element)

Neither conflicts with `(Type, Type)` in type positions or `(Term, Term)` in term positions, since the comma distinguishes tuples from grouping, and the preceding name distinguishes function application.

No existing valid program is invalidated by this change.

## Implementation Notes

Implemented in tree-sitter-anthill grammar, parse IR, converter, loader, codegen, and stdlib reflect.

### Parenthesized Expression Rule

Adding `tuple_literal` (which starts with `(`) to `_atom_term` created an ambiguity with `prefix_term`. Before tuples, `not(x)` always parsed as `fn_term` because no `_atom_term` started with `(`. With `tuple_literal` available, tree-sitter's GLR parser could also interpret `(x)` as a (failed) tuple literal inside `prefix_term`, causing parse errors in `bool.anthill`.

The fix: add `paren_expr: $ => seq('(', $._term, ')')` to `_atom_term`. This gives single-element parenthesized expressions `(a) = a` a clean parse path. Tree-sitter's GLR naturally resolves `not(x)` as `fn_term` without needing dynamic precedence — both paths produce valid parses, and the fn_term path wins.

### Representation

- **Grammar**: `tuple_literal` (term position, `prec(-2)`), `tuple_type` (type position), `paren_expr` (grouping)
- **Parse IR**: `TypeExpr::Tuple(Vec<(Symbol, TypeExpr)>)` — uses `Vec` (not `SmallVec`) because tuples can contain tuples, creating a recursive type
- **Term representation**: `Term::Fn { functor: "TupleLiteral", pos_args: [], named_args: [...] }` — same pattern as `SetLiteral`
- **Stdlib**: `entity TupleLiteral` in `anthill.reflect`, registered in `register_stdlib_scopes` with global import

## Extension (2026-11-16): a tuple is a `NamedTuple`

### The problem

A tuple type is structural, and no sort stands behind it, so nothing can provide a spec at a
tuple. An arrow had the same gap and was given a sort, `Function` (proposal 002, "Correction
(2026-11-03)"). Where a spec is needed at a tuple today, each reader has its own special case or
refuses. Measured on `f9cd2403`, over a `Pt` whose own `eq` compares `x` alone:

```anthill
sort Pt
  entity pt(x: Int64, y: Int64)
  provides PartialEq[T = Pt]
  provides Eq[T = Pt]
  operation eq(a: Pt, b: Pt) -> Bool =
    match a case pt(ax, ay) -> match b case pt(bx, by) -> PartialEq.eq(ax, bx)
end
```

| | Program | Today |
|---|---|---|
| T1 | `rule t1() :- (pt(1, 2), 3) = (pt(1, 9), 3)` | holds, with no member: each component is compared through the equality index, which reads `pt`'s constructor (kernel-language §8.3: "A tuple has no `eq` member") |
| T2 | `operation same[A](a: A, b: A) -> Bool requires PartialEq[T = A] = PartialEq.eq(a, b)`, called as `same((pt(1, 2), 3), (pt(1, 9), 3))` | refused at load: "its carrier is `(_1: Pt, _2: Int64)`, a STRUCTURAL FORMER — a tuple or an arrow — and nothing provides `PartialEq`" |
| T3 | `rule t3() :- [(pt(1, 2), 3)] = [(pt(1, 9), 3)]` | refused at load: no impl provides `PartialEq` at the tuple, so `List`'s derived equality has nothing to derive from |
| T4 | `TypeValue.type_value[T = (a: Int64, b: String)]()` | refused at load: a tuple carries no provision (proposal 065 §7 step 2, "FORMERS deferred") |
| T5 | `Map[K = (Int64, Bool), V = Int64]` | loads, by a special case in the key check (`typing/coherence.rs`, which reads a tuple by its components); `Map[K = (a: Float), V = Int64]` is refused |

WI-20261105-CBRD2 makes an untyped equality at a carrier with its own `eq` an error at run time
(decided 2026-11-16). T1 is typed, but its goal carries no member, so it cannot be told from an
untyped one, and its components would start to error.

### The rule

1. **A tuple type is the sort `NamedTuple` applied to its components.** `(l₁: T₁, …, lₙ: Tₙ)` is
   `NamedTuple` with one parameter per component, the label its name, in order; `(A, B)` is
   `(_1: A, _2: B)` as before, and `()` is `NamedTuple` with none. The sort lives in
   `anthill.prelude`. It is written only as tuple syntax; `NamedTuple` names the sort where a
   sort is named (a derived provision, a message). The rules above are unchanged: identity is
   the labels, the component types and their order (rule 4a), `<:` is by label with width and
   permutation, and a component's label is distinct (rule 8).
2. **Its provisions are derived, as a composite's classification is** (kernel-language §8.3).
   A tuple provides `PartialEq` when each component's type provides it, and `Eq` when each
   provides `Eq`; `()` provides both. It provides `TypeValue` when each component's type does
   (065 §2, now for the tuple former too). No program writes a provision at `NamedTuple`.
3. **The derived member compares the components through their own members**, in order, as a
   composite's derived `eq` compares its fields. Its law is the components': `Eq` at the tuple
   holds where it holds at each component.
4. **The instance is a dictionary**, of the shape every dictionary has
   (`eval/dictionary.rs`): `Dictionary(d₁ … dₙ, impl: NamedTuple)`, one sub-dictionary per
   component, in component order. A component at a type parameter takes the caller's dictionary
   for that parameter. It is passed as any dictionary is: T2's `same` is handed it, and `List`'s
   derived equality at `List[T = (Pt, Int64)]` enters with it.
5. **A typed `=` at a tuple is a call of the tuple's `eq` through its instance.** It carries the
   member, so no component is compared without one, and the equality index is not read.

### Target programs, as they answer under the rule

| | Answer |
|---|---|
| T1 | holds, through `NamedTuple`'s `eq` entered with `Dictionary(‹Pt's›, ‹Int64's›, impl: NamedTuple)`; `(pt(1, 2), 3) = (pt(2, 2), 3)` does not |
| T2 | loads, and answers `true` |
| T3 | loads, and holds |
| T4 | answers the type `(a: Int64, b: String)` |
| T5 | unchanged; the key check reads the derived `Eq` provision instead of its special case |
| T7 | `(Int64, Relation[T = (x: Int64), E = {}])` provides no `PartialEq` (a `Relation` provides none), and `PartialEq.eq` at it is refused at load, as today (measured: "`PartialEq[T = Relation[…]]` cannot be supplied") |
| T8 | `(Int64, Float)` provides `PartialEq` and not `Eq`: `Map[K = (Int64, Float), V = Int64]` is refused, as today (measured, at the `Float` component) |

### What it replaces

- kernel-language §4.5: one sentence, a tuple type is `NamedTuple` applied to its components.
- kernel-language §8.3: "A tuple has no `eq` member: its equality is its components'" and "a
  tuple as a type argument (`List[T = (String, String)]`) … derives nothing" go; the key check's
  "A tuple provides `Eq` when each of its components' types does" is read as the derived
  provision.
- 065 §7 step 2: the tuple half of "FORMERS deferred".

### Not in this extension

- The arrow half of the formers (`Function` is a sort since 002's correction; a closure carrying
  the arrow type it was typed at, and `domain` at an arrow): WI-20261021-VF8GT.
- A tuple type written as a value in a rule body's data slot (VF8GT's (3)).

### Open questions

1. **Which specs derive at a tuple.** Proposed: `PartialEq`, `Eq` and `TypeValue`. `SortDomain`
   and type patterns (VF8GT, proposal 071) follow the same rule and could be added here; with a
   type pattern at a tuple, an `Error.reify` boundary could catch an `Error[(Int64, Int64)]`
   payload, which today waits on a tuple's instance (065, the open question withdrawn
   2026-10-16). `Ord` (lexicographic, by component order) is not proposed.
2. **Whether a program may name `NamedTuple`** as a type (`x: NamedTuple`, any tuple) or write a
   provision at it. Proposed: neither, in this extension: one written form for a tuple type, and
   derived provisions only.

### Stages

1. The sort, and its derived `PartialEq` and `Eq` with their dictionary: WI-20261116-JWCNN.
2. `TypeValue` at a tuple (065 §7 step 2's tuple half), and whatever open question 1 adds.

