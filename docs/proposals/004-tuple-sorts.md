# Proposal 004: Tuple Sorts

**Status:** Implemented
**Depends on:** None
**Affects:** Kernel Language Specification §4, §11

## Motivation

The kernel language has no anonymous product types. To group values, users must define named entities:

```
entity Pair(fst: A, snd: B)
```

This is adequate for domain-specific types where field names carry meaning (`entity Point(x: Int, y: Int)`), but verbose for transient groupings — intermediate results, multi-value returns, or generic specifications where named fields add no information.

Moreover, operation parameter lists are already named tuples in disguise:

```
operation divmod(a: Int, b: Int) -> (Int, Int)
--               ^^^^^^^^^^^^^^     ^^^^^^^^^^
--               named tuple        unnamed tuple
```

Tuple sorts make this implicit concept explicit.

## Core Idea: One Concept

There is only one construct: **named tuples**. Every tuple element has a name.

Positional syntax `(A, B, C)` is sugar for `(_1: A, _2: B, _3: C)` — elements get auto-generated positional names `_1`, `_2`, `_3`, etc. This follows Scala's approach where `Tuple2` has fields `._1` and `._2`.

This means:

- `(Int, String)` and `(_1: Int, _2: String)` are the **same sort**
- `(a: Int, b: String)` is a **different sort** (different field names)
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

**All-or-nothing naming:** either all elements have explicit names or none do (in which case `_1`, `_2`, ... are inferred). Mixing `(a: Int, String)` is not allowed.

## Desugaring

Positional tuples desugar to named tuples with `_N` names:

| Surface syntax | Desugared form |
|---|---|
| `(A, B)` | `(_1: A, _2: B)` |
| `(Int, String, Bool)` | `(_1: Int, _2: String, _3: Bool)` |
| `(?x, ?y)` | `(_1: ?x, _2: ?y)` |
| `(1, "hello")` | `(_1: 1, _2: "hello")` |
| `()` | `()` (unit, no fields) |

## Examples

### Named tuples

```
(a: Int, b: String)                     -- named pair
(x: Int, y: Int, z: Int)               -- named triple
(name: String, age: Int)               -- record-like

(a: 1, b: "hello")                     -- named tuple value
rule swap((a: ?x, b: ?y)) = (a: ?y, b: ?x)
```

### Positional tuples (sugar for `_1`, `_2`, ...)

```
(Int, String)                           -- same as (_1: Int, _2: String)
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
| `operation f(a: Int, b: String) -> R` | parameter list = `(a: Int, b: String)` |
| `entity Point(x: Int, y: Int)` | nominal wrapper around `(x: Int, y: Int)` |
| `Pair(fst: A, snd: B)` | nominal wrapper around `(fst: A, snd: B)` |

An `entity` declaration adds a **nominal** type around a named tuple — the distinction is that `entity Point(x: Int, y: Int)` creates a new sort, while `(x: Int, y: Int)` is structural:

```
(x: Int, y: Int)                        -- structural: any (x: Int, y: Int) matches
entity Point(x: Int, y: Int)            -- nominal: only Point values match
```

### Named tuples and Operation

Operation parameter lists are named tuples. This means `Operation{A, B, E}` can use a named tuple for `A`:

```
-- operation deposit(account: Account, amount: Money) -> Account
-- is an Operation{A = (account: Account, amount: Money), B = Account, E = ...}

rule apply(?op, (account: ?a, amount: ?m)) = ...
```

This preserves parameter names through the `Operation` abstraction.

## Disambiguation

Tuples use parentheses `(A, B)`. The only existing parenthesized forms are:

- `Name(args)` — function application (preceded by a name)
- `(expr)` — grouping (single element, no comma)

Neither conflicts: `Name(` is function application, `(A, B)` with a comma is a tuple, `(A)` is grouping. No lookahead needed.

Named tuples `(a: Int, b: String)` are distinguished from positional tuples by `name :` after `(`. This uses the same `name : Type` pattern as existing `field_decl` in entity/param declarations.

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
operation divmod(a: Int, b: Int) -> (Int, Int)
  requires neq(b, 0)

rule divmod(?a, ?b) = (div(?a, ?b), mod(?a, ?b))
```

### Named multi-value returns

```
operation divmod(a: Int, b: Int) -> (quotient: Int, remainder: Int)
  requires neq(b, 0)

rule divmod(?a, ?b) = (quotient: div(?a, ?b), remainder: mod(?a, ?b))
```

### Operation as first-class sort

With tuples, `Operation{A = (Int, String), B = Bool, E = ...}` naturally represents multi-argument operations:

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
operation op_e(env: Env, a: A) -> (R, Env, List{T = Event})
  effects (Error)
```

## Semantic Rules

1. There is one tuple construct: named tuples. Positional syntax is sugar for `_1`, `_2`, ... names.
2. Tuple sorts are structurally typed — identity is determined by field names and types.
3. `(A, B)` and `(_1: A, _2: B)` are the same sort.
4. `(a: Int, b: String)` and `(Int, String)` are different sorts (different names).
5. `()` is the unit sort with a single value `()`.
6. Tuple values are constructed and destructured via pattern matching.
7. All-or-nothing naming: either all elements have explicit names or none do.

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
