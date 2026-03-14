# Proposal 018: Expressions and Operation Implementation

**Status:** Draft
**Depends on:** [016-extensible-infix-operators](016-extensible-infix-operators.md)
**Related:** [002-arrow-sorts](002-arrow-sorts.md) (arrow sort `(A) -> B` syntax, not yet implemented; `Function{A, B}` from stdlib available now)
**Affects:** Kernel Language Specification §5, §8; Grammar; Reflect stdlib

## Motivation

Anthill currently describes *what* operations do (signatures, contracts, laws) but not *how* they compute. Operation bodies — the actual implementation — must be provided externally via `Implementation` facts pointing to host-language source files.

This proposal adds an **expression sublanguage** so that operations can be implemented directly in anthill, making it a programming language — not just a specification language.

The key distinction:

- **Rules** are universal properties that hold for ANY implementation. They are the spec.
- **Expression bodies** are one SPECIFIC implementation — operational, executable code.
- **`Implementation` facts** link to EXTERNAL implementations (Rust, Scala, C files).

These three coexist. An operation may have rules (spec), an expression body (anthill implementation), an external `Implementation` (host-language code), or any combination.

## Expression Syntax

### Operation Bodies

An operation may have an expression body after its signature and clauses:

```anthill
sort List{T = ?}
  entity nil
  entity cons(head: T, tail: List{T})

  operation length(l: List{T}) -> Int
    match l
      nil -> 0
      cons(_, tail) -> 1 + length(tail)
    end
  end

  operation append(l1: List{T}, l2: List{T}) -> List{T}
    match l1
      nil -> l2
      cons(h, t) -> cons(h, append(t, l2))
    end
  end

  operation map(f: (T) -> U, l: List{T}) -> List{U}
    match l
      nil -> nil
      cons(h, t) ->
        let mh = f(h)
        let mt = map(f, t)
        cons(mh, mt)
    end
  end
end
```

The body is the last part of the operation declaration, after any `requires`/`ensures`/`effects` clauses. The body is an expression; the last expression in a block is the return value.

### Expression Forms

#### Match

Pattern matching on entity constructors:

```anthill
match expr
  pattern1 -> body1
  pattern2 -> body2
end
```

With guards:

```anthill
match expr
  cons(h, t) | gt(h, 0) -> cons(h, filter_positive(t))
  cons(_, t) -> filter_positive(t)
  nil -> nil
end
```

#### If-then-else

```anthill
if cond then expr1 else expr2
```

Desugars to match on Bool. Nested:

```anthill
if gt(x, 0) then
  x
else if eq(x, 0) then
  0
else
  neg(x)
```

#### Let bindings

Block-sequential — no `in` keyword, the last expression is the result:

```anthill
let x = f(a)
let y = g(x)
add(x, y)
```

Scope: each `let` binding is visible in all subsequent expressions within the same block.

#### Lambda

```anthill
lambda x -> x
lambda x y -> add(x, y)
```

With type annotations (parenthesized per param):

```anthill
lambda (x: Int) (y: Int) -> add(x, y)
```

Without type annotations, parameter types are logical variables (`?`) — inferred from context.

Lambda expressions inherit the enclosing scope's `requires` constraints. A lambda inside an operation on `sort Polynom{R = ?} requires Ring{T = R}` can call `Ring.add` without declaring its own constraints.

#### Function application

```anthill
length(my_list)
add(a: x, b: y)       -- named arguments
f(x)                   -- apply arrow-sorted value (proposal 002)
```

Named and positional arguments follow existing operation call conventions.

#### Constructor application

```anthill
cons(head: x, tail: xs)
nil
some(42)
none
```

Constructors (entity names) are used directly.

#### Variable reference

```anthill
x          -- refers to a let-bound or parameter name
```

#### Literals

```anthill
42         -- Int
3.14       -- Float
"hello"    -- String
true       -- Bool
```

### Infix Operators in Expressions

Infix operators are syntax sugar for operation calls, as defined by proposal 016:

```anthill
x + y              -- add(x, y)
x * y + z          -- add(mul(x, y), z)
a == b             -- eq(a, b)
!valid(x) | x > 0  -- or(not(valid(x)), gt(x, 0))
```

No special expression form needed — the parser produces flat operator chains and the Pratt resolver (proposal 016) desugars them to `apply` nodes.

### Complete Example: Polymorphic Operations

```anthill
sort Polynom{R = ?}
  requires Ring{T = R}

  entity polynom(coefficients: List{T = R})

  operation add(p1: Polynom{R}, p2: Polynom{R}) -> Polynom{R}
    let cs = zip_with(lambda a b -> Ring.add(a, b),
                      coefficients(p1),
                      coefficients(p2))
    polynom(coefficients: cs)
  end

  operation evaluate(p: Polynom{R}, x: R) -> R
    fold(lambda acc c -> Ring.add(Ring.mul(acc, x), c),
         Ring.zero,
         coefficients(p))
  end
end
```

Here `Ring.add`, `Ring.mul`, `Ring.zero` resolve through the `requires Ring{T = R}` constraint. The concrete dispatch target is determined at instantiation time (when `R` is bound to a specific sort).

## Reflect Representation

Expressions are represented as terms in the KB via sorts in `anthill.reflect`.

### Expr Sort

```anthill
sort Expr
  entity match_expr(scrutinee: Expr, branches: List{T = MatchBranch})
  entity if_expr(cond: Expr, then_branch: Expr, else_branch: Expr)
  entity let_expr(name: Symbol, value: Expr, body: Expr)
  entity lambda(params: List{T = LambdaParam}, body: Expr)
  entity apply(fn: Symbol, args: List{T = ApplyArg})
  entity constructor(name: Symbol, args: List{T = ApplyArg})
  entity var_ref(name: Symbol)
  entity literal(value: Term)
end

entity MatchBranch(
  pattern: Term,
  guard: Option{T = Expr},
  body: Expr
)

entity LambdaParam(
  name: Symbol,
  type_ann: Option{T = Term}
)

entity ApplyArg(
  name: Option{T = Symbol},
  value: Expr
)
```

### TypedExpr Sort

Type checking transforms `Expr` to `TypedExpr`:

```anthill
sort TypedExpr
  entity typed(expr: Expr, type: Term)
end
```

Typing is an operation — a pure transformation from `Expr` to `TypedExpr`:

```anthill
operation typecheck(expr: Expr, scope: Scope) -> TypedExpr
```

Phase distinction is enforced by the sort system: you cannot pass an unchecked `Expr` where a `TypedExpr` is expected.

### OperationImpl Entity

Links an operation to its anthill expression body:

```anthill
entity OperationImpl(
  operation: Symbol,
  params: List{T = Symbol},
  body: Expr
)
```

The loader converts expression syntax in operation declarations to `OperationImpl` facts in the KB.

## Resolution Order

When the system needs to execute an operation:

1. **External implementation**: `Implementation{target: op, language: current_target}` — delegate to host-language code via toolchain
2. **Anthill implementation**: `OperationImpl{operation: op}` — evaluate the `Expr` tree via `Runtime`
3. **Neither** — operation is abstract (only spec, no implementation)

For code generation, external `Implementation` takes priority. For the anthill runtime (interpreter/evaluator), `OperationImpl` is primary. Both are facts in the KB, both queryable.

## Relationship to Rules

Rules and expression bodies serve different purposes:

```anthill
sort List{T = ?}
  -- Rule: universal property, any implementation must satisfy this
  rule length(nil) :- 0

  -- Expression body: one specific implementation
  operation length(l: List{T}) -> Int
    match l
      nil -> 0
      cons(_, tail) -> 1 + length(tail)
    end
  end
end
```

The rule `length(nil) :- 0` is a **specification** — it states a property that must hold. The expression body is an **implementation** — it says how to compute the result. The kernel can verify that the implementation satisfies the rule, but they are separate concerns.

## Grammar Changes

### Operation body

Add an optional expression body to `operation_declaration` and `operation_entry`:

```js
operation_declaration: $ => seq(
  repeat(field('description', $.description_block)),
  optional($.visibility),
  'operation',
  field('name', $.name),
  '(',
  optional(commaSep1($.param)),
  ')',
  '->',
  field('return_type', $._type),
  repeat($.operation_clause),
  optional(field('body', $.expr_body)),    // <-- new
  optional($.meta_block),
),
```

### Expression grammar

```js
expr_body: $ => choice(
  $.match_expr,
  $.if_expr,
  $.let_chain,
  $._simple_expr,
),

match_expr: $ => seq(
  'match', field('scrutinee', $._simple_expr),
  repeat1($.match_branch),
  'end',
),

match_branch: $ => seq(
  field('pattern', $._pattern),
  optional(seq('|', field('guard', $._simple_expr))),
  '->',
  field('body', $.expr_body),
),

if_expr: $ => seq(
  'if', field('condition', $._simple_expr),
  'then', field('then', $.expr_body),
  'else', field('else', $.expr_body),
),

let_chain: $ => seq(
  repeat1($.let_binding),
  field('result', $._simple_expr),
),

let_binding: $ => seq(
  'let', field('name', $.identifier),
  '=', field('value', $.expr_body),
),

lambda_expr: $ => seq(
  'lambda',
  repeat1($.lambda_param),
  '->',
  field('body', $.expr_body),
),

lambda_param: $ => choice(
  $.identifier,                                         // untyped: x
  seq('(', $.identifier, ':', $._type, ')'),            // typed: (x: Int)
),

// Simple expressions: applications, constructors, variables, literals, lambdas
_simple_expr: $ => choice(
  $.call_expr,
  $.lambda_expr,
  $.variable_ref,
  $.literal,
  seq('(', $.expr_body, ')'),             // grouping
),

call_expr: $ => seq(
  field('function', $.name),
  '(', optional(commaSep1($.call_arg)), ')',
),

call_arg: $ => choice(
  seq(field('name', $.identifier), ':', field('value', $.expr_body)),  // named
  field('value', $.expr_body),                                         // positional
),
```

## Evaluation Pipeline

```
source text
  → parse (tree-sitter)
  → Expr (untyped expression tree)
  → typecheck
  → TypedExpr (typed expression tree)
  → evaluate (Runtime) or codegen (LanguageMapping)
```

Each phase has its own sort. The sorts enforce that you cannot skip type checking.

## Open Questions

1. **Effects in expressions.** When an operation has `effects (Modifies(store))`, how do expression bodies handle effectful operations? This likely needs a sequencing mechanism (monadic do-notation or effect handlers). Deferred to a future proposal.

2. **Recursion.** The examples above use direct recursion (`length` calls `length`). Should there be a totality checker to ensure termination? For now, no restriction — the runtime allows general recursion.

3. **Pattern exhaustiveness.** Should the type checker verify that `match` branches cover all constructors of the scrutinee's sort? Desirable but not required for the initial implementation.

4. **Mutual recursion.** Operations within the same sort can call each other. Cross-sort mutual recursion needs consideration.

## Implementation Plan

### Phase 1: Grammar and Parse IR

Add expression syntax to `grammar.js`. Extend the parse IR (`ParsedFile`) with expression nodes. Run `tree-sitter test` with new test cases.

### Phase 2: Expr Sort in Reflect

Add `Expr`, `TypedExpr`, `MatchBranch`, `LambdaParam`, `ApplyArg`, `OperationImpl` to `stdlib/anthill/reflect/`.

### Phase 3: Loader

Extend the loader to convert parsed expression trees into `Expr` terms and emit `OperationImpl` facts into the KB.

### Phase 4: Type Checker

Implement `Expr → TypedExpr` transformation with sort inference and constraint resolution.

### Phase 5: Evaluator

Extend `Runtime.evaluate` to handle `TypedExpr` trees — pattern matching, let scoping, lambda closures, operation dispatch (including dispatch through spec constraints).
