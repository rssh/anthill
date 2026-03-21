# Proposal 018: Expressions and Operation Implementation

**Status:** Draft
**Depends on:** [016-extensible-infix-operators](016-extensible-infix-operators.md), [022-typing-as-facts](022-typing-as-facts.md) (Occurrences, TypeOf)
**Related:** [002-arrow-sorts](002-arrow-sorts.md) (arrow sort `(A) -> B` syntax, not yet implemented; `Function[A, B]` from stdlib available now)
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
sort List[T = ?]
  entity nil
  entity cons(head: T, tail: List[T])

  operation length(l: List[T]) -> Int
    match l
      nil -> 0
      cons(_, tail) -> 1 + length(tail)
    end
  end

  operation append(l1: List[T], l2: List[T]) -> List[T]
    match l1
      nil -> l2
      cons(h, t) -> cons(h, append(t, l2))
    end
  end

  operation map(f: (T) -> U, l: List[T]) -> List[U]
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
  cons(h, t) | h > 0 -> cons(h, filter_positive(t))
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
if x > 0 then
  x
else if x = 0 then
  0
else
  -x
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

Lambda always takes **one** argument. Multiple parameters use tuple destructuring:

```anthill
lambda x -> x                              -- single param
lambda (a, b) -> add(a, b)                 -- tuple destructuring
lambda (acc: A, elem: B) -> add(acc, elem) -- named tuple with type annotations
```

This avoids comma ambiguity when lambdas are used as function arguments — the tuple parens naturally delimit the parameter pattern:

```anthill
map(lambda x -> x + 1, my_list)
fold(lambda (acc, x) -> add(acc, x), zero, my_list)
zip_with(lambda (a, b) -> Ring.add(a, b), xs, ys)
```

Without type annotations, parameter types are logical variables (`?`) — inferred from context.

Lambda expressions inherit the enclosing scope's `requires` constraints. A lambda inside an operation on a sort with `requires Ring[R]` can call `Ring.add` without declaring its own constraints.

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
sort Polynom
  sort R = ?
  requires Ring[R]

  entity polynom(coefficients: List[R])

  operation add(p1: Polynom[R], p2: Polynom[R]) -> Polynom[R]
    let cs = zip_with(lambda (a, b) -> a + b,
                      coefficients(p1),
                      coefficients(p2))
    polynom(coefficients: cs)
  end

  operation evaluate(p: Polynom[R], x: R) -> R
    fold(lambda (acc, c) -> acc * x + c,
         Ring.zero,
         coefficients(p))
  end
end
```

Here `Ring.add`, `Ring.mul`, `Ring.zero` resolve through the `requires Ring[T = R]` constraint. The concrete dispatch target is determined at instantiation time (when `R` is bound to a specific sort).

## Reflect Representation

Expressions are represented as ExprOccurrences in the KB (see [Proposal 022](022-typing-as-facts.md) for the Occurrence/ExprOccurrence concept). Each expression node is an ExprOccurrence — it has a unique OccurrenceId, a hash-consed TermId (for structural pattern matching), a Span (source position), and an owner (the containing declaration — operation, rule, or fact). Children are referenced by ExprOccurrence, enabling tree navigation with position tracking.

Expr entities are stored in the OccurrenceStore and queried via builtins (not as regular KB facts). This keeps the fact base lean while making expressions fully queryable from anthill rules.

### Expr Sort

```anthill
sort Expr
  entity match_expr(scrutinee: ExprOccurrence, branches: List[T = MatchBranch])
  entity if_expr(cond: ExprOccurrence, then_branch: ExprOccurrence, else_branch: ExprOccurrence)
  entity let_expr(pattern: Pattern, value: ExprOccurrence, body: ExprOccurrence)
  entity lambda(param: Pattern, body: ExprOccurrence)
  entity apply(fn: Symbol, args: List[T = ApplyArg])
  entity constructor(name: Symbol, args: List[T = ApplyArg])
  entity var_ref(name: Symbol)        -- lexical variable: x, acc
  entity int_lit(value: Int)
  entity float_lit(value: Float)
  entity string_lit(value: String)
  entity bool_lit(value: Bool)
end

entity MatchBranch(
  pattern: Pattern,
  guard: Option[T = ExprOccurrence],
  body: ExprOccurrence
)

entity ApplyArg(
  name: Option[T = Symbol],
  value: ExprOccurrence
)

sort Pattern
  entity var_pattern(name: Symbol, type_ann: Option[T = Term])
  entity tuple_pattern(elements: List[T = Pattern])
  entity named_tuple_pattern(fields: List[T = NamedPattern])
  entity constructor_pattern(name: Symbol, args: List[T = Pattern])
  entity literal_pattern(value: Term)
  entity wildcard
end

entity NamedPattern(
  name: Symbol,
  pattern: Pattern
)
```

### Logical Variables in Expressions

Logical variables (`?x`) can appear anywhere in an expression. Since expressions are terms in the KB, and terms support logical variables and substitution, this requires no special mechanism — it already works the same way as in rules.

```anthill
-- ?x in a rule (already works):
rule length(nil) :- 0

-- ?T in an expression (works the same way — expressions are terms):
rule gen_add(?T) :- Ring[?T],
  OperationImpl[
    operation: add,
    body: lambda (a, b) -> apply(Ring.add, a, b)
  ]
```

Two kinds of variables in expressions:

- **`x`** — lexical variable, bound by `let`, `lambda`, or `match`. Resolved by the evaluator via scope lookup.
- **`?x`** — logical variable, bound by KB unification/substitution. Resolved by the standard term substitution machinery before evaluation.

An expression containing unbound `?variables` is a **template** — a partially specified computation. When all logical variables are grounded through substitution, the expression becomes fully concrete and evaluable. This is anthill's equivalent of quasi-quotation in Lisp or splicing in Template Haskell/Scala 3 macros, but with no special syntax — just the standard `?` prefix that already works in rules.

### Typing: TypeOf facts over Occurrences (Proposal 022)

Typing is no longer a transformation from `Expr` to a separate `TypedExpr`. Instead, the typing pass emits `TypeOf(occ, type)` facts for each expression occurrence. The expression itself stays unchanged — types are external annotations.

```anthill
sort TypeOf {
    entity TypeOf(occ: ExprOccurrence, type: Sort)
}
```

This means:
- **No TypedExpr sort** — replaced by TypeOf facts
- **No `typecheck(Expr) -> TypedExpr` operation** — the typing pass walks occurrence trees and emits facts
- **Gradual typing** — some occurrences may be typed, others not yet
- **Types are queryable** — `TypeOf(occ: ?occ, type: ?type)` is a regular KB query
- **Errors carry positions** — TypeOf references ExprOccurrences, which have Spans
- **Owner provides context** — the occurrence's owner links to the containing operation/rule/fact, giving the typing pass its top-down context (expected return type, parameter types, etc.)

See [Proposal 022](022-typing-as-facts.md) for details on bidirectional type propagation, type-directed desugaring, and constraint-based error reporting.

The evaluation pipeline:

```
source text
  → parse (tree-sitter) → ExprOccurrence tree (expressions with positions + owners)
  → substitution (KB unification grounds ?variables)
  → typing pass → TypeOf facts emitted into KB
  → constraint checking (type_mismatch fires on errors)
  → evaluate (Runtime) or codegen (LanguageMapping)
```

Phase distinction: an operation can only be evaluated when all its ExprOccurrences have TypeOf facts and no type_mismatch constraints fire.

### OperationImpl Entity

Links an operation to its anthill expression body:

```anthill
entity OperationImpl(
  operation: Symbol,
  params: List[T = Symbol],
  body: ExprOccurrence
)
```

The `body` is an ExprOccurrence (root of the expression tree in the OccurrenceStore, owned by this operation). The loader converts expression syntax in operation declarations to `OperationImpl` facts in the KB.

## Resolution Order

When the system needs to execute an operation:

1. **External implementation**: `Implementation[target: op, language: current_target]` — delegate to host-language code via toolchain
2. **Ensures sort**: a sort with `ensures Spec[Type]` that provides a body for the operation
3. **Default implementation**: operation body in the spec sort itself
4. **Neither** — operation is abstract (only spec, no implementation)

For code generation, external `Implementation` takes priority. For the anthill runtime (interpreter/evaluator), `ensures` sorts and defaults are primary. All are facts in the KB, all queryable.

## Relationship to Rules

Rules and expression bodies serve different purposes:

```anthill
sort List[T = ?]
  -- Rule: universal property, any implementation must satisfy this
  rule length(nil) :- 0

  -- Expression body: one specific implementation
  operation length(l: List[T]) -> Int
    match l
      nil -> 0
      cons(_, tail) -> 1 + length(tail)
    end
  end
end
```

The rule `length(nil) :- 0` is a **specification** — it states a property that must hold. The expression body is an **implementation** — it says how to compute the result. The kernel can verify that the implementation satisfies the rule, but they are separate concerns.

## Implementation Sorts

A sort can separate its **specification** (operation signatures, laws) from its **implementation** (operation bodies). The spec sort defines *what*; the implementation sort provides *how*. These can live in different files — like C++ headers vs source files, or Rust traits vs impls.

### Spec/Implementation File Separation

```
stdlib/algebra/ring.anthill        -- spec: sort Ring with operations and laws
stdlib/algebra/int_ring.anthill    -- impl: sort IntRing ensures Ring[Int]
stdlib/algebra/float_ring.anthill  -- impl: sort FloatRing ensures Ring[Float]
generated/matrix_ring.anthill      -- auto-generated implementation
```

The spec file defines the interface. Implementation files import the spec and provide bodies. Multiple implementation files can coexist — for different types, profiles, or generated vs hand-written code. The loader processes all files and connects `ensures` sorts to their specs via the KB.

This enables three workflows:

1. **Hand-written implementation** — developer writes both spec and impl files
2. **Auto-generated implementation** — codegen reads the spec from KB, produces impl file with expression bodies
3. **Host-language implementation** — external `Implementation` fact points to a Rust/Scala/C file; no anthill impl file needed

### `ensures` — the dual of `requires`

- `requires Ring[R]` — "I depend on Ring for R" (consumer)
- `ensures Ring[Int]` — "I provide Ring for Int" (implementor)

```anthill
-- Spec sort (ring.anthill): defines the interface
sort Ring
  sort T = ?

  -- Abstract operations (no body) — must be provided by implementors
  operation add(a: T, b: T) -> T
  operation mul(a: T, b: T) -> T
  operation neg(a: T) -> T
  operation zero() -> T
  operation one() -> T

  -- Default operations (have body) — inherited unless overridden
  operation sub(a: T, b: T) -> T
    add(a, neg(b))
  end

  operation square(a: T) -> T
    mul(a, a)
  end

  -- Laws (hold for all implementations)
  rule ?a + zero = ?a
  rule ?a + neg(?a) = zero
  rule ?a + ?b = ?b + ?a
  rule (?a + ?b) * ?c = ?a * ?c + ?b * ?c
end
```

```anthill
-- Implementation sort (int_ring.anthill): provides the bodies
sort IntRing
  ensures Ring[Int]

  -- Required: provide all abstract operations
  operation add(a: Int, b: Int) -> Int
    a + b
  end

  operation mul(a: Int, b: Int) -> Int
    a * b
  end

  operation neg(a: Int) -> Int
    -a
  end

  operation zero() -> Int
    0
  end

  operation one() -> Int
    1
  end

  -- sub and square are inherited from Ring's defaults
  -- (can be overridden here if a more efficient version is needed)
end
```

### Abstract vs Default vs Concrete

The presence or absence of a body determines the operation's status:

- **No body in spec sort** → abstract, `ensures` sort MUST provide it
- **Body in spec sort** → default, `ensures` sort inherits it (can override)
- **Body in `ensures` sort** → concrete implementation (or override of default)

This follows the same convention as Rust traits and Haskell typeclasses — no new keywords needed beyond `ensures`.

### Multiple Implementations

Different sorts can provide different implementations for different types or profiles:

```anthill
sort IntRing
  ensures Ring[Int]
  -- ... Int operations using native arithmetic
end

sort FloatRing
  ensures Ring[Float]
  -- ... Float operations using floating-point arithmetic
end

sort MatrixRing
  ensures Ring[Matrix]
  -- ... Matrix operations using linear algebra
end
```

Each `ensures` sort is a named entity in the KB — queryable, reflectable, selectable by profile.

### Non-Coherent Implementations (Multiple for Same Type)

A spec may have multiple valid implementations for the same type. Classic example: `Monoid[Int]` — both `(+, 0)` and `(*, 1)` are valid monoids.

```anthill
sort IntAddMonoid
  ensures Monoid[Int]
  operation combine(a: Int, b: Int) -> Int
    a + b
  end
  operation identity() -> Int
    0
  end
end

sort IntMulMonoid
  ensures Monoid[Int]
  operation combine(a: Int, b: Int) -> Int
    a * b
  end
  operation identity() -> Int
    1
  end
end
```

**Selection** uses the named implementation sort in `requires`:

```anthill
-- Unambiguous: require the specific implementation, not the abstract spec
sort SumReducer
  requires IntAddMonoid    -- brings additive Monoid[Int] into scope
end

sort ProductReducer
  requires IntMulMonoid    -- brings multiplicative Monoid[Int] into scope
end
```

Since `IntAddMonoid` ensures `Monoid[Int]`, requiring `IntAddMonoid` transitively provides all `Monoid` operations — with the additive implementation.

**Conflicting implementations in the same scope** — qualify by name:

```anthill
sort BothMonoids
  requires IntAddMonoid
  requires IntMulMonoid

  operation sum_and_product(a: Int, b: Int) -> (Int, Int)
    (IntAddMonoid.combine(a, b), IntMulMonoid.combine(a, b))
  end
end
```

`IntAddMonoid.combine` and `IntMulMonoid.combine` are distinct qualified names. Standard dotted name resolution handles disambiguation — no new syntax needed.

### Relationship to External Implementations

An `ensures` sort provides anthill expression bodies. For host-language implementations, use `Implementation` facts as before:

```anthill
-- Anthill implementation (expression bodies)
sort IntRing
  ensures Ring[Int]
  operation add(a: Int, b: Int) -> Int
    a + b
  end
end

-- External implementation (host-language file)
fact Implementation{
  target: "Ring",
  artifact: "src/ring_simd.rs",
  language: "rust",
  profile: "simd",
  carrier: [CarrierBinding("T", "f64")]
}
```

Both are valid implementation strategies. The resolution order (§Resolution Order above) determines which takes priority.

### Grammar

`ensures` is a sort-level clause, syntactically parallel to `requires`:

```
EnsuresDecl ::= 'ensures' Type
```

The type expression is a parameterized sort reference: `Ring[Int]`, `Functor[List]`, etc. The `ensures` sort must provide bodies for all abstract operations of the referenced spec.

## Proof Obligations

When an `ensures` sort provides an implementation, the kernel generates **proof obligations** — one for each law (rule) in the spec. These are `Obligation` facts in the KB (defined in `stdlib/anthill/realization/`).

### Proofs are terms

In anthill, `rule head :- body` already has proof semantics: "head holds because body holds." A proof obligation is a term; discharging it is providing a rule that derives it:

```anthill
sort IntRing
  ensures Ring[Int]

  operation add(a: Int, b: Int) -> Int
    a + b
  end

  -- Kernel generates obligation: prove add(?a, zero) = ?a
  -- Discharged by rule:
  rule add(?a, zero) :- ?a + 0, ?a
end
```

The `:-` IS the proof justification. This requires no new syntax — rules are already the proof language.

### Discharge mechanisms

Proof obligations can be discharged by:

1. **Abstract interpretation** — mechanical symbolic evaluation. The kernel evaluates `add(a, zero)` using the body `a + 0`, simplifies to `a`. Automatic for arithmetic identities and simple structural cases.

2. **KB resolution** — the obligation is a query. If the KB's existing rules/facts can derive it, it's discharged automatically.

3. **Explicit rules** — the user writes a rule in the `ensures` sort that derives the obligation. The `:-` body is the proof.

4. **Context propagation** — `if`/`match` guards and prior `let` bindings provide knowledge at call sites for precondition discharge.

5. **External proofs** — reference a proof artifact (Lean, Coq, SMT solver output):
```anthill
sort IntRing
  ensures Ring[Int]
  -- ...
end [proofs: "proofs/int_ring.lean"]
```

6. **Trust annotations** — mark as trusted with evidence level:
```anthill
sort IntRing
  ensures Ring[Int]
  -- ...
end [trust: tested-1000]
```

### Preconditions at call sites

When an operation has `requires`, each call site generates an obligation:

```anthill
operation divide(a: Int, b: Int) -> Int
  requires b != 0

-- Call site obligation: prove y != 0
if y != 0 then
  divide(x, y)     -- discharged by if-guard context
else
  0
end
```

### Postcondition propagation

After calling an operation with `ensures`, postconditions become available facts:

```anthill
operation abs(x: Int) -> Int
  ensures result >= 0

let y = abs(x)
-- y >= 0 is now known in scope
divide(1, y + 1)   -- precondition y + 1 != 0 discharged: y >= 0 implies y + 1 > 0
```

### Minimal Proof Interface

A proof obligation is a term. Discharging it produces a `ProofResult`:

```anthill
sort ProofResult
  entity proved(obligation: Term, method: ProofMethod)
  entity failed(obligation: Term, reason: String)
  entity pending(obligation: Term)
end

sort ProofMethod
  entity by_resolution                                -- KB resolution reduced to true
  entity by_simplification                            -- abstract interpretation / rewriting
  entity by_tool(name: String, artifact: String)      -- external prover (Lean, SMT, etc.)
  entity by_trust(level: TrustLevel)                  -- manual annotation
end
```

**Internal proof = query.** An obligation `P` is discharged if `?- P` succeeds in the KB. This is standard backward chaining — the existing `kb::resolve` machinery handles it:

```anthill
-- Obligation: add(?a, zero) = ?a
-- KB has rule: rule ?a + zero = ?a
-- Resolution: ?- add(?a, zero) = ?a → succeeds
-- Result: proved(add(?a, zero) = ?a, by_resolution)
```

No new proof engine needed for the basic case — internal proof IS just a query.

**External proof = tool call.** For obligations that can't be discharged internally, delegate to an external prover and record the result:

```anthill
-- Obligation too complex for KB resolution
-- Delegate to Lean:
fact ProofResult{
  proved(
    distributivity(Ring, Int),
    by_tool("lean", "proofs/int_ring.lean")
  )
}
```

The proof check operation:

```anthill
operation check_obligation(obligation: Term, kb: KB) -> ProofResult
  -- 1. Try KB resolution: ?- obligation → if succeeds, proved(by_resolution)
  -- 2. Try simplification: rewrite using rules → if reduces to true, proved(by_simplification)
  -- 3. Check for existing ProofResult fact (external proof already recorded)
  -- 4. Otherwise: pending(obligation)
end
```

### Obligation Lifecycle

```
ensures Ring[Int]
  → kernel generates Obligation facts (status: Pending)
  → check_obligation tries internal discharge (resolution, simplification)
  → externally proved obligations recorded as ProofResult facts
  → remaining Pending obligations surface to user
  → user provides rules (proofs), external evidence, or trust annotations
  → all proved → implementation is verified
  → any failed → error, implementation does not satisfy spec
```

Detailed proof block syntax and integration with specific external provers is deferred to a future proposal.

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
  field('param', $._pattern),
  '->',
  field('body', $.expr_body),
),

// Patterns (shared by lambda, match branches)
_pattern: $ => choice(
  $.identifier,                                         // variable: x
  '_',                                                  // wildcard
  $.literal,                                            // literal: 42, "hello"
  $.tuple_pattern,                                      // (a, b) or (a: Int, b: Int)
  $.constructor_pattern,                                // cons(h, t)
),

tuple_pattern: $ => seq(
  '(', commaSep1($._pattern_arg), ')',
),

_pattern_arg: $ => choice(
  $._pattern,                                           // positional: a
  seq($.identifier, ':', $._type),                      // typed: a: Int
),

constructor_pattern: $ => seq(
  $.name, '(', optional(commaSep1($._pattern)), ')',
),

// Simple expressions: applications, constructors, variables, literals, lambdas
_simple_expr: $ => choice(
  $.call_expr,
  $.lambda_expr,
  $.variable_ref,                         // lexical: x, acc
  $.variable_term,                        // logical: ?x, ?T (resolved by substitution)
  $.int_literal,
  $.float_literal,
  $.string_literal,
  $.boolean_literal,
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
  → parse (tree-sitter) → ExprOccurrence tree (Expr nodes with OccurrenceIds + Spans + owners)
  → substitution (KB unification grounds ?variables)
  → typing pass → TypeOf(occ, type) facts emitted into KB
  → constraint checking (type_mismatch fires on errors)
  → evaluate (Runtime) or codegen (LanguageMapping)
```

Expressions are ExprOccurrence trees, not separate Expr terms. Each occurrence knows its owner (the operation/rule/fact it belongs to), providing typing context. Typing produces TypeOf facts per occurrence — no intermediate TypedExpr. Logical variables (`?x`) are resolved before typing — they are part of the term layer, not the expression layer. See [Proposal 022](022-typing-as-facts.md) for the full typing design.

## Open Questions

1. **Effects in expressions.** When an operation has `effects (Modifies(store))`, how do expression bodies handle effectful operations? This likely needs a sequencing mechanism (monadic do-notation or effect handlers). Deferred to a future proposal.

2. **Recursion.** The examples above use direct recursion (`length` calls `length`). Should there be a totality checker to ensure termination? For now, no restriction — the runtime allows general recursion.

3. **Pattern exhaustiveness.** Should the type checker verify that `match` branches cover all constructors of the scrutinee's sort? Desirable but not required for the initial implementation.

4. **Mutual recursion.** Operations within the same sort can call each other. Cross-sort mutual recursion needs consideration.

## Implementation Plan

### Phase 1: Grammar and Parse IR

Add expression syntax to `grammar.js`. Extend the parse IR (`ParsedFile`) with expression nodes. Run `tree-sitter test` with new test cases.

### Phase 2: Expr Sort in Reflect

Add `Expr`, `Pattern`, `MatchBranch`, `ApplyArg`, `OperationImpl` to `stdlib/anthill/reflect/`. Add `Occurrence`, `Span`, `TypeOf` sorts (Proposal 022). Remove `TypedExpr`.

### Phase 3: Loader + OccurrenceStore

Extend the loader to create Occurrence trees from parsed expressions and emit `OperationImpl` facts into the KB. Implement `OccurrenceStore` (Proposal 022).

### Phase 4: Typing Pass (Proposal 022)

Implement the typing pass: walk expression occurrence trees, emit `TypeOf(occ, type)` facts, run constraint checking for type errors.

### Phase 5: Evaluator

Extend `Runtime.evaluate` to handle expression occurrence trees with TypeOf facts — pattern matching, let scoping, lambda closures, operation dispatch (including dispatch through spec constraints).
