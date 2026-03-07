# 016: Extensible Operators

## Status: Proposal

## Depends on: 014 (Union Types)

## Motivation

Anthill currently has 8 hardcoded infix operators (`=`, `>`, `>=`, `<`, `<=`, `+`, `-`, `*`) that are desugared to named functors at parse time. The operator set and the symbol-to-functor mapping are both fixed in the grammar and converter.

This is limiting in two ways:

1. **New operators require grammar changes.** Adding `|` for union types (proposal 014) or `&` for intersection types means editing `grammar.js` and `convert_infix` each time.

2. **Operators can't work across contexts.** The `|` symbol should mean union in type position (`field: Int | String`) and logical disjunction in term position (`a | b`). Currently, infix operators exist only in `_term` — there's no infix support in `_type`.

## Design

### Principle: Flat Parse, Desugar in Resolver

Parsers (tree-sitter, Scala, etc.) produce a **flat infix chain** — a sequence of operands and operator tokens with no precedence structure. The **resolver** (in the converter or a later phase) restructures the chain into nested `Term::Fn` calls using a single **operator dictionary**.

```
Source:          a + b * c + d
Parse IR:        InfixChain [a, "+", b, "*", c, "+", d]
After resolve:   add(add(a, mul(b, c)), d)
```

This separates concerns cleanly:

- **Parsers** only need to recognize operator tokens — no precedence encoding
- **The dictionary** is the single source of truth for precedence, associativity, and default functor
- **The resolver** applies Pratt's algorithm over the flat chain, reading from the dictionary
- **Context** (type vs term position) determines which desugaring target to use

### The Operator Dictionary

One canonical dictionary mapping operator patterns to their properties. This is the language spec for operators — all tools read from it. Each entry is a **pattern** where `_` marks argument positions.

#### Pattern language

Each entry is a **pattern** where:
- **`_`** — an argument slot (parsed as a Pratt sub-expression)
- **`_,..`** — a repeated argument slot (zero or more `_` separated by a delimiter)
- **keywords/tokens** — literal tokens that must match

These two slot types plus literal tokens cover everything: prefix, infix, ternary, binding, control flow, and variable-length sequences.

#### Arithmetic & logical operators

**Prefix operators** (nud — no left operand):

| Pattern | Level | Functor | Category |
|---------|-------|---------|----------|
| `! _` | 9 | `not` | logical negation |
| `- _` | 9 | `neg` | arithmetic negation |

**Infix operators** (led — left and right operand):

| Pattern | Level | Assoc | Term functor | Type meaning | Category |
|---------|-------|-------|--------------|--------------|----------|
| `_ \| _` | 1 | left | `or` | `SortUnion` | disjunction / union |
| `_ & _` | 2 | left | `and` | `SortIntersection` | conjunction / intersection |
| `_ = _` | 3 | none | `eq` | — | equality |
| `_ != _` | 3 | none | `neq` | — | equality |
| `_ < _` | 4 | none | `lt` | — | comparison |
| `_ <= _` | 4 | none | `lte` | — | comparison |
| `_ > _` | 4 | none | `gt` | — | comparison |
| `_ >= _` | 4 | none | `gte` | — | comparison |
| `_ + _` | 5 | left | `add` | — | additive |
| `_ - _` | 5 | left | `sub` | — | additive |
| `_ * _` | 6 | left | `mul` | — | multiplicative |
| `_ / _` | 6 | left | `div` | — | multiplicative |
| `_ % _` | 6 | left | `mod` | — | multiplicative |
| `_ ^ _` | 7 | right | `pow` | — | exponentiation |
| `_ -> _` | 8 | right | `arrow` | `FnType` | arrow (future) |

**Ternary operators** (led with continuation token):

| Pattern | Level | Assoc | Functor | Category |
|---------|-------|-------|---------|----------|
| `_ -> _ effect _` | 8 | right | `arrow_effect` | arrow with effect |
| `_ ? _ : _` | 0 | right | `cond` | conditional (future) |

#### Binding & control-flow operators

Binding constructs are prefix (nud) handlers — the keyword starts parsing with no left operand, then consumes sub-expressions and continuation tokens:

| Pattern | Level | Kind | Functor | Category |
|---------|-------|------|---------|----------|
| `\ _ -> _` | 0 | prefix | `lambda` | lambda |
| `let _ = _ in _` | 0 | prefix | `let_in` | let binding |
| `if _ then _ else _` | 0 | prefix | `cond` | conditional |
| `match _ { _ -> _,.. }` | 0 | prefix | `match` | pattern match |
| `[ _ \| _,.. ]` | 0 | prefix | `comprehension` | comprehension |

Here `_,..` denotes a repeated sub-expression with a separator (comma by default). The `match` nud handler parses the scrutinee, then enters the braces and loops parsing `pattern -> expr` arms. The `comprehension` nud handler parses the head, then the `|`, then loops parsing generators/guards.

These are still Pratt: the opening keyword/token acts as a nud, and the handler knows (from the pattern) which continuation tokens to expect and when to loop. Not all of these are needed now — they are listed to show the pattern language's expressiveness. Concrete syntax additions go through their own proposals.

#### Rules

Lower level = lower precedence (binds looser). Prefix operators bind tighter than all infix operators.

**Associativity rules:**
- `left`: `a + b + c` = `add(add(a, b), c)`
- `right`: `a -> b -> c` = `arrow(a, arrow(b, c))`
- `none`: `a = b = c` is a resolver error — use explicit grouping
- prefix: always right-binding (`!!x` = `not(not(x))`)

**Word operators:** Word tokens can serve as operators at the same level as their symbolic equivalents:

| Word | Same as | Level |
|------|---------|-------|
| `or` | `\|` | 1 |
| `and` | `&` | 2 |
| `not` | `!` | 9 (prefix) |
| `mod` | `%` | 6 |
| `div` | `/` | 6 |

**Extending:** Add a row to the dictionary. No grammar changes, no parser changes.

### Pratt Parsing and the Dictionary

The dictionary maps directly to Pratt parser concepts:

- **Simple prefix** (`! _`, `- _`) → **nud**: parse one right operand at binding power
- **Compound prefix** (`if _ then _ else _`, `let _ = _ in _`) → **nud with continuations**: parse sub-expressions interleaved with expected continuation tokens
- **Prefix with repetition** (`match _ { _ -> _,.. }`, `[ _ | _,.. ]`) → **nud with sub-loop**: parse fixed prefix, then loop over repeated elements with separator
- **Infix** (`_ + _`, `_ * _`) → **led**: left operand already parsed, parse one right operand
- **Ternary** (`_ -> _ effect _`) → **led with continuation**: like infix, but expects a continuation token and a third operand

The pattern notation is descriptive — the actual implementation is a standard Pratt loop reading precedence/associativity from the dictionary. No grammar formalism is needed.

### Parse IR: Flat Operator Chain

The parse IR stores operator expressions as flat chains — no precedence tree:

```
OpChain:
  elements: [element, element, element, ...]

element = operand          -- a term/type expression
        | operator_token   -- raw token text: "+", "!", "mod", etc.
```

Where `operator_token` is the raw token text — an unresolved string, not a symbol. Resolution happens later when the Pratt desugarer looks up the token in the dictionary.

Examples of what the parser produces:

```
a + b * c       →  [a, "+", b, "*", c]
!x + y          →  ["!", x, "+", y]
a -> B effect E →  [a, "->", B, "effect", E]
a + (b * c)     →  [a, "+", (b*c)]     -- parens already grouped
!!x             →  ["!", "!", x]
-a + b          →  ["-", a, "+", b]
```

The resolver distinguishes prefix from infix by consulting the dictionary: if a token appears where a left operand is expected but none exists, it must be a prefix operator (nud). If it appears after a left operand, it's infix (led).

### Pratt Desugaring (in Resolver)

The resolver applies Pratt's algorithm to restructure each `OpChain`:

```
desugar(chain, context, min_bp=0):
    // 1. nud phase: handle prefix or read operand
    //    - If next token is a prefix operator (e.g. "!", "-"):
    //      look up in dictionary → (level, functor)
    //      right = desugar(chain, context, level)
    //      left = Term::Fn(functor, [right])
    //    - Otherwise: left = next operand
    //
    // 2. led loop: handle infix/ternary
    //    While next token is an operator with level >= min_bp:
    //      look up in dictionary → (level, assoc, functor, continuation?)
    //      If ternary (has continuation token):
    //        middle = desugar(chain, context, 0)
    //        expect continuation token
    //        right = desugar(chain, context, level)
    //        left = Term::Fn(functor, [left, middle, right])
    //      Else (binary infix):
    //        right_bp = level + 1 if left-assoc, level if right-assoc
    //        right = desugar(chain, context, right_bp)
    //        left = Term::Fn(functor, [left, right])
    //      If `none`-associative and same-level op follows → error
    //
    // 3. Return left
```

This is ~40 lines of code. The dictionary lookup is the only configuration point.

**Context-dependent desugaring:**

In term position, the resolver uses the "Term functor" column:
```
!x       →  not(x)
-a       →  neg(a)
a | b    →  or(a, b)
a + b    →  add(a, b)
```

In type position, the resolver uses the "Type meaning" column:
```
A | B    →  TypeExpr::Union(A, B)     → SortUnion(A, B) in KB
A & B    →  TypeExpr::Intersection(A, B)  — future
A -> B   →  TypeExpr::Arrow(A, B)     — future
```

Operators without a type meaning (arithmetic, comparison, prefix) are resolver errors in type position.

### Boundary: Tree-sitter vs Pratt Dictionary

Tree-sitter and the Pratt dictionary own different concerns:

- **Tree-sitter owns delimited forms**: function calls `f(x, y)`, list literals `[a, b]`, record literals `{x: 1}`, grouping parens `(a + b)`. These have matched delimiters that tree-sitter handles structurally.
- **Pratt dictionary owns flat operator chains**: everything between already-parsed operands. Operators, binding keywords, control-flow keywords.

This means `_ ( _,.. )` as `apply` does NOT go in the dictionary — tree-sitter already parses `f(x)` as a call expression. The Pratt resolver only sees operands that tree-sitter has already structured. For `f(x) + g(y)`, tree-sitter produces:

```
infix_expr:
  left:  call_expr(f, [x])    -- tree-sitter structured this
  op:    +
  right: call_expr(g, [y])    -- tree-sitter structured this
```

The Pratt resolver sees `[call(f,x), "+", call(g,y)]` and produces `add(call(f,x), call(g,y))`.

Similarly, `[a, b, c]` is a list literal parsed by tree-sitter, not a dictionary pattern. But `[x | x <- xs, x > 0]` (comprehension) could be a dictionary pattern IF tree-sitter leaves it flat — or tree-sitter could parse the delimiters and the Pratt resolver handles the interior.

### Parser Implementations

Since parsers only produce flat chains between already-structured operands:

**Tree-sitter** (CST for editor tooling):

```js
// Prefix operators
prefix_expr: $ => seq($._prefix_op, $._term),

_prefix_op: $ => choice('!', '-', 'not'),

// Infix/ternary — all operators at one flat level, no precedence
infix_expr: $ => prec.left(1, seq(
    $._term,
    repeat1(seq($._infix_op, $._term))
)),

_infix_op: $ => choice(
    '|', '&', '=', '!=', '<', '<=', '>', '>=',
    '+', '-', '*', '/', '%', '^', '->',
    'or', 'and', 'mod', 'div', 'effect',
    '?', ':'
),

// Binding/control — tree-sitter recognizes the keyword structure,
// Pratt resolver handles precedence of sub-expressions
if_expr: $ => seq('if', $._term, 'then', $._term, 'else', $._term),
let_expr: $ => seq('let', $._pattern, '=', $._term, 'in', $._term),
lambda_expr: $ => seq('\\', $._pattern, '->', $._term),

// Type position — restricted set
infix_type: $ => prec.left(1, seq(
    $._type,
    repeat1(seq($._type_infix_op, $._type))
)),

_type_infix_op: $ => choice('|', '&', '->', 'effect'),
```

Adding a new operator = add one token to `_prefix_op` or `_infix_op`. No grammar rule changes. Tree-sitter provides highlighting and error recovery; the LSP server provides precise diagnostics.

**Note:** For binding/control forms, tree-sitter and the Pratt dictionary cooperate. Tree-sitter provides the structural parse (matched keywords, delimiters). The Pratt resolver uses the dictionary to determine how sub-expressions within these forms interact with surrounding operators.

**Scala/JVM parser** (Pratt parsing):

```scala
// The same dictionary, used directly by a Pratt parser
val operators: Map[String, OpInfo] = Map(
  "|"  -> OpInfo(1, Left,  "or"),
  "+"  -> OpInfo(5, Left,  "add"),
  "*"  -> OpInfo(6, Left,  "mul"),
  "^"  -> OpInfo(7, Right, "pow"),
  // ...
)
```

The Scala parser can run Pratt directly during parsing (no flat IR needed), or produce a flat chain and restructure — same result either way.

**LSP server** (Rust, using anthill-core):

The LSP server runs the full resolver with the dictionary. It provides:
- Precise diagnostics (precedence errors, invalid operator in type position)
- Semantic tokens (highlight `|` differently in type vs term position)
- Hover info (show operator precedence and resolved functor)

### Meta Annotations for Binding

Sorts and operations declare their operator binding via meta annotations:

```anthill
-- Sort-level: declares that `|` in type position maps to this sort
sort Union {
    sort A = ?
    sort B = ?
} [infix: "|"]

-- Operation-level: declares that `|` in term position maps to this operation
sort Bool
    operation or(a: Bool, b: Bool) -> Bool [infix: "|"]
    operation and(a: Bool, b: Bool) -> Bool [infix: "&"]
end

sort Numeric
    sort T = ?
    operation add(a: T, b: T) -> T [infix: "+"]
    operation sub(a: T, b: T) -> T [infix: "-"]
    operation mul(a: T, b: T) -> T [infix: "*"]
end
```

The `[infix: "|"]` annotation declares the binding. It does NOT set precedence — precedence comes from the dictionary. If two operations declare `[infix: "+"]` in different sorts, that's fine (overloading via sort context).

The system validates that the meta-declared operator symbol exists in the dictionary. Declaring `[infix: "|||"]` would be a load-time warning.

### Ternary Operators

Ternary operators use two tokens with three argument positions (`_ tok1 _ tok2 _`). They appear in the dictionary as patterns:

```
_ -> _ effect _    →  arrow_effect(A, B, E)
_ ? _ : _          →  cond(c, a, b)
```

In the flat chain, they appear as extended sequences:

```
A -> B effect E    →  [A, "->", B, "effect", E]
c ? a : b          →  [c, "?", a, ":", b]
```

The resolver handles them in the led phase: after parsing the first infix token (`->`), it parses the middle operand, then expects the continuation token (`effect`), then parses the third operand.

## Integration with Proposal 014 (Union Types)

Proposal 014 defines `|` as a type operator. This proposal generalizes the approach:

- Dictionary: `|` at level 1, type meaning = `SortUnion` (from this proposal)
- Resolver: `A | B` in type position → `TypeExpr::Union(A, B)` (from proposal 014)
- Loader: flattens to `SortUnion(A, B, C)` (from proposal 014)
- `type_compatible` rules: handle `SortUnion` (from proposal 014)

This proposal adds the term-level `|` (`or`) and the general framework; proposal 014 handles the specific type-level semantics.

## Examples

### Union type + logical OR

```anthill
-- Type position: `|` means union
entity Result(
    value: Int | String,
    valid: Bool
)

-- Term position: `|` means logical or
rule is_acceptable(?x)
    :- valid(?x) = true | override(?x) = true
```

### Arithmetic with operator syntax

```anthill
-- Current (works today):
rule double(?x) = add(?x, ?x)

-- With operator syntax (same semantics):
rule double(?x) = ?x + ?x

-- Mixed:
rule distance(?a, ?b) = abs(?a - ?b)
```

### Sort with declared operator

```anthill
sort Lattice {
    sort T = ?
    operation join(a: T, b: T) -> T [infix: "|"]
    operation meet(a: T, b: T) -> T [infix: "&"]
}
```

### Prefix operators

```anthill
sort Bool
    operation not(a: Bool) -> Bool [prefix: "!"]
end

-- Usage:
rule invalid(?x) = !valid(?x)
rule double_neg(?x) = !!?x          -- not(not(?x))
rule mixed(?x) = !?x | ?x = unknown -- not(?x) | eq(?x, unknown)
```

### Word operators

```anthill
sort Int
    operation mod(a: Int, b: Int) -> Int [infix: "mod"]
    operation div(a: Int, b: Int) -> Int [infix: "div"]
end

-- Usage: same precedence as * and /
rule remainder(?a, ?b) = ?a mod ?b
rule quotient(?a, ?b) = ?a div ?b
```

## Backward Compatibility

The existing 8 operators (`=`, `>`, `>=`, `<`, `<=`, `+`, `-`, `*`) continue to work identically — same tokens, same functor mapping, same `Term::Fn` representation. The change:

1. Moves precedence from the grammar into the resolver (using the dictionary)
2. Adds new operator tokens (`|`, `&`, `!=`, `/`, `%`, `^`, `->`, word operators)
3. Extends infix to type positions

The meta annotations are optional — existing stdlib operations work without them. Adding `[infix: "+"]` to `Numeric.add` is purely declarative.

## Implementation Plan

### Phase 1: Flat infix chain in parse IR

Change the grammar to produce flat `infix_expr` (no precedence levels). Add `InfixChain` to the parse IR. Implement Pratt desugaring in the converter using a hardcoded dictionary. Existing tests continue to pass — same `Term::Fn` output.

### Phase 2: New operators + type position

Add `|`, `&`, `!=`, `/`, `%`, `^` to the flat operator token set. Add `infix_type` to the grammar. Implement type-position desugaring in the resolver. Connect `|` to proposal 014's `SortUnion`.

### Phase 3: Meta annotations

Add `[infix: "..."]` as a recognized meta key. Store in KB as metadata on sorts/operations. Validate that the declared symbol exists in the dictionary.

### Phase 4: Stdlib annotations

Add `[infix: ...]` annotations to existing prelude sorts (`Eq`, `Ordered`, `Numeric`) for documentation and tooling.

## Design Rationale: Why Flat Parse + Dictionary

We surveyed approaches used by proof assistants and extensible languages:

| System | Strategy | Operator extensibility |
|--------|----------|----------------------|
| **Lean 4** | Pratt parser with mutable dispatch tables | `notation` inserts into live Pratt table |
| **Isabelle** | Earley parser over generated CFG | `notation` → new grammar production, regenerate |
| **Agda** | Parse flat, restructure with DAG precedences | Post-processing phase |
| **Maude** | MSCP parser over generated CFG | Mixfix decl → new grammar, regenerate |
| **Idris 2** | Pratt parser (Haskell-style) | `infixl`/`infixr` fixity declarations |
| **Raku** | Pratt + recursive descent hybrid | Grammar subclassing ("slangs") |

Anthill's approach is closest to **Agda** (flat parse + external precedence table) but with a simpler linear precedence (not a DAG). This is the lightest-weight approach:

- Tree-sitter grammar stays simple and never changes for new operators
- LSP server runs the real Pratt desugarer with the full dictionary
- The Scala compiler reads the same dictionary
- One dictionary, multiple consumers

## What This Does NOT Cover

- **User-defined precedence levels** — precedence is fixed in the dictionary. If 9 levels aren't enough, the dictionary can be extended, but user-declared precedence at the sort level would require dynamic table updates.
- **Postfix operators** — (`x!`, `x?`) could be added with postfix patterns (`_ !`). Not yet needed.
- **Operator sections** — partial application like `(+ 1)`. Not planned.
- **Delimited forms** — function calls `f(x)`, list literals `[a,b]`, record literals `{x:1}` are owned by tree-sitter's structural parser, not the operator dictionary.

## Relationship to Other Proposals

- **014 (Union Types)**: This proposal provides the operator infrastructure (`|` in type position); 014 provides the semantics (`SortUnion`, `type_compatible` rules).
- **011 (Type Resolution)**: Operator-typed expressions need type resolution. Infix in type position produces type terms; infix in term position produces operation calls.
- **012 (Sort Defined Syntax Sugar)**: This proposal subsumes 012's OQ2.6 (operator syntax). The pattern-based dictionary with binding/control-flow entries also addresses 012's broader vision — sorts can opt in to syntax forms by having the required operations, and the dictionary is the activation mechanism (answering 012's OQ1). Forms not covered here (comprehensions, builders) remain in 012's scope.
