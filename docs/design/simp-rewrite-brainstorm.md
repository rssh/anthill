# Dot syntax via equational rewrites

## Status: Brainstorming draft

## Relates to

- **WI-139 (delivered)** — equational-rule attributes `[simp]`, `[unfold]`, `[hint]` already exist and are tested (`anthill-core/tests/include/equational_attr_test.rs`). The dot proposal builds on this substrate.
- **Proposal 025.1** (Z3 tactic DSL) — `§"Anthill-rule-aware simplification (deferred)"`. Defers the *Z3-side translation* of simp-tagged rules and the *scope semantics* (default simp set, transitive `requires`, etc.), not the attribute itself.
- `operation-call-model.md` — operations and dispatch.
- `occurrence-as-value-type.md` — NodeOccurrence design; the substrate for expression-position content and macro-introduced occurrences.
- `kernel-language.md §9` — Maude analogy; `rule head :- body` is derivation, `rule lhs = rhs` is equation.

## The problem

Anthill today has no method-call syntax. Operations are always written `op(?x, ?y)`. The chaining ergonomics this forces are bad:

```
fold(map(filter(?xs, ?p), ?f), 0, plus)        // write order opposite to evaluation order
?xs.filter(?p).map(?f).fold(0, plus)           // wanted
```

Adding `.` cleanly requires answering, in order:

1. How does `?x.foo(?y)` resolve to an operation?
2. Can a sort customize what `.` means on it (Either-style elimination, smart-pointer transparency, refinement preservation, KB-query DSLs)?
3. How does this interact with the effect system?
4. Does it integrate with tooling (LSP completion-after-dot)?

The brainstorm landed on a single answer that addresses all four — and, critically, it **does not require new kernel machinery**. The substrate is already in the language design; the missing piece is one annotation that proposal 025.1 had already flagged as needed for unrelated reasons.

## The key insight

Equational rules (`rule lhs = rhs`) already exist in the kernel language. They appear in the codebase:

```
rule add_zero(?x) = ?x
rule add(?a, ?b) = add(?b, ?a)              // commutativity — not for rewriting
rule first([?h | ?_]) = ?h
rule add_identity: add(?a, zero-val) = ?a
```

Equational rules are detected by the loader (`kb::is_equation` checks for head functor `eq` with two positional args) and handled inside the SLD resolver as a **rewriting fallback during resolution** (`kb/resolve.rs §"SLD resolution + equational simplification"`, gated by `apply_equational_fallback`). The earlier e-graph framing in `rust-term-store-design.md §Layer 2` is forward-looking design, not the current implementation — today's equations live entirely in the resolver path.

WI-139 added attribute syntax that gates resolver participation:

```
rule my_def: foo(?a) = bar(?a)         [simp]      // indexed in by_functor → goal resolution
rule comm: comm(?a, ?b) = comm(?b, ?a)              // bare → cite-required, NOT indexed
rule expand: g(?a) = h(?a)              [unfold]    // indexed (parallel to [simp])
rule lemma: p(?x) = q(?x)               [hint]      // parses; SMT-side semantics deferred in v0
```

So the annotation question 025.1 was deferring — "how do users mark which equations are directionally rewritable?" — is **already answered for the resolver phase**. `[simp]` and `[unfold]` exist; both put a rule into `by_functor` so SLD goal resolution can apply it directionally.

**What 025.1 still defers is downstream:**
- the *Z3 translation* of simp-tagged rules (when does `tactic: simplify` see them?),
- the *scope semantics* (default simp set, named sets, transitive `requires`),
- and, by extension, any *other phase* where simp-tagged rules ought to fire.

**The dot proposal's contribution is precisely one of those other phases: applying simp-tagged rules to expression-position content as the typer walks operation bodies.** Today, `[simp]` makes equations available to the resolver. The dot proposal needs them to *also* fire during typer-driven rewriting, turning `?x.foo(?y)` into `foo(?x, ?y)`. That's the new firing site; the attribute already exists. (Why it's interleaved with typing rather than a standalone pre-pass: open question 10.)

## What this means concretely

**The parser node.** Surface `.` syntax does **not** appear in the rules — you can't define `.` using `.`. Instead the parser lowers `x.foo(y)` to a plain `Expr` node `dot_apply(receiver: x, name: foo, args: [y])`, in the same spirit as `[a, b, c]` lowering to `ListLiteral(a, b, c)` today (`kernel-language.md`). The name follows the `reflect.anthill` `Expr`-constructor convention — snake_case, sibling to `apply` / `ho_apply` (the literals like `ListLiteral` are PascalCase because they're a separate, term-shared category; a dot-call is purely an expression form). The simp rules match that functor. The name slot is a `Symbol`, the receiver and args are expressions. This must be a *distinct* node, not desugared to a bare `apply(foo, [x, y])` at parse time — `apply`'s functor resolves through lexical scope, which would reintroduce the import requirement that "Resolution" eliminates. `dot_apply` carries the "resolve via the receiver's sort" intent that the rule acts on.

The dot-expansion rules are then ordinary `rule lhs = rhs` forms over `dot_apply`, tagged with the existing WI-139 `[simp]` attribute (decided in open question 1 — reuse `[simp]`). The guards below are shown in simplified form; the default rule's guard is refined under "Resolution" so the RHS emits a *qualified* operation reference:

```
rule default_dot: dot_apply(?x, ?name, ?args) = ?name(?x, ?args)
  :- operation_exists(typeof(?x), ?name)            -- refined to find_operation_on_sort; see "Resolution"
  [simp]

rule either_delegate: dot_apply(?e, ?name, ?args) = dot_apply(eliminate(?e), ?name, ?args)
  :- typeof(?e) = Either[L = ?L, R = ?R],
     not method_on_self(Either, ?name)
  with effect ?L
  [simp]

rule querybuilder_dot: dot_apply(?q, ?name, ?args) = nested_query(?q, ?name, ?args)
  :- typeof(?q) = QueryBuilder[Domain = ?D],
     entity_of(?name, ?D)
  [simp]
```

Note `either_delegate`'s RHS re-emits a `dot_apply` on the eliminated value — delegation is just "rewrite the dot-call onto the inner value," and the result re-fires with receiver type `R`. Wrapper-own-wins falls out of guard exclusivity: `default_dot` fires iff the wrapper has its own `?name`, `either_delegate` iff it doesn't.

What changes:

- Simp-tagged rules gain a second firing site: besides the SLD resolver, they apply during **typer-driven rewriting** of expression-position content (NodeOccurrence trees). Today `[simp]` only enters `by_functor` for SLD resolution; this proposal extends its meaning to "also fire while the typer walks expression bodies." (Why interleaved with typing, not a standalone pre-pass: open question 10.)
- Rewriting is **bottom-up**: the typer classifies children first, fires applicable rules on the parent, then types the result — repeating to fixpoint.
- Each rewrite produces a fresh `NodeOccurrence` with `origin: Synthesized { from, by }` pointing back to the source.
- The typer type-checks the post-rewrite form; error diagnostics walk the `Synthesized` chain to report at source spans.

What does *not* change:

- The kernel doesn't grow a new "macro" concept.
- The `[simp]` / `[unfold]` / `[hint]` attribute syntax stays as WI-139 defined it.
- Equational rules continue to participate in the SLD resolver's equational fallback as today; load-time application is *additional*, not a replacement.
- The rule body, head, and matching machinery are unchanged.

## Grounding in the current implementation

`.` is **not** a blank slate — the grammar already parses it and the converter/resolver already give it meaning. The proposal fills a gap and coexists with what exists; it does not introduce `.` from scratch.

### How `.` is processed today

Grammar (`tree-sitter-anthill/grammar.js`): `field_access` (`_atom_term '.' identifier`, prec 10, left-assoc) covers `?x.y`; `fn_term` accepts a `field_access` as its functor name, so `x.y(args)` also parses. No grammar change is needed.

The converter (`parse/convert.rs`) routes by shape:

| Surface | Converter result | Status |
|---|---|---|
| `?x.field` (no parens) | `Term::Fn { functor: "field_access", [object, field] }` (convert.rs:1020) | works |
| `Foo.bar(args)` (identifier/sort receiver) | `convert_name` flattens to qualified Name `[Foo, bar]` → qualified call (sort companion / namespace member) | works |
| `Map[K=String].empty()` (instantiation receiver) | flattened; type-bindings erased for runtime, typer reads them separately (proposal 035) | works |
| **`?x.method(args)` (variable/value receiver)** | `collect_field_access_segments` (convert.rs:342) handles only `field_access`/`identifier`/`instantiation_term` objects — a `variable` object is **dropped**, so the functor becomes just `method` and the receiver is lost | **gap** |

The `field_access` builtin (`kb/resolve.rs:1975`, registered `mod.rs:2308`) has two modes: (1) entity-field extraction when the object's functor is in the `entity_fields` registry; (2) sort-component lookup when the functor is a sort. The 2-arg form (`?x.y`) is structural-match only; the 3-arg form binds a result; unbound object/field → DELAY.

So the method-call case `?x.method(args)` on a *value* receiver is the actual gap. The proposal fills it: when the `field_access` object is a value expression, the converter emits `dot_apply(receiver, name, args)` instead of flattening to a Name. That is a targeted converter change — the grammar and the `field_access` builtin are untouched.

### Disambiguation: field access vs method

`.` is overloaded (projection, qualified-name, and — proposed — method dispatch). The receiver's kind and the entity-field registry disambiguate. The parser emits `dot_apply(?x, ?name, ?args)` for value receivers; two guard-exclusive simp rules then split it:

```
rule dot_field:   dot_apply(?x, ?name, []) = field_access(?x, ?name)
  :- is_entity(typeof(?x)), has_field(typeof(?x), ?name)
  [simp]

rule default_dot: dot_apply(?x, ?name, ?args) = ?op(?x, ?args)
  :- find_operation_on_sort(typeof(?x), ?name, ?op)
  [simp]
```

- `dot_field` fires only when the receiver is an entity, the selector is a declared field, **and** there are no args → rewrites to the existing `field_access` builtin (projection). `has_field` / `is_entity` are answerable from the `entity_fields` registry.
- `default_dot` fires otherwise → method dispatch.

So `field_access` stops being a parser-level decision and becomes the *target* of a rewrite — the existing builtin keeps working, just reached via a rule. Field access and method call unify under one dot syntax, split by the entity-field check.

**Parens settle most cases on their own:** `?x.sel(args)` has non-empty `?args` → only `default_dot` matches → always method (fields don't take args; calling a field-held closure is `(?x.f)(args)`, an explicit higher-order apply). `?x.sel` (no parens) → empty `?args` → the entity-field check decides field vs nullary method.

**Precedence when a name is both** a field and an operation on the sort: pick field-first (same shape as wrapper-own-wins), with an optional load-time lint flagging the collision.

**Orthogonal split, kept separate:** the entity-field rule handles *value* receivers. The existing *sort/namespace* receiver case (`Foo.bar` → qualified name) stays in `convert.rs` — the parser only sees syntactic kind (`variable` → value → `dot_apply`; `identifier` → maybe sort, resolved later). That is a different disambiguation from the entity-field one.

## What firing a `[simp]` rule does

**`[simp]` tags rules, never operations.** There is no special calling convention on operations — they stay ordinary. The "macro" behaviour lives entirely in two rule-level mechanics:

1. **Rule matching binds source occurrences to rule variables.** When a `[simp]` rule matches `dot_apply(?x, ?name, ?args)` against an operation body, `?x` binds to the `Value::Node(Rc<NodeOccurrence>)` at that position — a reflect `Expr` value, not an evaluated runtime value. (This is the substrate from "What a simp rule operates on.")
2. **Firing the rule reduces its RHS to normal form** at compile time, and the result replaces the matched node.

Reducing the RHS is one uniform operation that covers both "build code" and "compute code":

- **Reflect `Expr` constructors** (`apply`, `add`, `lambda`, `dot_apply`, …) are **irreducible** — they *are* the residual code. `apply(?op, cons(?x, ?args))` reduces to an apply-node and stops. This is how a rule emits a code template.
- **Operations over `Expr`** (e.g. `derive(e: Expr, x: Symbol) -> Expr`) **reduce via their own definitions** — running arbitrary compile-time computation and returning an `Expr`. This is how a rule delegates to a *function-macro*. Such operations are **plain operations, not `[simp]`-tagged**; they get reduced simply because they are reached while normalizing a `[simp]` rule's RHS.

So a function-macro in the Scala `Expr[X] -> Expr[Y]` sense is just an operation over the reflect `Expr` sort, called from a rule's RHS. The `Expr` sort is the macro interface; rules are the entry points; Expr-operations are helpers. There is no second macro mechanism and no operation-level `[simp]`.

**Two readings of an operation reached in an RHS** (this is where Point A's STUCK applies):
- An operation that **reads `Expr` structure** (`derive` pattern-matching `add(?a, ?b)`) reduces fine — it consumes syntax, never needs a runtime value.
- An operation that **needs a value** (`compare` in `min`'s guard) reduces only if its `Expr` argument constant-folds to a literal; otherwise it is **STUCK** (non-constant), and the enclosing rule residualizes (leaves the call for runtime). The same operation may do both — match structure freely, compute only on constants.

The alternative we rejected is **explicit quoting** at every call site (`derive(quote(\?x => ?x + 1), 'x)`, Lisp / Scala 3 `'{...}` style). It's honest about phase but kills the dot ergonomics — `?f.diff(?x)` is impossible if `?f` must be quoted first. Binding source occurrences in rule matching is what lets `.` dispatch and AD-style rewrites share the same surface syntax without per-call quoting.

## What a simp rule operates on

The one-line framing for the whole design: **a simp rule is a reflect-level metaprogram.** Its pattern variables bind to reflect `Expr`/`Node` values — not to typed AST nodes, and not to raw `Term`s.

This dissolves the "is rule input typed or untyped?" question, which has no single answer because it's the wrong frame. A pattern variable like `?x` is a **syntax object whose type is a queryable attribute**, not a baked-in property of the binding:

- **Structural match**: `?x = add(?a, ?b)` destructures the reflect `Expr`.
- **Type query**: `typeof(?x)` is a reflect operation reading the occurrence's `classification`. Under typer-driven rewriting (open question 10), children are classified bottom-up, so `typeof(?x)` answers for already-typed subterms and is what makes type-directed guards like `find_operation_on_sort(typeof(?x), …)` work.
- **Metadata query**: span, owner, `origin` via reflect ops.
- **Construction**: the RHS builds new (untyped) `Expr` values — `?op(?x, ?args)` is a reflect constructor producing an `Expr::Apply`, which the typer then visits.

So the three intuitions are all simultaneously true and reconciled by the reflect framing:

| Intuition | How it holds |
|---|---|
| "Input is typed code" | Type info is present (children classified) and reachable via `typeof`. |
| "Arguments should be untyped" | The binding is a syntax object; you get a type only when you ask. |
| "Represented as reflect call" | This is the mechanism that makes both of the above true at once. |

It also unifies with rule matching (see "What firing a `[simp]` rule does"): a rule variable binds to `Value::Node`, and a `Value::Node` *is* a reflect `Expr`. "Bound to source, not evaluated" and "bound to a reflect value" are the same statement — and it's a property of *rule matching*, not of any operation.

**Carried-over subterms keep their classifications.** When `?x.map(?f)` rewrites to `map(?x, ?f)`, `?x` retains its type — correct, because a value's sort is intrinsic to it, not to its syntactic position. The typer then **type-checks** (not necessarily re-infers) the constructed output: new nodes get inferred; reused subterms keep their types but are verified against their new positions. A reused subterm whose type conflicts with its new context is a genuine type error, reported via the `Synthesized` chain to source.

## Resolution: type-directed, not scope-directed

A method call must **not** require importing the operation. Writing `?l.map(?f)` should work whenever `?l` is a List, without `import ...map` — the operation is found via the receiver's sort, not via lexical scope. This is the defining difference between method dispatch and free-function calls, and the design must respect it.

In the stdlib today, operations like `length`, `member`, `append` are defined *inside* the `enum anthill.prelude.List` body — they are **associated with** List by being in its body. `map` would be defined the same way. Dot resolution keys on this association.

The two paths:

- **Free call** `map(?l, ?f)`: `map` resolves via lexical scope (local → imports → parent exports). Needs `map` imported.
- **Method call** `?l.map(?f)`: `map` resolves via `typeof(?l)`. Needs `List` (which you have, since you have a list), not `map`.

For the dot rule to honor this, its guard must **resolve and bind the qualified operation**, and the RHS must use that resolved symbol — not re-emit a bare name that would re-resolve through scope:

```
rule default_dot: dot_apply(?x, ?name, ?args) = ?op(?x, ?args)
  :- find_operation_on_sort(typeof(?x), ?name, ?op)   -- ?op = anthill.prelude.List.map (qualified)
  [simp]
```

`?op` comes back fully qualified; the RHS emits a resolved `Ref` (riding the existing Ident→Ref promotion), so no import of `map` ever happens.

**What "associated with the sort" means** — two tiers, differing on imports:

1. **Operations in the sort/enum body** (`length`, `member`, `append`, `map`): reachable via `.` with **no import**, the way a class's methods need no separate import in OO. `find_operation_on_sort` searches here first.
2. **Operations defined elsewhere whose first param matches the sort** (extension / UFCS style): follow **normal import rules**, exactly like Rust traits (`use Trait`), Scala 3 extensions, Kotlin extensions. `frobnicate(xs: List, ...)` in `my.utils` makes `?l.frobnicate()` work only when `my.utils` is in scope.

Tier 1 covers the common case (stdlib methods) with no import; tier 2 matches every method-syntax language's "extension must be in scope" behavior.

## Three patterns as equational rules

### 1. Default method dispatch

```
rule default_dot: dot_apply(?x, ?name, ?args) = ?op(?x, ?args)
  :- find_operation_on_sort(typeof(?x), ?name, ?op)   -- ?op fully qualified; see "Resolution"
  [simp]
```

`?xs.map(?f)` parses to `dot_apply(?xs, map, [?f])` and rewrites to `map(?xs, ?f)` — with `map` resolved to its qualified name via the receiver's sort, so no import is needed (see "Resolution: type-directed, not scope-directed"). No new mechanism; just an equation tagged with the existing `[simp]` attribute, fired during typer-driven rewriting.

### 2. Wrapper delegation

A wrapper sort declares its delegation as tagged equations alongside its definition. `Either` is an `enum` (sum type) with two type parameters declared as abstract sub-sorts:

```
enum anthill.prelude.Either
  export Either, left, right
  sort L = ?
  sort R = ?
  entity left(value: L)
  entity right(value: R)
end

rule either_delegate: dot_apply(?e, ?name, ?args) = dot_apply(eliminate(?e), ?name, ?args)
  :- typeof(?e) = Either[L = ?L, R = ?R],
     not method_on_self(Either, ?name)
  with effect ?L
  [simp]
```

The RHS re-emits a `dot_apply` on the eliminated value, so it re-fires with receiver type `R` and resolves `?name` on `R`'s sort. Possible future sugar (**not** existing syntax — proposed for ergonomics) that would desugar to the rule above:

```
enum anthill.prelude.Either
  ...
  delegate_dot_to = R with !L          -- proposed; not part of current grammar
end
```

The kernel only needs to see the tagged equation. Whether that comes from hand-written rule or from in-body sugar is a separate design decision (open question 13).

Patterns the delegation rule covers (hand-written today, or via future sugar):

| Wrapper type                  | Delegate to | Effect       | Use case                          |
|-------------------------------|-------------|--------------|-----------------------------------|
| `Either[L, R]`                | `R`         | `!L`         | Error propagation                 |
| `Option[T]`                   | `T`         | `!None`      | Absence as effect                 |
| `Rc[T]`, `Box[T]`             | `T`         | none         | Smart pointer transparency        |
| `Lazy[T]`                     | `T`         | `!Forces`    | Lazy thunks                       |
| `Future[T]`                   | `T`         | `!Awaits`    | Async transparency                |
| `Logged[T]`                   | `T`         | `!Logs`      | Aspect wrapping                   |
| `UserId = String` (alias)     | `String`    | none         | Newtype transparency              |
| `PositiveInt = Int64{?x > 0}`   | `Int64`       | none         | Refinement preservation           |

Wrapper-defines-own-method always wins. `Either` can declare its own `map`, `flat_map`, etc.; those are receiver-tagged operations and the wrapper's own dispatch picks them first. The `not method_on_self(Either, ?name)` guard on the delegation rule enforces this — when an own-method matches, the delegation rule doesn't fire.

### 3. Custom DSL

Sorts that need arbitrary dispatch (KB navigation, term-with-substitution, temporal projection) write their own tagged equation directly:

```
rule querybuilder_dot: dot_apply(?q, ?name, ?args) = nested_query(?q, ?name, ?args)
  :- typeof(?q) = QueryBuilder[Domain = ?D],
     entity_of(?name, ?D)
  [simp]
```

Same machinery as patterns 1 and 2, just a less constrained rule body.

## Worked examples

Two examples that stress the design beyond simple method dispatch: `min` (typeclass + symmetry interaction) and automatic differentiation (recursive rewriting at scale). They surface several of the open questions concretely.

### Example A: `min`

`min` is defined on a typeclass (Ord), is symmetric, and has cheap algebraic laws that benefit from load-time simplification.

```
sort Ord
  requires Eq[T = T]
  sort T = ?
  operation compare(a: T, b: T) -> Int64
  operation min(a: T, b: T) -> T
end

-- Defining equations: min in terms of compare.
-- constant_fold(?const, ?source) bridges source occurrence → value: it binds
-- ?xc to ?x's literal value when ?x constant-folds, and STUCKs (→ residualize)
-- otherwise. At runtime it is identity. compare then sees only values.
rule min_le: min(?x, ?y) = ?x
  :- constant_fold(?xc, ?x), constant_fold(?yc, ?y), compare(?xc, ?yc) <= 0   [simp]
rule min_gt: min(?x, ?y) = ?y
  :- constant_fold(?xc, ?x), constant_fold(?yc, ?y), compare(?xc, ?yc) >  0   [simp]

-- Algebraic laws (structural — no value needed, so no constant_fold)
rule min_idem:  min(?a, ?a) = ?a                                [simp]
rule min_comm:  min(?a, ?b) = min(?b, ?a)                        -- bare; would loop if [simp]
rule min_assoc: min(min(?a, ?b), ?c) = min(?a, min(?b, ?c))     [simp]
rule min_top:   min(?a, top) = ?a :- has_top_element(typeof(?a)) [simp]
```

The default dot rule rewrites `?a.min(?b)` to `min(?a, ?b)`; the `min_*` rules then continue firing where guards match. Note `compare` is a **pure value operation** — it receives `?xc`/`?yc` (folded values), never occurrences. `constant_fold` is the single occurrence-aware predicate; everything else works on values. The RHS returns `?x` (the original source occurrence), not `?xc`, so `min(3, 5)` rewrites to the source `3` with its span intact.

What this exposes:

- **Symmetric operation, biased dot.** `?a.min(?b)` and `?b.min(?a)` produce different intermediate terms. `min_comm` must stay *bare* (not `[simp]`) or the load-time phase loops — the same non-termination 025.1 flags for `add_comm`. The other rules are oriented enough to make progress without commutativity.
- **Constant folding via `constant_fold`.** `min(3, 5)` reduces to `3` because `constant_fold` folds both args to literals and `compare(3, 5) <= 0` then computes. `min(?age, ?threshold)` STUCKs at `constant_fold` (non-constant occurrence) → residualizes to a runtime `min` call. The folding power available is open question 14.
- **Typeclass dispatch falls out.** `?a.min(?b)` works iff `typeof(?a)` satisfies Ord — the same condition the operation needs. The default dot rule's guard (`operation_exists(typeof(?x), ?name)`) handles it with no typeclass special-casing.

### Example B: Automatic differentiation (symbolic, forward-mode)

The canonical equational-rewriting workload. `diff` is a **plain operation over `Expr`** — *not* `[simp]`-tagged. Its behaviour is defined by `[simp]` **rules** (the rules carry the attribute, the operation does not). The rules pattern-match `Expr` structure, so `diff`'s `Expr` parameter is consumed as syntax — never constant-folded.

```
namespace anthill.math.diff
  export diff

  operation diff(expr: Expr, var: Symbol) -> Expr        -- plain operation, defined by the rules below

  -- Base cases
  rule diff_var_same:  diff(?x, ?x) = 1                                          [simp]
  rule diff_var_other: diff(?y, ?x) = 0 :- is_var(?y), not_same(?y, ?x)          [simp]
  rule diff_const:     diff(?c, ?x) = 0 :- is_const(?c)                          [simp]

  -- Linearity
  rule diff_add:   diff(add(?a, ?b), ?x) = add(diff(?a, ?x), diff(?b, ?x))       [simp]
  rule diff_scale: diff(mul(?c, ?a), ?x) = mul(?c, diff(?a, ?x)) :- is_const(?c) [simp]

  -- Product rule
  rule diff_mul: diff(mul(?a, ?b), ?x) = add(mul(diff(?a, ?x), ?b),
                                             mul(?a, diff(?b, ?x)))              [simp]

  -- Chain rule
  rule diff_sin: diff(sin(?a), ?x) = mul(cos(?a), diff(?a, ?x))                  [simp]
  rule diff_pow_const: diff(pow(?a, ?n), ?x) = mul(mul(?n, pow(?a, sub(?n, 1))),
                                                   diff(?a, ?x)) :- is_const(?n) [simp]
end

-- Arithmetic simp rules to keep diff output clean
rule mul_zero_l: mul(0, ?a) = 0    [simp]
rule mul_one_l:  mul(1, ?a) = ?a   [simp]
rule mul_one_r:  mul(?a, 1) = ?a   [simp]
rule add_zero_r: add(?a, 0) = ?a   [simp]
```

For `diff(add(mul(x, x), mul(3, x)), x)` the phase reduces (linearity → product/scale rules → base cases → arithmetic cleanup) to `add(add(x, x), 3)`, i.e. `2x + 3`. Correct.

What this exposes:

- **Recursive rewriting to fixpoint.** Each rule application yields a tree that must keep reducing. The simp phase runs to fixpoint within an expression, not one pass — needs a divergence bound.
- **Inlining is load-bearing.** Symbolic AD only works if function bodies are visible. The natural mechanism is the existing `[unfold]` attribute: mark the function being differentiated (and its dependencies) `[unfold]` so the phase expands its body before `diff` rules pattern-match. This makes `[unfold]`-at-load-time a prerequisite (open question 15).
- **Rule specificity.** `diff_scale` (const × subexpr) and `diff_mul` (general product) both match `mul(3, x)`. Either authors order specific-first, or the phase picks most-specific-LHS, or general-then-cleanup is accepted (the arithmetic rules absorb the slop). Needs a documented firing strategy (open question 16).
- **`diff` operates on the expression, not the value.** `diff(parabola(x), x)` is meaningful even though `parabola(x)` evaluated is just a number — `diff`'s rules pattern-match the `Expr`, not the result. Because `diff` is defined by `[simp]` rules, it also works at runtime via the resolver's equational fallback on runtime `Expr` values.
- **Rule-form vs function-macro for `diff`.** The pattern-rule definition above is rule-form. If the transformation were too irregular for finite pattern rules, `diff` could instead have an operation *body* that `match`es on `Expr` and constructs the result — a function-macro — invoked from a thin entry rule. Same operation, same `Expr` interface; only the definition style differs. Either way `[simp]` stays on the entry rules, never the operation.
- **Where rewriting is the wrong tool.** Symbolic AD covers forward-mode + scalar. Reverse-mode and tensor AD need code generation (tape construction + execution), not pure rewriting. The stdlib design should be honest about this boundary.

## Effect propagation

The Either elimination raises the L value as an effect. Concretely:

```
operation notify_user(?e: Either[Error, User]) -> Unit !Error, Modifies(store)
  ?e.notify()       // dispatch on User; if Left(err), perform Error(err)
  ?e.archive()
end
```

Three notes:

- The effect is **just the sort** (`!Error`), not a wrapped form like `!Yields[Error]`. Same shape as `!Modifies(store)`. Error sorts are effect-able sorts; `Modifies(store)` is the existing parallel.
- The call site has **no marker** (`?`, `!`, `try`, etc.). Visibility is at the operation signature, where Anthill already prefers truth to live.
- The "where does L go" question is answered by **effect propagation**, not by inserting markers at every use site. If the enclosing operation doesn't declare `!Error`, the body fails to type-check — exactly when the user wanted to know.

## Occurrence semantics

This section grounds the "What a simp rule operates on" framing in the concrete `NodeOccurrence` representation, and gives the three reasons the occurrence wrapper (not a raw `Term`) is the right binding.

When a flagged rule's LHS pattern `dot_apply(?x, ?name, ?args)` matches the parsed form of `?e.notify()`:

- `?e` is in **expression position** (the receiver slot of a `dot_apply` inside an operation body), so per `occurrence-as-value-type.md` it is a `NodeOccurrence` with `kind: Expr { … }`.
- The pattern variable `?x` binds to `Value::Node(Rc<NodeOccurrence>)`, not to a raw `Term` — this is the reflect `Expr` value from "What a simp rule operates on."
- Pattern syntax descends transparently. Writing `?x = let_expr(?b, ?body)` in a guard is shorthand for "match `?x`'s underlying Expr against the let shape." The `Rc<NodeOccurrence>` stays bound; the user writes against the structure.

Three reasons this matters and is consistent with the existing design:

1. **Spans survive.** Hash-consed `Term` drops spans by design. Diagnostics that point at source code need the occurrence wrapper to carry positional metadata.
2. **Identity per call site.** Two structurally-identical `Either` arguments at different sites must distinguish — they can attach different effects, different `CallClass`. `Rc::ptr_eq` distinguishes occurrences; hash-consed terms merge.
3. **`origin: Synthesized { from, by }` is exactly the macro-trace channel.** Rules produce fresh occurrences tagged with the source occurrence they rewrote from and the rule that did it. Later passes can walk the chain to report errors at source or to explain what an expression came from.

## LSP integration

Completion-after-dot is a KB query with the name field unbound. When the user types `?x.<cursor>`:

1. Determine the sort `S` of `?x` from surrounding context.
2. Query: `[simp] rule dot_apply(?x, ?name, ?args) = ?result :- ...` with `typeof(?x) = S` and `?name` unbound.
3. The resolver returns all bindings of `?name` consistent with some simp-flagged rule and the receiver's sort.
4. For each, look up doc, signature, propagated effects via further KB queries.
5. Rank and return.

The case-by-case behavior:

- **Default sort**: `find_operation_on_sort(typeof(?x), ?name, ?op)` with `?name` unbound enumerates every operation associated with the sort → standard method-completion list.
- **Delegating sort**: returns the wrapper's own methods, plus the delegate's completions (recursively, via the delegation rule's RHS — see the `not method_on_self` guard), annotated with the propagated effect.
- **DSL sort**: the rule's guard body itself constrains valid names (`entity_of(?name, Domain)`). The resolver returns every entity in the domain — exactly the right completion set. **The author defines completion by defining the rule.** No parallel `complete_dot` function to keep in sync.

This works because **the flagged rules are data, not opaque code**. The resolver runs them in both directions: forward (given `dot_apply(?x, foo, [?y])`, produce the expansion) and inverse (given `dot_apply(?x, ?n, ?args)` with `?n` unbound, enumerate `?n`). Tooling gets the inverse direction for free.

The non-negotiable: **flagged equations live in the KB as ordinary rules**. If any flagged equation ever became a Rust callback or opaque function, the inverse-direction query is lost and tooling has to be implemented twice. The brainstorm's whole tooling story rests on this property.

## Why this fits Anthill's philosophy

The substrate-as-data invariant carries through:

- Sorts are facts in the KB.
- Operations are facts in the KB.
- Rules (derivation and equation) are facts in the KB.
- **Method dispatch is also rules in the KB** — specifically, simp-flagged equations.

No new subsystem. The `[simp]` annotation already exists (WI-139); the syntax gains one grammar form (`'.' name '(' args ')'`); the typer gains a rewriting step (fire applicable simp rules bottom-up, type the result). Everything else — default dispatch, delegation, DSLs — is library code shipped as `[simp]`-tagged equational rules in the prelude.

## Open questions

The annotation already exists (WI-139). The live questions are about extending its firing phases and the specifics of dot dispatch.

### Attribute semantics

1. **Reuse `[simp]` or introduce `[rewrite]`? — DECIDED (2026-05-21): reuse `[simp]`.** Today `[simp]` means "index this equation in `by_functor` so the resolver can apply it directionally during goal resolution." A `[simp]` rule now *also* fires during typer-driven rewriting of expression bodies — one attribute, two firing sites, consistent with "this equation is directionally usable." The rejected alternative (B) was a phase-specific attribute like `[rewrite]`/`[expand]` for load-time-only use; it adds vocabulary for a separation no concrete use case has yet demanded. If authors later need "syntactic-sugar-only, not proof normalization," B can be added then. Until then, `[simp]` carries both meanings.
2. **Scope of a simp set.** Global? Per-namespace? Transitive `requires` chain? Multiple named sets (e.g., `simp(dot)`, `simp(arithmetic)`)? 025.1 deferred this; load-time application reraises it because expression bodies cross namespace boundaries.
3. **Termination at the load-time phase.** Today's `[simp]`-tagged rules can loop inside the resolver, which has search bounds. Load-time rewriting needs explicit termination. Options: (a) syntactic LHS-size > RHS-size check; (b) explicit `decreases` metric; (c) run-and-detect with depth limit + diagnostic; (d) trust the author. Whatever we pick should not retroactively restrict resolver-phase use.
4. **Interaction with SLD resolver's equational fallback.** Given question 1's decision (reuse `[simp]`), a `[simp]` rule fires in both phases — the resolver's equational fallback and typer-driven rewriting. Confirm the two paths agree: same reduction strategy (question 20), same ground/non-ground boundary (question 14), no semantic drift. This is now a verification task, not a design fork.

### Specific to dot dispatch

5. **`self` marker for operations.** Originally a dispatch gate; in this design, it's redundant (the default simp rule fires for any matching op). Keep as a documentation/codegen hint only, or drop entirely? Lean: drop.
6. **Symmetric operations** (`merge`, `concat`, `add`): these enter `.` dispatch by default. `?a.merge(?b)` biases `?a`. Acceptable, or worth a "non-method" opt-out marker? Lean: live with it.
7. **Name shadowing under refactor.** Adding a method to a wrapper sort silently shifts dispatch from delegate to wrapper. Mitigation candidates: explicit `override`-style marker; lint warning; require explicit annotation when delegate already has a same-named method.
8. **Delegation cycles.** Forbid statically. The delegation graph must be a DAG. Loader checks at KB-build time, surfaced as a load error.
9. **Stacked auto-peel.** `Either[E, Option[T]]` peels one layer per `.`. Confirm we reject recursive auto-peel (user writes combinators for deeper); the simp termination rule probably enforces this naturally if size-based.
10. **Phase ordering — resolved toward typer-driven rewriting.** The dot guard `find_operation_on_sort(typeof(?x), ?name, ?op)` needs `typeof(?x)`, but a naive `parse → scan → simp-rewrite → load → typecheck` order would rewrite before types exist. Classic macro-expansion-vs-typing problem. **Recommended resolution: the typer drives the rewriter, bottom-up.** Not a separate pre-pass:
    - Typer walks the NodeOccurrence tree depth-first, typing children first.
    - With children typed, it checks whether the node matches a simp rule with a now-satisfiable guard (`typeof(?x)` is answerable).
    - If so, the rewriter produces a **fresh, untyped** NodeOccurrence (`classification = None`, `origin: Synthesized { from, by }`).
    - The typer recurses into the new node, typing it (which may trigger further rewrites — delegation chains, AD cascades), then classifies.

    This fits the existing design directly: `NodeKind::Expr.classification: RefCell<Option<Box<CallClass>>>` already exists because "the typer mutates this after construction." A synthesized node arrives with `classification = None` — that *is* "untyped." The typer fills it on visit. No new field, no new arena.

    **Requirement it imposes:** the typer must be reentrant/incremental — callable as `type_node(node, ctx)` on a freshly-built subtree, not a monolithic single pass. Check this before committing; if the typer is a monolith it needs refactoring into callable-per-node form first.

    **One mechanism for syntactic and type-directed rules.** AD's `diff_add` (matches `add(?a, ?b)`, no `typeof`) and the dot rules (need `typeof`) both work under typer-driven firing: guard satisfiability gates when each can fire. No need to split syntactic vs type-directed rewriting into separate phases.

    **Reduction strategy is innermost (bottom-up), and forced.** For `p(p(?x, ?y), ?z)`, the outer rule can't dispatch until `typeof(p(?x, ?y))` is known, which requires reducing-and-typing the inner term first. So type-directed dispatch and bottom-up reduction are the same constraint — leftmost-innermost / call-by-value. See open question 20 for the consequences (strict semantics, no lazy discard).

    The older options — (a) separate earlier sort-inference pass, (c) defer-then-rewrite — remain fallbacks if reentrant typing proves impractical.
10a. **Import semantics for dot dispatch.** Tier-1 operations (in the sort body) need no import; tier-2 (extension operations defined elsewhere) follow normal import rules. Confirm `find_operation_on_sort` implements exactly this split, and decide whether tier-2 visibility is checked at the rewrite phase (when scope is known) or deferred.
11. **Diagnostic quality.** "Method `frobnicate` not found on `Rc[Lazy[Either[E, Foo]]]`: walked Rc → Lazy → Either → Foo, none defined frobnicate." Diagnostic layer needs to walk the delegation chain when no simp rule fires, and walk the `Synthesized` chain when post-rewrite typecheck fails. Engineering work.
12. **Reflection use.** Code that introspects "what methods does sort S have?" queries the same simp rules. Same machinery as LSP completion — should land as a stdlib reflect operation.
13. **Delegation-sugar surface.** `delegate_dot_to = T with !E` syntax — exact spelling, placement in sort body, interaction with `requires`. Smaller design task.

### From the worked examples (min, AD)

14. **Resolver power inside the simp phase + STUCK (not DELAY) handling.** Both examples evaluate guards during simp (`compare(3, 5) <= 0`, `is_const(?c)`). The simp phase runs guards through the resolver — making it a **partial evaluator**: reduce what's a compile-time constant, residualize what isn't.

    The subtlety: in the simp phase a rule variable like `?x` is **not** an unbound logical variable — it's *bound* to a source occurrence (a reflect `Expr`). So SLD's DELAY (which means "unbound logical variable") is the wrong concept. The real outcome is **STUCK**: the bound term is a *non-constant source expression* whose runtime value isn't known at compile time. Three outcomes:

    | Guard `?x` bound to | Outcome | Action |
    |---|---|---|
    | occurrence that constant-folds to a literal (`int_lit(3)`) | computes → true/false | fire / try the next rule |
    | occurrence that doesn't fold (`var_ref(age)`, `f(age)`) | **STUCK** (non-constant) | residualize → leave the term as a runtime call |
    | genuinely unbound logical var | DELAY | proof-time only; shouldn't arise in the simp phase |

    So `min(3, 5)` folds to `3` at compile time, while `min(?age, ?threshold)` stays a runtime `min` call.

    **Recommended form: explicit `constant_fold` in the rule body.** Rather than teaching every value operation to fold-or-STUCK on occurrence args, put a single occurrence-aware predicate in the guard:

    ```
    rule min_le: min(?x, ?y) = ?x
      :- constant_fold(?xc, ?x), constant_fold(?yc, ?y), compare(?xc, ?yc) <= 0  [simp]
    ```

    `constant_fold(?const, ?source)` is the **only** occurrence-aware builtin: at compile time it binds `?const` to `?source`'s literal value when it folds, STUCKs (→ residualize) otherwise; at runtime it is identity. `compare` and every other value operation stay occurrence-unaware, receiving folded values. This collapses the implementation from "occurrence-handling in every value operation" down to "one `constant_fold` builtin; everything else unchanged." (An implicit auto-fold path could be offered later as ergonomic sugar, but explicit `constant_fold` is the principled default.) Note DELAY proper does not arise here — the rule var is bound to a source occurrence, not unbound; the outcome is STUCK, not DELAY (the category error this question corrects).

    Two consequences:
    - **One rule set, two phases.** A residualized `min(?age, ?threshold)` is evaluated at runtime by the *same* `min_le`/`min_gt` equations (they're already in `by_functor` per WI-139). The `[simp]` equations are simultaneously `min`'s definition (runtime) and its partial evaluator (compile time); STUCK is just the boundary. At runtime args are values, `constant_fold` is identity, the guard computes. Reinforces questions 4 and 20 — the phases share the rules, so they must share strategy and the constant/non-constant boundary.
    - **Structure-reading vs value-needing operations.** An operation that pattern-matches `Expr` structure (`diff` on `add(?a,?b)`) never STUCKs — it consumes syntax. Only operations that need a *value* (`compare`, arithmetic) can STUCK, and only when their `Expr` arg doesn't constant-fold. Dispatch rules (`default_dot`, `either_delegate`) read structure + types only, so they never STUCK either.

    Open sub-question: how much resolver power for constant-folding guards — (a) literal arithmetic only; (b) ground-term resolution; (c) full SLD search? More power means more compile-time folding but higher cost and tighter termination obligations.
15. **`[unfold]` at the load-time phase.** Symbolic AD requires function bodies to be visible so `diff` rules can pattern-match. The existing `[unfold]` attribute (WI-139) is the natural mechanism — but its load-time semantics need specifying (when does a `[unfold]`-tagged operation expand: always, only inside a simp-tagged context, only when reached by a firing rule?). This dovetails with 025.1's deferred `[unfold]` work.
16. **Rule firing strategy / specificity.** When multiple simp rules match (e.g., `diff_scale` and `diff_mul` both match `mul(3, x)`), the phase needs a deterministic order. Options: most-specific-LHS-first (Maude/Mathematica), textual order (Prolog), or general-then-cleanup (accept a more-general result and let other simp rules normalize). The resolver phase has its own search order; the load-time phase needs its own documented strategy.
17. **Function-macros (Expr-operations) and their opacity.** `[simp]` lives on rules only; operations are never tagged. A function-macro is a plain operation over the reflect `Expr` sort, reduced when reached while normalizing a `[simp]` rule's RHS (see "What firing a `[simp]` rule does"). Two things to settle: (a) **opacity** — unlike rule LHS patterns (data, queryable both directions for LSP completion), an Expr-operation's body is forward-only/opaque; this is fine because completion keys on rule *LHS*es, not RHS computation, but confirm no completion path needs to see through the operation. (b) **discoverability** — is any marker wanted to flag "this operation is intended as a macro helper / only meaningful at compile time," or is "takes/returns `Expr`" signal enough? Lean: no marker; the `Expr` signature is the signal.
18. **Termination interaction with symmetric laws.** The `min` example shows `min_comm` must stay bare or the load phase loops. This generalizes: any commutative/associative-commutative law is unsafe as `[simp]` at load time. Should the loader *reject* a `[simp]` tag on a rule it can detect is non-terminating (LHS and RHS same size, permuted args)? Or warn? Or trust the author? Ties into open question 3.
19. **Re-check vs re-infer for carried-over subterms.** Reused subterms keep their `classification` in the RHS. Is type-*checking* (verify the subterm fits its new position) sufficient, or do contextual/bidirectional-inference cases require re-*inference*? Determines whether a rewrite can ever invalidate a previously-sound subterm type, and how that surfaces as a diagnostic. Type-checking is cheaper and safe for intrinsic types; re-inference is needed only if a subterm's solved type genuinely depended on its old syntactic context.
20. **Reduction strategy (which redex first) — innermost.** Distinct axis from question 16 (which rule fires when several match *one* redex); this is *which redex* reduces first. For `p(p(?x, ?y), ?z)` the design is **leftmost-innermost / bottom-up**, forced by type-directed dispatch (the outer rule needs `typeof` of the reduced inner term) and matching the typer's bottom-up walk. Consequences to confirm:
    - **Strict, no lazy discard.** `fst(pair(?a, ?b)) = ?a` still reduces `?b` first; a looping subterm hangs the rewrite even if the enclosing rule would discard it. Outermost would dodge this; innermost gives it up.
    - **Confluence caveat.** For a confluent + terminating simp set, Church-Rosser makes the normal form strategy-independent — innermost is then only an efficiency/termination choice. For non-confluent sets it is the *defined* semantics.
    - **Phase consistency (ties to question 4).** A `[simp]` rule fires both in the SLD resolver's equational fallback and in typer-driven rewriting. Both must use the same strategy or the rule yields different results in the two phases. Confirm the resolver's `apply_equational_fallback` strategy and match it.
    - **Future escape hatch.** If laziness is needed for specific operators (short-circuit `and`/`or`, lazy constructors, discard-without-reduce), Maude-style per-operator `strat` / `frozen` annotations graft on without changing the default.

## Next steps

1. ~~Decide `[simp]` vs new attribute~~ — **done (2026-05-21): reuse `[simp]`** (open question 1).
2. **Confirm the typer is reentrant** (`type_node(node, ctx)` callable per-subtree). This gates the typer-driven rewriting approach (open question 10); if the typer is monolithic, refactoring it is the real first task. With question 1 settled, this is now the first open design task.
3. **Spec typer-driven rewriting** — how the typer invokes the rewriter bottom-up, produces `Synthesized` nodes, and recurses. Not a standalone loader phase.
4. **Termination + cycle story** (open questions 3, 18) — including the `Synthesized.from` ancestor-loop check.
5. **Write the prelude simp rules**: default dispatch, delegation pattern. Validate on `Either` and one DSL case (KB query).
6. **Decide on the `self` question** (likely: drop as dispatch gate; defer hint-marker decision).
7. **Diagnostic surface design** — error spans through `Synthesized` chains, delegation-walk explanation.
8. **LSP server impl** — completion query + ranking + caching layer.

## Interaction with interpreter IR

`docs/design/interpreter-ir.md` proposes lowering each operation body to a resolved `CompiledOp` IR *after* type-checking, serving both a faster interpreter and codegen. The two designs are **mostly independent — sequential phases**, with one shared dependency.

**Independent on the compile path.** Simp rewriting is typer-driven (during type-checking); IR lowering runs after. By the time lowering runs, `?x.map(?f)` is already `Apply { functor: map, … }`, so the IR never sees `.` syntax — it lowers `map(?x, ?f)` to `CallStatic` like any other call. No dot-awareness in the IR, no feedback loop:

```
typecheck { …interleaved simp rewriting… }  →  IR lowering  →  eval-v2 / codegen
```

The IR's `CallViaReq` (names-model requirement dispatch) even aligns with typeclass operations here: `min`'s `requires Ord[T]` means `compare` lowers to `CallViaReq` — same mechanism, no conflict.

**Shared dependency: equation-defined operations.** The IR assumes operations have a `NodeOccurrence` body to lower. But `[simp]`-defined operations (like `min`) have *no body* — they're defined entirely by equational rules. This isn't new (`add_zero`, `first` already work this way), but the dot design leans on it: every value-conditional rule residualizes to a runtime call to a possibly-body-less operation. Resolution (must be settled in the IR doc, not here):
- **Compile the equation set into a `CompiledOp`** — `min`'s rules become `if compare(a,b) <= 0 then a else b` (an `If` over a `CallViaReq`). Feasible for deterministic + complete sets; *required* for codegen (can't ship the resolver's equational fallback into emitted Rust).
- **Keep an equational-fallback path** in eval-v2 for body-less ops — smaller step for the interpreter, insufficient for codegen.
- Likely both: compile where the equation set is deterministic + complete; fall back to the resolver otherwise.

**Minor: source spans through the IR.** Rewritten nodes carry `origin: Synthesized { from, by }`. The IR sketch carries no span/origin; for runtime errors in lowered-rewritten code to map back to source, the IR should carry a source-span handle (the `Synthesized`-resolved span) on at least call/match instructions.

## What's deliberately not in scope

- **General user-authored sugar beyond dot.** The simp-set annotation enables this in principle (any flagged equation rewrites at load time), and that's a coherent direction. But this brainstorm is specifically about dot syntax. If the simp-set proposal opens the door more widely, that's its scope to address; this doc commits only to the dot use case.
- **Bidirectional simp rewriting.** Flagged rules apply LHS→RHS only during typer-driven rewriting. The SLD resolver's equational fallback handles other directions for proof and normalization; not the same phase, not the same purpose. (If an e-graph layer materializes per `rust-term-store-design.md §Layer 2`, the bidirectional case would live there.)
- **Tactic-driven rewriting.** Proposal 025.1 contemplates a future `tactic: anthill_simplify(scope: ...)` that consumes simp-flagged rules at proof time. Sibling use case; not this proposal's concern.
- **Macros with side effects.** Flagged rules are pure (they're rules). Anything that needs side effects at expansion time is not in scope and probably shouldn't be a rewrite.
