# Proposal 043 — The `[simp]` rewriting engine

## Status: Proposal — revised 2026-05-22.

> **Revision (2026-05-22).** Corrected after a design review (see
> `docs/design/simp-dot-finding.md`). The original framed the engine as
> *type-independent structural rewriting* with dot bolted on; that was the
> error. The engine is **type-directed and integrated with the typer**; a
> `[simp]` rule's guard is its explicit `:- …` **plus its enclosing sort's
> `requires`** (so in-sort rules are type-directed even with no written guard);
> `typeof` is **`min_sort`** (widen to the least declared sort) — the receiver's
> type, **consumed in guard evaluation** (and expressible as a typer-phase
> builtin), not a vague `typeof` operation. A rule is defined over *expressions*,
> so firing is compile-time; the only real boundary is **expression vs value**,
> not "two phases." Dot dispatch is one client of this type-directed engine.
> §4.1/§4.7 (and §6) rewritten accordingly; §4.6 next.

The `[simp]` attribute (WI-139) marks an equational rule as directionally rewritable. Today that has one consumer: the SLD resolver's equational fallback, over runtime `Term`s. **This proposal gives `[simp]` a second firing site — the type-checker, over expression-position occurrences — turning tagged equations into compile-time rewrites.** The engine is the language feature; user-authored compile-time simplification (§5) is its most direct use, and method-call (dot) syntax (§6) is its first packaged client.

## Relates to

- `docs/design/simp-rewrite-brainstorm.md` — the design exploration this proposal distills (rationale, tooling/LSP, delegation, worked examples).
- `docs/design/simp-rewrite-design.md` — the rustland implementation design (one rewriter over expressions, sharing the `TermView` matcher; substrate audit; build order). This proposal is the *semantics*; that doc is the *how*.
- **WI-139 (delivered)** — `[simp]`/`[unfold]`/`[hint]` attributes (`anthill-core/tests/include/equational_attr_test.rs`).
- **Proposal 025.1** (Z3 tactic DSL) — deferred the Z3-side translation of simp rules and their scope semantics; this proposal addresses a *different* deferred firing site (the typer), not the Z3 one.
- `docs/design/occurrence-as-value-type.md` — `NodeOccurrence` / `Value::Node` substrate. `docs/design/interpreter-ir.md` — downstream consumer (equation-defined operations).
- `docs/kernel-language.md §9` — `rule head :- body` is derivation, `rule lhs <=> rhs` is equation (Maude analogy). The equational head connective is `<=>` (unification), not `=` (the semantic-equality *test*) — proposal 049.

## Goal

Make a `[simp]`-tagged equation `lhs <=> rhs` fire **as a rewrite during type-checking**, not only during proof/runtime resolution. The same rule then has two roles — runtime simplification (existing) and compile-time elaboration (new) — and must behave identically in both (§4.7). The feature stands on its own (§5); on top of it, three surface features fall out as library rules: method dispatch (§6), compile-time folding (§7), and symbolic rewriting (§8). No new kernel concept: the kernel does **not** grow a "macro" — `[simp]` rules are ordinary equational rules with a second firing phase.

---

## 4. The engine (semantics)

### 4.1 A `[simp]` rule rewrites *expressions* — i.e. it is compile-time

A `[simp]` rule is an equation (head `LHS <=> RHS`, i.e. `unify(LHS, RHS)` —
proposal 049 relabelled the empty-body equational head from `eq` to the
unification connective `<=>`) tagged **directionally rewritable** (LHS→RHS). Its guard is its explicit `:- …` **plus the `requires`
of its enclosing sort** — a rule defined inside a sort inherits that sort's
`requires` implicitly, so an in-sort rule is *not* body-less. An explicit guard
may be **any** resolvable condition — type-level (`min_sort` / `is_entity` /
`has_field` / `requires`) **or value-level** (e.g. `compare(?x, ?y) <= 0`,
`constant_fold` — §7). Type-directedness is one *kind* of guard, not the only
one; the engine evaluates the guard generally (by resolution).

**A rule is defined over expressions, so firing it is compile-time.**
"Compile-time" here is not a clock but a *mode*: to hold an **expression** (a
structural object — a `NodeOccurrence` / a term being matched, **not** an
evaluated value) is to know (or be able to derive) its type, so type-directed
rewriting applies. There is **one rewriter over expressions**; it runs wherever
an expression is held:

- **Typer (operation bodies):** the typer walks a body and rewrites its
  expression-position content (this proposal).
- **The resolution engine, used at compile time to resolve rules:** the
  equational fallback rewrites the expressions it holds while resolving rules
  during compilation — the same compile-time activity, a different caller
  (exists).

These are **not two semantic phases to reconcile** — one rewriter, invoked
wherever expressions are processed (§4.7).

**A caution about the resolution engine.** It is a *general* engine: besides the
compile-time rule-resolution above, it **also runs at runtime**, and there the
goals it resolves are **not expressions** — they may be evaluated values, or
something else entirely. Simp rewriting does **not** apply to that runtime use.
So the domain is "compile-time, over expressions," **not** "SLD" as such; the
only real boundary is **expression vs value**: simp rewrites expressions and
never touches evaluated values. Because an expression carries its type, the
type-directed parts (`min_sort`, `requires` guards) apply uniformly at every
expression call site.

**A `[simp]` rule may target any functor** — `add`, `transpose`, `min`,
`dot_apply`, a user's domain constructor — not a privileged set. The clients
(§6–§8) are rule libraries over particular functors.

> *Indexing note:* guarded equations must be indexed for firing too — today
> `is_equation` requires an empty body, so guarded `[simp]` rules aren't indexed
> in `by_functor`; that is a gap to fix (WI-283).

### 4.2 What pattern variables bind to — and expression-accepting builtins

A rule's pattern variable binds to the **reflect `Expr`/occurrence** at that
position — a syntax object, not an evaluated value (`Value::Node(Rc<NodeOccurrence>)`). Three queries over that binding:

- **Structural:** `?x = add(?a, ?b)` destructures the occurrence's `Expr`.
- **Type:** `min_sort(?x)` widens the bound expression to its least declared
  sort (`= sort_head` of its type). It reads the occurrence's **inferred type**:
  the typer produces **typed occurrences** (it keeps each occurrence's
  `TypeResult.ty` instead of discarding it, as any statically-typed compiler
  keeps a typed AST). *How* the type is kept — a node field, a side table keyed
  by occurrence, or `type_of` facts — is an **implementation detail**; the
  design only requires that the type is available on the occurrence. `min_sort`
  is the precise replacement for the proposal's vague `typeof`.
- **Metadata:** span, owner, `origin`.

**Builtins are classified by argument domain.** A builtin that accepts
**expressions** — `min_sort`, `find_operation_on_sort`, `constant_fold`, the
reflect/`Expr` builtins — is a **compile-time builtin**: it runs while
expressions are being processed (§4.1), which is the only time an expression
(and hence its type) is in hand. A builtin over **values** runs at evaluation.
The boundary is expression-vs-value, **not a clock**: to call an
expression-builtin "at runtime" you first **construct an expression** (quote /
reify a value) and pass that — possible, so the model is uniform rather than
walled. `min_sort` is therefore an ordinary expression-accepting builtin,
alongside the existing reflect ones.

Carried-over subterms keep their type: when `?x.map(?f)` rewrites to `map(?x, ?f)`, `?x` retains its sort (intrinsic to the value, not its syntactic position). The typer type-checks the constructed output; a reused subterm that conflicts with its new position is a genuine type error, reported via the `Synthesized` chain to the source span.

### 4.3 Firing model

Bottom-up: the typer classifies children first, then, at a node whose children are typed, queries `by_functor` for `[simp]` rules whose LHS matches; matches the LHS, evaluates the guard (if any), and on success synthesizes the RHS as a fresh occurrence (`origin: Synthesized { from, by }`), re-typing it (which may trigger further rewrites — chains, cascades).

### 4.4 Reduction strategy — leftmost-innermost (forced)

For `p(p(?x, ?y), ?z)` a type-directed outer rule can't fire until `min_sort(p(?x, ?y))` is known, which requires reducing+typing the inner term first. So type-directed dispatch and innermost reduction are the same constraint, and it matches both the typer's walk and the resolver's existing strategy. Consequence: strict, no lazy discard (a looping discarded subterm still hangs the rewrite). Future escape hatch: Maude-style per-operator `strat`/`frozen`.

### 4.5 Termination

- **Structural** where the LHS functor cannot reappear in the RHS, or the RHS is strictly smaller (`add(?x, 0) = ?x`; `dot_apply → apply`). No machinery needed.
- **Fuel-bounded** for value-conditional and recursive rules (AD, `min` algebra). Commutative / associative-commutative laws (`add(?a,?b)=add(?b,?a)`) must stay **bare** (non-`[simp]`) or the phase loops. Plus a `Synthesized.from` ancestor-loop check. Open: should the loader reject a `[simp]` tag on a detectably non-terminating rule (LHS≡RHS, args permuted)?

### 4.6 Firing specificity — structural narrowing, then sort-directed matching, then guard

When several `[simp]` rules could rewrite one redex, selection is **three
steps**, and "most-specific-first" applies on **two dimensions** — argument
structure *and* receiver sort:

1. **Structural narrowing (discrimination tree).** `discrim.rs query_node` keys
   on the term's *structure* — functor, name, argument shape — yielding
   candidates, concrete-edge before variable-edge. This separates e.g.
   `dot_field: dot_apply(?x, ?n, [])` (concrete `nil` args) from
   `default_dot: dot_apply(?x, ?n, ?args)` (variable args). It does **not** see
   the receiver's sort: `List.map` and `Either.map` are structurally identical
   here.
2. **Sort-directed matching (type-aware, subsort-aware).** A rule defined on
   sort `S` matches a redex only if the receiver **conforms** to `S` —
   `min_sort(receiver) <: S` (the subsort relation, **not** equality). So a rule
   on `B` fires on objects of any `A <: B`, and — conformance being transitive —
   a rule on `C` fires on objects of any `A <: B <: C` as well. For an object of
   `A`, **all three** rules (on `A`, `B`, `C`) match; ordering then picks the
   most specific. This needs the type (`min_sort`), so it is part of *matching*,
   not the structural tree, and not the `requires`-guard.
3. **Guard (`requires`).** The explicit `:- …` plus the sort's `requires` is
   evaluated on the matched binding (e.g. the matched sort satisfies a needed
   spec).

**Specificity ordering** combines both dimensions. Among rules passing (2), the
**most-specific receiver sort** wins — for `A <: B <: C`, a rule on `A` outranks
one on `B` outranks one on `C` (override-style); within one sort, structural
specificity from (1) breaks ties. A rule with **no sort scope** and an
all-variable LHS (`default_dot`) is effectively scoped to the top sort — the
**total fallback**, tried last.

So a sort customizes its own behavior simply by declaring a rule on itself (or
any supersort): conformance (2) makes it apply, and sort-specificity makes it
outrank more-general rules. (The discrim tree still does the cheap structural
narrowing; `apply_eq_rules` already uses `query()` for that. What earlier drafts
got wrong is treating structure as the *whole* of specificity — it omits the
subsort-aware step (2), so it cannot distinguish two rules that differ only by
receiver sort.)

**Export consequence — most-specific-first ⇄ exclusion guards.** The override
in the previous paragraph is an *engine ordering* policy; it is implicit. When
the same rules are **exported as plain logical rules** — to the resolver as
unordered candidates, to codegen, or to an external solver — there is no
ordering: *every* conforming rule fires. Since `A <: B <: C`, the rules on `B`
and `C` also match an `A`-object, so they would wrongly handle the `A` case too.
To preserve the override in a flat rule set, **synthesize exclusion guards** on
the less-specific rules, *per goal*:

- rule on `A` (most specific for this goal): no exclusion;
- rule on `B`: `:- not (min_sort(receiver) <: A)`;
- rule on `C`: `:- not (min_sort(receiver) <: B)` — which excludes `A` too,
  since `A <: B`.

Each less-specific rule excludes the subsort already handled by the
next-more-specific rule **for the same goal** (sorts that don't redefine the
goal add no exclusion). This turns the engine's *ordered* override into an
equivalent *unordered* rule set. The exclusion guard is itself
`min_sort`/subsort-based, so it is an ordinary expression-level guard (§4.2) —
the same machinery, made explicit at export. (This is also *why* structural
discrim alone is insufficient: the override is not a structural fact, so it
survives export only as a guard.)

### 4.7 One rewriter over expressions — not "two phases"

Earlier drafts framed this as "a `[simp]` rule fires in two phases that must
agree." **Dropped.** There is **one** rewriter over **expressions** (§4.1),
invoked wherever an expression is held — the typer over operation bodies, the
resolver over goal terms. Both invocations run the same matcher + strategy over
the same rule set, so consistency is **structural**, not an obligation to
police. The only true boundary is **expression vs value**: simp rewrites
expressions; once an expression has been **evaluated to a value** there is
nothing to rewrite. `min(3, 5)` simplifies identically as an *expression*
(whether it sits in an op body or a goal term); the value `3` it evaluates to is
outside simp's domain. So there is no "phase agreement" obligation — only the
expression/value boundary.

---

## 5. Using the engine directly — compile-time simplification *(no dot)*

A user tags equational rules `[simp]`; the engine rewrites matching
**expressions** in operation bodies at compile time (§4.1). The rules are
ordinary data — the same set the resolver rewrites goal-expressions with — and
tooling can read both directions (forward to rewrite, inverse to enumerate).

```
-- algebraic identities and a domain law, tagged for compile-time rewriting
rule add_zero:        add(?x, 0) <=> ?x                      [simp]
rule mul_one:         mul(?x, 1) <=> ?x                      [simp]
rule mul_zero:        mul(?x, 0) <=> 0                       [simp]
rule double_neg:      neg(neg(?x)) <=> ?x                    [simp]
rule double_transpose: transpose(transpose(?m)) <=> ?m      [simp]   -- a user/domain law

operation residual(v: Vector, k: Int64) -> Vector
  add(mul(v, k), mul(v, 0))      -- typer rewrites at compile time → mul(v, k)
end
```

**These are type-directed, not guard-free.** `add`/`mul`/`neg` are *sort*
operations (`Numeric.add`, …), so each rule carries its sort's `requires
Numeric[T]` **implicitly**, and the rule's `add` matches a concrete `Int64.add`
only via the satisfaction relation — both need the operand's type (§4.1).
`double_transpose` is likewise type-directed if `transpose` lives in a `Matrix`
sort. A *genuinely* guard-free rule would be one over a **top-level concrete
functor** with no enclosing-sort `requires` — uncommon.

What these rules *do* have is **structural termination** — each RHS is no larger
than its LHS, so no fuel is needed (§4.5). That is about RHS *size* and is
independent of the guard being type-directed; do not conflate the two (the
earlier draft wrongly called them "guard-free" on the strength of structural
termination).

The user gets declarative compile-time simplification, as ordinary rules. A
commutative law must stay bare (§4.5); overlapping redexes follow the
specificity policy (§4.6). `dot_apply` (§6) is just one more functor a `[simp]`
rule can target.

---

## 6. Client A — method-call (dot) syntax  *(the first packaged client)*

Dot is one client of the type-directed engine (§4): `dot_apply` is a functor,
and dispatch rules are sort-scoped, `requires`-guarded `[simp]` rules fired in
the typer (where `min_sort` is in hand). Gives `?xs.map(?f).filter(?p)` instead
of `filter(map(?xs, ?f), ?p)`, and lets a sort customize its own dispatch (a
custom `Either.map`) by declaring a rule on itself (§4.6).

### 6.1 The `dot_apply` node

A new `Expr` variant (reflect `Expr` constructor, snake_case, sibling to `apply`):

```
entity dot_apply(receiver: ExprOccurrence, name: Symbol, args: List[ApplyArg])
```

The surface `.` does not appear in rules (you can't define `.` with `.`); the parser lowers `?x.foo(?y)` to `dot_apply(?x, foo, [?y])`, a distinct node — **not** desugared to `apply(foo, [?x, ?y])`, whose functor would re-resolve through lexical scope and reintroduce the import requirement that dot dispatch eliminates (§6.4).

### 6.2 Parser & converter

The grammar already parses `?x.y` and `?x.y(args)` — **no grammar change**. The converter (`parse/convert.rs`) emits `dot_apply(receiver, name, args)` when the receiver is a **value** (`variable`), for both the bare `?x.field` form (args empty) and the call `?x.method(args)` form. Sort/namespace receivers (`Foo.bar`, `Map[K=…].empty()`) keep today's qualified-name flattening. This fixes the current gap where `?x.method(args)` drops the receiver in `collect_field_access_segments` (`convert.rs:342`, no `variable` branch).

### 6.3 Dispatch rules (shipped in the prelude)

Guards use `min_sort` (the receiver's least declared sort, §4.2) and the
expression-accepting builtins `is_entity`/`has_field`/`find_operation_on_sort`
— not a `typeof` *goal*, which does not exist.

```
rule dot_field: dot_apply(?x, ?name, []) = field_access(?x, ?name)
  :- is_entity(min_sort(?x)), has_field(min_sort(?x), ?name)
  [simp]
```

- `dot_field` → entity receiver, declared field, no args → the existing
  `field_access` builtin (`kb/resolve.rs:1975`), unchanged. Fully writable.
- **Sort-specific rules** (the extensible case) are ordinary writable rules with
  a **concrete** RHS, declared on the sort and fired by conformance + specificity
  (§4.6):

  ```
  -- in sort Either:
  rule either_map: dot_apply(?e, map, [?f]) = either_map(?e, ?f)   [simp]
  ```

  Its sort scope (`Either`) is the implicit guard; it outranks the default for
  `Either` receivers.

- **The global default** is the catch-all "resolve `name` to an op on
  `min_sort(?x)`." Its result functor is *dynamically resolved* (`?op`), so a
  literal rule `dot_apply(?x,?name,?args) = ?op(?x,?args)` has a
  **variable-functor RHS** and is **not a writable term**. Two ways to express
  it (open choice):
  - **engine fallback logic** — the engine builds `apply(op, [receiver, …args])`
    directly when no sort-specific rule applies; or
  - an **`apply_op(?op, [?x | ?args])` builtin** that applies a resolved op
    symbol to args, making even the default a writable rule:
    `default_dot: dot_apply(?x,?name,?args) = apply_op(?op, cons(?x, ?args)) :- find_operation_on_sort(min_sort(?x), ?name, ?op) [simp]`.

  `apply_op` makes the *whole* dispatch data (LSP/tooling read it uniformly); the
  engine-logic option is less surface area. (See §6.4 for what
  `find_operation_on_sort` resolves over.)

### 6.4 Type-directed resolution — `find_operation_on_sort`

A method call must **not** require importing the operation: `?l.map(?f)` works whenever `?l` is a `List`, with no `import …map` — found via the receiver's sort, not lexical scope. KB query `find_operation_on_sort(sort, name) -> op` (qualified), resolving in this order, all subsort-aware (§4.6 step 2 — a method on a supersort applies):

- **Tier 1 — the sort's own operations** (`length`, `map` in `enum List`): reachable with **no import**; the qualified op name is returned so the rewritten `apply` references it directly. The defining property.
- **Tier 1b — operations of specs the sort *satisfies*** (`?n.min(?m)` for `n: Int64` → `Ordered.min`, because `fact Ordered[Int64]`). This is the headline `requires`-typeclass case and must be covered; today the WI-240 `sort_ops` table covers user `fact Spec[ImplSort]` impls but **not** builtin satisfaction like `Int64 → Ordered` — a gap to close (WI-281).
- **Tier 2 — extension operations** elsewhere whose first param matches the sort: normal import rules (Rust trait / Scala 3 extension style).

Resolution walks the receiver's sort and its supersort/satisfied-spec chain (most-specific first), so an operation on a supersort or a satisfied spec is found, mirroring the rule-firing conformance of §4.6.

### 6.5 Errors & deliverable

Neither rule fires → "no field or method `name` on sort `S`", at the source span. Deliverable: chaining (`xs.map(f).filter(p)`), field access (`p.x`) via the unified path, no-import method resolution, clear errors, byte-identical behavior for `Foo.bar` / `?x.field`-as-field.

### 6.6 Type parameters and `requires` clauses

The rewrite produces an **ordinary** `apply(op, [receiver, …args])` with no explicit type arguments. It is then type-checked and requirement-elaborated by the *same* machinery as a hand-written call — there is **no dot-specific path**:

- **Type parameters** infer as usual. `?xs.map(?f)` → `map(?xs, ?f)`: with `xs: List[Int64]` and `map[T, U](xs: List[T], f: T -> U) -> List[U]`, the receiver's type argument pins `T` through the **first parameter** (`T = Int64`), and `?f` pins `U` — exactly as for a written `map(xs, f)`. The rewrite threads no type arguments explicitly; the receiver is just the first argument, and `T` flows in through it.
- **`requires` clauses** play **two distinct roles** — don't conflate them:
  1. **Selection guard.** A sort-scoped dot rule (and `find_operation_on_sort`'s
     Tier-1b) *uses* `requires`/conformance to decide it applies: `Either.map`
     fires because `min_sort(?e) <: Either`; `Ordered.min` resolves for `Int64`
     because `Int64` satisfies `Ordered`. This is part of matching/selection (§4.6).
  2. **Downstream check.** The *produced* `apply(op, [receiver, …args])` is then
     requirement-elaborated by `req_insertion`, which runs *after* the rewrite,
     exactly as for a hand-written call. `?a.min(?b)` → `min(?a, ?b)` typechecks
     iff `min_sort(?a)` satisfies `min`'s `requires Ord[T]`; an unsatisfied
     requirement is a genuine "sort `S` does not satisfy `Ord`/`Eq`" error at the
     dot-call span via the `Synthesized` chain. **Typeclass dispatch falls out**
     of the existing requirement machinery — no dot-specific logic.

This holds because the rewrite completes **before** the produced apply is type-parameter-inferred, classified, and requirement-elaborated (see the impl design's pipeline placement). **Open question (D6):** should `find_operation_on_sort` be *requirement-aware* at selection (role 1) — early/precise "no `Ord` for `S`" and overload disambiguation — or resolve by name+sort and let the produced apply's `requires` check (role 2) report downstream? Lean: name+sort for resolution, `requires` checked downstream (reuses the existing error path) — but note Tier-1b (specs the sort satisfies) already needs *some* conformance at selection, so the two roles are not fully separable.

---

## 7. Client B — value-conditional simp (`min`)  *(sketch)*

Adds compile-time partial evaluation on the same engine:

- **`constant_fold(?const, ?source)`** — the single occurrence→value bridge: at compile time binds `?const` to `?source`'s literal value if it folds, else **STUCK** (→ residualize); at runtime, identity. The only occurrence-aware value builtin; every other value op stays occurrence-unaware.
- **STUCK** (non-constant operand) ≠ DELAY (unbound logical var): the rule doesn't fire, the call is left for runtime.
- Value rules, e.g. `min_le: min(?x,?y) = ?x :- constant_fold(?xc,?x), constant_fold(?yc,?y), compare(?xc,?yc) <= 0 [simp]`. (A **guarded** equational head keeps `=`, not `<=>`: the `=`→`<=>` migration is scoped to empty-body `is_equation` heads, and a `:- guard` body excludes this rule — proposal 049 / the indexing note in §4.2.) `min(3,5) → 3` folds as an *expression* (§4.1); `min(?age,?thr)` residualizes and is rewritten by the *same* rules whenever it is later processed as an expression during resolution — one rule set, one rewriter, no separate phase (§4.7).

## 8. Client C — symbolic AD (`diff`)  *(sketch)*

`diff` is a plain operation over `Expr`, defined by `[simp]` rules (rules tagged, operation not). Recursive rewriting to fixpoint (§4.5 fuel); `[unfold]` at the typer phase to inline bodies before pattern-matching; firing specificity (§4.6). Pure structural rewriting — never STUCKs. The §5 arithmetic-cleanup rules (`mul_zero`, `add_zero`, …) normalize `diff`'s output. Reverse-mode / tensor AD need codegen, not rewriting — out of scope.

---

## Scope / layering

- **Shippable:** the engine core in its type-directed, structurally-terminating regime (§4 minus fuel/STUCK), exercised by **§5 (direct simplification)** and **§6 (dot)**. This is the deliverable.
- **Later, same engine:** value-conditional firing (`constant_fold`/STUCK, fuel, residualization) for Clients B/C.

## Implementation

See `docs/design/simp-rewrite-design.md`. In brief: extend `TermView` so `Value::Node` is structural (today opaque) so rule LHSs can match Expr occurrences; add an occurrence build/rewrite side (spans/`Synthesized` preserved); a typer-phase rewriter that walks op bodies bottom-up and writes them back before req_insertion/eval/IR. The substrate change (structural `Value::Node`) is a prerequisite WI.

## Open questions

- **Scope of a simp set** — global / per-namespace / transitive `requires` / named sets. 025.1 deferred it; the typer phase reraises it (expression bodies cross namespaces). Especially live now that §5 invites *user-authored* simp rules across the codebase.
- **`[unfold]` at the typer phase** — when does a tagged op expand (always / inside a simp context / when reached by a firing rule)? (Client C.)
- **`constant_fold` power** — literal arithmetic only / ground resolution / full SLD. More power ⇒ more folding, tighter termination.
- **Termination policy** — reject vs warn vs trust on detectably non-terminating `[simp]` tags (§4.5).
- **`self` marker** — redundant for dispatch under this design; keep as doc/codegen hint or drop? Lean: drop.
- **Symmetric ops** (`merge`, `concat`) enter `.` dispatch and bias the receiver — live with it, or opt-out marker?
- **Delegation** (wrapper auto-peel: `Either`/`Option`/`Rc`) and **DSL dispatch** — later layers; delegation graph must be a DAG (load-time cycle check).
- **Identifier-receiver disambiguation** — `Foo.bar` where `Foo` is value-or-sort; Client A keeps the qualified-name path.

## Non-goals

- No grammar change (`.` already parses).
- No new "macro" concept; `[simp]`/`[unfold]`/`[hint]` syntax stays as WI-139.
- Not replacing `field_access` (reached via `dot_field`, builtin unchanged).
- Not the Z3-side translation of simp rules (025.1's separate deferral), nor bidirectional simp (LHS→RHS only in the typer phase), nor side-effecting expansion (rules are pure).
