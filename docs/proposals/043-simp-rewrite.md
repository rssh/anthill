# Proposal 043 — The `[simp]` rewriting engine

## Status: Proposal — for review.

The `[simp]` attribute (WI-139) marks an equational rule as directionally rewritable. Today that has one consumer: the SLD resolver's equational fallback, over runtime `Term`s. **This proposal gives `[simp]` a second firing site — the type-checker, over expression-position occurrences — turning tagged equations into compile-time rewrites.** The engine is the language feature; user-authored compile-time simplification (§5) is its most direct use, and method-call (dot) syntax (§6) is its first packaged client.

## Relates to

- `docs/design/simp-rewrite-brainstorm.md` — the design exploration this proposal distills (rationale, tooling/LSP, delegation, worked examples).
- `docs/design/simp-rewrite-design.md` — the rustland implementation design (one rewriter run in two phases, sharing the `TermView` matcher; substrate audit; build order). This proposal is the *semantics*; that doc is the *how*.
- **WI-139 (delivered)** — `[simp]`/`[unfold]`/`[hint]` attributes (`anthill-core/tests/include/equational_attr_test.rs`).
- **Proposal 025.1** (Z3 tactic DSL) — deferred the Z3-side translation of simp rules and their scope semantics; this proposal addresses a *different* deferred firing site (the typer), not the Z3 one.
- `docs/design/occurrence-as-value-type.md` — `NodeOccurrence` / `Value::Node` substrate. `docs/design/interpreter-ir.md` — downstream consumer (equation-defined operations).
- `docs/kernel-language.md §9` — `rule head :- body` is derivation, `rule lhs = rhs` is equation (Maude analogy).

## Goal

Make a `[simp]`-tagged equation `lhs = rhs` fire **as a rewrite during type-checking**, not only during proof/runtime resolution. The same rule then has two roles — runtime simplification (existing) and compile-time elaboration (new) — and must behave identically in both (§4.7). The feature stands on its own (§5); on top of it, three surface features fall out as library rules: method dispatch (§6), compile-time folding (§7), and symbolic rewriting (§8). No new kernel concept: the kernel does **not** grow a "macro" — `[simp]` rules are ordinary equational rules with a second firing phase.

---

## 4. The engine (semantics)

### 4.1 A `[simp]` rule and its two firing sites

A `[simp]` rule is an equation (head `eq(LHS, RHS)`, empty body) tagged so it is **directionally rewritable** (LHS→RHS). WI-139 keeps such rules indexed in `by_functor`. The engine fires them to normal form at **two sites**:

- **Resolver / `Term` (exists):** the equational fallback rewrites runtime terms during SLD resolution.
- **Type-checker / `NodeOccurrence` (this proposal):** as the typer walks an operation body, applicable `[simp]` rules rewrite expression-position content.

Both sites are the *same rewrite relation*; the design doc realizes them as one rewriter run in two phases — a shared matcher and strategy, differing only in what each phase constructs for the rewritten result (a `Term` vs a `NodeOccurrence`). **A `[simp]` rule may target any functor** — `add`, `transpose`, `min`, `dot_apply`, a user's domain constructor — not a privileged set. That generality is the feature; the clients (§6–§8) are just rule libraries over particular functors.

### 4.2 What pattern variables bind to

In the typer phase a rule's pattern variable binds to the **reflect `Expr`/`Node` occurrence** at that position — a syntax object, not an evaluated value (`Value::Node(Rc<NodeOccurrence>)`). Three queries over that binding:

- **Structural:** `?x = add(?a, ?b)` destructures the occurrence's `Expr`.
- **Type:** `typeof(?x)` reads the occurrence's inferred type. (Implementation note: this is *not* the occurrence's `classification` — that field holds dispatch info, not the type; see design doc §3. The type comes from the typer's result for that subtree.)
- **Metadata:** span, owner, `origin`.

Carried-over subterms keep their type: when `?x.map(?f)` rewrites to `map(?x, ?f)`, `?x` retains its sort (intrinsic to the value, not its syntactic position). The typer type-checks the constructed output; a reused subterm that conflicts with its new position is a genuine type error, reported via the `Synthesized` chain to the source span.

### 4.3 Firing model

Bottom-up: the typer classifies children first, then, at a node whose children are typed, queries `by_functor` for `[simp]` rules whose LHS matches; matches the LHS, evaluates the guard (if any), and on success synthesizes the RHS as a fresh occurrence (`origin: Synthesized { from, by }`), re-typing it (which may trigger further rewrites — chains, cascades).

### 4.4 Reduction strategy — leftmost-innermost (forced)

For `p(p(?x, ?y), ?z)` a type-directed outer rule can't fire until `typeof(p(?x, ?y))` is known, which requires reducing+typing the inner term first. So type-directed dispatch and innermost reduction are the same constraint, and it matches both the typer's walk and the resolver's existing strategy. Consequence: strict, no lazy discard (a looping discarded subterm still hangs the rewrite). Future escape hatch: Maude-style per-operator `strat`/`frozen`.

### 4.5 Termination

- **Structural** where the LHS functor cannot reappear in the RHS, or the RHS is strictly smaller (`add(?x, 0) = ?x`; `dot_apply → apply`). No machinery needed.
- **Fuel-bounded** for value-conditional and recursive rules (AD, `min` algebra). Commutative / associative-commutative laws (`add(?a,?b)=add(?b,?a)`) must stay **bare** (non-`[simp]`) or the phase loops. Plus a `Synthesized.from` ancestor-loop check. Open: should the loader reject a `[simp]` tag on a detectably non-terminating rule (LHS≡RHS, args permuted)?

### 4.6 Firing specificity

When several rules match one redex (`diff_scale` vs `diff_mul` on `mul(3, x)`), the engine fires the **most specific** matching rule first, in the order the **discrimination tree** already yields: concrete-edge matches before variable-edge matches (`discrim.rs` `query_node`). Fixed for the engine, not per client.

This is not new machinery — it is exactly how the resolver phase already fires equations: `apply_eq_rules` (`resolve.rs`) builds `eq(redex, ?result)` and calls `query()`, which walks the discrimination tree most-specific-first and takes the first match. The typer phase's `try_fire` (`kb/simp_rewrite.rs`) currently does a `by_functor(eq)` linear scan with accidental first-match; it is brought onto the same `query()`-ordered lookup, which both fixes specificity and makes §4.7 phase-agreement structural (one lookup, both phases).

**Consequence for sort-specific vs global rules.** A rule's specificity *is* its placement in the tree, so "global" and "sort-specific" are not a dichotomy and need no separate mechanism:

- A **global** rule with an all-variable LHS (`default_dot: dot_apply(?x, ?n, ?args)`) sits on the variable edges — the **total fallback**, tried last.
- A more **specific** rule — `dot_field: dot_apply(?x, ?n, [])` (concrete `nil` args), or a **sort-specific** rule with a concrete name and/or a sort-discriminating guard — sits on concrete edges and is tried first.

So a sort customizes its own dot behavior simply by declaring a more-specific `[simp]` rule (or a sort-guarded one); it always outranks the total global rule, and "global rules are total" is precisely what makes them the safe catch-all.

### 4.7 Phase-agreement invariant

A `[simp]` rule fires in **both** phases. They **must** agree: same reduction strategy (§4.4), same constant/non-constant boundary (§7), no semantic drift. The design doc makes this structural by sharing the matcher + strategy core across both phases; here it is the normative requirement. (For pure dispatch rules the runtime phase is vacuous — `dot_apply` terms don't exist at runtime and the guard needs `typeof` — so agreement is trivially satisfied; it bites only for value rules like `min`.)

---

## 5. Using the engine directly — compile-time simplification *(no dot)*

The engine is a feature in its own right, independent of any client. A user tags equational rules `[simp]`; the type-checker rewrites matching expressions in operation bodies at compile time. No `dot_apply`, no method syntax, no `typeof` — just structural rewriting of the user's own functors.

```
-- algebraic identities and a domain law, tagged for compile-time rewriting
rule add_zero:        add(?x, 0) = ?x                       [simp]
rule mul_one:         mul(?x, 1) = ?x                       [simp]
rule mul_zero:        mul(?x, 0) = 0                        [simp]
rule double_neg:      neg(neg(?x)) = ?x                     [simp]
rule double_transpose: transpose(transpose(?m)) = ?m       [simp]   -- a user/domain law

operation residual(v: Vector, k: Int) -> Vector
  add(mul(v, k), mul(v, 0))      -- typer rewrites at compile time → mul(v, k)
end
```

These are **guard-free, structurally-decreasing** rewrites: they match `Expr` structure (`mul(?_, 0)`, `transpose(transpose(?_))`), need no `typeof` and no value folding, and each RHS is no larger than its LHS — so they fire in the shippable engine core (§4 minus fuel/STUCK) and terminate structurally (§4.5). The user gets declarative compile-time simplification / known-identity elimination, expressed as ordinary rules that:

- the resolver **also** runs at runtime (§4.7) — one rule set, two phases;
- tooling can read **both directions** (forward to rewrite, inverse to enumerate) because they are data, not callbacks.

Caveats this surfaces are the **engine's**, not any client's: a commutative law must stay bare (§4.5), and overlapping redexes follow the specificity policy (§4.6). This is precisely why the engine — not dot — is the proposal's subject: `dot_apply` is just one functor a `[simp]` rule can target. Everything in §6–§8 is a rule library over this one mechanism.

---

## 6. Client A — method-call (dot) syntax  *(the first packaged client)*

Type-level guards only, structurally terminating. Gives `?xs.map(?f).filter(?p)` instead of `filter(map(?xs, ?f), ?p)`.

### 6.1 The `dot_apply` node

A new `Expr` variant (reflect `Expr` constructor, snake_case, sibling to `apply`):

```
entity dot_apply(receiver: ExprOccurrence, name: Symbol, args: List[ApplyArg])
```

The surface `.` does not appear in rules (you can't define `.` with `.`); the parser lowers `?x.foo(?y)` to `dot_apply(?x, foo, [?y])`, a distinct node — **not** desugared to `apply(foo, [?x, ?y])`, whose functor would re-resolve through lexical scope and reintroduce the import requirement that dot dispatch eliminates (§6.4).

### 6.2 Parser & converter

The grammar already parses `?x.y` and `?x.y(args)` — **no grammar change**. The converter (`parse/convert.rs`) emits `dot_apply(receiver, name, args)` when the receiver is a **value** (`variable`), for both the bare `?x.field` form (args empty) and the call `?x.method(args)` form. Sort/namespace receivers (`Foo.bar`, `Map[K=…].empty()`) keep today's qualified-name flattening. This fixes the current gap where `?x.method(args)` drops the receiver in `collect_field_access_segments` (`convert.rs:342`, no `variable` branch).

### 6.3 Dispatch rules (shipped in the prelude)

```
rule default_dot: dot_apply(?x, ?name, ?args) = ?op(?x, ?args)
  :- find_operation_on_sort(typeof(?x), ?name, ?op)   -- ?op fully qualified
  [simp]

rule dot_field: dot_apply(?x, ?name, []) = field_access(?x, ?name)
  :- is_entity(typeof(?x)), has_field(typeof(?x), ?name)
  [simp]
```

- `dot_field` → entity receiver, declared field, no args → the existing `field_access` builtin (`kb/resolve.rs:1975`), unchanged.
- `default_dot` → method dispatch otherwise.
- Guard-exclusive; field-first on collision (optional load-time lint). `is_entity`/`has_field` answerable from the `entity_fields` registry.

### 6.4 Type-directed resolution — `find_operation_on_sort`

A method call must **not** require importing the operation: `?l.map(?f)` works whenever `?l` is a `List`, with no `import …map` — found via the receiver's sort, not lexical scope. New KB query `find_operation_on_sort(sort, name) -> op` (qualified):

- **Tier 1** — operations in the sort/enum body (`length`, `map` in `enum List`): reachable with **no import**; the qualified op name is returned so the rewritten `apply` references it directly. The defining property.
- **Tier 2** — extension operations elsewhere whose first param matches the sort: normal import rules (Rust trait / Scala 3 extension style).

### 6.5 Errors & deliverable

Neither rule fires → "no field or method `name` on sort `S`", at the source span. Deliverable: chaining (`xs.map(f).filter(p)`), field access (`p.x`) via the unified path, no-import method resolution, clear errors, byte-identical behavior for `Foo.bar` / `?x.field`-as-field.

### 6.6 Type parameters and `requires` clauses

The rewrite produces an **ordinary** `apply(op, [receiver, …args])` with no explicit type arguments. It is then type-checked and requirement-elaborated by the *same* machinery as a hand-written call — there is **no dot-specific path**:

- **Type parameters** infer as usual. `?xs.map(?f)` → `map(?xs, ?f)`: with `xs: List[Int]` and `map[T, U](xs: List[T], f: T -> U) -> List[U]`, the receiver's type argument pins `T` through the **first parameter** (`T = Int`), and `?f` pins `U` — exactly as for a written `map(xs, f)`. The rewrite threads no type arguments explicitly; the receiver is just the first argument, and `T` flows in through it.
- **`requires` clauses** are enforced by requirement-insertion, which runs *after* the rewrite on the produced apply. `?a.min(?b)` → `min(?a, ?b)` succeeds iff `typeof(?a)` satisfies `min`'s `requires Ord[T]`; `?l.contains(?e)` iff the element type satisfies `Eq`. An unsatisfied requirement is a genuine "sort `S` does not satisfy `Ord`/`Eq`" error, reported at the dot-call's source span via the `Synthesized` chain. **Typeclass dispatch falls out** of the existing requirement machinery — no dot-specific typeclass logic.

This holds because the rewrite completes **before** the produced apply is type-parameter-inferred, classified, and requirement-elaborated (see the impl design's pipeline placement). **Open question:** should `find_operation_on_sort` itself be *requirement-aware* — rejecting `?x.min(?y)` early with a precise "no `Ord` for `S`" message, or disambiguating overloads by satisfiable `requires` — or should it resolve by name+sort only and let the produced apply's normal `requires` check report downstream? Lean: name+sort for resolution, `requires` checked downstream (simplest; reuses the existing error path).

---

## 7. Client B — value-conditional simp (`min`)  *(sketch)*

Adds compile-time partial evaluation on the same engine:

- **`constant_fold(?const, ?source)`** — the single occurrence→value bridge: at compile time binds `?const` to `?source`'s literal value if it folds, else **STUCK** (→ residualize); at runtime, identity. The only occurrence-aware value builtin; every other value op stays occurrence-unaware.
- **STUCK** (non-constant operand) ≠ DELAY (unbound logical var): the rule doesn't fire, the call is left for runtime.
- Value rules, e.g. `min_le: min(?x,?y)=?x :- constant_fold(?xc,?x), constant_fold(?yc,?y), compare(?xc,?yc) <= 0 [simp]`. `min(3,5) → 3` at compile time; `min(?age,?thr)` residualizes to a runtime `min` evaluated by the *same* rules via the resolver phase — one rule set, two phases (§4.7).

## 8. Client C — symbolic AD (`diff`)  *(sketch)*

`diff` is a plain operation over `Expr`, defined by `[simp]` rules (rules tagged, operation not). Recursive rewriting to fixpoint (§4.5 fuel); `[unfold]` at the typer phase to inline bodies before pattern-matching; firing specificity (§4.6). Pure structural rewriting — never STUCKs. The §5 arithmetic-cleanup rules (`mul_zero`, `add_zero`, …) normalize `diff`'s output. Reverse-mode / tensor AD need codegen, not rewriting — out of scope.

---

## Scope / layering

- **Shippable:** the engine core in its guard-free / type-level-guard, structurally-terminating regime (§4 minus fuel/STUCK), exercised by **§5 (direct simplification)** and **§6 (dot)**. This is the deliverable.
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
