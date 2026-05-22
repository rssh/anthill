# Finding: the `[simp]` rewriting engine is type-directed; dot dispatch is one of its clients

Status: **settled 2026-05-22** (with user). Corrects proposal
`docs/proposals/043-simp-rewrite.md` §4/§5/§6 and
`docs/design/simp-rewrite-design.md` §5.4/§7.1.

## The error

Proposal 043 §5 frames the `[simp]` engine as *independent of the typer* — "the
type-checker rewrites matching expressions … **no `typeof`** — just structural
rewriting of the user's own functors." **Independence from the typer is the
error.** The engine is **type-directed** and must run **with the typer**.

## Why

A rule fires by matching its LHS and checking its guard. **A rule's guard is its
explicit `:- …` *plus* the `requires` of its enclosing sort** — a rule defined
inside a sort inherits that sort's `requires` *implicitly*. So even
`add_zero: add(?x, 0) = ?x` (no explicit guard) is type-directed when it lives
in `Numeric`: it carries `requires Numeric[T]`, and its `add` is `Numeric.add`,
matching a concrete `Int.add(x,0)` only via the satisfaction relation. The
**only** genuinely guard-free / type-independent rules are **top-level rules
over concrete functors** with no enclosing-sort `requires` — rare. The trivial
`transpose(transpose(?m)) = ?m` is type-free *only* if declared at top level
over a concrete `transpose`; inside a `Matrix` sort it too is type-directed.

The rules that matter are defined **in specs/sorts**:

```
Numeric:  add_identity:  add(?a, 0) = ?a                  -- requires Numeric[T]
Ordered:  min(?a, ?b) = ite(lte(?a, ?b), ?a, ?b)          -- requires Ordered[T]
```

The rule's `add` is `Numeric.add`; a real term is `Int.add(x, 0)` — a
**different symbol**. The rule matches only if `Int` *satisfies* `Numeric`, and
its `requires` holds only if the type satisfies it. **Both need the type.** So
firing spec/sort rules is type-directed — it *cannot* be done independent of the
typer. Type-independent firing covers only trivial monomorphic identities.

## Consequences

1. **One type-directed, guard-aware engine, integrated with the typer.** Firing
   = structural LHS match (`TermView`) + a guard check that, for sort/spec
   rules, uses the type (sort satisfaction, `requires`) — known only in the
   typer.
2. **Dot dispatch is one of its clients**, the same shape as a spec/sort rule: a
   sort-scoped, `requires`-guarded rule (e.g. a custom `Either.map`). 043's "dot
   is a `[simp]` client" thesis is right.
3. **`typeof` is not a goal.** It is **`min_sort`** — widen a term to its least
   declared sort (`= sort_head(TypeResult.ty)`; `sort_functor_of` already
   extracts it). A compile-time typer notion the engine uses to *select and
   guard* sort-scoped rules. Not a runtime op, not a rule goal.

## The two concrete errors in 043 to fix

- **§4/§5** — "engine is type-independent / has no `typeof`": false; it is
  type-directed (the type-free claim holds only for trivial monomorphic
  identities).
- **§6.3** — `typeof(?x)` written as a guard *goal*, and `default_dot`'s
  `?op(?x, ?args)` variable-functor RHS: neither is writable. The `typeof`
  "guard" is the engine selecting rules by `min_sort`; the global default is
  engine fallback logic, not a rule.

## Status of the work

- **Guards are missing in both firing sites today** — `apply_eq_rules`
  (`resolve.rs:1410`) and `simp_rewrite`, both gated by `is_equation` (empty
  body). So `requires`-guarded spec/sort rules fire **nowhere** — incomplete,
  and unsound if a guard-free firing rewrites where the requirement is unmet.
  Adding type-directed guard evaluation, in the typer, is the core work:
  **WI-283** (the engine), with **WI-279** (dot firing) as a client.
- The `Expr::DotApply` substrate + converter (b) are kept. The reverted WI-278
  (c)/(e) increment was wrong because it ran *before* the typer with a
  reconstructed flat env — i.e. it tried to be typer-independent, the very error
  above.
