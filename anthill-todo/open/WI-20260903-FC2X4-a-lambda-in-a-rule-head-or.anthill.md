## Attributes

- id: WI-20260903-FC2X4-a-lambda-in-a-rule-head-or
- created: 2026-09-03T08:34:51Z

- status: Open
- status_agent: user
- status_at: 2026-09-03T08:34:51Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A LAMBDA IN A RULE HEAD OR BODY BUILDS A MALFORMED `Expr::Lambda` — ITS `param` IS A REFLECT `Expr::Apply`, NOT A `NodeKind::Pattern`.

MEASURED on the WI-20260903-FCZ3N tree, and PRE-EXISTING (it is NOT that ticket's doing — the two positions below fail IDENTICALLY, and one of them is a walk FCZ3N never touched):

  namespace zzp3
    import anthill.prelude.{Int64, Function}
    operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)
    rule lamb(1) :- apply1(lambda (x: Int64) -> x + 1, 2) = 3
  end

  -> 1:1: type mismatch in <bottom>.expr: expected surface expression, got bottom / post-elaboration form

The SAME program written as a `[simp]` RHS (`rule lam(?n) <=> apply1(lambda (x: Int64) -> x + 1, ?n) [simp]`) now reports the SAME single error, because WI-20260903-FCZ3N put the RHS on the same walk the rule BODY has always used. Before that ticket the RHS went through the head TERM instead and reported a DIFFERENT bogus pair — `x.name: expected resolved name, got unresolved`, twice. Both spellings were refusals; the ticket only made them agree, on a defect that is the walk's own.

THE DIAGNOSIS, dumped from `Loader::equation_rhs_occurrence`: `build_body_atom_occurrence` builds the lambda as

  Lambda { param: <Expr::Apply(reflect var-pattern form) over Ident(x)>, body: ... }

`Expr::Lambda.param` is supposed to be a `NodeKind::Pattern` occurrence (that is what `for_each_pattern_child` / `reassemble_pattern` and the typer's binder scoping read). The reflect-form arm of the walk builds an `Expr` node for it instead, so the parameter never becomes a binder and the body's `x` has nothing to bind to. Both the `1:1` location and the `<bottom>` are downstream of that.

ACCEPTANCE. The program above LOADS and `apply1(lambda (x: Int64) -> x + 1, 2)` answers 3, in a rule body AND in a `[simp]` RHS (drive the RHS through a consumer operation and assert the value, not the load). Say which rows fail when the change is backed out. Note that a fixture asserting the CURRENT refusal must not be left behind — it would go red on the fix.

Split out of WI-20260903-FCZ3N, which measured it and does not own it.

## Changes

### 2026-09-03T12:22:39Z — feedback — claude

THIS TICKET'S FIX MAKES A SECOND, CURRENTLY-UNREACHABLE DEFECT REACHABLE — `reparent_spliced` DOES NOT REPARENT A PATTERN NODE.

Raised by `/code-review` on WI-20260903-W9D4Z (finding 1 of 4) and MEASURED here rather than taken from the report.

`simp_rewrite::reparent_spliced`'s `Build` arm calls `reparented_from(from, pass, from.owner)` only on the `as_expr()` branch. The `as_pattern()` branch goes through `reassemble_pattern`, which rebuilds with `occ.owner`, and the fallback branch is a bare `Rc::clone`. So a spliced PATTERN keeps the RULE's owner (`None`, as the loader builds body atoms) while its sibling `Expr` nodes get the REDEX's — the exact silent move `NodeOccurrence::reparented_from`'s own doc says a `self.owner` default would cause, "quietly under readers in `typing` and `resolve` that ask which declaration a node sits in". The term path it replaced (`subst_visit`'s `synthesized_expr(expr, from, pass, from.owner)`) gave every node the redex's owner, so this is a behaviour change WI-20260903-FCZ3N introduced, not a pre-existing gap.

IT IS NOT DRIVABLE TODAY, MEASURED: a probe on both non-`Expr` branches, run over the whole `wi_tests` binary (4 073 tests), records ZERO hits. Nothing in the corpus puts a `NodeKind::Pattern` inside a fired `[simp]` RHS — because of the defect THIS ticket is about: the lambda's `param` is built as a reflect `Expr::Apply`, never a `Pattern`, so the pattern branch has nothing to reach it with.

WHICH IS WHY IT BELONGS HERE. The moment a lambda in a rule head or `[simp]` RHS builds a real `NodeKind::Pattern`, that branch starts being taken — and it will hand the typer a parent and child that disagree about which declaration they sit in. So this ticket's acceptance owes one more row than it currently states: after the fix, a `[simp]` RHS carrying a lambda, spliced at a redex, must have its PATTERN node carry the redex's owner like its `Expr` siblings. A `debug_assert` or an owner comparison at the splice is enough to pin it; the branch cannot be tested before the lambda fix lands, which is exactly the ordering that would let it ship unnoticed.

