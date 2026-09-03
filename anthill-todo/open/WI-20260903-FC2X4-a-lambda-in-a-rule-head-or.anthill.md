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

