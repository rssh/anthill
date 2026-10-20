## Attributes

- id: WI-20261020-VQPRP-a-free-variable-read-as-a
- created: 2026-10-20T07:56:47Z

- status: Open
- status_agent: user
- status_at: 2026-10-20T07:56:47Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A FREE VARIABLE READ AS A VALUE IN AN OPERATION BODY LOADS CLEAN AND DIES AT RUN TIME. MEASURED on 663ac457, the same on 098ce8a9: `operation anyPat(n: Int64) -> Bool = type_admits(?, Int64)`, an operation returning `?`, `some(?)`, `if ? then …`, `case x | ? -> …`, `boom(reason: ?)`, `[1, ?]`, `match ?`, and a relation called as a value with `edge(1, ?)` each load and die "unknown operation: _"; a free named variable dies with its name — `edge(1, ?y)`, "unknown operation: y", and `Boom[Reason = ?t]` with no `t` bound, "unknown operation: t". The typer types a genuinely free `?x` as a fresh type variable, "not a typer-level error" (visit.rs, the `Expr::Var` arm), and nothing after refuses it. WHERE A `?` IS IN USE TODAY AND STAYS SO: a type value's argument, which is an open slot (SQZPQ); a call argument a `@[simp]` rewrite discards (`ite(true, 4, ?)`; `rule firstOf(?a, ?_) <=> ?a @[simp]` called `firstOf(4, ?)`); an in-body proof's `conclude` term (`proof h by derivation conclude neq(n, ?) end`); type positions (`User[S = ?].go1(…)`, `g[A = Bag[T = ?]](5)`, `let x: Option[T = ?] = …`, `lambda (x: Option[T = ?]) -> 4`); and a named variable a parameter or a `let` binds. DECISION TO TAKE WITH THE USER BEFORE IMPLEMENTING: whether a free variable that survives typing in an evaluated position of an operation body is a load error — a value nothing gives — so that the typer's fallback goes. FIX DIRECTION, if so: a walk over the typed, stored body after `@[simp]` rewriting and the type-value frame, as `check_operation_bodies` refuses a rigid read that survives typing, skipping a proof's `conclude` term and every type position. ACCEPTANCE: each measured program refused at load naming the variable; every position above unchanged; back-out measured; full gate green.

