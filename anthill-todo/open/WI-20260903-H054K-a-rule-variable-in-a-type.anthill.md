## Attributes

- id: WI-20260903-H054K-a-rule-variable-in-a-type
- created: 2026-09-03T09:29:43Z

- status: Open
- status_agent: user
- status_at: 2026-09-03T09:29:43Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RULE VARIABLE IN A TYPE POSITION OF A `[simp]` RHS IS NEVER INSTANTIATED — THE TYPER'S FIRE BINDS `Value::Node` AND `apply_subst` IS TERM-WORLD.

MEASURED on the WI-20260903-FCZ3N tree, with `import anthill.prelude.Map.{empty, put, size}` in `zzt`, driven by `size(put(mk(…), "a", 1))` — the mismatch being `"a"` against the receiver's `K`:

| `[simp]` RHS                                  | before FCZ3N | after FCZ3N |
|---|---|---|
| `Map[K = Bool, V = Int64].empty()` (GROUND)   | 0 errors | **1** |
| `Map[K = ?k,   V = Int64].empty()` (VARIABLE) | 0 errors | **0** |
| the same call written directly in an operation body | 1 | 1 |

The GROUND row is FCZ3N's own gain — the term path dropped `recv_type` altogether, so the receiver the author wrote was never checked. The VARIABLE row is UNMOVED, 0 before and 0 after, so this is NOT a regression that ticket introduced; it is a pre-existing silent drop that FCZ3N made visible by fixing its neighbour. Found by `/code-review` on FCZ3N, which graded it high on the belief that FCZ3N opened it — the back-out says otherwise.

THE MECHANISM, traced not read. `simp_rewrite::build_rhs_template` applies σ through `node_occurrence::substitute_occurrence`, whose type-position arm is `subst_value_type` -> `map_value_type` -> `SubstTypeRewrite::term` = `KnowledgeBase::apply_subst`. That function is term-world by design and says so: "a non-`Term` carrier (a `Value::Node`) can't be a `Term` child, so a var bound to one stays the var." The typer's `[simp]` fire binds every rule variable to a `Value::Node` (a redex's children ARE occurrences, WI-246), so the type position keeps the throwaway `fresh` global — which unifies with anything, hence 0 errors on a WRONG program. Dumped: the stored+opened `recv_type` is `Fn{Map, [V = Int64, K = Var(Global(1566))]}` and σ binds `1566` to `Node(TypeValue{Bool})`; the term is byte-identical before and after σ.

WHY IT IS NOT SIMPLY A LOAD REFUSAL. Whether the binding can be represented depends on the REDEX, not on the rule: the resolver's `fire_simp_equation` with a term-bound match WOULD substitute, since `apply_subst` handles a `Value::Term` binding. A load-time refusal therefore over-reaches into a case that works. The decision belongs at the FIRE, where the carrier is known.

TWO CANDIDATE ANSWERS, and this ticket picks one:
 (a) CONVERT a type-shaped `Value::Node` binding (an `Expr::TypeValue` / `Expr::Ref` naming a sort) into the type term it denotes, and substitute. This is the feature working.
 (b) REFUSE AT THE FIRE, naming the variable and the type position, when the binding is not representable there. This is loud-over-silent without inventing a feature.

BLAST RADIUS, censused: **0** of the 21 `[simp]`/`[unfold]` equations in a stdlib load carry a type position (`recv_type` or `type_args`) in their RHS at all, let alone a variable in one. So nothing shipped depends on either answer, and (a) can be taken without a migration.

ACCEPTANCE. The VARIABLE row answers 1, naming the same mismatch the direct-in-an-operation-body spelling names, with the GROUND row and the direct row unchanged at 1. If (b) is chosen instead, the VARIABLE row is a located refusal naming `?k` and the receiver — never 0. Say which rows fail when the change is backed out, and keep `wi_fcz3n_simp_rhs_occurrence_test`'s rows green either way.

Split out of WI-20260903-FCZ3N, which measured it and does not own it.

