## Attributes

- id: WI-20260903-H054K-a-rule-variable-in-a-type
- created: 2026-09-03T09:29:43Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-03T20:34:50Z

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

## Changes

### 2026-09-03T20:34:42Z — feedback — user

DELIVERED as answer (a): the leaf reads sigma CARRIER-NEUTRALLY and asks what TYPE the
binding denotes. `SubstTypeRewrite::term` is now `node_occurrence::subst_type_term` --
`apply_subst`'s own `Fn` walk with one arm changed.

THE TICKET'S TABLE, closed. The VARIABLE row answers 1, in the same sentence as the other
two: `type mismatch in put.key (op-arg): expected Bool, got String`.

WHAT THE TICKET DID NOT KNOW, and it is the half that took the work. The obvious repair --
compose the KB's carrier-neutral sigma (`reify`) with the occurrence->term boundary
(`try_occurrence_to_term`) -- is wrong TWICE, both measured:
 1. `reify` answers with a `Value::Entity`, and a `Value::Entity` in a TYPE position is a
    carrier the type layer does not read (`resolved_type_is_ground_g`'s `_ => false`), so
    the check is SKIPPED and the row stays at ZERO. Delivering the binding on a carrier
    every reader skips only moves the drop.
 2. `try_occurrence_to_term` answers "is there a GOAL-TERM shape", which is strictly wider
    than "does this denote a TYPE". A call, a value parameter and a list literal all
    arrived as ground PSEUDO-TYPES and were named -- `expected idk`, `expected
    var_ref[name = s]`, `expected ListLiteral` -- two of them leaking the reflect encoding.

ANSWER (b) IS REFUSED BY A ROW, not by argument: implemented, it falsely refuses
`Map[K = ?k]` fired at `mkr(String)` with a String key. That row also DRIVES the feature
(`dr()` evaluates to `Int(1)`). (b) survives only as the residue: a binding that denotes no
type becomes a GROUND `bottom`, so it is CHECKED rather than skipped. Censused at the arm
through a file the harness cannot capture (an `eprintln` reads ZERO -- libtest swallows a
test's stderr, and the first cut of this census believed it): 5 hits across 36 binaries and
6 376 tests, all five the new file's own.

TWO /code-review PASSES, both of which found something no fixture would have. The second
found that a TUPLE type reached through the variable was FALSELY REFUSED while its ground
twin loaded clean -- a structural type has no nominal name, so it never arrives classified.
A ground-vs-variable census over every writable type shape found the named and nested
tuples beside it and is now a row; the only disagreement left is the arrow, refused at the
PARSER before sigma sees it.

DECLINED, with the measurement: an UNBOUND type-position variable keeps its variable. In a
VALUE position that is malformed (`bottom_out_unbound`); in a TYPE position it is the
spelling for an UNCONSTRAINED slot, and all three ground spellings load clean, so the rule
spelling loading clean is AGREEMENT.

BLAST RADIUS, re-censused past the ticket's "0 of 21": axis 1 backed out fails EXACTLY 4
ROWS of 4 084 over the whole `wi_tests` binary, all four in the new file; axis 2 fails 2.
Channels: only `recv_type` is drivable from a `[simp]` RHS -- the `type_args` bracket is
refused at load there (BAD3V) and a row pins that refusal.

