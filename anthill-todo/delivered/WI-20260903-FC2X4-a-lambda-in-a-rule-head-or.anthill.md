## Attributes

- id: WI-20260903-FC2X4-a-lambda-in-a-rule-head-or
- created: 2026-09-03T08:34:51Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-04T09:45:02Z

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

### 2026-09-04T09:44:57Z — feedback — user

DELIVERED. A compound expression written in a RULE is now the one the author wrote, in all
five surfaces, and `apply1(lambda (x: Int64) -> x + 1, 2)` answers 3 in a rule body AND in
a `[simp]` RHS.

THE DIAGNOSIS WAS ONE LAYER DOWN FROM THE TICKET'S. `Expr::Lambda.param` being an
`Expr::Apply` is a SYMPTOM: the rule walk did not lower the marker AT ALL. The converter
emits `lambda_expr(param, body)` POSITIONALLY (`alloc_marker_term`), and exactly one walk
reads that layout — `visit_load`, which also scopes the binder. `build_body_atom_occurrence`
had no such arm, so a marker reached `materialize_from_handle_spanned`, whose `visit_fn`
reads the NAMED keys, found none, and filled every slot with `⊥`.

AND THE LAMBDA IS THE LOUD TAIL OF A FIVE-MEMBER POPULATION, not the whole of it. The other
four compound surfaces (`convert::is_expr_body_kind`'s set, admissible in every delimited
value position since WI-20260829-YBBC3) LOADED CLEAN AND ANSWERED — with a ⊥-filled node:

  :- ?y <=> (if 1 = 1 then 10 else 20)              ANSWERS  If{⊥, ⊥, ⊥}
  :- ?y <=> (let a = 5  a + 1)                      ANSWERS  Let{<marker>, ⊥, ⊥}
  :- ?y <=> (match 1 case 1 -> 100 case _ -> 200)   ANSWERS  Match{⊥, branches: []}
  :- ?y <=> (proof q by derivation end 7)           ANSWERS  Proof{⊥}

FOUR PLACES, not one, each measured by backing it out (the matrix is in the test file and
is NOT a diagonal):

  1. LOADER — `Loader::compound_expression_occurrence` routes a MINTED compound-expression
     marker in a rule to `convert_expr_term`, the walk that owns the layout and does the
     binder scoping. Memoized per parse node (a `[simp]` head is walked twice).
  2. TYPER — a binder form is `CallDispatch::BinderForm`: handed WHOLE to
     `type_check_node`, whose `Expr::Lambda`/`Let`/`Match` arms bind the pattern into Γ
     (`bind_and_label_pattern`). This walk has no Γ to extend, so descending typed
     `plus(x, 1)` in an empty environment and reported the binder as an unresolved NAME.
     NOT REACHABLE BEFORE: the body was `⊥`, so there was no `x`.
  3. EVAL — a `Value::Node(Expr::Lambda)` local is callable where it is APPLIED
     (`dispatch_call_with_requirements_inner` → `closure_of_applied_lambda_node`). The
     resolver has no closure arena, so a lambda it proved crosses as an occurrence; the
     callee's `f(n)` looked for a local holding a `Closure` and died
     `unknown operation: apply1.f`.
  4. `visit_load`'s ARROW arm ("a bare `->` is a keyword-less lambda") is an
     OPERATION-BODY reading. In a rule an arrow is a TYPE and the rule side has its own
     scoped reader (`check_bare_arrow_typo`), so firing both told an author writing
     `lambda t -> (t -> t)` that "a lambda needs the `lambda` keyword". Gated on
     `Loader::lowering_rule_compound_expr`; the rule-side reader still refuses a genuine
     typo inside a lambda body, asserted.

THREE OF THOSE ARE `/code-review`'s, and two of its findings were defects I shipped in the
first cut and then MEASURED myself before repairing:

  * A first cut of (2) short-circuited the binder form in `dispatch_calls_in_occ` alone,
    leaving the subtree neither walked NOR typed. An undispatched `Expr::DotApply` inside
    a rule-body lambda then reached eval as a pre-dispatch form —
    `unhandled Expr variant in eval`, a `debug_assert` in debug and a silent 0 in release —
    and every diagnostic inside a binder was lost (`nosuchname` accepted in a rule,
    refused in its operation-body twin). Putting the shape in `call_dispatch_shape`
    instead also restores the pre-scan pairing that function's own comment promises.
  * A first cut of (3) converted at the bridge BOUNDARY, gated on the callee's declared
    parameter type. That gate was needed because a `[simp]` MACRO reaches the same entry
    and reads its lambda as SYNTAX (`guarded_of(r: NodeOccurrence, cond: NodeOccurrence)`)
    — converting unconditionally felled 85 rows across the relation algebra — and it was
    still wrong for a `Function`-typed slot the callee RETURNS rather than applies, which
    handed the resolver an opaque `Value::Closure` where it had had a carryable
    `Value::Node`. Converting at the APPLY needs no gate and moves neither case.

THE FEEDBACK'S SECOND DEFECT IS FIXED AND DRIVEN. `reparent_spliced`'s `Pattern` branch now
takes `from.owner` like its `Expr` siblings (`node_occurrence::reassemble_pattern_at`, which
treats a changed owner as a change so a childless binder is not handed back as the stored
rule's own `Rc`). IT IS NOT DRIVABLE THROUGH A PROGRAM, measured: instrumented over the
whole `wi_tests` binary, `from.owner` is `None` at ALL 542 splice fires — every expression
occurrence the loader builds takes `owner: None`, and `current_owner` reaches TYPE
occurrences only. An end-to-end row would compare `None` with `None` and pass under the
back-out. Driven instead by
`kb::simp_rewrite::tests::a_spliced_pattern_takes_the_redexs_owner`, which varies the
deciding axis directly. (The census also updates the feedback's "ZERO hits" note: after this
ticket the pattern branch IS reached, by the new `[simp]`-RHS-with-a-lambda row.)

WHAT THIS DOES NOT MOVE, deliberately: the TERM carrier. `convert_term` still builds the
positional marker for a fact head, a rule head and a query pattern, so
`fact p(lambda x -> 1)` and a goal `p(lambda x -> 1)` still do not unify — that is
WI-20260829-8VGRW, whose own feedback says the family must move together. Lowering the term
here would move ONE member: `if` has no binder and would start matching, while `lambda` and
`let` alpha-rename per SITE and would not — the asymmetry that ticket exists to avoid.
`wi_ybbc3_compound_expression_positions_test::a_compound_form_in_a_rule_data_position_loads_and_matches_nothing`
is unmoved, verified both ways.

TWO PROGRAMS NOW REFUSED THAT USED TO "LOAD" (both with a ⊥ body, i.e. meaning nothing),
because a binder form is typed with `expected: None` — the enclosing call sits in a rule
DATA slot and WI-1058 deliberately does not type-check one:
`?r <=> apply1(lambda x -> x + 1, 2)` (unannotated: "ambiguous dispatch of Additive.add";
the annotated twin answers 3 and so does the op-body twin) and
`?y <=> (lambda t -> (t -> t))` ("`arrow` … unknown functor"). An unannotated binder whose
body PINS it from its own call is unaffected (wi620's `lambda (x) -> is_pos(x)` loads clean).
Supplying the slot's arrow, and whether an arrow term inside a rule-body lambda is a TYPE,
is WI-20260904-50B2K.

ROWS: `wi_fc2x4_lambda_in_a_rule_test` (9) + `simp_rewrite::tests::a_spliced_pattern_takes_
the_redexs_owner` (1). `wi618_bare_arrow_logic_test::lambda_binder_under_inner_arrow_still_loads`
is the existing row that falls to the arrow axis.

VERDICT: cargo 6403 passed / 0 failed (36 binaries; the test-NAME set diff against the
pre-change baseline is exactly +10 new, -1 scratch — nothing lost). scaland sbt 539 / 0.

