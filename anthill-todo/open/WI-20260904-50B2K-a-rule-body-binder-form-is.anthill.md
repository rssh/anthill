## Attributes

- id: WI-20260904-50B2K-a-rule-body-binder-form-is
- created: 2026-09-04T09:31:41Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T09:31:41Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RULE-BODY BINDER FORM IS TYPED WITH NO EXPECTED TYPE, so an unannotated lambda whose body needs one is refused and an arrow term in its body is read as a value.

MEASURED on the WI-20260903-FC2X4 tree, with `operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)` in scope:

  rule value(?r) :- ?r <=> apply1(lambda x -> x + 1, 2)
    -> ambiguous dispatch of `anthill.prelude.Additive.add`: 3 instances provide
       `anthill.prelude.Additive` … and the call selects none

  rule value(?y) :- ?y <=> (lambda t -> (t -> t))
    -> type mismatch in arrow.apply: expected known operation or arrow-typed variable,
       got unknown functor

THE TWO CONTROLS. The ANNOTATED twin `apply1(lambda (x: Int64) -> x + 1, 2)` answers 3, and so does the OPERATION-BODY twin `operation viaop() -> Int64 = apply1(lambda x -> x + 1, 2)` — where the callee's arrow slot supplies the binder's type through `hof_arg_hint`. And an unannotated binder whose body PINS it from its own call is unaffected: `all_match(?xs, lambda (x) -> is_pos(x))` (wi620's fixture) loads clean, because `is_pos` declares `n: Int64`.

WHY. WI-20260903-FC2X4 made a rule-body binder form a `CallDispatch::BinderForm` — handed WHOLE to `type_check_node_at`, which is the only thing in the typer that binds a pattern into Γ. It is handed `expected: None`, because the ENCLOSING call (`apply1(…)` in a `<=>` operand) is a `CallDispatch::DataTerm`, and WI-1058 deliberately does not type-check one — for three measured reasons stated at `data_functor_error`, the first of which is "lost expectation". So no arrow reaches the binder.

NEITHER PROGRAM WORKED BEFORE. Both "loaded" only because the lambda's body was `⊥` (FC2X4's defect) and answered nothing. This is a refusal replacing a silent meaningless load, not a regression — but it is a NARROWING against the operation-body spelling, and the two positions should agree.

WHAT TO DECIDE — one question with two parts:

  (a) SHOULD THE WALK SUPPLY THE SLOT'S ARROW? `dispatch_calls_in_occ` knows the parent `Expr::Apply`'s functor and the child's index, so it can read the declared parameter type (`op_info`) and hand it down — `hof_arg_hint`'s question, asked one altitude up. That is NOT the same as type-checking the DataTerm parent (which WI-1058 refuses for reasons that stand); it passes a HINT to a child that is checked anyway. Measure what it moves.

  (b) IS AN ARROW TERM INSIDE A RULE-BODY LAMBDA A TYPE? In a rule, types are terms (`?y <=> (t -> t)` loads today — `wi618_bare_arrow_logic_test::lowercase_rule_type_var_arrow_still_loads`). A lambda BODY is a value expression, so `lambda t -> (t -> t)` is refused. Deciding it needs the spec sentence, not just an arm.

ROWS. `wi_fc2x4_lambda_in_a_rule_test::an_arrow_inside_a_rule_body_lambda_is_not_read_as_a_keyword_typo` pins the SECOND program's current refusal (it asserts WHICH sentence — not the self-contradictory keyword advice); flipping it to a load is the signal to close part (b). Nothing pins the first program, deliberately: it would go red on part (a)'s fix.

