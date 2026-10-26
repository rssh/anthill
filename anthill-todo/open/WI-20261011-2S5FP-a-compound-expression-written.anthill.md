## Attributes

- id: WI-20261011-2S5FP-a-compound-expression-written
- created: 2026-10-11T20:14:56Z

- status: Open
- status_agent: user
- status_at: 2026-10-11T20:14:56Z

- acceptance: cargo-test

- tags: proposal-068

## Description

A COMPOUND EXPRESSION WRITTEN IN A RULE BODY'S VALUE SLOT IS NOT EVALUATED — an `if`, a `let` or a `match` there is bound as it is written, compared as data, left a residual under a call, and kills the process when the callee reads into it. Measured 2026-10-11 on b3f238c0; found while delivering WI-20261011-3HN0N. Proposal 068 §1: a binder form is a functional fragment, evaluated by the evaluator that runs operation bodies; §1.2: nothing stored in a binding is an unevaluated call.

THE PROGRAMS, each a rule `value(?r)` in its own namespace, with `operation inc(p: Int64) -> Int64 = p + 1` and `operation fstof(p: (Int64, Int64)) -> Int64 = p._1`. (1) AT A `<=>` OPERAND, bound as written, a DEFINITE answer: `?r <=> (if 1 = 1 then 10 else 20)` answers `?r = if eq(1, 1) then 10 else 20`; `?r <=> (let a = 5  a + 1)` answers `let a = 5 in add(a, 1)`; `?r <=> (match 1 case 1 -> 100 case _ -> 200)` answers the match. (2) AS AN OPERAND OF `=`, A DEFINITE REFUTATION OF A TRUE GOAL: `(if 1 = 1 then 10 else 20) = 10, ?r <=> 1` answers nothing; so do `(let a = 5  a + 1) = 6` and `(match 1 case 1 -> 100 case _ -> 200) = 100`. And `not((if 1 = 1 then 10 else 20) = 10), ?r <=> 1` answers `?r = 1`, definite — a falsehood proved. (3) AS AN ARGUMENT, a residual: `?r <=> inc((if 1 = 1 then 10 else 20))` is conditional on `unify(?_, inc(if eq(1, 1) then 10 else 20))`, and the same for the `let` and the `match`; `inc((if 1 = 1 then 10 else 20)) = 11` is conditional on `eq(inc(…), 11)`. (4) AS AN ARGUMENT THE CALLEE READS INTO, the process dies: `?r <=> fstof((if 1 = 1 then (4, 5) else (6, 7)))` panics in `bridge_op_to_eval`, 'internal evaluator error: field_access: entity has no field _1' — the operation is handed the `if` as a node. CONTROL: with `operation pick(c: Bool) -> Int64 = if c then 10 else 20`, `?r <=> inc(pick(true))` answers 11; a lambda written in a rule body is run when the operation it is handed to applies it.

MECHANISM, as far as read. The loader builds what stands under a compound-expression marker — lambda, if, let, match, in-body proof — with the walk that builds an operation body (`compound_expression_occurrence`, kb/load.rs), and its comment says the subtree is evaluated. The rule-body walk hands a lambda, a let and a match to the typer whole and enters an `if` itself (`call_dispatch_shape`, typing/rule_dispatch.rs: `BinderForm` is a node with a pattern child). At run time nothing evaluates the form: §1.1's strategy (WI-20260926-K4JGC) evaluates an operation application, and a compound expression is neither that nor data. 068 §1 names `lambda` / `let` / `match` as fragment roots and does not name `if`.

WHAT. A compound expression in a value slot denotes its value, as it does in an operation body: evaluated by §1.1's strategy where its free variables are bound, SUSPENDED on them where they are not, and never bound, compared or handed to an operation as it is written. DECIDE FIRST, with the user: whether `if` and an in-body proof are fragment roots beside the three §1 names — the loader already treats the five alike — and that a lambda stays a value, run where it is applied. Related, not this: WI-892 (pre-opened: `if` as a goal, the grammar gate) and WI-20260829-8VGRW (a compound form in a data position of a fact or a head matches nothing).

CONTROLS. A row per program: (1) answers 10, 6 and 100; (2) holds, and its `not` answers nothing; (3) answers 11; (4) answers 4. Each fails today as measured above — (2)'s `not` row answers a falsehood and (4) kills the process. Pass either way: the operation-body `if`, and the lambda rows of wi_3hn0n_tuple_on_rhs_test. WHEN THIS LANDS: `TypingEnv::under` is asked at `dispatch_calls_in_occ`'s descent under a note that no row drives it, an `if` of a rule body not being evaluated (WI-20261011-3HN0N) — give it its row: a collection literal an equation leaves under a rule-body `if` that is then evaluated.

## Changes

### 2026-10-26T12:52:12Z — feedback — claude

CARRIED FROM WI-20261023-Y2HFK (user, 2026-10-26: Y2HFK rejected as superseded by this ticket, whose `let` case it is; WI-20261013-R1W5A depends on this ticket in its place). Its rows, measured 2026-10-23 on 38a260a6, over `operation idI(x: Int64) -> Int64 = x`: `rule letPure(?v) :- ?v <=> (let x = 3  x + 1)` and `rule letInArg(?v) :- ?v <=> idI(let x = 3  x + 1)` each answer the term `let x = 3 in add(x, 1)` — owed: 4, definite. The cell twin `?v <=> (let c = Cell.new(3)  Cell.get(c))` loads (R1W5A's typing masks the `let`'s own cell) and its value is never computed — owed: 3.

