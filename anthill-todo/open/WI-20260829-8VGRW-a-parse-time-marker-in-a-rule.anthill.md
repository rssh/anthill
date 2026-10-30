## Attributes

- id: WI-20260829-8VGRW-a-parse-time-marker-in-a-rule
- created: 2026-08-29T13:26:15Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T13:26:15Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A PARSE-TIME MARKER IN A RULE DATA POSITION LOADS AND MATCHES NOTHING. `fact p(lambda x -> 1)` and a goal `p(lambda x -> 1)` — the SAME text — do not unify. The goal answers nothing, silently, and the load is clean.

MEASURED, in `wi_ybbc3_compound_expression_positions_test::a_compound_form_in_a_rule_data_position_loads_and_matches_nothing`:

  fact p(lambda x -> 1)   /  rule written(1) :- p(lambda x -> 1)    written  = 0
  fact p(if true then 1 else 2) / rule written(1) :- p(if …)        written  = 0
  fact p(1)               /  rule written(1) :- p(1)                written  = 1
  either compound fact    /  rule variable(1) :- p(?z)              variable = 1

So the fact IS stored and IS reachable — a variable goal finds it. It is the WRITTEN form that cannot address it, and only when the argument is a compound expression.

PRE-EXISTING, NOT INTRODUCED BY WI-20260829-YBBC3. A `lambda` has been admissible in an argument position — and therefore in a rule head, a rule body goal and a `fact` argument, which are all `_fn_arg` — since long before that ticket; the `lambda` row above is the control and it behaves identically. What YBBC3 changed is REACH: the same silent non-match is now available through `match` / `if` / `let` / `proof` as well, so four more spellings load clean and decide nothing.

WHY IT MATTERS. This is the fail-open shape the project's development principles single out: a program that loads clean and answers the empty set, with no diagnostic naming the reason. `anthill.reflect.Expr` exists precisely so a rule CAN talk about expression syntax (that is what a `@[simp]` macro reads, proposal 056), so "a compound form in a rule data position" is not obviously a mistake to refuse — which is exactly why the current behaviour is the worst of the three options: it is neither a refusal nor a match.

WHAT TO DECIDE, and it is one question with three answers, not a bug with a fix:

  (a) MAKE IT MATCH. Two identical spellings should build one term. Find why they do not — the suspect is `Converter::alloc_marker_term`, which stamps a binder-form provenance mark (WI-618, folded in by WI-AKKWF); if that mark or a per-occurrence var identity is part of term identity, two textually identical markers are two terms. `p(?z)` answering shows the fact is indexed, so whatever separates them is on the equality/unification side, not the storage side.

  (b) REFUSE IT, located, at the rule data position — "a compound expression is an operation-body form; a rule term cannot contain one, write `Expr.if_expr(…)` if you mean the reflect term". Cheapest, and it turns a silent empty answer into a message. But it forecloses (c).

  (c) DECIDE THAT THE REFLECT SPELLING IS THE ONLY ONE and say so in the spec — a rule addresses expression syntax through `anthill.reflect.Expr`, and writing the surface form in a rule is refused as in (b). This is (b) plus the spec sentence that makes it a rule rather than a limitation.

FIRST STEP EITHER WAY: find what separates the two marker terms. Print both `TermId`s and their structural keys for `fact p(lambda x -> 1)` against a goal `p(lambda x -> 1)`; the answer decides whether (a) is a one-line identity fix or a design change.

PINNED: the test named above asserts `written = 0` today and FAILS the day it starts answering, which is the signal to close this. Its `lambda` row is the control that attributes the behaviour to the marker rather than to YBBC3's widening, and its `fact p(1)` row is the control that says rule data positions do match ordinary terms.

## Changes

### 2026-08-29T13:48:05Z — feedback — user

THE "A FEW LINES IN convert_rule_heads / push_fn_term" ESTIMATE IS WRONG, and it is worth writing down because it is the obvious first read. `Converter` carries NO rule-versus-body context: `push_fn_term` builds a rule head, a rule-body goal, a `fact` argument and an operation-body call through the SAME production and cannot tell them apart, and `convert_rule_heads` sees only heads — not goals, not `fact` terms. The converter's own WI-1129 comment states the shape of this problem for the `...` rest-capture and the machinery it needed: a PENDING list filled during conversion and drained by a later pass that knows which position it is in, because "a rule head and an operation-body call are the same `fn_term` production, so the grammar can only say 'somewhere in a call' and this list says which one". Refusing option (b) needs that same machinery or a post-conversion walk over each rule's terms.

AND REFUSING WOULD REACH `lambda` TOO, which has been admissible in these positions since long before WI-20260829-YBBC3. Refusing only the four forms that ticket added would privilege one member of the family again — the exact asymmetry the widening removed — so option (b) is "refuse the family", a behaviour change to programs that load today, and it needs a corpus measurement before it is chosen. A `grep` over the repo's 229 `.anthill` files finds no rule or fact writing a compound form in a data position, so the measurement is likely cheap; it has not been run.

OPTION (a) REMAINS THE BETTER ANSWER if the diagnosis is small, and nothing here changes that: two textually identical markers building two different terms is a bug whichever way the design question is settled.

### 2026-10-26T16:23:21Z — feedback — claude

MEASURED 2026-10-26 (found delivering WI-20261011-2S5FP, the same on its parent 030aec34): THE REFLECT SPELLING ALSO MATCHES NOTHING AS A RULE BODY GOAL'S ARGUMENT — the spelling option (c) would make the only one. Over `rule id2(?x, ?y) :- ?y <=> ?x`: `rule viaIf(?r) :- id2(anthill.reflect.Expr.if_expr(cond: true, then_branch: 1, else_branch: 2), ?r)` and `rule viaLambda(?r) :- id2(anthill.reflect.Expr.lambda_expr(param: 1, body: 2), ?r)` answer NOTHING, silently, beside `rule viaEntity(?r) :- id2(bx(v: 1), ?r)` answering `?r = bx(v: 1)`; the same goal typed as a CLI query, `id2(anthill.reflect.Expr.if_expr(…), ?r)`, answers `?r = if true then 1 else 2`. Bound by `<=>` in a rule body the constructor is data and destructures (`?y <=> if_expr(…), if_expr(cond: ?c, then_branch: ?r, else_branch: ?e) <=> ?y` answers 1), so it is the goal-argument route that loses it. Since 2S5FP the rule body builds the constructor and the `if` syntax as one `Expr::If` node told apart by `NodeKind::Expr.compound_syntax`, the syntax evaluated and the constructor data.

### 2026-10-30T19:25:33Z — feedback — claude

MEASURED 2026-10-30 (found delivering WI-20261023-Y6QW2, on 91d34582 and after): a QUERY that writes the compound form a fact holds matched it through the shared positional marker — over `fact p(lambda x -> 1)`, `fact q(if true then 1 else 2)`, `fact k(lambda () -> 3)`, the queries `p(lambda x -> 1)`, `q(if true then 1 else 2)` and `k(lambda () -> 3)` each answered `true`. Y6QW2 reads a compound expression in a query pattern as a clause's walk reads it (a lambda is a function value, an `if` is evaluated), so those three now answer nothing, as the rule-body goal of the same text already did (`rule written(?n) :- p(lambda x -> 1), …`); `p(?f)` still finds the fact. The query side of this question now agrees with the rule body; the fact side keeps the marker. Pinned by `wi_y6qw2_function_value_from_a_rule_test::a_query_and_a_rule_body_read_a_compound_form_alike`, which asserts the two agree and fails the day either moves alone.

