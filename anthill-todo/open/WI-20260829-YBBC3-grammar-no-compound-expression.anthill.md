## Attributes

- id: WI-20260829-YBBC3-grammar-no-compound-expression
- created: 2026-08-29T11:48:35Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T11:48:35Z

- acceptance: cargo-test, scaland-sbt-test

## Description

GRAMMAR: no COMPOUND EXPRESSION -- `match`, `if`, `let`, `lambda` -- can appear in an ARGUMENT, a LIST ELEMENT, or anywhere else a term is expected, and parentheses do not help. Found by the WI-20260829-ARQ5X capability matrix while crossing positions with routes.

MEASURED, all six PARSE errors, none reaching the typer:

  takes_int(match r case row(x, f) -> x)      syntax error near `r case row`
  takes_int((match r case row(x, f) -> x))    syntax error near `r case row`
  takes_int(if true then 1 else 2)            syntax error near `if true then 1 else`
  takes_int((if true then 1 else 2))          syntax error near `if true then 1 else`
  takes_int((let v = 1
    v))                                       syntax error near `let v = 1`
  head_apply([lambda x -> x + 1], 41)         syntax error near `lambda`
  [(match r case row(x, f) -> x)]             syntax error near `r case row`

THE MECHANISM IS STRUCTURAL, not a missing case. In `tree-sitter-anthill/grammar.js`:

  _expr_body: $ => choice(match_expr, if_expr, let_chain, lambda_expr, proof_statement, _term)
  paren_expr: $ => seq('(', $._term, ')')

`_expr_body` is the OPERATION BODY rule. Arguments, list elements and every other nested slot are built from `_term`, which does not include the four compound forms -- and `paren_expr` wraps a `_term` rather than an `_expr_body`, which is precisely why parenthesizing does not rescue them. So the stratification is: a compound expression is admissible where a BODY is expected and nowhere else.

WHY IT MATTERS. `f(if c then a else b)` is ordinary code in every language with expressions, and the workaround -- bind to a `let` first -- is what every fixture in the corpus silently does, so the limitation is invisible in the test suite while being one of the first things a person writes. It is also the reason WI-20260828-5NSZY could not offer "write a lambda instead" as the repair for a bare operation name in a list literal: that spelling does not parse either.

WHAT TO DECIDE, and it is a grammar question rather than a typo. Making `paren_expr` wrap `_expr_body` admits all four forms in every nested slot at the cost of new ambiguities the current stratification exists to avoid -- `prec` notes at grammar.js:1440-1454 show the tuple/paren split is already delicate, and `match`'s `repeat1(match_branch)` is right-recursive with no terminator, so `f(match x case a -> 1, y)` has a real "where does the arm list end" problem that parentheses would have to settle. A narrower move -- admit the compound forms ONLY inside `paren_expr` -- gets `f((if c then a else b))` with one bracket and leaves the bare spelling out, which may be the honest trade.

CELLS THAT TRACK IT: `typer_capability_matrix_test::a_compound_expression_is_not_a_term` (the six rows above) and `the_remaining_positions_across_their_routes`, whose `match` row is skipped in the three nested routes with this ticket named. They FAIL when the grammar admits these forms, which is the signal to flip them and close this.

