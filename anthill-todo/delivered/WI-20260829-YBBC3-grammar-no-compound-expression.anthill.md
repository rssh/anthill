## Attributes

- id: WI-20260829-YBBC3-grammar-no-compound-expression
- created: 2026-08-29T11:48:35Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-29T14:08:32Z

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

## Changes

### 2026-08-29T14:08:25Z — feedback — user

DELIVERED. The decision the ticket asked for was taken by MEASUREMENT rather than by picking one of its two candidates, and the answer is neither: not "admit the compound forms everywhere" and not "admit them only inside `paren_expr`", but ADMIT THEM WHERE A DELIMITER ENDS THEM, and make `paren_expr` the escape for everywhere else.

THE RULE. Every compound form is `prec.right` and extends as far right as it can, so it is admissible exactly where a `,` or a closing bracket STOPS it — a call argument, a named-argument value, a tuple component, a list element — and `paren_expr` now wraps an `_expr_body`, which reaches the positions that have no delimiter (an infix operand, a dot receiver, a `match` scrutinee, a set element). `_term` itself is UNCHANGED, so a compound form is still not an atom.

THE TICKET'S "REAL AMBIGUITY" DID NOT MATERIALIZE, and that is what turned the decision. `f(match x case a -> 1, y)` was the worry; measured, it is unambiguous — no `match_branch` can start at `,`, so the arm list ends there and `f` has two arguments. `tree-sitter generate` reports NO new GLR conflicts and the 209-case corpus stayed green through every step. `pair_up(match mk(7) case row(x, f) -> x, 3)` EVALUATES to 703 under a deliberately non-commutative combiner, which is the assertion that says both slots were filled and by which value.

ONE POSITION WAS MEASURED AND DECLINED: a set literal's elements stay `_term`. `{ a, b }` is already the braced-body and rule-goal-list spelling, and admitting `_expr_body` there is a REAL conflict — `Unresolved conflict for symbol sequence: 'rule' '{' _term . ',' …`, `_expr_body` against `_goal`. A set element takes the parenthesized form like any other atom position, and that limit is a test, not a comment.

SHIPPED, both implementations:
 * `tree-sitter-anthill/grammar.js` — `_positional_fn_arg`, `named_arg`'s value, `collection_literal`'s elements and `paren_expr` all take `_expr_body`.
 * `rustland/…/parse/convert.rs` — `paren_expr` dispatches its inner node as an `ExprBody`; `is_expr_body_kind` is the one list `fn_arg_work_kind` (routing) and `is_term_kind` (collection) both read, so the two cannot drift; `push_collection_literal` routes elements the way a call argument is routed.
 * `scaland/…/AnthillParser.scala` — `namedArg`'s value and `collectionLiteral`'s elements widened to `exprBody`. Scaland's positional `fnArg` was ALREADY `exprBody`, so this brings the two into parity rather than adding a capability there.
 * `docs/kernel-language.md` §4.8 — a new "Where an `Expr` may be written" section stating the delimited-position rule, the parenthesized escape, the set-literal exception with its reason, and the rule-data-position caveat below.
 * `testdata/parser-parity/wi777` — 2 accept + 2 reject cases, so BOTH implementations are pinned to the same verdict on the widened positions and on the two limits.
 * `tree-sitter-anthill/test/corpus/expressions.txt` — 5 cases, including the trees for `match` delimited by a comma and for the three parenthesized escapes.

EVIDENCE, and it is values rather than parses. `wi_ybbc3_compound_expression_positions_test` (13 tests) DRIVES every position through `Interpreter::call`: `if`/`match`/`let` as arguments, as a named-argument value, as tuple components and as list elements, plus the three parenthesized escapes and the set one. `an_ill_typed_compound_argument_is_refused_located` is what says the position is TYPE-CHECKED and not merely parsed — four ill-typed compound arguments are each refused with a `line:col:` span naming the `Bool`.

BACK-OUT, MEASURED: restore the four grammar rules to `$._term` ⟹ 10 of those 13 fail, every one at PARSE, and 4 of `typer_capability_matrix_test`'s tests fall with them. The three `control_` tests pass either way and each names why — two are the limits the change did not lift, one is the ordinary spellings.

THE CELLS THIS TICKET NAMED ARE FLIPPED. `a_compound_expression_is_not_a_term` is `a_compound_expression_is_a_value_expression`, its rows load verdicts now with two negatives and the two limits kept as parse assertions; `the_remaining_positions_across_their_routes`' skip list is GONE, so `match` sweeps all five routes; the census's four `Unspellable` cells are Built and `unspellable` is asserted at ZERO. `a_lambda_inside_a_list_literal_does_not_parse` became `a_lambda_inside_a_list_literal` — that spelling loads now, which finally makes "write a lambda instead" a checkable repair for WI-20260828-5NSZY's routes 6/7 rather than advice that did not parse.

TWO DEFECTS FOUND ON THE WAY, both filed rather than fixed here:
 * WI-20260829-8VGRW — a compound form in a RULE DATA position (a rule head, a body goal, a `fact` argument) loads and unifies with nothing: `fact p(if true then 1 else 2)` is not matched by a goal spelling the same text, while `p(?z)` matches. PRE-EXISTING for `lambda`, which the ticket's control demonstrates; the widening gave it four more spellings. Pinned by a test that fails the day it starts working, and named in the spec so a reader is not sent into it.
 * WI-20260829-WBXGX — a collection literal's element type is its FIRST element's and every later element is unchecked: `takes_list([1, "a"])` loads, `takes_list(["a", 1])` refuses. Distinct from WI-20260826-7JDWY, and on the very route 7JDWY's own table uses as its control.

