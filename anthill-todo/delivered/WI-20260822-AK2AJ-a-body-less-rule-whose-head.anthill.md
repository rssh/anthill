## Attributes

- id: WI-20260822-AK2AJ-a-body-less-rule-whose-head
- created: 2026-08-22T06:45:52Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-22T19:16:52Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BODY-LESS RULE WHOSE HEAD CARRIES A USER FUNCTOR NAMED `typed_var` IS FALSELY REFUSED,
citing a typed column the source does not contain.

MEASURED (/code-review, on 061's tree): `rule p(typed_var(1))` with no body is refused
with "A typed column `?x: T` has exactly one enforcer, a rewrite's typed-pattern bound
(WI-903)…". Under 061 that head would otherwise DECLARE `p`, so this is a false REFUSAL,
not only a misleading sentence.

THE CAUSE IS A BARE NAME TEST. `is_typed_column` (kb/load.rs) asks
`parse_sym.local_name(*functor) == "typed_var"` with no provenance pairing — WI-948's
"a name, not a verdict" trap. `head_carries_typed_column`'s own doc records that the trap
was seen and that the head node is deliberately not asked for exactly this reason; the
split narrowed the trap from the head to the ARGUMENTS rather than removing it, and
`is_typed_column` recurses into nested arguments too.

THE REPAIR AND ITS HAZARD, both already established so they are not re-derived:
`parse/convert.rs`'s `typed_var_arg` arm builds the marker (`self.intern("typed_var")`)
and does NOT `mark_minted` the node it allocates. Minting it and pairing the name with
`is_minted` is the fix — but `is_minted` has TEN readers in `kb/load.rs` (arrow-functor
arms, connective heads, the equation-subject gate at `is_minted(subject)`, the
declaration reading's `is_minted(*tid)`), and `mark_minted` has seven producers, so
adding one is a CENSUSED change. Census per READER, not per method — the answer to "was
this written as a call" is not the same question each of those ten is asking.

ACCEPTANCE: `rule p(typed_var(1))` with no body LOADS and DECLARES `p` (drive it — ask
the KB for `p`'s clauses and its declaration, not that the load returned Ok), while a
genuine `rule p(?x: Int64) <=> …` typed column keeps its WI-903 enforcement and a
body-less rule carrying one is still refused with the same message. Say at each site
which rows fail on a back-out, and name any reader whose verdict the new mint moves.
cargo-test green via rustland/scripts/test.sh.

## Changes

### 2026-08-22T19:16:48Z — feedback — claude

DELIVERED. The mint landed and both readers now pair the name with it.

WHAT THE TICKET NAMED, and what it did not. `is_typed_column` was one of TWO bare-name
readers of "is this the converter's `typed_var` marker?", not one. The second is
`convert_term`'s `typed_var` STRIP (`kb/load.rs`), and it is reachable exactly where the
ticket's own shape is not: a rule that HAS a body never touches the declaration path, so
`is_typed_column` is never asked and the strip decides alone. MEASURED before the fix,
`rule pc(typed_var(?x, type: Int64)) :- qc(?x)` took the strip, found no
`ParseAux::TypeExpr` behind the user's ordinary `type:` argument, and reported "WI-582:
typed rule pattern `?x: T` is missing its type" -- after which the `Bottom` bound it
invented tripped the rewrite-shape refusal too. Two errors, neither about anything in the
source. Fixed inline rather than spun off: it is one `&&`, and the ticket's own root
("a bare name test") owns it.

THE CENSUS ANSWER: NO EXISTING READER'S VERDICT MOVES. The ticket said TEN readers of
`is_minted`; there are NINE (`kb/load.rs` 5169, 5422, 5579, 14650, 15653, 15677, 15759,
15785, 17473 -- the tenth was the `parse/ir.rs` definition). Asked per READER, not per
method, every one of the nine pairs the mint with a NAME or a POSITION a `typed_var`
marker fails:

  * `parse_connective_head`, `bodyless_declares_nothing_detail` and
    `rule_introduced_functor_name` ask it of a rule HEAD or an equation's LHS operand.
    `rule_heads` is `commaSep1($._goal)` and `typed_var_arg` sits ONLY in
    `_positional_fn_arg`, so the marker is an ARGUMENT and can never occupy either
    position. This is the grammar, not a convention -- checked in `grammar.js`.
  * `minted_connective_symbol` additionally requires `is_equality_family_functor`;
    `parse_connective_head` also requires 2 positional args (the marker has one).
  * `check_bare_arrow_typo`, `first_unresolvable_arrow_leaf` and `convert_expr`'s arrow
    arm additionally require `is_arrow_functor`, `binder_form_layout` (`lambda_expr` /
    `match_branch` / `let_expr`), or `field_access` | `dot_apply`.

The census is recorded AT THE MINT SITE in `convert.rs`, so the next producer added there
reads it before adding one.

WHAT MOVED IN THE DOCS. `head_carries_typed_column`'s doc justified the head/argument
split by "that pairing is NOT available here". It is available now, so the split is
restated as what it actually is -- a SHAPE statement the grammar makes true -- rather than
left reading as a guard.

BACK-OUTS, RUN AND NOT PREDICTED (all by MUTATING the guard, never by deleting code --
a deletion back-out measures loadability, not capability):

  * THE MINT (`mark_minted` removed): 2 of 5 fail --
    `a_genuine_typed_column_still_declares_nothing_to_attach_to` and
    `a_genuine_typed_column_still_gates_a_rewrite`. `wi582_typed_rule_pattern_test` drops
    4 of 5 in the same run.
  * THE DECLARATION READER (`is_minted` -> `true` in `is_typed_column`): 1 of 5 --
    `a_written_typed_var_argument_declares_its_predicate`.
  * THE STRIP (`is_minted` -> `true` in `convert_term`): 1 of 5 --
    `a_written_typed_var_in_a_clause_keeps_its_shape`.

No row fails under two of them, which is what says the three edits answer three questions.

THE MEASUREMENT THAT NEEDED A SECOND TRY. My first drive for the strip asserted that a
goal `pc(?x)` does NOT reach a marker-headed clause. It does -- a VARIABLE goal unifies
with the marker term itself and answers definitely, so the row was green under both
readings and measured nothing. The discriminator has to be the bare VALUE: `pc(1)` fails
against `pc(typed_var(1, type: 7))` and succeeds against the stripped `pc(?x)`, so the
answer INVERTS. Constants ride in the head (`rule reaches_marker(9) :- ...`), not as
`, ?m = 9`, per WI-20260822-WZX6B.

ACCEPTANCE. `cargo-test` via `rustland/scripts/test.sh`: 36 binaries, 5530 passed, 0
failed. `scaland-sbt-test`: 508 passed, 0 failed. Scaland needs no port -- it has neither
`typed_var` nor `minted`. New file
`anthill-core/tests/include/wi_ak2aj_written_typed_var_test.rs` (5 tests), registered in
`wi_tests.rs`; the aggregator/include diff is clean.

