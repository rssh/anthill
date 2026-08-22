## Attributes

- id: WI-20260822-AKKWF-convert-expr-s-marker-dispatch
- created: 2026-08-22T19:09:11Z

- status: Open
- status_agent: claude
- status_at: 2026-08-22T19:09:11Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`convert_expr`'S MARKER DISPATCH IS A BARE NAME TEST AND A USER-WRITTEN CALL PANICS THE
LOADER -- WI-20260822-AK2AJ's defect, one coordinate over, and louder.

`Loader::convert_expr` (`kb/load.rs`, the `Term::Fn` arm around 17379) dispatches the
converter's surface-form markers on `local_name(functor)` ALONE and then indexes
`pos_args` unconditionally. Only ONE of its ten arms pairs the name with provenance --
`n if pratt::is_arrow_functor(n) && self.parsed.terms.is_minted(parse_id)`, which WI-618
added. Every other arm fires on a name a user may write, and none of the names is
reserved.

MEASURED, 2026-08-22, each as `operation f() -> Int64 = <expr>` inside a namespace
importing `Int64`, via `try_load_kb_with` under `catch_unwind` (found by /code-review on
AK2AJ's tree; this table is my own re-run, which found one row more than the review did):

  if_expr(1)           PANIC   load.rs index out of bounds (len 1, index 2)
  match_expr()         PANIC   `pos_args.len() - 1` underflow
  match_branch(1)      PANIC
  let_expr(1)          PANIC
  lambda_expr(1)       PANIC
  proof_stmt()         PANIC
  pattern_var()        PANIC   `load_pattern_var`'s `pos_args[0]`
  pattern_literal()    PANIC
  pattern_wildcard()   no panic, but HIJACKED -- it is nullary, so nothing indexes out of
                       range and the call is silently read as a `Pattern`: "expected
                       Int64, got Pattern". A wrong value rather than a crash.
  typed_var(1)         clean type error -- AK2AJ fixed this one.

A LOADER PANIC ON A USER PROGRAM IS WORSE THAN THE WRONG-MESSAGE FAILURE AK2AJ FIXED. It
is not a diagnostic at all: the process aborts, so no other error in the file is reported
either.

THE REPAIR IS AK2AJ's, APPLIED TO THE REST OF THE FAMILY: pair each arm's name with
`SimpleTermStore::is_minted`, so a WRITTEN call named like a marker falls through to
ordinary conversion and gets its own accurate diagnostic. It splits in two, and the halves
have different costs:

  * ALREADY MINTED, so the pairing alone is the whole fix -- `match_branch`
    (`convert.rs` ~2298), `let_expr` (~2337), `lambda_expr` (~2357). Three arms, one `&&`
    each, no new producer and no new census.
  * NOT MINTED, so the mint must be added at the builder FIRST -- `match_expr` (~2284),
    `if_expr`, `proof_stmt` (~2396), `pattern_var` (~1804), `pattern_literal`,
    `pattern_wildcard`.

THE HAZARD, and why this is not a drive-by: ADDING A `mark_minted` PRODUCER IS A CENSUSED
CHANGE. `is_minted` has NINE readers (all in `kb/load.rs`: 5169, 5423, 5580, 14651, 15654,
15678, 15760, 15786, 17489) and "was this written as a call" is NOT the same question at
each. The census must be per READER, not per method. AK2AJ's census is recorded at
`convert.rs`'s `typed_var_arg` arm and is the worked example -- but its conclusion does NOT
transfer: it turns on `typed_var` failing every one of the six name lists and on a marker
being unable to occupy a head position. `lambda_expr`, `let_expr` and `match_branch` are
IN `binder_form_layout`, so `check_bare_arrow_typo` and `first_unresolvable_arrow_leaf`
already act on their mints -- those two arms must be re-read for each newly-minted name
rather than assumed inert. Note also `SimpleTermStore::minted`'s doc (WI-AK2AJ) and the
comment at `bodyless_declares_nothing_detail`: a marker reachable in HEAD position would
falsify that diagnostic's text, so any new mint must be checked against it.

ACCEPTANCE: every row of the table above LOADS without panicking and reports an ordinary
diagnostic naming the user's own call, and `pattern_wildcard()` stops being read as a
`Pattern`. DRIVE the other direction too, in its own fixture: each marker's REAL surface
form still elaborates -- a genuine `if`/`match`/`lambda`/`let`/proof/pattern still loads
and still evaluates -- because pairing an arm whose builder forgot to mint would silently
switch the real form off, which is the failure mode this repair can introduce. Say at each
site which rows fail on a back-out, back out by MUTATING the guard rather than deleting
code, and name any reader whose verdict each new mint moves. `cargo-test` green via
`rustland/scripts/test.sh`; `scaland-sbt-test` green (scaland has no `minted` and no marker
lowering, so there is nothing to port).

