## Attributes

- id: WI-20260822-AKKWF-convert-expr-s-marker-dispatch
- created: 2026-08-22T19:09:11Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-23T19:58:01Z

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

## Changes

### 2026-08-23T19:57:49Z — feedback — user

DELIVERED, WITH THREE CORRECTIONS TO THIS TICKET'S OWN TEXT.

THE REPAIR. `visit_load`'s marker dispatch now matches on `Option<&str>` — `Some(name)`
only when `SimpleTermStore::is_minted` says the converter built the node — so the
pairing is ONE gate rather than a `&&` per arm, and a new marker arm cannot be added
without it. The eleven builders that did not mint now do, through
`convert::alloc_marker_term` / `alloc_marker_term_with_named`, which FUSE the mint to
the allocation: no marker anywhere is minted by a separate line a future edit can omit,
which was the shape of this defect. `typed_var` (AK2AJ's) was routed through the same
factories for uniformity; its mint is unchanged.

CORRECTION 1 — THE POPULATION WAS THREE ARMS LARGER THAN THE TABLE. Re-running the
census over ALL of `visit_load`'s arms rather than the ticket's list found
`pattern_constructor`, `pattern_tuple` and `dot_apply` panicking too. FOURTEEN written
calls crashed the loader, not nine: `if_expr(1)`, `match_expr()`, `match_branch(1)`,
`let_expr(1)`, `lambda_expr(1)`, `proof_stmt()`, `pattern_var()`, `pattern_literal()`,
`pattern_constructor()`, `pattern_constructor(1)`, `pattern_tuple()`,
`pattern_tuple(1, 2)`, `dot_apply()`, `dot_apply(1, 2)`, plus `pattern_wildcard()`
hijacked as a `Pattern`. All fifteen now report an ordinary diagnostic naming the
author's own call, and `pattern_wildcard()` is no longer read as a `Pattern`.

CORRECTION 2 — `dot_apply` MUST NOT BE PROVENANCE-GATED, AND I MEASURED THAT THE WRONG
WAY ROUND FIRST. It is minted, so the ticket's recipe applies on its face; but in a TERM
position `dot_apply(?receiver, member, ?x)` is a SPELLED KERNEL FORM, the surface of a
sort-scoped dot rule (kernel-language.md). I added the pairing at `convert_term`'s
re-encode on the strength of a "hijack" I had measured — and 8 tests fell
(`wi279_dot_dispatch`, `wi538_local_proof`, four `wi902_dot_rule_macro`, `wi903`), every
one reporting "expected operation declared on the receiver's sort" for the method the
dot rule was there to supply. My measured hijack WAS the documented spelling working.
Backed out, and `visit_load`'s `dot_apply` arm takes the SHAPE guard instead (arity >= 2
with an `Ident` at the name slot), which stops the two panics without answering a second
question. Measured both ways: under a mint gate the applicative op-body spelling
`dot_apply(?b, special, 7)` is refused while the `?b.special(7)` surface keeps loading,
and exactly 1 of 3416 tests in `wi_tests` catches it — the new one this ticket adds.
Both readers say so at their site, and `SimpleTermStore::minted`'s doc records that the
flag is not the only gate available.

CORRECTION 3 — "scaland has no `minted` and no marker lowering" is wrong on the first
clause. Scaland has both, and had already answered this question BETTER: WI-1009's
`parse/ExprMarker.scala` gives markers a provenance set of their OWN, and excludes
`field_access` / `dot_apply` / `ho_apply` / `unify` / the collection literals for the
reason I rediscovered above — those are names the loader is MEANT to resolve. The
ticket's OPERATIVE claim still holds: scaland's copy of `convert_expr_term` was deleted
unused (WI-1007), so it has no marker arms and there is nothing to port. The
correspondence, and why rustland can reuse `minted` where scaland could not, is recorded
at `alloc_marker_term`.

THE CENSUS THE NEW PRODUCERS OWE, MEASURED. `is_minted` has eleven readers (ten
pre-existing). EIGHT pair the mint with a name or name-derived layout no marker answers
to. TWO — `rule_introduced_functor_name` and `bodyless_declares_nothing_detail` — ask it
of a RULE HEAD with no name pairing, and are the two a new mint could move. Both head
readers plus every marker build were instrumented for one
`cargo test --workspace --no-fail-fast`: 2 586 767 marker mints (all thirteen shapes,
including `proof_stmt` 16 and `pattern_literal` 12 — so the negative is not vacuous),
115 574 minted heads at `rule_introduced_functor_name` (`eq` 86 628, `not` 28 870, `add`
33, `mul` 26, `unify` 8, `struct_eq` 6, `dot_apply` 3) and NO MARKER NAME among them; 0
at `bodyless_declares_nothing_detail`, said rather than counted as agreement. Both
enforcement-site comments were updated: their head-unreachability now rests on TWO
grammar facts (AK2AJ's `_positional_fn_arg` one does not cover this producer set), and
each names the case a future author would otherwise ship silently.

BACK-OUTS, EACH RUN. Reader gate -> `Some(name.as_str())`: 2 of 8 here (a loader PANIC
and the `Pattern` hijack), 7 of 3416 across `wi_tests` — the other five are WI-605/618
arrow rows, because the shared binding subsumes the arrow arm's own pairing. The FACTORY
mint: NOT attributable — the stdlib itself stops loading, 2398 of 3416 — so the
per-producer question is answered by three named-arg mutations instead, each 1 of 8 and
each the right one. The `dot_apply` shape guard -> mint gate: 1 of 3416.

TESTS. New `wi_akkwf_written_marker_call_test.rs`, 8 rows: the written-call table, the
`pattern_wildcard` negative (`!contains("got Pattern")`), a control in its own fixture,
five real-form rows that DRIVE evaluation (`interp.call`, not "it loads"), and the
spelled-dot-form guard, which asserts the rewritten value 7 rather than a clean load.
Ran `/code-review high`; its two substantive findings (the enforcement-site comments,
the guarded-wildcard arm placed above `Some("pattern_tuple")`) are fixed, as is the
"loads clean" weakness in the dot-form row and the count drift in the census docs. Its
critical finding was an artifact of reviewing mid-back-out; the tree is restored and
carries no instrumentation.

ACCEPTANCE. rustland `scripts/test.sh`: 5631 passed, 0 failed, 36 result lines, exit 0.
scaland `sbt test`: 538 passed, 0 failed (untouched).

