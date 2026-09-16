## Attributes

- id: WI-20260827-W1YKH-the-term-accessor-family-is
- created: 2026-08-27T11:16:54Z

- status: Delivered
- status_agent: user
- status_at: 2026-09-16T17:54:33Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE TERM-ACCESSOR FAMILY IS CARRIER-BLIND: `term_field` REFUSES A `Value::Entity`, WHICH IS EXACTLY WHAT `as_term` PRODUCES — so the composition the reflection surface exists for cannot run. Split out of WI-20260827-1ZG70's analysis; independent of it, and a wrong answer on GROUND input today.

`as_term[E](e: E) -> Term` is the IDENTITY at the host level (`eval/builtins.rs`: `let [e] = ...; Ok(e)`), and its own declaration says why that is right — "at runtime the engine's carriers already let a `Value::Entity` inhabit `Term`". So `as_term(some(7))` hands on a `Value::Entity`. `term_field` then matches `Value::Term { id }` and `other => return Err(type_mismatch("Term", ...))`. The canonical way to GET a term is rejected by the operation that exists to READ one.

MEASURED 2026-08-27 on the tree at b09aa9f1:

  rule f1(?t) :- term_field(as_term(some(7)), "value") <=> ?t
      SUSPENDS.  Correct answer: some(7).

The suspension is the mild half. `bridge_op_to_eval` residualizes the error, `reduce_op_value` restores the un-reduced CALL, and the ENCLOSING accessor then reads that call as data and COMMITS — the WI-880 wrong-answer class, one operation over. Those rows are WI-20260827-4XXSD's, which owns the enclosing half; this ticket owns the CAUSE. Landing 4XXSD alone turns the wrong answers into suspensions and leaves f1 suspended; landing this alone makes f1 answer. Both are wanted, neither subsumes the other.

THE FAMILY IS NOT UNIFORM, and the census is the ticket rather than the one-line fix:

  term_functor_name   CARRIER-NEUTRAL already — `value_head_symbol`, and its own
                      comment records the migration off a hand-matched Fn/Ref/Ident/
                      Entity nest.
  term_field          `Value::Term` ONLY; anything else is a LOUD type_mismatch that
                      residualizes into the silent wrong answer above.
  term_as_int         `Value::Term` only; everything else falls to `_ => None` and
                      answers `none()` SILENTLY. A refusal spelled as an answer.
  term_as_string      same shape as term_as_int.
  term_as_entity      carrier-AWARE (`Value::Term` and `Value::Entity` both), which is
                      the shape the rest should have.

So three distinct behaviours for one question, and two of the three are wrong in DIFFERENT directions — one loud-then-silently-swallowed, one silent from the start. `term_list_items`, `term_to_string` and `extract` are NOT in the list above because I did not read their carrier handling; census them rather than assume.

WHAT `none()` MAY AND MAY NOT MEAN. `term_as_int`'s declaration says "Returns none() unless the term is exactly `Const(IntLiteral(_))`" — so `none()` for an ENTITY is arguably correct and only the SILENCE is wrong. `term_field`'s says "Returns none() when the term has no matching named arg or is not Fn-shaped" — and an Entity with that named arg HAS one, so `none()` there would be a wrong answer and the current `type_mismatch` is at least honest. Decide per operation against its own declared contract, not family-wide.

THE REPAIR DIRECTION, prototyped and measured for `term_field` alone: read the `Value::Entity`'s named args directly. f1 goes from SUSPEND to `some(7)`; `term_functor_name(term_field(...))` from `some("term_field")` to `some("some")`; `term_to_string(term_field(...))` from the printed CALL text to `"some(value: 7)"`. Full workspace 5863 passed / 0 failed with it, and 5863 / 0 without it — THE CORPUS DOES NOT REACH THIS, so green is not evidence and every row must be driven.

TWO ROWS ARE BLIND, recorded so they are not mistaken for witnesses: `term_as_int(term_field(as_term(some(7)), "value"))` answers `none()` before AND after (before, from reading the un-reduced call; after, because the argument is the `Option` wrapper, not a `Const` int), and the `= some(7)` row is 0/0 both ways. Same value, opposite reasons.

RELATION TO CLAUDE.md's localized invariants: this is the "per-carrier host-op keying" rule, which is stated in docs/kernel-language.md and enforced at a doc-commented site. Check whether that site should have caught this family and did not.

ACCEPTANCE: `term_field(as_term(some(7)), "value")` answers `some(7)`, driven, on a carrier the program can actually produce; the family census above is completed (`term_list_items` / `term_to_string` / `extract` read, not assumed) and each operation's behaviour on a non-`Term` carrier is either made neutral or DOCUMENTED at its declaration as deliberate; no accessor answers `none()` for a carrier it simply did not recognise — that is a refusal spelled as an answer, and the loud-over-silent rule forbids it; the two blind rows are recorded AS blind; full workspace green via rustland/scripts/test.sh.

REFERENCE: `term_field` / `term_as_int` / `term_as_string` / `term_as_entity` / `term_functor_name` (rustland/anthill-core/src/eval/builtins.rs), `as_term`'s declaration in stdlib/anthill/reflect/reflect.anthill, WI-880 (which host-mapped the family), WI-20260827-4XXSD (the enclosing half).

## Changes

### 2026-08-27T11:39:02Z — feedback — user

THIS TICKET IS THE EXPIRY OF `wi_4xxsd_unreduced_host_arg_test`, delivered 2026-08-27. That file borrows THIS defect as its un-reducible inner call, so landing this one changes its rows and it must be updated in the same commit.

WHAT CHANGES THERE, with the values already written at the test site:

  rule f1(?t)      :- term_field(as_term(some(7)), "value") <=> ?t
      asserted TODAY as a suspension, under a comment calling it the PREMISE.
      With this ticket it answers `some(7)` and that assertion is the TRIPWIRE that
      fires — it is written to say exactly this, not to be silently relaxed.
  rule functor(?n) :- term_functor_name(term_field(as_term(some(7)), "value")) <=> ?n
      asserted TODAY as a suspension; becomes 1 DEFINITE `some("some")`.
  rule printed(?s) :- term_to_string(term_field(as_term(some(7)), "value")) <=> ?s
      asserted TODAY as a suspension; becomes 1 DEFINITE `"some(value: 7)"`.

DO NOT SIMPLY UPDATE THE THREE EXPECTATIONS AND MOVE ON. 4XXSD's claim is that a host op never reads an inner call the bridge could not reduce, and those two witnesses are the only rows driving it. Once this ticket makes the inner call reduce, they no longer exercise a FAILED inner call at all and 4XXSD is left with a control and no witness. Either re-point them at an inner call that still fails, or say at the site that no such call remains reachable from source — which would be a real narrowing of the class and worth recording rather than losing.

NOTE ONE SHAPE THAT IS NOT A CANDIDATE, measured while filing: a declared-but-unimplemented operation (`sort_as_term`) does NOT reproduce it. `is_unreduced_op_call` deliberately excludes a body-less unmapped op — that is the symbolic-algebra boundary its own doc argues (the wi616 five) — so such a call passes the refusal AND the ground gate and the host does read it. That is the intended boundary, not a gap this ticket or 4XXSD moves.

AND THE BLIND ROWS STAY BLIND, for a THIRD reason. `term_as_int(term_field(as_term(some(7)), "value"))` answers `none()` before 4XXSD (reading the un-reduced call), after 4XXSD (the argument suspends), and after THIS ticket (the argument is the `Option` WRAPPER `term_field` returns, which is not a `Const` int). Three mechanisms, one value. They are recorded as blind in 4XXSD's file header; do not promote either into a witness here.

### 2026-09-16T09:51:48Z — feedback — user

CLAIMED 2026-09-16, and WI-20260916-WVVAM IS FOLDED IN AS A DUPLICATE of this item's
first half. WVVAM was filed without checking the open queue; its measurements carry over
and are restated below, its status is Rejected pointing here.

THE EXPIRY OBLIGATION IN THIS ITEM'S 2026-08-27 FEEDBACK IS VOID AS WRITTEN. It says
"THIS TICKET IS THE EXPIRY OF `wi_4xxsd_unreduced_host_arg_test`, delivered 2026-08-27"
and names three suspension rows to be re-pointed in the same commit. Verified today:
WI-20260827-4XXSD is still **Open**, no `wi_4xxsd_unreduced_host_arg_test.rs` exists in
the tree, and `is_unreduced_op_call` (resolve.rs:10889, which did land) is driven by
`a_bare_nullary_op_name_is_still_data`, not by those rows. So there are no three
expectations to update. The WARNING behind the obligation still stands and should be
honoured if 4XXSD ever lands with those witnesses: making the inner call reduce leaves
4XXSD with a control and no witness.

MEASURED UNDER WVVAM, carried here (all on one KB, so the operation is the only
variable; a rule body joins `DeclarationMeta` and binds the operand as an OCCURRENCE):
 * `term_field(?m, "internal") = none()`  -> RESIDUAL on every row. The raise is real but
   the operand fold's `Err(_) => None` arm turns it into "no answer" rather than "did not
   run" — this item's "loud-then-silently-swallowed" class, confirmed.
 * `term_list_items(?m) = ?xs`            -> PROCESS PANIC, not a residual. It raises
   `EvalError::Internal` (`alloc_from_value` answering `UnsupportedVariant("Node")`),
   which `bridge_op_to_eval` treats as an invariant breach and asserts on. This item's
   census said to READ `term_list_items` rather than assume; read, and it is worse than
   the other two directions it lists.
 * `term_functor_name(?m) = some("meta")` -> DEFINITE, as this item already records
   (`value_head_symbol`). It is the control that proves the others are carrier-specific.
 * `meta_has_flag(?m, "internal") = true` -> DEFINITE. The meta readers lower through
   `value_to_term`, which IS `Node`-aware, so they were never in this family's defect.

AND ONE THE FIX ITSELF CREATES, which belongs in the census: `term_to_string` lowers via
`alloc_from_value`. That was unreachable while every accessor hard-matched `Value::Term`;
the moment `term_field` / `term_list_items` hand back a child on its own carrier it is
live, through a chain that ships (`term_field` -> `term_list_items` -> `term_to_string`,
anthill-todo/anthill/main.anthill). Made `Node`-aware — lowering is right AT THAT SITE
because printing is a leaf that renders to a String rather than passing a carrier on.

A CORRECTION THIS ITEM SHOULD CARRY, because the wrong version is in the tree: Z73FX put
into docs/kernel-language.md §5.8 the claim that a host op with a STRING-LITERAL argument
does not reduce in a rule body. That is false — `meta_has_flag(?m, "internal") = true`
answers definite. It was filed off a measurement taken before those operations were
host-mapped and never re-run. §5.8 now states the carrier rule instead.

DONE SO FAR under this item's acceptance: `term_field`, `term_list_items` and
`term_to_string` made carrier-neutral, `term_field` keeping a `ViewHead::Functor` check so
a non-term still RAISES rather than answering `none()` (this item's "refusal spelled as an
answer" rule). REMAINING: the rest of the census — `term_as_int`, `term_as_string`,
`extract` — each either made neutral or documented at its declaration as deliberate; the
headline row `term_field(as_term(some(7)), "value")` answers `some(7)` driven; full
workspace green.

### 2026-09-16T11:32:43Z — feedback — user

CORRECTION — "THE SILENT SWALLOW" DOES NOT EXIST, AND WAS MY MEASUREMENT ERROR
(2026-09-16).

Three notes on this item and on WVVAM said the operand fold's `Err(_) => None` arm turns
a host op's raise into a residual, so a failed call reads as "a relation with no rows"
rather than "did not run" — and that the mechanism "will hide the next one exactly as
well". ALL OF THAT IS FALSE.

WI-20260911-0V0F7 ALREADY PARTITIONED IT, and its own comment states the very thing I
was claiming as an open defect: "EVERY eval error used to leave here as `None` ... a goal
whose callee RAN AND RAISED came back indistinguishable from one the fold merely
declined". `bridge_op_to_eval` (resolve.rs ~10608) now reads the error's
`bridge_disposition` and answers Schedule / Truncation / Fault; `TypeMismatch` — exactly
what `term_field` raised — maps to **Fault** (eval/error.rs:306), which calls
`faults.fault(...)` and marks the search incomplete. `EvalError::Internal` additionally
trips a `debug_assert!`.

IT FIRED DURING MY OWN MEASUREMENTS AND I DID NOT READ IT. The probe output carried
"note: the search is INCOMPLETE — a goal could not be evaluated (see the warning(s) on
stderr)". I had filtered every probe through `grep -E "solution|residual"` and discarded
stderr, then built a narrative on the absence of a message I had filtered out.

WHAT REMAINS TRUE, and it is the whole of the defect: the VALUE answer is `None`, by
design (WI-483 substitution-transparency — a callee's failure must not break the
enclosing rule). So a rule body still gets NO DATA out of an accessor it was entitled to
read, and the accessor's carrier-blindness is still the bug this item fixes. What is NOT
true is that the engine says nothing about it.

CONSEQUENCES, all corrected in the same commit: docs/kernel-language.md §5.8 (which I had
just written the false version into), the test module header, and /code-review's
"altitude" finding, which was downstream of my framing and recommended extending a
partition that already exists.

### 2026-09-16T14:08:40Z — feedback — user

MEASURED WHILE TESTING, NOT FIXED — `meta_value`'s PAYLOAD IS UNREACHABLE FROM A RULE
BODY (2026-09-16). Recording because it is a usability gap the accessor work exposes
rather than causes, and because the next person to write this row will otherwise
rediscover it the way I did (three wrong guesses at the pattern).

FIXTURE: `entity marked(x: Int64) @[Tag: "kept"]`, joined as
`DeclarationMeta(name: ?n, meta: ?m), term_functor_name(?n) = some("marked")`, so `?m`
is `meta(Tag: "kept")` riding as an occurrence.

  not(meta_value(?m, "Tag") = none())     -> 1 solution. The key IS found.
  meta_value(?m, "Tag") = ?v              -> RESIDUAL (eq never binds; §5.3, F0HHB).
  meta_value(?m, "Tag") = some(?v)        -> 0. Unbound var inside the pattern.
  meta_value(?m, "Tag") = some("kept")            -> 0.
  meta_value(?m, "Tag") = some(as_term("kept"))   -> 0.

So a rule body can assert THAT a key is present and never WHAT it holds. The last two
rows are the interesting ones: the payload is the key's child on ITS OWN carrier — a
`Term`-carried `Const(StringLiteral)` — while both spellings above are a bare `String`
(`as_term` is the host-level identity, so it does not wrap). Whether those two should
compare equal is a question about carrier equality (WI-616's `SemEq` → carrier eq), not
about this accessor, and it is not answered here.

CONSEQUENCE FOR TESTS, and it is why this is worth a note rather than a shrug: the
obvious positive assertion is unavailable, so a row written the obvious way answers 0
WHETHER OR NOT THE READER WORKS — it measures nothing while looking like it measures
everything. Both rule-body rows in `wi_w1ykh_term_accessor_carrier_test.rs` are
therefore spelled `not(… = none())`, with the payload asserted separately from an
OPERATION body (`field_of_as_term`, which reads `term_field`'s result down to the
`Int64`) where a result does bind.

### 2026-09-16T17:54:23Z — feedback — user

DELIVERED (2026-09-16), commit 1a93fc79.

ACCEPTANCE, row by row.
 1. `term_field(as_term(some(7)), "value")` answers `some(7)` — DRIVEN, and read down to
    the `Int64` rather than stopping at `some(…)`, from an operation body (a rule body's
    `=` does not bind; §5.3). This is the row the item recorded as a SUSPENSION at filing.
 2. THE CENSUS IS COMPLETE and the family is uniform. Fixed here: `term_field`,
    `term_list_items`, `term_to_string`. Already carrier-neutral, verified by reading not
    assuming: `term_functor_name` (`value_head_symbol`), `term_as_int` / `term_as_string`
    (`TermView::literal_*` — this item's census was STALE on those two; WI-20260827-2YHZ3
    moved them), `term_as_entity`, `extract` (hands `&Value` to `extract_type`).
    Deliberately untouched: `replace_named_arg` and `unify`, which CONSTRUCT and unify
    rather than read, so a `TermId` is what they need.
 3. NO ACCESSOR ANSWERS `none()` FOR AN UNRECOGNISED CARRIER, and the converse is driven
    too: a LEAF term answers `none()` (the contract, and what `anthill-todo`'s
    `unwrapped_string` — "Total by design" — rests on), while a value naming nothing
    raises. Which values those are defers to `value_functor`, the existing owner: a
    hand-rolled `ViewHead` test admits `Value::OpRef`, whose head names its reflect
    ENCODING, and hands a dictionary's internals back as fields.
 4. THE BLIND ROWS: the obligation as written is VOID. It names three suspension rows in
    `wi_4xxsd_unreduced_host_arg_test`, "delivered 2026-08-27" — but WI-20260827-4XXSD is
    still Open and that file never landed (`is_unreduced_op_call`, which did land, is
    driven by `a_bare_nullary_op_name_is_still_data`). Nothing to re-point. The warning
    behind it stands if 4XXSD ever lands with those witnesses.
 5. GREEN: rustland/scripts/test.sh — 36 binaries, 7086 passed, 0 failed. scaland
    `sbt test` — 575 passed, 0 failed. 11 new rows in
    `wi_w1ykh_term_accessor_carrier_test.rs`, of which two FAIL when the change is backed
    out (verified by reverting and re-running, not asserted) and the rest are new coverage
    or declared controls.

WHAT THE FIX IS. A rule body binds an operand as an OCCURRENCE — σ-applied goals are
deliberately not interned — so `Value::Term`-only readers refused every rule-body call.
`term_field` raised (reported as a Fault, but the rule still got no data);
`term_list_items` raised `EvalError::Internal`, which the bridge ASSERTS on, so a rule
body PANICKED the process. `TermView::named_field` is now the single owner of the
by-local-name lookup four sites had open-coded, with in-place overrides on the `TermId`
carriers so the `@[simp]` gate got cheaper rather than paying a `Vec` per call.

CARRIED IN, ON USER DIRECTION: the kernel meta readers are rewritten as view reads as the
first step of moving `meta` off `TermId` onto values. They were NOT broken — they lower
through the Node-aware `value_to_term` — and the row covering them is a stated control
that passes both ways.

THREE `/code-review` ROUNDS, and most of what rounds 2 and 3 found were defects in the
earlier rounds' fixes: a `ViewHead::Functor` test that silently dropped the `Ident`
spelling the original match had; a receiver guard that broke a shipped "Total by design"
path; a `term_to_string` repair that interned on the printing path while quoting this
item's own "do not lower" rule (`TermPrinter::print_occurrence` renders an occurrence
natively); a `project_field` rewrite that collapsed "key unresolvable" into "key absent".
Each is now fixed at an existing owner rather than patched locally.

TWO CLAIMS OF MINE THAT MEASUREMENT KILLED, recorded because both reached the tree before
they were caught. (a) "Lowering leaks one interned term per joined row" — FALSE; the
store is hash-consed, and the growth test written to pin it passed with the whole change
backed out. (b) "The raise is silently swallowed" — FALSE; WI-20260911-0V0F7 already
partitions the bridge's dispositions and `TypeMismatch` lands on `Fault`, which prints
"could not be evaluated … an empty answer set here is NOT a refutation". I had filtered
stderr out of my own probes. docs/kernel-language.md §5.8 carried the second claim (put
there by Z73FX, along with a third — that a STRING-LITERAL argument is what fails to
reduce) and now states the carrier rule instead.

MEASURED, NOT FIXED: `meta_value`'s payload is unreachable from a rule body. `not(… =
none())` answers 1, but `= some(?v)`, `= some("kept")` and `= some(as_term("kept"))` all
answer 0 — the payload rides as a `Term`-carried `Const` while the last two are bare
`String`s. So a rule body can assert THAT a key is present and never WHAT it holds, and
the obvious positive assertion measures nothing while looking like it measures
everything. Whether those should compare equal is a carrier-equality question (WI-616),
not this item's.

REMAINING, NOT DONE HERE: three cons/nil spine walkers now exist (this one, the printer's
and its occurrence twin) and they MUST agree — their key-matching was measured to
disagree on a dotted unresolved name and is aligned, but consolidating them onto one
carrier-neutral owner changes what the printer WRITES TO DISK and wants its own driven
rows.

