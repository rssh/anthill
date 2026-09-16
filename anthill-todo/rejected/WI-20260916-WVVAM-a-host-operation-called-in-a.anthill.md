## Attributes

- id: WI-20260916-WVVAM-a-host-operation-called-in-a
- created: 2026-09-16T04:07:27Z

- status: Rejected
- status_agent: user
- status_at: 2026-09-16T09:42:54Z

- acceptance: cargo-test

- tags: reflect

## Description

A HOST OPERATION CALLED IN A RULE BODY WITH A STRING-LITERAL ARGUMENT DOES NOT REDUCE — it flounders, so the rule silently answers nothing instead of erroring. Found while delivering WI-20260914-Z73FX (its test module records the measurement); PRE-EXISTING, not introduced there.

MEASURED, WITH CONTROLS (2026-09-15, on the built tree, one file, through a rule body):
 * `term_functor_name(?m) = some("meta")` over a `DeclarationMeta` join answers 923 DEFINITE — a host op with a variable argument reduces.
 * `Bool.and(true, false) = false` answers 1 — a host op with two LITERAL arguments reduces, so it is not arity and not literal-ness as such.
 * `term_field(7, "x") = none()` FLOUNDERS — and this is the SHIPPED two-argument reflect accessor, not a probe invented for the ticket.
 * `meta_has_flag(?m, "internal") = true` flounders identically.
The distinguishing argument in every floundering row is a STRING literal. The same calls reduce from an OPERATION BODY, which is how Z73FX's readers are driven.

WHY IT MATTERS. Every reflect accessor that takes a `String` KEY is unusable from a rule body: `term_field`, `meta_has_flag`, `meta_value`. That is precisely the shape "select the declarations whose meta carries this flag" wants, so KB reflection stays operation-body-only and a rule cannot filter on a named thing. And it fails in the one direction this repo's principles exclude — a silent flounder reads as "no such fact", not as "this did not run" (`docs/kernel-language.md`; CLAUDE.md "prefer a loud error over a silent skip").

WHERE TO LOOK. The rule-body reduction path: `KnowledgeBase::host_op_reducible_at_a_value` and its `reduce_args` caller (`rustland/anthill-core/src/kb/resolve.rs` ~11269 and ~10178/10258), with `is_host_mapped_op` / `is_interpreter_mapped_op` (`kb/mod.rs` ~11073). WI-20260826-VPEWK (delivered) states the GOAL-position vs OPERAND-position asymmetry for host ops and is the nearest prior art; WI-20260822-F0HHB (open, deferred) owns what `=` should mean in a rule body and may subsume part of this. FIRST QUESTION FOR WHOEVER TAKES IT: is the string literal failing to reach the host op as a `Value::Str`, or is the op never selected for reduction because an argument carrier is not recognised? The two have different fixes and the measurement above does not separate them.

NOT ASSUMED: that the right answer is "make it reduce". A loud refusal at load — "this host operation cannot be called from a rule body" — would also satisfy the repo's rule and may be the honest fix if the reduction path cannot carry it; that choice wants discussion before implementation.

ACCEPTANCE:
 1. A rule body calling a shipped two-argument reflect accessor with a string-literal key (`term_field(?t, "x")`, `meta_has_flag(?m, "internal")`) either ANSWERS or is REFUSED with a message naming the position — never flounders.
 2. CONTROL: `term_functor_name(?m)` over a join still answers definite, and `Bool.and(true, false) = false` still answers 1 — the rows that already work are not broken by the fix.
 3. CONTROL: the same calls from an OPERATION BODY keep answering as they do today (Z73FX's `meta_readers_answer_from_a_body` and the `wi_z73fx` rows stay green).
 4. Whichever direction is taken is stated in `docs/kernel-language.md` beside VPEWK's asymmetry, so the next reader does not measure it again.
 5. Full workspace green via rustland/scripts/test.sh.

## Reason

DUPLICATE of WI-20260827-W1YKH (filed 2026-08-27), which owns this defect and is broader. W1YKH already names `term_field` as `Value::Term`-only whose loud type_mismatch residualizes into a silent wrong answer, records `term_functor_name` as already carrier-neutral via value_head_symbol (which is why it was my passing control), and asks for exactly the census of `term_list_items` / `term_to_string` / `extract` that turned up the two readers I fixed. It also warned about the trap I fell into: 'THE CORPUS DOES NOT REACH THIS, so green is not evidence and every row must be driven'. Filed in error without checking the open queue first. The measurements recorded in this item's feedback stand and carry over to W1YKH: the carrier — not a string-literal argument — is what a rule body decides; `term_list_items` PANICKED rather than residualizing; and `term_to_string` gains a reachable Node path once the readers hand back a child on its own carrier. The work in progress moves to W1YKH.

## Changes

### 2026-09-16T05:48:50Z — feedback — user

DIAGNOSIS CORRECTED — THE TICKET'S PREMISE WAS WRONG (2026-09-16).

"A host operation called in a rule body with a STRING-LITERAL argument does not reduce"
is FALSE. It was filed off a measurement taken BEFORE the Z73FX `operation_map` entries
existed and never re-run afterwards; the reading was carried into the delivery note, the
test module doc and this ticket without being re-measured. What a string literal does is
nothing at all.

RE-MEASURED, all four rows in ONE KB so the operation is the only variable:
 * `meta_has_flag(?m, "internal") = true`     -> 1 solution, DEFINITE. A string literal.
 * `term_functor_name(?m) = some("meta")`     -> 2 solutions, DEFINITE.
 * `term_field(?m, "internal") = none()`      -> RESIDUAL on every row.
 * `meta_has_flag(?m, "internal") = ?b`       -> RESIDUAL. Same call, unbound result.

THE ACTUAL CAUSE IS THE ARGUMENT'S CARRIER. A rule body hands an operand over as an
OCCURRENCE (`Value::Node`, or an `Entity` wrapping one): the resolver's sigma-applied
goals are deliberately not interned. A reader that matches `Value::Term` alone therefore
refuses EVERY rule-body call. `term_functor_name` always worked because it reads the
occurrence head instead of lowering — which is also the shape of the repair.

ONE CAUSE, THREE SYMPTOMS, and the middle one is why this rated a ticket at all:
 * `term_field` raised `TypeMismatch`, and the fold's `Err(_) => None` arm turned the
   raise into a RESIDUAL — the goal read as "no answer" rather than "did not run".
 * `term_list_items` raised `EvalError::Internal`, which `bridge_op_to_eval` treats as
   an invariant breach and ASSERTS on: a rule body PANICKED the process. Measured:
   `DeclarationMeta(meta: ?m), term_list_items(?m) = ?xs` ->
   `bridge_op_to_eval: internal evaluator error ... UnsupportedVariant("Node")`.
 * `meta_has_flag` / `meta_value` answered — but only by lowering through
   `value_to_term`, which takes `&mut KnowledgeBase` and hash-conses what it lowers.
   One permanent term PER ROW of a join, to answer a read-only question. That is the
   growth WI-20260905-N20EZ removed from the resolver, reintroduced by Z73FX's own
   `meta_term_operand` — mine, shipped 2026-09-16, green because answering correctly
   and answering cheaply are different questions and only the first had a test.

THE FIX IS ONE IDEA IN THREE PLACES: read the carrier through `TermView`, never lower
it. `term_field` and the meta readers become view reads; `kb::load::meta_has_flag` /
`meta_value` now share ONE carrier-neutral owner (`meta_named_arg`) that the
`Option<TermId>` forms delegate to, so `@[simp]` and a rule body cannot disagree about
what `@[Marker]` means. `term_list_items` gets a view-based spine walker — SHORTER than
the printer's `unwrap_list_spine` it mirrors, because `ViewHead::nullary` already
collapses `Ref(nil)` and `Fn{nil,[],[]}` into one head.

NOT TOUCHED, DELIBERATELY: `replace_named_arg` and `unify` also refuse a `Node` input,
but they CONSTRUCT and UNIFY terms rather than read them, so a `TermId` is what they
actually need and interning there is correct. Their input tolerance is a smaller,
separate question.

TWO FINDINGS THIS TICKET DOES NOT CLOSE, both measured above:
 1. AN UNBOUND RESULT STILL RESIDUALIZES. `meta_has_flag(?m, "internal") = ?b` does not
    answer while `= true` does: a host op can be TESTED in a rule body but not used to
    BIND. Whether that is a limitation or the intended reading belongs with
    WI-20260822-F0HHB (`=` in a rule body), not here.
 2. THE SWALLOW IS THE REASON THIS HID. `Err(_) => None` on the fold's host arm turns
    any raise into a residual, so a reader that cannot run is indistinguishable from a
    goal with no answers. Fixing these three readers removes today's instances; the
    swallow will hide the next one exactly as well.

### 2026-09-16T06:00:33Z — feedback — user

CORRECTION TO THE PREVIOUS NOTE — THE INTERNING CLAIM WAS WRONG (2026-09-16).

That note said the meta readers cost "one permanent term PER ROW of a join". That is
FALSE, and a backed-out test run is what caught it. The store is HASH-CONSED: lowering
an occurrence whose structure is already interned returns the EXISTING TermId and
allocates nothing, and a DeclarationMeta row's block came from a declaration, so it
always is. A term-store-growth test written to pin the claim PASSED with the whole
change backed out — it measured nothing, and by the repo's own rule ("a test that
passes both with and without the change measures nothing") it was deleted rather than
kept as decoration.

WHAT IS TRUE, with the grounds restated honestly:
 * `term_field` and `term_list_items` WERE broken from a rule body, and those two are
   the ticket. Verified by reverting both source files and re-running: the field row
   drops to zero DEFINITE solutions, the list row PANICS in the bridge.
 * `meta_has_flag` / `meta_value` were NOT broken — they answered before and answer
   now. Rewriting them as view reads is a refactor, worth doing because `kb::load`'s
   two readers become single-owner over one carrier-neutral `meta_named_arg` (so
   `@[simp]` and a rule body cannot drift about what `@[Marker]` means) and because a
   read path stops demanding `&mut KnowledgeBase`. Not because it fixes a leak.

THE Z73FX SELF-CRITICISM IN THE PREVIOUS NOTE IS WITHDRAWN on the same grounds:
`meta_term_operand` as shipped was not reintroducing WI-20260905-N20EZ's growth. It was
doing unnecessary work on a read path, which is a smaller thing and is now gone.

TESTS, four rows, two of which fail when the change is backed out and two of which are
CONTROLS stated as passing both ways by design (`term_functor_name`, which always read
the head and never lowered; `meta_has_flag`, which pins that the refactor changed no
answer). The controls are what keep the two real rows from passing vacuously on an
empty join.

### 2026-09-16T08:44:45Z — feedback — user

AFTER /code-review — SCOPE CUT TO THE ACTUAL BUG, AND TWO REGRESSIONS OF MINE FIXED
(2026-09-16). 14 findings; 9 acted on, 1 rejected, 4 left as dispositions.

THE META HALF IS FULLY REVERTED. Those readers were never broken from a rule body, my
stated reason for touching them (interning) was false, and the review found a third
thing I had missed: the rewrite changed `meta_value`'s answer CARRIER from always-Term
to the child's own, and consumers call `expect_term` on that payload — which is LOUD
(WI-477). `wi_z73fx_visibility_reflect_test.rs:337` does exactly that. So the refactor
could have panicked a shipped consumer to buy nothing. `kb/load.rs` is untouched now.

A REGRESSION I INTRODUCED AND THE REVIEW CAUGHT: reading `term_field` through the view
without a head check made `term_field(7, "x")` answer `none()` instead of raising
`TypeMismatch` — a silent skip where there had been a loud error, in the file whose own
sibling refuses exactly that hazard. A `ViewHead::Functor` check restores the refusal
while keeping the carrier-neutral read.

A SECOND ONE, WORSE, AND ONLY REACHABLE BECAUSE OF THE FIX: `term_to_string` lowers via
`alloc_from_value`, which refuses every `Node` as an `EvalError::Internal` — the
disposition `bridge_op_to_eval` ASSERTS on. That was dead code while every accessor
hard-matched `Value::Term`; the moment `term_field` hands back a child on its own
carrier it becomes live, through a chain that SHIPS: `term_field` -> `term_list_items`
-> `term_to_string` in `anthill-todo/anthill/main.anthill`. Fixed by taking the
Node-aware boundary there, which is right at that site because printing is a LEAF (it
renders to a String rather than passing a carrier on).

TESTS REWORKED, and one of the review's points was exactly the repo's rule: the field
row asserted only the NEGATIVE answer (`= none()`), which a reader that finds nothing
satisfies just as well. Fixing it turned up something worth recording: the obvious
positive spelling `term_field(?m, "Tag") = some(?v)` answers 0 EVEN WITH THE FIX IN,
because an unbound variable inside the pattern does not bind (§5.3, `eq` never binds —
WI-20260822-F0HHB). The control `term_functor_name(?m) = some(?s)` fails identically,
which is what proves it is the connective and not the reader. The row is therefore
spelled `not(term_field(?m, "Tag") = none())`, which requires the call to RUN and to
FIND the key. Also: the list walker now folds a REAL 3-element spine from an operation
body (the emptiness row alone is satisfied by a walker that answers None for
everything), and the DeclarationMeta join is narrowed to this file's own declaration
(measured: with a whole-KB join, the fixture sort could be deleted and every row stayed
green).

ONE FINDING REJECTED as a false positive: a claimed divergence between the new spine
walker's key test (`local_name_of`) and the printer's (`sym_name`). They are the same
function — `KnowledgeBase::sym_name` is defined as `self.symbols.local_name(sym)`.

LEFT FOR A DECISION, NOT SILENTLY DROPPED: the `Err(_) => None` swallow on the operand
fold is the class fix — WI-20260911-0V0F7 already partitioned `bridge_op_to_eval`'s
dispositions via `EvalError::bridge_disposition`, and extending that partition to this
fold would retire the whole family rather than three instances. Not done here; it wants
its own discussion.

docs/kernel-language.md §5.8 now states the carrier rule — AND CORRECTS THE FALSE CLAIM
Z73FX PUT THERE, which said a host op with a string-literal argument does not reduce in
a rule body. It does. The literal was never the variable.

