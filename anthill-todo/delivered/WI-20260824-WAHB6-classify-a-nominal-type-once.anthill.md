## Attributes

- id: WI-20260824-WAHB6-classify-a-nominal-type-once
- created: 2026-08-24T05:04:18Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-24T06:47:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

CLASSIFY A NOMINAL TYPE ONCE, AT THE LOADER, AND MAKE THE TYPER CONSUME THE RECORD (proposal 055 umbrella A, step 1).

Implement docs/design/055-implementation.md §1 and the §2 resolution table for the OPERATION-EXPRESSION path only: a bare sort / in-scope type-parameter reference and a sort-headed BRACKET application become an explicit resolved TypeValue occurrence form, recorded once, and every later consumer reads the record instead of rediscovering type-ness from the expected sort, from syntax, or from the carrier.

MEASURED -- where the decision is already made, and where it is thrown away:

  * APPLIED form: `load.rs:19497` (`build_load`, WI-927) already reads `self.parsed.terms.is_type_application(outer_parse_id)` so a bracketed sort-headed application is never read as a construction. That IS the classification -- and the occurrence it builds keeps only `Expr::Apply { functor: <sort>, .. }`, which is the same shape a paren call produces. The decision is discarded at the moment it is made.
  * BARE form: not classified at load at all. It arrives as `Expr::Ref` / `Expr::Ident` and `check_bare_ref` (`typing.rs:6334`) decides it by the EXPECTED sort (`expects_reflect_type`, the WI-206 arm) -- exactly the expectation-directed classification §1 forbids.

So this ticket does not invent a pass. It gives the loader's existing decision an explicit carrier and moves the bare form's decision to the same place.

CARRIER: prefer a distinct `Expr` variant over a side channel. `Expr::Constructor.from_projection`'s own doc states the reason and it applies verbatim here: a field INSIDE the `Expr` makes every rebuild site a compile error, and the rebuild sites are not just `rebuilt_expr` -- `substitute_occurrence`, `term_view`, `resolve`, `body_specialize` all mint replacement nodes directly, and a missed one is SILENT. Arms to carry it: `for_each_child`, `child_labels`, `drain_expr_children`, `map_*`, `node_to_debruijn` / `open_debruijn_node`, `occurrence_to_term`, print, eval, plus the typer arm. Do NOT reuse `NodeKind::Expr.classification` -- that channel answers `CallClass` (dispatch), a different question, and loading a second question onto one channel is a repeat of a defect this repo has already paid for.

SCOPE FENCE. Acceptance does not widen for the APPLIED form here. The BARE form's diagnostic DOES flip wherever the classification is now unconditional: `UnresolvedName` becomes `expected <S>, got Type`. Proposal 055 §2 blesses that flavor change explicitly ("two costs of uniformity"). Do NOT add a temporary typer-side gate reproducing the old rejection -- that re-introduces the expectation-directed classifier this ticket exists to remove, and hides which sites the record actually reached. The §3 occurrence matrix and the removal of `type_slot_arg_hint` are separate tickets.

CONTROL (this is the point, not an afterthought). (1) A DRIVING test must read the recorded classification off the occurrence for a bare and an applied form and assert what it says -- "it loads" is not evidence, and a test that only asserts a declaration loaded keeps passing when the name resolves to nothing. (2) The WI-206 / WI-707 / WI-709 / WI-710 test files stay green while the typer arm no longer consults `expects_reflect_type` to DECIDE denotation (it may still consult it to VALIDATE). (3) State at the test site which rows fail when the record is backed out and the typer falls back to the hint, and which rows pass either way by design.

ACCEPTANCE: full Rust workspace via rustland/scripts/test.sh; scaland has no typer, so `sbt test` need only stay green.

## Changes

### 2026-08-24T05:55:07Z — feedback — user

MEASURED DEVIATION FROM THIS TICKET'S OWN SCOPE FENCE, reported rather than papered over.

The fence said "acceptance does not widen for the APPLIED form here". That is now measured WRONG, and the reason is structural rather than an implementation slip: once the loader classifies unconditionally -- which is what §1 asks for and where WI-927 had already put the decision -- the reading stops depending on the position for BOTH faces at once. So `operation via_let() -> Type = let t = Cell[V = Int64] ...` now loads and evaluates, where before the unannotated `let` gave the applied form no `Type` hint, its argument got none either, and `Int64` was reported as an unresolved name.

Preserving the old rejections would have meant a typer-side gate that rejects a CLASSIFIED type value in the positions where the old hint could not fire -- an expectation-directed rejection, i.e. exactly the fallback this ticket forbids, added only to be deleted by WI-20260824-JM6ZW, and it would make WI-20260824-Q0093's controls meaningless (they could not tell "the record reached this family" from "the temporary gate happened to allow it").

CONSEQUENCE FOR Q0093: the widening arrives with this ticket for every position at once, so Q0093's job is narrower than its text assumes -- it PINS the widening per family (driving test + negative destination + adjacent-role control) rather than delivering it family by family. Its acceptance is unchanged.

WHAT ELSE THE SPLIT'S STEP-1/STEP-2 BOUNDARY BUYS, since it is not nothing: the two are still separately measurable. This ticket's rows measure the RECORD (the occurrence says what it is; the two carriers key alike); Q0093's measure the CONSUMERS (every ValueExpression family reads it, every adjacent role does not).

