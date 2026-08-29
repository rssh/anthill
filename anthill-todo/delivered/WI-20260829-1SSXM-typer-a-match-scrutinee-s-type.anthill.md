## Attributes

- id: WI-20260829-1SSXM-typer-a-match-scrutinee-s-type
- created: 2026-08-29T06:34:49Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-29T08:20:35Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

Typer: a MATCH SCRUTINEE's type error is SILENTLY DROPPED — `MatchAfterScrutinee` reads the scrutinee's result through `.ok()` three times and never re-pushes its `Err`. The match then types its arms against `scr_ty = None` and puts the UN-REWRITTEN scrutinee node back into the stored tree, so the whole match reports nothing. Every other build frame propagates a child failure (`LambdaBody` re-pushes it; `IfExpr` / `Apply` / `Constructor` run their children through `collect_arg_errors`); this one does not, and it is the only frame that does not.

MEASURED, on the WI-20260828-N2FHM tree (rustland/anthill-core/src/kb/typing.rs, `TypeBuildFrame::MatchAfterScrutinee`). Propagating the `Err` — an eight-line change, `let scr_r = match scr_r { Ok(r) => r, Err(e) => { results.push(Err(e)); return; } };` plus dropping the three `.ok()` reads — turns 13 currently-green corpus tests RED, across THREE unrelated roots. All three are programs the typer had already decided were ill-typed; none is a false refusal introduced by the propagation:

  R1 — `rustland/anthill-todo/anthill/store.anthill:391`, `match term_as_entity(t)`.
       `term_as_entity[E](t: Term) -> Option[T = E]` puts `E` only in its RETURN, and a
       match scrutinee has no expected type to pin it from, so `E` is unconstrained.
       Diagnostic: "expected a type for 'E', got unconstrained — use `term_as_entity[E = …](…)`".
       REPAIR, one line, RUN AND MEASURED GREEN: `match term_as_entity[WorkItem](t)`.
       It alone fixes 7 of the 13 (wi204_smoke × 2, wi204_let_ctor_env × 2,
       wi204_sort_param × 1, wi236_call_with_requirements × 4 — minus overlap) and
       236 failures in `anthill-todo`'s `cmd_tests`, which all load this file.
       (The sibling call at store.anthill:470 is inside an ARM, where the operation's
       declared return does pin `E` — which is why only one of the two ever leaked.)

  R2 — `kb_query_test.rs` and `wi531_solution_residual_test.rs` both write
       `import anthill.prelude.LogicalStream.{splitFirst}` and then apply it to
       `execute(kb(), …)`, whose declared return is `Stream[T = Solution, E = Error]`.
       Diagnostic: "type mismatch in splitFirst.s (op-arg): expected LogicalStream, got
       Stream[T = Solution, E = Error]". The refusal is TRUE — provision runs
       `LogicalStream provides Stream`, not the reverse — and it works at run time only
       because eval dispatches on the value.
       REPAIR, RUN AND MEASURED GREEN: import `Stream.{splitFirst}` and retype the
       consumer's param `Pair[Solution, LogicalStream]` as
       `Pair[A = Solution, B = Stream[T = Solution, E = Error]]`. 2 tests.

  R3 — `wi590_witness_param_carrier_test.rs` and
       `wi606_unqualified_dispatch_return_threading_test.rs`. Both fixtures declare a lazy
       carrier `sort Mapped { sort Source = ?; entity mk(source: Source, …) }` and peel it
       with `Stream.splitFirst(src)` where `src : Source` — an abstract sort param under NO
       `requires`. Diagnostic: "expected Stream, got ?Source".
       NOT REPAIRED, and this is the reason this is a ticket rather than an inline fix.
       The real stdlib `MappedStream` (combinators.anthill) does not have this shape: it
       declares `requires Iterable[C = Source, Element = Src, E = ES]`, types the field on
       that spec view, peels via `Stream.splitFirst(Iterable.iterator(src))`, and returns a
       BARE `Stream` tail — with a comment saying why the tail cannot be a
       `MappedStream[Source = Source]` ("the tail wraps the SOURCE's tail, so its `Source`
       is that tail's sort, NOT this carrier's"). But WI-606's whole subject is that
       `Mapped.splitFirst`'s declared return IS the CONCRETE carrier tail
       (`B = Mapped[Source = Source, …]`), which is what the unqualified `splitFirst(m)`
       must thread; adopting the stdlib's bare-`Stream` tail would delete what that test
       measures. Reconstructing `mk(rest, fn)` from a `Stream`-typed tail cannot type
       against a self-similar `Source`, so there is no local rewrite that keeps both the
       signature and a truthful body. Deciding what those two fixtures should assert is a
       judgement about WI-590/WI-606, not a typo fix — which is why it is here.

WHAT SHIPPED INSTEAD, and what it does not cover. WI-20260828-N2FHM added
`surviving_dot_apply` (typing.rs, called from `check_operation_bodies` after the body is
written back): a STORED operation body containing an `Expr::DotApply` is a load error. That
closes the one consequence that is un-catchable at run time — eval has no arm for a
`DotApply` and raises `Internal("unhandled Expr variant in eval")`, which is not a `Raised`
payload, so no handler sees it. It does NOT close the class: any OTHER kind of type error in
a scrutinee (R1's unconstrained type param, R2's op-arg mismatch, R3's receiver mismatch) is
still dropped, and the program still loads.

ACCEPTANCE: the propagation lands, R1/R2 are repaired as measured above, R3 is resolved by
deciding what WI-590/WI-606's fixtures assert (and recording that decision at those
fixtures), and the workspace is green via rustland/scripts/test.sh. A test that DRIVES it:
a program whose match scrutinee holds a type error must FAIL TO LOAD with that error — with
a stated control naming what passes either way. `surviving_dot_apply` stays: once the
scrutinee error propagates it should never fire, and a backstop that never fires is what an
invariant looks like once it holds.

