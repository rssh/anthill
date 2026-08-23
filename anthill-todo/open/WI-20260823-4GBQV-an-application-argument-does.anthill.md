## Attributes

- id: WI-20260823-4GBQV-an-application-argument-does
- created: 2026-08-23T10:52:49Z

- status: Open
- status_agent: claude
- status_at: 2026-08-23T10:52:49Z

- acceptance: cargo-test

## Description

AN APPLICATION ARGUMENT DOES NOT RE-KEY A CALLEE'S `Modify[<param>]`, so the CALLEE'S OWN
PARAMETER NAME survives into the caller's row. Found while delivering
WI-20260823-39AD2 and PRE-EXISTING — measured with that ticket's change backed out, on
`Cell.set`, whose row has read `Modify[c]` since proposal 037.

MEASURED:
    operation mk() -> Cell[V = Int64] effects Modify[result] = Cell.new(0)
    operation via_app() -> Unit effects {} = Cell.set(mk(), 1)
  => "type mismatch in via_app.effects (op-effects): expected declared: [],
      got undeclared effect: Modify[T = c]"
`c` is `Cell.set`'s parameter. It appears nowhere in the caller's text, so the author is
sent to look for a symbol that does not exist in their scope. LOUD, not silent — which is
why this is a diagnostic-and-expressiveness defect rather than a soundness one.

WHY. `param_to_arg_sym` / `param_to_arg_head` (kb/typing.rs, `check_apply`) populate from
exactly TWO argument shapes:
  * a bare VARIABLE reference, via `extract_var_ref_sym_node` — `Cell.set(k, 1)` gives
    `c |-> k`, so `Modify[c]` becomes `Modify[k]`;
  * a field PROJECTION, via `stable_receiver_path` — `Cell.set(c.rep, 1)` gives the HEAD
    (WI-506, `Modify[c]` covers `Modify[c.rep]`).
Anything else — an application, a literal, a constructor call — gets no entry. The
comment above `param_to_arg_head` already predicts the consequence in words ("the callee's
`Modify[<param>]` would survive un-re-keyed (a spurious 'undeclared effect')"); nothing
acts on it.

WHAT IT COSTS TODAY — THE AMBIENT-RESOURCE IDIOM IS NOT WRITABLE.
`prelude/effects.anthill`'s runtime note describes exactly this shape: "one arena keyed by
the target's FUNCTOR SYMBOL — `set(store, v)` and `set(counter, v)` share the same handler
but live in separate slots". Writing it needs a nullary constructor to NAME a slot:

    sort CounterState
      entity counter
    end
    operation write(n: Int64) -> Unit effects Modify[counter] = set(counter(), n)

Both halves fail:
  * `Modify[counter]` does NOT lower to a denoted place. The single-segment
    value-in-type arm (kb/load.rs, `symbol_is_value_place` + the WI-313 zero-arg
    `Operation` escape) does not admit a nullary CONSTRUCTOR, so the label classifies as
    a TYPE and `check_modify_targets` refuses it.
  * even if it did, `set(counter(), n)` passes an APPLICATION, so the row would not
    re-key.
`eval_test`'s three m5 fixtures were written in this idiom and only type-checked because
`ModifyRuntime.set`'s row was over the TYPE — which WI-20260823-39AD2 established was a
defect. They now take the resource as a PARAMETER, which keeps them driving the arena but
no longer exercises the ambient spelling.

CARE — THE EPONYMOUS-CONSTRUCTOR INTERACTION IS THE TRAP. Admitting a nullary constructor
to the value-place set is one line, and it is NOT obviously safe: WI-926 records that an
eponymous constructor IS its sort, so a sort with one could make `Modify[<Sort>]`
reclassify from a TYPE (refused, correctly) to a PLACE (admitted), silently un-refusing
the shape WI-20260823-39AD2 exists to refuse. MEASURE that population before touching the
set — `a_concrete_sort_in_a_modify_target_is_refused_too` uses a sort whose constructor is
NOT eponymous and would not notice.

PINNED, BOTH ARMS: `wi506_modify_field_coverage_test::an_application_argument_does_not_
rekey_and_leaks_the_callees_param_name` asserts the CONTROL (a bare-variable argument DOES
re-key) beside the gap, so the row cannot pass by "Modify never re-keys". When the re-key
learns this shape that row flips to `Ok`.

DECIDE FIRST, THEN BUILD:
 1. WHICH ARGUMENT SHAPES NAME A PLACE? A nullary constructor / zero-arg call is the
    ambient resource. A general application (`f(x)`) names no stable slot and probably
    should stay a refusal — but then the DIAGNOSTIC must say so, instead of leaking `c`.
 2. Whichever is admitted needs BOTH the load-side classification (kb/load.rs) and the
    call-site map (`param_to_arg_head`) — one without the other repairs nothing, and that
    split is what makes this bigger than an inline fix.

ACCEPTANCE: the ambient idiom above loads and runs (an m5-style write-then-read through
the arena), OR a general application argument is refused with a message naming the
CALLER's own expression rather than the callee's parameter; the eponymous-constructor
population is measured and reported either way; `a_concrete_sort_in_a_modify_target_is_
refused_too` and the rest of wi347 stay green; the wi506 pin is updated to whichever
verdict lands.

