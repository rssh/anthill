## Attributes

- id: WI-20260823-4GBQV-an-application-argument-does
- created: 2026-08-23T10:52:49Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-23T13:46:02Z

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

## Changes

### 2026-08-23T13:15:05Z — feedback — user

DELIVERED, and BOTH branches of the acceptance's OR, because the ticket's decision 1 asked
about the same two shapes from either side.

DECISION 1 — WHICH ARGUMENT SHAPES NAME A PLACE.
  * A NULLARY CONSTRUCTOR does: it is a CONSTANT of its sort, hence a value, hence a name
    for the slot `Env(counter)`. Both spellings — `set(counter(), n)` and `set(counter, n)`
    — since both allocate to one term (WI-511's `Fn{c,[],[]}`->`Ref(c)` canon), and they
    arrive as two different `Expr` variants (`Constructor` and `Ref`). Reading only
    `Expr::Apply` was my first cut and left the ticket's own spelling leaking.
  * A CONSTRUCTOR WITH FIELDS does not — a function, naming no slot until applied.
  * A GENERAL APPLICATION does not, and stays refused; the diagnostic now names the
    CALLER's own expression at the CALL, with a repair that is DRIVEN, not described.

THE EPONYMOUS POPULATION, measured before the set was touched. 200 eponymous constructor
sites tree-wide; 3 in loadable `.anthill` sources (`geometry.anthill`'s `Vec3`, two cli
fixtures' `Person`); exactly TWO of the 200 are NULLARY, both test fixtures
(`parse_test.rs`'s `Error`, `wi933_carrierless_provision_test.rs`'s `Wi933Unit`), and
neither stands in a `Modify` target. So the WI-926 exclusion (`!has_kind(Sort)`) closes the
whole population BY CONSTRUCTION and costs nothing in use.
`an_eponymous_nullary_constructor_stays_a_type` is its trip-wire.

THE TICKET'S "ONE LINE" WAS THE WRONG PLACE, and this is the finding worth carrying. Adding
the nullary constructor to the loader's GENERAL single-segment value-in-type arm — the one
line the ticket describes — dropped 9 tests across three files
(`wi9pgcm_type_level_precondition_test` 6, `wi1fkr2_op_type_var_threads_test` 2,
`wi_rkmd4_type_var_param_slot_test` 1), plus 5 in `parse_test` and one in cpp-gen. Every one
of them on a shape the ticket never names: LABEL-AS-TYPE-PARAMETER, `Text[L = Untrusted]`
where `Untrusted` is a nullary entity standing for a type. Reading it as a place makes
`flows_to(?l, Public)` unreadable and the obligation vacuous. The eponymous trap the ticket
warned about was real but SMALL; the trap it did not name was 15 tests wide.

So the admission is SCOPED TO `Modify`'S OWN TARGET SLOT, which is not caution but the
spec: kernel-language.md 5.6 says that bracket holds a resource NAME, not a type, and it is
the one slot in the language where a bare entity name is not a type. Every other type
position keeps WI-313's rule unchanged. `an_entity_in_an_ordinary_type_slot_is_still_a_type`
is the control and passes under every back-out.

ONE PREDICATE, TWO SITES: `KnowledgeBase::is_ambient_resource_name`, read by the loader's
`Modify`-target lowering and by the typer's `arg_place_head`. Either alone repairs nothing —
a label that lowers but never re-keys is an undeclared effect at every call, and a re-key
onto a name no declaration can spell is the leak in another spelling. Measured: each
back-out fails the end-to-end test, in a different place.

THE LEAK WAS WORSE THAN THE TICKET RECORDED. With the caller owning a parameter also spelled
`c`, the message read `expected declared: [Modify[T = c]], got undeclared effect:
Modify[T = c]` — the same rendering on both sides of a mismatch, because the two `c`s are
different symbols in different scopes. Refusing at the call closes that too. CORPUS COST OF
THE REFUSAL: ZERO — the full suite fell by exactly one test, this ticket's own wi506 pin,
which the ticket said to update.

A `let` REPAIR CANNOT DECLARE ITS PLACE, and the message does not claim it can: `let x =
mk()` binds a BODY local, out of scope in the signature, so the row is `{}` and the label is
elided. Driven in the wi506 pin rather than described.

ALSO FIXED: `eval_test.rs` pointed at `m5_modify_an_ambient_resource_argument_does_not_rekey`,
a test name that EXISTS NOWHERE (WI-20260823-39AD2 named the pin differently in wi506).

SHIPPED: `is_ambient_resource_name` (kb/mod.rs), `type_expr_to_child_modify_target`
(kb/load.rs), `arg_place_head` / `nullary_constructor_arg` / `unrekeyed_modify_argument` /
`placeless_arg_shape` / `denoted_place_ref_sym` (kb/typing.rs), kernel-language.md 5.6,
`prelude/effects.anthill`, `wi4gbqv_ambient_resource_test.rs` (8 rows),
`eval_test::m5_modify_an_ambient_resource_write_then_read`, wi506 pin rewritten.
Full workspace: 5616 passed, 0 failed (was 5607 before the new rows).

NOT DONE, and it is the ticket's own second SCOPE bullet rather than a new gap: a field path
off an ambient resource (`Modify[counter.field]`) is not admitted — the compound
`try_denoted_value_path` head set is untouched. Nothing in the tree writes one, and the
question is the same callback-binder measurement WI-20260823-39AD2 deferred.

### 2026-08-23T13:45:58Z — feedback — user

/code-review (high) FOUND FIVE, and one was an unsound ACCEPT this ticket itself created.
All fixed and pinned; final suite 5623 passed / 0 failed.

1. HIGH — THE ARROW BINDER WAS CAPTURED BY AN ENCLOSING NAME. The `Modify`-target lowering
   resolves in the ENCLOSING scope, and it ran BEFORE the delegate's `arrow_binder_scope`
   arm. So `f: (a: Cell) -> Unit @ Modify[a]` did not gain a reading, it LOST one: adding
   an unrelated `sort Amb { entity a }` anywhere in the namespace re-pointed the callback's
   `Modify[a]` at that entity, and declaring `effects Modify[a]` then LOADED CLEAN while
   the op still mutated the caller's list. A declaration's meaning depending on an
   unrelated name elsewhere in the file. Fixed by checking `arrow_binder_scope` and
   `is_type_param` FIRST — the helper now adds the ambient reading only where the delegate
   would have built a bare `make_sort_ref`. Pinned by
   `an_arrow_binder_is_not_captured_by_an_enclosing_name`, whose discriminator had to be
   WHICH resource the row names (`Modify[T = l]` vs `Modify[T = a]`): my first version
   asserted only "some Modify escaped" and passed WITH the capture in place. Verified by
   back-out.

2. THE RE-KEY MINTED LABELS NO DECLARATION CAN SPELL. `set(wrap, n)` (field-bearing
   constructor) and `set(Slot, n)` (eponymous) re-keyed `Modify[target]` onto the
   constructor, producing `Modify[T = wrap]` / `Modify[T = Slot]` — whose only lawful
   declaration is a load error, so the program was unwritable and neither message said so.
   The loader's admission set and the typer's had drifted apart. Two new rows pin both.

3. A FIELD-PATH DECLARATION LEAKED THROUGH A SPELLING ONE SEGMENT LONGER.
   `poke(d: Box) effects Modify[d.contents]` with a placeless argument still emitted
   `undeclared effect: Modify[T = d.contents]` — this ticket's own defect wearing a
   `.contents` — because the check read only a bare `Ref` off the denoted. Now reads the
   path HEAD, which is also the resource (`Modify[c]` covers `Modify[c.rep]`, WI-506).

4. `term_place_head_sym` descended into `pos_args[0]` of ANY `Term::Fn`; now gated on the
   `field_access` functor, the same gate `stable_receiver_path` puts on its own descent.

5. The `param_to_placeless_arg` comment claimed "empty for nearly every call" — a LITERAL
   argument populates it too (`Cell.set(k, 1)` records the `1`). Comment corrected.
   Also RECORDED rather than silently inherited: `names_modify_place`'s operation arm is
   arity-BLIND while §5.6 and the diagnostic both say "zero-arg operation", so
   `Modify[twoArgOp]` lowers as a place. Pre-existing, separate measurement, noted at the
   site.

THE POSITIVE PREDICATE WAS THE WRONG SHAPE, and 250 tests said so. Gating the argument
re-key on "does this name a value place" refused `match c case wrap(r) -> Cell.set(r, …)`:
a pattern binder carries no declared kind, so the positive test answers NO for every
binder. The gate has to be the NEGATIVE one — "is this a constructor the `Modify` slot
REFUSES" (`is_unplaceable_constructor`) — under which an unknown name stays admitted and
the ordinary undeclared-effect check keeps the last word. Same lesson as the one-name-two-
questions cluster: the loader sees a resolved name in a type slot and can afford
exclusivity; the typer sees binders and cannot.

