## Attributes

- id: WI-20260828-MDWEW-typer-project-a-bare-spec
- created: 2026-08-28T08:49:52Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-28T13:11:59Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

Typer: project a BARE SPEC-TYPED ARGUMENT's provision into a carrier-param spec FIELD. A value typed as a bare spec (`s: Stream`) flowing into an entity field typed on a DIFFERENT spec it provides (`source: Iterable[C = Source, Element = Src, E = ES]`) threads nothing — the field's params stay unbound and the constructed carrier's row leaks.

REPRODUCTION (wi594_finite_map_effect_threading_test::bare_receiver_map_threads_source_effect, with WI-590's consolidation applied):
  operation bare_map[Dst, EffP](s: Stream, f: (x: s.T) -> Dst @ {EffP, -Modify[x]})
    -> Stream[T = Dst, E = {s.E, EffP}] = mapped(s, f)
Once `mapped`'s source field is typed `Iterable[C = Source, …]` rather than `Stream[Src, ES]`, this stops loading.

WHY THE EXISTING READERS DECLINE, traced:
  * `bare_spec_arg_self_projection` (WI-594) handles a bare receiver into a field applying the SAME spec — here the argument's spec is `Stream` and the field's is `Iterable`, so its `base == field_base` gate fails.
  * `carrier_arg_provision_projection` -> `carrier_provision_short_bindings` handles the spec-METHOD face, gated on `enclosing_sort() == field_base`; `bare_map` is a FREE op, so it returns None at that gate.
Neither knows `Stream provides Iterable[C = Stream, Element = T, E = E]`, which is exactly the fact that would thread `Src` and `ES`.

DISTINCT from the two delivered fixes: e9b46fb4 grounds a DISPATCH from the enclosing sort's `requires`; 2c44a257 instantiates a WITNESS head. This is the CONSTRUCTION side with a bare spec-typed argument and no enclosing sort to consult — the argument's own sort is the only place the provision lives.

RELATED, and worth landing together: the ambient-`requires` face of `carrier_provision_short_bindings` (a free op licensing `c` through an enclosing `requires FieldSpec[C = C2, …]`) is ALSO unimplemented. It was written and verified working during WI-590 and then REMOVED before commit, because the only fixture that drove it also type-checked with the change backed out — its declared return pinned exactly the params the construction left free. WI-590's stdlib consolidation is a real driver for it. NOTE, measured: the effect value must NOT be row-wrapped on that path — a `provides` fact writes a row, a `requires` clause writes the bare row PARAM, and wrapping yields `ES = {E}` which the witness's own `requires FiniteCollection[E = ES]` then cannot discharge against `E`.

ACCEPTANCE: a bare spec-typed argument flowing into a field typed on a spec its sort provides threads that spec's params; a test that DRIVES it plus a stated control. Blocks WI-590 (wi594).

## Changes

### 2026-08-28T13:11:21Z — feedback — user

DELIVERED. Two faces implemented, both measured; plus a finding for WI-590 and a rebuilt artifact.

(1) THE TICKET'S OWN CASE — `bare_spec_arg_provision_projection` (typing.rs), the third face
beside WI-594's self-projection and WI-599's carrier-param one. A bare spec-typed argument
(`s : Stream`, either spelling — bare sort ref, or WI-1059's materialized `Stream[T = s.T,
E = s.E]`) into a field typed on a spec that argument's SORT provides. It reads the argument
sort's own `provides Iterable[C = Stream, Element = T, E = E]`, substitutes each of that
sort's parameters with the receiver's projection of it (`substitute_carrier_params`, keyed by
canonical param VarIds), and keys the result by the FIELD's binding symbols. Wired LAST in
`field_arg_type`, so it runs only where both existing readers declined.

NAMES ARE NOT THE JOIN, and the user raised exactly this ("do not assume names in type
arguments are short — `MyType[T = x.S, S = x.T]`"). It is load-bearing twice: the projection
MEMBER comes from the ARGUMENT SORT's parameter that the provision names (`Element ↦ Stream.T`
⟹ `s.T`), never from the field's key; and the field-key ↔ provision-key match is by the spec's
canonical param VarId, not by short name.

(2) THE "RELATED" HALF DOES HAVE A DRIVER — `enclosing_requires_provision_bindings`, the
ambient-`requires` face of `carrier_provision_short_bindings`. The ticket records that WI-590
implemented it, verified it worked, and removed it because "the only fixture that drove it also
type-checked with the change backed out". That is a property of the RETURN, not of the face: a
return spelled as the constructed carrier (`-> MappedStream[Source = C, …]`) seeds every
still-free param from `expected` AFTER the field loops, so nothing needs to thread. Route the
return through the carrier's PROVISION instead (`-> Seq[Elem = Dst, Row = {E, EffP}]`) and
`expected` has nothing to pin — MEASURED RED without the face, green with it. So it ships, with
a driving test and the unmeasurable fixture KEPT as a control that says why.

Its gates are the construction-side twins of `enclosing_requires_licensing_clause`'s: the
clause must be ABOUT THIS ARGUMENT (VarId identity through the body rigids), and it reads
`direct_requires`, not the flattened chain — a transitively required spec's clause is written
in ANOTHER sort's variables.

THE TICKET'S ROW-WRAP WARNING DOES NOT HOLD as written ("the effect value must NOT be
row-wrapped on that path … wrapping yields `ES = {E}` which the witness's own `requires
FiniteCollection[E = ES]` then cannot discharge against `E`"). MEASURED: with the existing wrap
in place (`sort_param_is_effect_row && !is_effects_rows_term`), the full consolidation runs at
the same single failure it has without the ambient face at all. No un-wrapped variant was
needed.

(3) TWO REAL DEFECTS THE REVIEW CAUGHT, both now fixed and pinned:
  * a `requires`-clause value was bound VERBATIM when it was neither a bare enclosing-param ref
    nor ground, so a COMPOUND value's leaves (`Element = Option[T = Other]`, a row `E = {ES}`)
    stayed free unification variables and the sibling field bound them to whatever the call
    supplied — granting a licence and binding a wrong rigid together. Now every enclosing
    parameter is substituted to its body rigid however deep, and what is still undetermined
    makes the whole clause decline.
  * `bare_spec_arg_provision_projection` used `substitute_carrier_params`' result with NO
    groundness gate, which that function's own doc requires of its callers and its other caller
    does. A provision binding a spec param to a FOREIGN sort's parameter (`provides
    Walk[Element = Other.X]`) survived substitution as a bare parameter ref and then UNIFIED
    with the sibling field instead of contradicting it — MEASURED loading clean where the
    concrete twin `Element = Int64` was correctly refused.
  Also made the WI-594 gate's sort compare CANONICAL, matching the new reader's: with a raw
  `Symbol` compare, one logical sort under two import-scope symbols declined in BOTH arms and
  the receiver threaded nowhere.

TESTS — `wi_mdwew_bare_spec_arg_provision_test.rs`, 8 cases, 3 driving + 5 controls. Every
refusal control asserts the DISTINGUISHING token, not just `!errs.is_empty()`. Five back-outs
measured, each turning exactly its own rows red:
  * `bare_spec_arg_provision_projection` → None: the 2 provides-face driving tests.
  * projection member taken from the FIELD's key (the WI-594 spelling): ALL THREE provides-face
    tests — the main one at `expected s.Element -> ?_, got s.Elem -> ?Dst`, the transposed one
    building `Hold[HL = x.Left, HR = x.Right]` (swap dropped), and the refusal control ACCEPTING
    the transposed return. That is the back-out that judges the predicate.
  * `enclosing_requires_provision_bindings` → None: the ambient driving test alone.
  * widened "about this argument" gate: its control alone, by loading a program nothing licenses.
  * either groundness gate dropped: its own control alone.

FOR WI-590, measured: with this change and the consolidation applied, `anthill-core` is at
1 failing test, DOWN FROM THE 6 the ticket lists. `wi594_finite_map_effect_threading_test::
bare_receiver_map_threads_source_effect` passes, and so does the ENTIRE wi614 group (4 tests) —
the `map_then_iterator_count.effects: undeclared effect ?_` left un-root-caused was the SAME
defect, not four separate ones. The one remaining is `wi1048_requires_shadow_refinement_test::
finite_map_refuses_a_stream_return`, the fixture question WI-590 already flagged ("check
whether the refusal it pins is still expressible"), not a kernel gap.

ARTIFACT — the saved `scratchpad/wi590-stdlib.patch` the ticket points at was in /tmp and a WSL
restart wiped it. Rebuilt from the diff, verified byte-exact by `git apply --check`, same 335
lines, and stored OUTSIDE /tmp at `~/anthill-artifacts/wi590-stdlib.patch`.

Shipped tree: full workspace 5705 passed / 0 failed (35 binaries); scaland 520 / 0.

### 2026-08-28T13:11:38Z — feedback — user

CORRECTION to the figures in the note above — it was drafted before the LAST review round and is stale on three counts.

A THIRD defect was found and fixed after it: both call sites still claimed a FOREIGN sort's parameter whose SHORT NAME COLLIDES with one of the anchor sort's. Root: `substitute_carrier_params` joins its leaves through `type_param_vid_in_sort`, which resolves a symbol by LOCAL NAME anchored to the sort — the very join `enclosing_requires_licensing_clause`'s `rigid_of` has a comment refusing to use. MEASURED at both sites: with `Foreign` declaring `X` and `Element`, a clause `Element = Foreign.X` was refused while `Element = Foreign.Element` LOADED CLEAN — two rows differing only by a name coincidence, and `T`/`E`/`C`/`Element` collide routinely across the prelude. Guarded at the CALLERS (`param_leaves_belong_to_sort`, asking the leaf's DECLARING SCOPE), not inside the shared function.

FINAL FIGURES: 10 tests (3 driving + 7 controls), SIX back-outs measured, workspace 5707 passed / 0 failed. Consolidation cross-check re-run with every fix in place: still 1 failing test (wi1048), wi594 and the whole wi614 group green.

Committed as e628c092.

