## Attributes

- id: WI-20260828-MDWEW-typer-project-a-bare-spec
- created: 2026-08-28T08:49:52Z

- status: Open
- status_agent: user
- status_at: 2026-08-28T08:49:52Z

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

