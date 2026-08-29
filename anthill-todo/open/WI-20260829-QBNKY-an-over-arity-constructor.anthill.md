## Attributes

- id: WI-20260829-QBNKY-an-over-arity-constructor
- created: 2026-08-29T14:51:50Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T14:51:50Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260827-1F0QP-a-mixed-constructor-pattern

## Description

AN OVER-ARITY CONSTRUCTOR PATTERN LOADS CLEAN -- `case two(p, q, r)` on `entity two(a: Int64, b: Int64)` -- and is refused only later, by whichever consumer happens to notice.

MEASURED 2026-08-29 while delivering WI-20260827-1F0QP:

  sort Two
    entity two(a: Int64, b: Int64)
  end
  sort C
    operation pick(t: Two) -> Int64 =
      match t
        case two(p, q, r) -> p        -- THREE sub-patterns, TWO fields
        case two(x, y) -> 0
  end

  -> `anthill check` reports 118 pass, 0 failed. IT LOADS.

THE TERM SIDE IS REFUSED AND THE PATTERN SIDE IS NOT. An over-arity constructor TERM is
a located load error naming the constructor and its declared fields
(`PositionalPlan::OverArity` -> the loader's `convert_term_with_expected`); the PATTERN
spelling of the same over-arity reaches no such check. That asymmetry is what makes
`anf_flatten`'s 'the loader already refuses this shape, so reaching it means a
runtime-built term' comment TRUE for terms and FALSE for patterns.

WHAT EACH CONSUMER DOES WITH IT TODAY, and no two agree:
  * `match_constructor_pattern` (rustland/anthill-core/src/eval/pattern.rs) refuses it at
    MATCH TIME via the arity-strict `pos + named != n` test -- so the arm silently does
    not match and a later arm answers, which is the WI-20260827-1F0QP failure mode all
    over again, one level up;
  * `fresh_pattern_occ` (rustland/anthill-core/src/kb/resolve.rs) DECLINES THE WHOLE
    UNFOLD -- so the case-split does not happen and the goal residualizes. Measured:
    `rule g(?t) :- C.pick(?t) = 0` answers '1 solution, 1 conditional (residual goals
    undischarged)' where a well-formed program decides;
  * `match_ctor_fields` (rustland/anthill-core/src/kb/body_specialize.rs) answers
    `PatOutcome::No` -- a DEFINITE non-match, statically pruning the arm;
  * the TYPER types the surplus binder from nothing (`field_types.get(i)` past the end
    -> `None`), so it binds untyped rather than being named.

Four consumers, four answers, none of them a diagnostic naming the line.

WI-20260827-1F0QP FOUND THIS BY TRIPPING ON IT. That ticket routed `fresh_pattern_occ`
through the shared `positional_to_named_plan` and, following `anf_flatten`'s precedent,
put a `debug_assert!(false, ..)` on the `OverArity` arm. The assert FIRED on the
fixture above -- an ordinary source program -- so it was replaced with a plain decline
and the measurement written at the site. The decline is correct for that function; what
is missing is the LOAD refusal that would make it unreachable.

ACCEPTANCE: an over-arity constructor pattern is a LOCATED LOAD ERROR naming the
constructor, the sub-pattern count and the declared fields -- the same message shape the
TERM side already emits, from the same `render_field_list` owner, so the two spellings
cannot drift. DRIVE it: assert the error text and its line:col on the fixture above, and
assert a well-formed pattern of every arity (nullary, all-positional, all-named, MIXED)
still loads. Say at the test site which of the four consumers above the refusal makes
unreachable, and restore `fresh_pattern_occ`'s `OverArity` arm to the debug-assert its
sibling `anf_flatten` uses -- that arm becoming assertable again is the check that the
refusal is complete. Full workspace green.

REFERENCE: the `PositionalPlan::OverArity` arm in `fresh_pattern_occ` and its
'MEASURED, ... LOADS CLEAN' comment (rustland/anthill-core/src/kb/resolve.rs), the term
side's refusal in `convert_term_with_expected` (rustland/anthill-core/src/kb/load.rs),
`match_constructor_pattern`'s arity-strict test (rustland/anthill-core/src/eval/pattern.rs).

