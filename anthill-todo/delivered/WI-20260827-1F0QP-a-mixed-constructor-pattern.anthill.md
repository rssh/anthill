## Attributes

- id: WI-20260827-1F0QP-a-mixed-constructor-pattern
- created: 2026-08-27T21:41:51Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-29T18:42:34Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A MIXED CONSTRUCTOR PATTERN AND A MIXED CONSTRUCTOR APPLICATION READ THE SAME SPELLING DIFFERENTLY, and the pattern side loses SILENTLY -- the arm simply does not match, so a later arm answers instead.

MEASURED 2026-08-27 while delivering WI-20260827-T2470, on the tree with that fix in:

  sort Two
    entity two(a: Int64, b: Int64)
  end
  operation twoMix() -> Two = two(2, a: 1)        -- APPLICATION: 2 fills `b`
  operation punmix(t: Two) -> Int64 =
    match t
      case two(y, a: 1) -> y                      -- PATTERN: y is given field `a`
      case two(p, q)    -> 0
  rule gmix(1)  :- C.twoMix() = two(a: 1, b: 2)   -> true   (after T2470)
  rule gpat(1)  :- C.punmix(two(a: 1, b: 7)) = 7  -> NO SOLUTIONS
  rule gpat0(1) :- C.punmix(two(a: 1, b: 7)) = 0  -> true   -- the FALLTHROUGH arm ran

THE TWO SIDES USE TWO DIFFERENT RULES. The APPLICATION side goes through the shared
`positional_to_named_plan` (rustland/anthill-core/src/kb/resolve.rs), whose rule is
RANK AMONG THE FIELDS NOT ALREADY GIVEN BY NAME -- so `two(2, a: 1)` puts 2 in `b`.
The PATTERN side has its own open-coded copy that fills the LEADING field indices:
`match_constructor_pattern` (rustland/anthill-core/src/eval/pattern.rs, the
`covered[i] = true; sub_values[i]` loop) gives the positional sub-pattern index 0
(= `a`), then the named `a: 1` finds index 0 already covered and returns None.
`fresh_pattern_occ` (rustland/anthill-core/src/kb/resolve.rs) has a SECOND copy of the
same leading-index rule (`fields.get(i)`) for the WI-580 unfold's pattern occurrences,
so the resolver path is expected to agree with eval and would need the same repair;
it was NOT separately driven here.

ALL-POSITIONAL AND ALL-NAMED PATTERNS ARE FINE -- `case two(p, q)` and
`case two(a: 1, b: ?)` both work. Only the MIXED spelling diverges, which is why
nothing has found it: the stdlib writes patterns one way or the other.

TWO READINGS AND THE TICKET MUST PICK ONE. docs/kernel-language.md states the
rank-among-not-named rule for SORT BINDINGS (S5.2) and for OPERATION CALLS (S2210,
`pair(b: 2, a: 1)` fills both slots) but says nothing about constructor PATTERNS.
Either (a) a mixed pattern means what the mixed application means, and both sides
must share `positional_to_named_plan`; or (b) a mixed constructor pattern is
ill-formed and must be a LOAD ERROR naming the field written twice. What is NOT
admissible is today's answer -- a silent no-match that hands the value to whatever
arm comes next, and answers 0 where the program says 7.

ACCEPTANCE: the three rows above driven, with the chosen reading asserted and the
control (`gmix`, and an all-positional and an all-named pattern) asserted unmoved;
a census of the open-coded leading-index copies of the rank rule (`match_constructor_pattern`,
`fresh_pattern_occ`, and whatever else `grep -n 'fields.get(i)\|covered\[i\]'` finds)
with each either routed through the shared owner or stated as exempt and why; the
resolver/unfold path driven separately from eval, since they are two producers; the
spec paragraph written for constructor patterns; full workspace green.

REFERENCE: `positional_to_named_plan` and `fresh_pattern_occ`
(rustland/anthill-core/src/kb/resolve.rs), `match_constructor_pattern`
(rustland/anthill-core/src/eval/pattern.rs), the `gpat`/`gpat0`/`gmix` rows in
rustland/anthill-core/tests/include/wi_t2470_positional_ctor_in_op_body_test.rs.

## Changes

### 2026-08-29T14:48:48Z — feedback — user

DELIVERED with the reading (a) the ticket named -- a mixed constructor PATTERN means what the mixed constructor APPLICATION means (rank among the fields NOT given by name) -- and with a SCOPE EXTENSION the ticket did not ask for, on the user's direction: the same rule now governs a mixed OPERATION CALL too.

THE CENSUS FOUND EIGHT COPIES, not the two the ticket named. `positional_to_named_plan` was split so the rank rule itself (`rank_positional_among_unnamed`, taking an explicit field list + an `is_named` predicate) is callable by the sites that key a field by SHORT NAME or already hold the declaration list, so all eight share one owner:

  1. eval::pattern::match_constructor_pattern      -- the runtime matcher (the ticket's)
  2. kb::resolve::fresh_pattern_occ                -- the WI-580 unfold (the ticket's).
     Carried a SECOND defect on the same line: `sort_by_key(s.index())` is INTERNING
     order where the canonical entity form is DECLARATION order; now
     `canonicalize_record_named_args`.
  3. kb::body_specialize::match_ctor_fields        -- the compile-time matcher. Worst:
     its wrong answer was PatOutcome::No, a DEFINITE non-match that prunes the arm.
  4. kb::body_specialize::ctor_field_occs          -- the SCRUTINEE side. A mixed
     constructor OCCURRENCE read as undecidable, so the specializer left a residual
     `match` over a value.
  5. eval::pattern::constructor_sub_values         -- the eval SCRUTINEE side. Its doc
     ASSERTED sub-values are in declaration order; concatenating pos ++ named made that
     false for a mixed carrier. Now established rather than assumed.
  6. kb::typing pattern binder typing              -- WHICH declared type a positional
     binder gets. Invisible while an entity's fields share a type; a WRONG BINDER TYPE
     when they don't.
  7. kb::typing::ctor_arg_unlocks_an_arrow_for_a_bare_name -- the arrow-hint heuristic.
  8. kb::load query-path `pos_field_type`          -- the expected-type HINT a mixed
     query's positional argument is converted under, which disagreed with the field the
     desugar put it in.

THE OPERATION-CALL EXTENSION (three more sites). Measured while writing the census:
`add2(2, a: 1)` was a LOAD ERROR ('named argument a binds a parameter already given')
while the constructor `two(2, a: 1)` was legal -- one shape, two answers, two models
for an author to learn. Filed as a follow-up first; the user directed that it be the
same rule, so it was folded in and the follow-up deleted:

  9.  kb::typing::bind_call_arguments        -- the coverage check that refused it
  10. kb::typing::reorder_named_args_in_apply -- THE SECOND PRODUCER, and the reason a
      typer-only fix would have been worse than the bug: the runtime binds argument i to
      parameter i (`start_apply` streams pos ++ named, `enter_operation` zips against
      params), so merely admitting the call would have bound it BACKWARDS. A mixed call
      is now rewritten ALL-POSITIONAL in parameter order -- the shape an all-positional
      call already has, so no downstream reader sees a novel form.
  11. kb::body_specialize::bind_params       -- the specializer's own copy.

STATED EXEMPT, each with a reason at the site: the TUPLE pattern alignment (S4.5 makes a
tuple's order its IDENTITY -- `canonicalize_record_named_args` is already a deliberate
no-op for an ordered product); named-argument SUBTYPING (`b_covered` matches actuals to
actuals); and kb::mod's spec-op carrier walk (it reads a GOAL at arity + 1, so ranking
would take the RESULT COLUMN for an argument, and WI-938 requires named_arity 0 so a
named-arg goal never becomes a call anyway).

SPEC: docs/kernel-language.md S6.3 now states the rule for constructor applications AND
patterns AND operation calls, with the worked `two` example. It did not state it for
constructors at all before.

TESTS: `wi_1f0qp_mixed_ctor_pattern_test` -- one row per PRODUCER, since a fix to one is
invisible to the others, each DRIVING the capability (resolve the goal, assert the
value) rather than asserting a clean load. The per-site back-out matrix is in its header,
measured by reverting one file at a time. Two rows pass either way BY DESIGN and say so:
an all-positional and an all-named pattern, and the mixed APPLICATION. `wi_t2470`'s
`gpat`/`gpat0`, pinned at their wrong values for this ticket to flip, are flipped and
the test renamed `a_mixed_constructor_pattern_now_agrees_with_a_mixed_application`.

The typer row is the only one that cannot be made site-pure, and the header says so:
proving a BINDER'S TYPE requires running the operation, and running it goes through the
matcher.

