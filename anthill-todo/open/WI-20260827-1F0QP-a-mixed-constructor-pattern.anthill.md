## Attributes

- id: WI-20260827-1F0QP-a-mixed-constructor-pattern
- created: 2026-08-27T21:41:51Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T21:41:51Z

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

