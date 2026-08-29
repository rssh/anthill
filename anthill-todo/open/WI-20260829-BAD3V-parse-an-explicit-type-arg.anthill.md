## Attributes

- id: WI-20260829-BAD3V-parse-an-explicit-type-arg
- created: 2026-08-29T20:57:07Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T20:57:07Z

- acceptance: cargo-test, scaland-sbt-test

## Description

PARSE: an explicit type-arg bracket is admitted on a dot call ONLY where the receiver is a NAME — a CHAINED hop cannot take one, so the repair a type-arg error suggests is unavailable exactly where it is needed.

FILED BECAUSE THE GAP HAD NO OWNER. It was recorded only inside DELIVERED items —
WI-439's delivery note and WI-20260829-X13YV's description — and a delivery note is not a
queue: nothing lists it, so nothing picks it up. Same shape as WI-20260829-70XVH.

BOTH OF THOSE NOTES ARE WRONG, and this is the measurement rather than their words.
Probed with `parse::parse` on one fixture, varying ONLY the receiver:

  A  xs.map[Dst = Int64](f)                        PARSES   -- dot, NAME receiver
  B  xs.map(f).map[Dst = Int64](g)                 SYNTAX ERROR -- dot, CALL receiver
  C  (xs.map(f)).map[Dst = Int64](g)               SYNTAX ERROR -- parens do NOT rescue it
  D  map(xs, f).map[Dst = Int64](g)                SYNTAX ERROR -- unqualified-call receiver
  E  Iterable.map(xs, f).map[Dst = Int64](g)       SYNTAX ERROR -- qualified-call receiver
  F  xs.map(f).map(g)                              PARSES   -- CONTROL: B without the bracket
  G  map(xs, f).map(g)                             PARSES   -- CONTROL: D without the bracket
  H  xs.map[Dst = Int64](f).map[Dst = Int64](g)    SYNTAX ERROR -- 2nd hop's receiver is a call
  I  xs.map[Dst = Int64](f).map(g)                 PARSES   -- bracket on hop ONE is fine

  and the two spellings the notes named:
     map[Dst = Int64](xs, f)                       PARSES   (unqualified)
     Iterable.map[Dst = Int64](xs, f)              PARSES   (QUALIFIED)

CORRECTIONS THIS FORCES:
  * WI-439's note says 'a QUALIFIED call with explicit type-arg brackets, e.g.
    FilteredStream.filter[S = Int64, Eff = {}](...), is a syntax error; only the
    unqualified-import form takes brackets.' NOT TRUE TODAY -- the qualified form parses.
    Presumably closed by WI-311's parameterized_type+instantiation_term merge; nobody
    re-measured the note.
  * WI-20260829-X13YV's description says 'a dot call takes no explicit type-arg bracket.'
    FALSE AS STATED -- row A parses. What fails is a dot whose RECEIVER IS COMPOUND.

THE ACTUAL RULE: the bracket is admitted where the dot's receiver is a NAME, and refused
where it is a CALL or a PARENTHESIZED expression. C is the row that says this is the
grammar's term/body split rather than an application-shape issue, and it is the same wall
WI-20260829-YBBC3 hit ('no compound expression is a term; parentheses do not rescue them'
-- grammar.js puts compound forms in _expr_body while every nested slot is _term, and
paren_expr wraps a _term). Start there.

WHY IT MATTERS BEYOND TIDINESS: a type-arg error's own message says 'use map[EffS = ...](...)'.
On a chained hop that repair DOES NOT PARSE, so the diagnostic sends the author somewhere
the grammar will not follow. That was live until WI-20260829-X13YV removed the shape that
produced the message; the grammar hole is untouched, and any future unconstrained
type-param on a chained dot re-exposes it.

RELATED, NOT DUPLICATE: WI-465 is the other axis -- what may appear INSIDE the brackets
(Modify[f(x)], computed type args). This is about WHERE a bracket may appear.

ACCEPTANCE: rows B, C, D, E, H parse; A, F, G, I still parse (they are the controls, and
they pass either way today -- say so at the site); a corpus test in tree-sitter-anthill plus
a parse::parse row per spelling; and correct the two delivered notes' claims where they are
quoted, or leave a pointer here so the next reader does not re-derive them.

