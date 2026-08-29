## Attributes

- id: WI-20260829-BAD3V-parse-an-explicit-type-arg
- created: 2026-08-29T20:57:07Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-29T22:29:25Z

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

## Changes

### 2026-08-29T22:29:26Z — feedback — claude

DELIVERED. The grammar admits the type-arg bracket on a dot callee (`dot_application` in
`fn_term`'s callee slot, with a declared GLR conflict so the trailing `(` decides), and the
CONVERTER decides what it means.

THE TICKET'S DIAGNOSIS WAS WRONG TWICE, and the measurements are the delivery:

(1) NOT the term/body split. The ticket said row C places this on WI-20260829-YBBC3's wall
("parentheses do not rescue them -- start there"). The CST says otherwise: `paren_expr`
already wraps an `_expr_body`, and the `field_access` over it BUILDS FINE. The `[` was
being taken as the DECLARATION'S `meta_block`, which is why the reported syntax error
landed on the `=` inside a misread `meta_entry`. The cause is one line: `application`'s
base is `name | absolute_name`.

(2) NOT "a chained hop cannot take one". The FIRST hop over a plain variable,
`?xs.map[Dst = Int64](f)`, was a syntax error too, as was `[1,2].map[...](f)`. And row A
parses only because `xs.map` is a dotted NAME, which the converter reads as the qualified
functor `xs.map` -- not a dot call at all. So the real rule: the bracket was admitted only
where the callee was a NAME PATH, which is exactly where the call is NOT a dot call. NO
value-receiver dot could take one, at any depth.

WHAT IT MEANS NOW, decided in the converter, not the grammar:
  * QUALIFIED companion receiver -- `Map[K = String, V = Int64].empty[T = Int64]()` is the
    call's type arguments, on the same `type_args` channel `Map.empty[T = Int64]()` feeds.
    NEW capability, driven end to end (`a_companion_receiver_call_drives_its_type_argument`
    evaluates `Box[E = Int64].ty[T = String]()` to `Cell[V = String]`; the receiver's own
    binding differs from the bracket's on purpose, so a dropped or swapped binding shows).
  * VALUE receiver -- REFUSED with a located error naming the applicative SHAPE.
    `Expr::DotApply` carries no `type_args` field; "a dot is bracket-less by construction"
    is the WI-842 premise the typer's tier-1 reasoning rests on, and proposal 058's ladder
    rung 3 states it as design ("a value-directed site carries no bracket"). So the refusal
    is the intended answer, not a placeholder -- NO follow-up filed.

TWO ROUTES REACH A DOT CALL AND BOTH ARE COVERED, the second found by /code-review:
`?x.m[...](...)` is a `dot_application` node, refused in the converter; `xs.m[...](...)`
where `xs` names a LOCAL has a bare NAME callee and becomes a dot call only in the LOADER
(`try_identifier_dot_call`, WI-443) -- refused there via a new
`CallTypeArgsPosition::DotCall`. That route was still live after the first cut: the bracket
made WI-443 decline the re-route, the call flattened to functor `xs.map`, and the author
read the typer's verdict on THAT ("got a callee with no type-parameter list"), naming a
callee nobody wrote. The loader now announces the drop and re-routes anyway -- mirroring
the converter's peer, which refuses and then builds the dot call without the bindings.
MEASURED: bracketed = exactly 1 error, the bracket-less control = 0.

WHY A SEPARATE PRODUCTION, MEASURED against the alternative (widen `application`'s own base
to admit a `field_access`): it does not GENERATE -- `application` is reachable from `_type`,
so three further GLR conflicts were needed, two in type positions. Forced through, `?x.m
[simp]` reads as `application(field_access(?x,m), sort_binding(simp))` with meta NONE: the
attribute EATEN and the equation INERT, the WI-881 trap extended to every dot head. The
tree-sitter corpus stayed 214/214 green under it -- `wi_bad3v_dot_type_arg_bracket_test`
is what fails.

/code-review (high) raised four, all reproduced and all repaired: (1) the refusal
prescribed "in an operation body" to a RULE HEAD -- the exact defect WI-839 split
`CallTypeArgsPosition` to avoid; it now names a shape and no position. (2) the
identifier-receiver route above. (3) scaland's message repair was wrong for the companion
shape, and the receiver-classification divergence is newly load-bearing (0 occurrences in
stdlib/examples -- censused). (4) the corpus pinned only `[simp]`, so it did not measure
the juxtaposition class: a NON-meta bracket takes a following entry's `(`, changing a
3-entry read into 1. Both readings refuse the program, so nothing that loaded stops
loading; pinned with a second corpus row, and the grammar comment's "has no `(`" claim --
true of the LINE, false of the FILE -- corrected.

Corrections filed as feedback on WI-439 and WI-20260829-X13YV. Spec: kernel-language.md
§"the bracket is read in exactly two positions". Scaland mirrored (`fieldSeg` admits the
bracket only when a call follows, matching the grammar's narrowness).

TESTS: rustland 36 binaries / 6127 passed / 0 failed; scaland 523/523; tree-sitter corpus
224/224. New: `wi_bad3v_dot_type_arg_bracket_test` (9), `dot_type_args.txt` (10 rows),
3 scaland ParseTest cases.

