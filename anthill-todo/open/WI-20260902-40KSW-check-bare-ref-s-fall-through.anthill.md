## Attributes

- id: WI-20260902-40KSW-check-bare-ref-s-fall-through
- created: 2026-09-02T14:18:22Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T14:18:22Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`check_bare_ref`'s FALL-THROUGH SAYS "unresolved" ABOUT A NAME THAT RESOLVED, once per segment of a dotted chain.

MEASURED BY ME while delivering WI-20260902-4NEKZ, which closed the ONE row of this
matrix that differed between the two positions and left the other five, since they are
IDENTICAL in both and therefore not a dotted-spelling question:

  chain names        operation body     rule body     (after 4NEKZ)
  a RULE                  1 error          1 error    <- 4NEKZ closed this
  a CONSTRUCTOR           3 errors         3 errors
  a SORT                  2 errors         2 errors
  a NAMESPACE             2 errors         2 errors
  an ENTITY               2 errors         2 errors
  NOTHING                 3 errors         3 errors

  e.g. `rule r(1) :- zzm.Color.red = 7` with `sort Color  entity red  end`:
    9:16: type mismatch in zzm.name:   expected resolved name, got unresolved
    9:16: type mismatch in Color.name: expected resolved name, got unresolved
    9:16: type mismatch in red.name:   expected resolved name, got unresolved

TWO FAULTS, and the second is the one with teeth:

 1. ONE ERROR PER SEGMENT. A single written name produces N diagnostics at ONE span,
    which the author must read as one. `zzm = 7` (a bare NAMESPACE, one segment, no dot)
    produces one, so the cascade is just the chain being walked leaf by leaf.

 2. THE MESSAGE IS FALSE. `zzm`, `zzm.Color` and `zzm.Color.red` all RESOLVE — to a
    namespace, a sort and a constructor. `TypeError::UnresolvedName` renders as "expected
    resolved name, got unresolved", and it is `check_bare_ref`'s FALL-THROUGH: the rungs
    above it answer for a local, a const, a constructor-with-expected, an eta lift, a
    zero-arg op call, a free-standing entity, a sort IN A `Type` SLOT, a relation, an
    equation functor — and anything else, RESOLVED OR NOT, lands on a message that says
    the name does not resolve. An author told "red does not resolve" about a constructor
    that is right there will look for a typo or a missing import; the truth is that a
    constructor has no VALUE reading in that slot.

    Note the SORT rung is deliberately gated on a `Type` slot (WI-206: "gating on the
    expected type keeps a stray sort name in an ordinary value position the loud
    `UnresolvedName` it is today") — so this fall-through is LOAD-BEARING for the sort
    case and cannot simply be deleted; what it needs is to distinguish "no such name" from
    "this name has no value reading here".

ACCEPTANCE: a resolved name with no value reading in the slot is reported ONCE per
written name, with a message that says what the name IS and why it cannot stand there —
never "unresolved". A chain naming NOTHING is still reported once, and still says so.
CONTROLS: a genuinely absent name must keep a diagnosis an author can act on (WI-1034's
"names nothing" census and repair); the SORT-in-a-`Type`-slot rung must keep answering
(WI-206); 4NEKZ's rule row must stay at one `eq.b (op-arg)` error; and the OPERATION BODY
and the RULE BODY must move TOGETHER — they agree today at every one of these five rows,
and a fix applied at one position only would re-open the split 4NEKZ just closed.

