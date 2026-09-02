## Attributes

- id: WI-20260902-T8H1W-scaland-has-no-partial-entity
- created: 2026-09-02T13:10:23Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T13:10:23Z

- acceptance: cargo-test, scaland-sbt-test

## Description

SCALAND HAS NO PARTIAL-ENTITY EXPANSION AT ALL, so §8.3's bare-entity goal is empty in BOTH nullary spellings.

MEASURED BY ME while checking WI-20260902-VNWAW's scaland acceptance (one file, both
qualifications, `sbt testOnly` on the delivered tree):

  namespace zzent.inner
    entity acct(n: Int64)
    fact acct(n: 1)
    rule bare(1)    :- acct        -- 0
    rule paren(1)   :- acct()      -- 0
    rule applied(1) :- acct(n: 1)  -- 1   <- the control that answers
  end
  namespace zzent.outer
    rule dotBare(1)    :- zzent.inner.acct        -- 0
    rule dotParen(1)   :- zzent.inner.acct()      -- 0
    rule dotApplied(1) :- zzent.inner.acct(n: 1)  -- 1
  end

rustland answers 1 on all six. The program loads clean in both, exit 0.

THE MECHANISM, traced: `KnowledgeBase.entityFieldNames` exists and is filled, and has
ZERO readers in scaland's main tree (`grep -rn entityFieldNames core/src/main/scala`
finds only its own declaration). So scaland has none of §8.3's "Partial entity patterns"
— not the bare case this row shows, and not the PARTIAL one either: `acct()` and
`acct(n: ?)` are ordinary terms that match only a fact spelling them identically. The
bare case is merely the loudest end of it.

NOT VNWAW'S AND NOT A DOTTED QUESTION. Both qualifications answer alike at every cell, so
there is no dotted-vs-one-segment divergence to close there; VNWAW's rustland fix has no
scaland mirror for exactly this reason and its scaland test PINS these rows so this ticket
has a fixture to flip. It is the F2 half of WI-20260902-CZJ2N — whose commit message says
"scaland mirrored end to end", which measured is true of the storage canon and the head
mint and NOT of §8.3's expansion.

SIZE: not a one-liner and that is why it is a ticket rather than an inline fix. It is the
whole partial-pattern feature — read the declared field list, fill the absent fields with
fresh vars, and take rustland's value-position asymmetry with it (WI-716: an absent
OPTIONAL fills with `none()` in a value position and a fresh var in a pattern, or a query
finds only the facts whose optional is absent) — at scaland's logical-position entry
points, which `reallocTerm`'s `atGoal` parameter already names.

ACCEPTANCE: the six rows above answer 1 in scaland, and a PARTIAL pattern
(`acct(n: ?)` against a two-field entity) answers too — the bare case alone would pass
with a bare-name special case that is not the rule §8.3 states. CONTROLS: a DATA slot must
keep the reference (`?t <=> acct` binds the name, not a fresh pattern) — rustland's split,
and a fixture driving only the goal position would pass with it broken; and a fact whose
field DISAGREES must still not match, so the fresh-var fill is not a wildcard on the
functor.

