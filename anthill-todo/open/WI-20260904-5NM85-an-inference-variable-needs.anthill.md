## Attributes

- id: WI-20260904-5NM85-an-inference-variable-needs
- created: 2026-09-04T15:58:57Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T15:58:57Z

- acceptance: cargo-test, scaland-sbt-test

## Description

An inference variable and a resolution variable are THE SAME TYPE — both `Var::Global(VarId)`
— so nothing can tell an escaped one from a legitimate one, and no check can be written.

WHERE THE CHECK WOULD GO, if it could be written: `DiscrimTree::insert_walk`
(`kb/discrim.rs`) is the single funnel where a term becomes index keys. But a blanket "no
`Var::Global` here" assert is FALSE — that site's own comment says a flex `Global` is an
EXPECTED stored-pattern variable ("a flex `Global` / bound `DeBruijn` is a WILDCARD pattern
var"). The only thing separating the two populations today is the NAME (`?param`, `?pat`),
and WI-1079 already ruled that out: "`id` IS THE IDENTITY AND `name` IS NOT".

WHY IT MATTERS — the hazard, stated correctly after three wrong tries in
WI-20260904-50B2K and WI-20260904-02ERR:

  * it is NOT "wildcard semantics are wrong". A flex var is an unfilled variable and
    matching any subterm is unification working.
  * it is NOT "a dangling variable in stored data". That is ordinary: `p(?X) :- q(?X)`
    stores a free variable and it is fine.
  * IT IS RENAMING. `Var`'s own doc: `DeBruijn` is "the canonical representation in stored
    terms", `Global` is "used during resolution AFTER OPENING binders". So a `Global` in a
    stored term HAS ALREADY BEEN OPENED AND WILL NEVER BE OPENED AGAIN — every use shares
    ONE variable, and a binding made at one use leaks to all the others.

MEASURED 2026-09-04 — UNREALIZED TODAY. A probe in `insert_walk` watching for a
`Var::Global` named `?param` / `?pat` fired ZERO times across 1485 tests. So the hazard is
real in principle and does not occur in the corpus. That is a LOWER BOUND (the corpus is
not the population), which is exactly why a structural check would be worth more than the
probe.

THE CARRIER DOES NOT FIX IT, and that is why this is its own ticket rather than part of
WI-20260904-02ERR. An escaped `Global` is an escaped `Global` in any carrier:
`Term::Var(Global)` interned as a `TermId` and a `TypeNode::Var` occurrence have IDENTICAL
behaviour here. 02ERR's `Node` shape fixes the LEAK (a permanently-refcounted store entry
per binder) and adds PROVENANCE (span + owner); it does not make an escape checkable.
Interning adds no aliasing risk of its own — `fresh_var` increments monotonically, so
`VarId`s are never reused.

THE SHAPE: a fourth `Var` kind beside `DeBruijn` / `Global` / `Rigid`, for a variable that
belongs to ONE type-check pass. Then `insert_walk` asserts against it soundly, and the
distinction stops riding on a name.

  IT IS THE SAME CORRECTION THIS AREA KEEPS NEEDING — one representation answering two
  questions. `type_var` answered "no type is available" and "to be inferred"
  (WI-20260904-50B2K); `TypeChild::Ground` answered "hash-consable" and "variable-free";
  `Var::Global` answers "resolution variable" and "inference variable". Each was found by
  asking what a name meant, not by a failure.

  WHAT TO WEIGH: `Var` is a hot, deeply-matched type (the discrimination tree keys on its
  kind, `unify_types` branches on it, reflect renders it). A fourth kind is a bigger blast
  radius than 02ERR's carrier change, and the population is every `match` on `Var` — census
  the CATCH-ALLS first, since a `_ =>` treating the new kind as flex is the silent failure.
## Changes

### 2026-09-04T19:39:56Z — feedback — user

At first, it is not about global vars only - rigid vars also can be from typing.  At second - how ids can clash? after typing? We know that befre typng wer have no unvloded typing variables.  And befroe running we have no global non-typing variables (because they are deBjumed). So,  if we see non-de-Buijed variable before rule, this is from typing. Can open vaiable be not -error,  maybe it should be deBjuined back after typing ?

