## Attributes

- id: WI-20260904-60143-a-discarded-boolean-unify
- created: 2026-09-04T17:21:39Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T17:21:39Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DISCARDED-BOOLEAN `unify_types` LEAVES ITS PARTIAL BINDINGS IN σ, AND SINCE
WI-20260904-50B2K THAT σ IS READ.

RAISED BY /CODE-REVIEW on the 50B2K tree, 2026-09-04. `unify_types` has no
snapshot/rollback: it binds into `subst` as it descends and returns `false` at the FIRST
mismatch, keeping everything it bound before that point. Ten call sites in `kb/typing.rs`
discard the boolean deliberately — the idiom's stated reason is that unify is EQUALITY
while the surrounding check is SUBTYPING plus three conversions, so a unify-false must
not reject:

  typing.rs  9262 14741 15839 15887 15943 16517 18862 18980 23402 44764 44774 44899
             60252 60257 65231   (grep `unify_types(kb, &mut subst`; not all discard)

THE IDIOM WAS HARMLESS WHILE NOBODY READ THE σ AFTERWARDS. 50B2K's edits 2 and 5 changed
that: the arrow-call path now resolves `ret_ty` AND the effect row through the same
`subst` (typing.rs ~19099), and the op-return check hands `types_compatible` the RESOLVED
value (~65231). So an argument that conforms by subtyping can now leave a return type
that depends on HOW FAR unification got before giving up.

THE REVIEWER'S SCENARIO, not yet driven: an arrow slot `Pair[L = Animal, R = ?v]` given
`Pair[L = Dog, R = Int64]`. Unify descends, `Dog` vs `Animal` is a mismatch under
EQUALITY, and whether `?v` was bound to `Int64` first depends on named-arg iteration
order. In the losing order the caller reports a spurious "expected …, got `??param`".

WHY THIS IS NOT AN INLINE FIX AT THE TWO 50B2K SITES. The question is the FILE'S idiom,
not those sites': repairing 2 of ~10 is the "a SHARED CALLEE is the wrong place for a
CALLER's guard" shape in reverse — the other eight keep the behaviour and the next reader
finds two rules. The census is the work.

THE CANDIDATE REPAIR IS CHEAP IF THE CENSUS SAYS SO. `Substitution.bindings` is an
`imbl::HashMap` (WI-569), so `Clone` is O(1) structural sharing — a snapshot is
`let before = subst.clone()` and a rollback is `subst = before`. CHECK BEFORE BELIEVING
IT: `Substitution` also carries `parent: Option<Box<Substitution>>`, whose `Clone` is a
DEEP copy of the chain, plus `contradiction_details` and the constraint store. Measure the
clone at a hot site rather than assuming the map's O(1) covers the struct.

WHAT THE TICKET OWES:
  1. WHICH of the ~15 sites discard the boolean, and for each, whether anything READS the
     σ afterwards. The two 50B2K sites do; the others are the population to establish, not
     to assume.
  2. A DRIVING program for the wrong-value case — a subtyping-conformant argument whose
     partial bindings change a reported type. Without one, a rollback is an unmeasured
     behaviour change and must not ship: some row may DEPEND on a partial binding, which
     is itself worth knowing.
  3. Then either the rollback at every reading site, or a stated rule at
     `unify_types` saying what a caller may assume about σ on `false` — the two-lists
     failure this file has been bitten by is exactly what an unstated one produces.

Pointed at from `validate_arg_against_param`'s Path-2 argument loop (the `ArgValidation::
Ok` arm), so the next reader of that site meets this ticket rather than re-deriving it.

