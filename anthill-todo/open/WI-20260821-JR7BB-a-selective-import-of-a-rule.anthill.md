## Attributes

- id: WI-20260821-JR7BB-a-selective-import-of-a-rule
- created: 2026-08-21T11:36:58Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T11:36:58Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A SELECTIVE IMPORT OF A RULE-INTRODUCED PREDICATE IS SILENTLY SHADOWED BY THE IMPORTING
SCOPE'S OWN HEAD. The author names the predicate they mean to contribute to, and gets a
second predicate plus a dead import.

MEASURED (rustland, current tree), the same intent in two spellings:
  namespace X { import Y.{p}  rule p(?x) :- f1(?x) }
  namespace Y { import X.{p}  rule p(?x) :- f2(?x) }
      -> LOADS. `X.p` = 1 clause, `Y.p` = 1 clause. TWO predicates. Each scope holds a
         local `p` AND an import alias `p -> the other's p`; `resolve_in_scope` checks
         locals before imports, so the alias is DEAD and every bare `p` in that
         namespace means the local -- the opposite of what was written.
  the same program with `import Y.*` / `import X.*`
      -> REFUSED, "no scope introduces the rule head `p`" (WI-980's cycle rule).
  one-way `import Y.{p}` with no reciprocal import
      -> LOADS, still two predicates, still a dead alias.

WHY THE SPELLINGS DIVERGE. `ImportKind::Wildcard` splices the target scope in as a
resolution parent during sub-pass 2, so WI-980's decision sees it. `ImportKind::Selective`
naming a rule-introduced predicate CANNOT resolve in sub-pass 2 -- the head-functor symbol
is not registered until sub-pass 3 -- so it is deferred to `pending` and wired by sub-pass
4, AFTER the decision and after every mint (WI-295). The guard therefore never sees the
one spelling that states the author's intent explicitly.

IT IS §WI-896's OWN NAMED HAZARD, from the other side: "introducing instead would put a
scope-local ahead of the candidates and decide the conflict silently". Here the conflict
is not even reported -- the local simply wins.

THE DECISION THIS NEEDS. Either the selective import must be visible to the mint guard --
which means resolving a rule-head import before sub-pass 3 decides, i.e. reordering or
splitting sub-pass 4 -- or a head whose name is selectively imported in the same scope
must be refused as a capture (059 R4 clause 3 refuses exactly this shape for
DECLARATIONS). What is not defensible is the present answer: accept both, let the local
win, and say nothing.

WATCH FOR: WI-295 exists because the deferral is what makes cross-namespace predicate
imports work at all (`import anthill.prelude.Bool.{ite}` is how `ordered.anthill` and
`int64.anthill` reach `bool.anthill`'s laws). Any reordering has to keep that working --
those are imports WITHOUT a competing local head, and they must stay silent.

ACCEPTANCE: the two spellings above must agree. Drive it: assert how many predicates
exist and that a bare `p` in each namespace resolves to the one the author named. Keep
the stdlib's `Bool.{ite}` shape as a control -- an import with no competing head still
resolves and still loads clean. cargo-test green via rustland/scripts/test.sh.

## Changes

### 2026-08-21T11:40:15Z — feedback — user

THE SHARPER STATEMENT (user, 2026-08-21): `import Y.{p}` MUST BE A SUBSET OF `import Y.*`.
For the name `p`, the two spellings have to give identical visibility -- the wildcard
brings in everything the selective one brings in. They do not, and MEASURED the break is
in exactly one place, the mint decision:

  imported name is a DECLARED operation                   wildcard == selective   OK
  RULE-INTRODUCED, importing scope writes NO head of it   wildcard == selective   OK
  RULE-INTRODUCED, importing scope ALSO writes a head     wildcard: X.p ABSENT (X yielded to Y)
                                                          selective: X.p EXISTS (X minted its own)

And the direction is backwards: the NARROWER import produces the MORE visible outcome --
a new symbol -- because the wildcard is wired in sub-pass 2, in time for the decision,
while the selective form is deferred to sub-pass 4 and arrives after every mint.

So this is not only "the local shadows the alias". It is that the import system's own
subset property fails, and it fails precisely at WI-980's question. Whatever fix is
chosen should be stated as restoring that property, and its acceptance should assert it
directly: for every name and every scope, `import Y.{n}` and `import Y.*` agree about
`n`. That is a stronger and more checkable claim than the two-spellings-agree row the
description asks for, and it covers shapes neither spelling was measured on.

### 2026-08-21T14:04:53Z — feedback — user

THE SAME ROOT, REACHED WITHOUT A SELECTIVE IMPORT — a mint in ONE FILE of a scope captures
a head in a SIBLING FILE of that scope. Found while fixing WI-980; recorded here because
it is this ticket's mechanism, not that one's.

MEASURED (rustland, WI-980's tree):
  file LIB  namespace zlib  { rule q(1) }
  file A    namespace zdemo { import zlib.*   rule q(2) }
  file B    namespace zdemo { rule q(3) }
  WITHOUT B -> `zlib.q` = 2 clauses, `zdemo.q` absent. A's head joined zlib.q, as written.
  WITH B    -> `zlib.q` = 1 clause,  `zdemo.q` = 2. A'S CLAUSE MOVED, and file A did not
               change. Same in both file orders, so this is a WRONG answer rather than an
               order-dependent one.

NEITHER AUTHOR IS WRONG. A imported `zlib` and extended its predicate. B, which cannot see
that import, introduced a fresh name. Three language rules meet and leave no consistent
reading:
  * imports are FILE-LOCAL (WI-995), so B genuinely sees no `q`;
  * symbols are PER-SCOPE, so B's mint belongs to all of `zdemo`, file A included;
  * locals beat imports in `resolve_in_scope`, so A's head then finds B's local first.
"What `q` means in `zdemo`" is a per-FILE question; "which symbols `zdemo` has" is a
per-SCOPE one, and a mint answers the second in a way that overrides the first.

WI-980 CORRECTED THE DECISION AND NOT THE OUTCOME, which is worth knowing before anyone
re-derives it. Ownership is now computed per `(scope, name, file)`, and it gets both
verdicts right: A's head is `By(zlib)`, B's is `Here`. But the decision does not PLACE the
clause -- placement happens later, when the loader re-resolves the head functor -- and by
then `zdemo.q` exists and shadows. So a correct verdict still yields the wrong predicate.

THREE WAYS OUT, none free:
  * CARRY THE VERDICT TO PLACEMENT. Exact, and it makes clause placement stop agreeing
    with ordinary name resolution: a BODY in file A reading a bare `q` would still see
    `zdemo.q`, so a rule's head and its body would resolve one name two ways.
  * REFUSE B'S MINT AS A CAPTURE -- 059 R4 clause 3's shape ("a declaration may not
    capture a name it does not override"), extended to per-file resolution. Loud, nothing
    moves silently; the cost is refusing B for a collision B cannot see.
  * ACCEPT AND DOCUMENT: the scope's local wins, and a file that means to extend an
    IMPORTED predicate must say so unambiguously (a qualified head), because any sibling
    file can take the short name.

ACCEPTANCE, whichever is chosen: the three-file program's answer must not depend on
whether file B exists -- either A's clause stays in `zlib.q`, or the program is refused
naming both sites. Drive the goals; assert clause counts on both predicates with and
without B.

