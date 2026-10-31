## Attributes

- id: WI-20260911-5TK6B-domain-bool-does-not-enumerate
- created: 2026-09-11T10:01:59Z

- status: Open
- status_agent: user
- status_at: 2026-09-11T10:01:59Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260925-SHED7-inductive-relations-proposal

## Description

DOMAIN: `Bool` does not enumerate — give the prelude a hand-written `Bool.domain`.

WI-743 makes a closed sort's constructor list its domain, so `?x: Colour` enumerates
red/green/blue from the declaration alone. `Bool` is left out, and the reason is
structural rather than an oversight: its values are LITERALS (`Term::Const(Bool)`), not
entity constructors, so there is no constructor list to read existentially. MEASURED
(`wi743_finite_domain_test::bool_has_no_derived_domain`):
`kb.has_domain_member(anthill.prelude.Bool)` is false where the same predicate answers
true for a sort with constructors.

THE FIX IS THE HOOK WI-743 ALREADY SHIPS, not new machinery. §2.2 admits a hand-written
`domain` on any sort: a 2-ary relation named `domain` in the sort's body, whose second
argument names that sort or is a variable, REPLACES the derivation and is read in both
modes. So this is one clause in `stdlib/anthill/prelude/bool.anthill`:

    rule domain(?x, Bool) :- ?x <=> true | ?x <=> false

ACCEPTANCE: `rule b(?x: Bool) :- true` answers 2 DEFINITE rows, `true` then `false`;
`rule b2(?x: Bool) :- ?x <=> true` still answers 1 (the hook is domain-DEFINING, so mode
(in) reads it too, and both literals are members); a `List[T = Bool]` spine with free
cells fills them, which is what tiny-sat writes a `Bit` sort for today. Say at the clause
whether the same treatment is wanted for the other literal-valued primitives — `Int64`
and `String` are INFINITE and must NOT get one (they keep WI-742's delay/flounder
ladder), which is exactly the line `Bool` sits on the other side of.

WHY IT IS ITS OWN TICKET: it is a stdlib clause plus a row, but it changes what a `Bool`
annotation MEANS in mode (out) — from "flounder loudly" to "enumerate" — and the same
question has to be answered for every other primitive at the same time.

## Changes

### 2026-10-31T05:34:58Z — feedback — claude

MOVES TO `SortDomain.fill` (user, 2026-10-31), so this waits on WI-20260925-SHED7. Since SHED7's step 1 every type has a `SortDomain` (proposal 060 §2.3) and a primitive's `fill` is the waiting type check, so `Bool` has a domain that does not enumerate: `rule anyBool(?x: Bool) :- true` answers one undecided row (`wi743_finite_domain_test::bool_has_a_primitive_domain_and_does_not_enumerate`). The fix is `Bool`'s `fill` enumerating `true`, `false`, not the clause `rule domain(?x, Bool) :- …` the Description proposes: SHED7's increment (e) retires `domain`.

