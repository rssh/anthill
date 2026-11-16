## Attributes

- id: WI-20260911-5TK6B-domain-bool-does-not-enumerate
- created: 2026-09-11T10:01:59Z

- status: Open
- status_agent: user
- status_at: 2026-09-11T10:01:59Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261115-YR3N7-a-typed-column-s-domain-check

## Description

DOMAIN: `Bool` does not enumerate — derive one fill clause per LITERAL, `fill(true)` and `fill(false)`, the shape a sort's constructors get (proposal 060 §2.3, "The head decides the mode"; decided 2026-11-15 on WI-20261115-YR3N7).

WI-743 makes a closed sort's constructor list its domain, so `?x: Colour` enumerates red/green/blue from the declaration alone. `Bool` is left out, and the reason is structural: its values are LITERALS (`Term::Const(Bool)`), not entity constructors, so there is no constructor list to read. Since WI-20260925-SHED7's step 1 every type has a `SortDomain` and a primitive's `fill` is the waiting type check, so `Bool` has a domain that does not enumerate: `rule anyBool(?x: Bool) :- true` answers one undecided row (`wi743_finite_domain_test::bool_has_a_primitive_domain_and_does_not_enumerate`).

NOT A HAND-WRITTEN DOMAIN. This ticket first proposed one clause in the prelude, `rule domain(?x, Bool) :- ?x <=> true | ?x <=> false`, through a hook SHED7 retired. Beyond the spelling it is the wrong shape: a hand-written domain is DOMAIN-DEFINING, so every `Bool` inside every typed value would be checked by the author's clauses, and a body that is a disjunction proposes each literal to a bound value in turn — it generates where it should check (WI-20261115-YR3N7). The derivation instead emits one clause per literal, the literal in the head, so a bound `Bool` selects its one clause and an unbound one enumerates `true`, then `false`.

ACCEPTANCE (every row driven):
  1 `rule b(?x: Bool) :- true` answers 2 DEFINITE rows, `true` then `false` (`bool_has_a_primitive_domain_and_does_not_enumerate` flips).
  2 `rule b2(?x: Bool) :- ?x <=> true` answers 1, through the `true` clause alone — no case tried and refuted.
  3 A `List[T = Bool]` spine with free cells fills them: tiny-sat written over `Bool` instead of its own `Bit` sort answers its 2 models.
  4 `Int64` and `String` keep the waiting check: they are INFINITE, the line `Bool` sits on the other side of. Say at the derivation which literal sorts are finite (`Bool` alone today).
Back-out: the literal clauses not derived reddens rows 1 and 3.

WHY IT IS ITS OWN TICKET: it changes what a `Bool` annotation MEANS in mode (out) — from waiting to enumerating — and the same question is answered for every other primitive at the same time.

## Changes

### 2026-10-31T05:34:58Z — feedback — claude

MOVES TO `SortDomain.fill` (user, 2026-10-31), so this waits on WI-20260925-SHED7. Since SHED7's step 1 every type has a `SortDomain` (proposal 060 §2.3) and a primitive's `fill` is the waiting type check, so `Bool` has a domain that does not enumerate: `rule anyBool(?x: Bool) :- true` answers one undecided row (`wi743_finite_domain_test::bool_has_a_primitive_domain_and_does_not_enumerate`). The fix is `Bool`'s `fill` enumerating `true`, `false`, not the clause `rule domain(?x, Bool) :- …` the Description proposes: SHED7's increment (e) retires `domain`.

### 2026-11-15T20:20:35Z — feedback — claude

DEPENDENCY ON WI-20260925-SHED7 DROPPED (user, 2026-11-15: "review dependency and it is now not needed - drop it"). It was for SHED7's step 1 (every type has a SortDomain), delivered 2026-09-25; SHED7's open steps (067 §5 q3, the monoid's home; §4, MiniSat over a builder) are not needed by Bool's derived literal clauses. It keeps WI-20261115-YR3N7, the shape those clauses are derived in.

