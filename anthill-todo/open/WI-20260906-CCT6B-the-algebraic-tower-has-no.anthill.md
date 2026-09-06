## Attributes

- id: WI-20260906-CCT6B-the-algebraic-tower-has-no
- created: 2026-09-06T06:25:24Z

- status: Open
- status_agent: user
- status_at: 2026-09-06T06:25:24Z

- acceptance: cargo-test, scaland-sbt-test

- tags: algebra

## Description

THE ALGEBRAIC TOWER HAS NO MORPHISMS, so a FIELD EXTENSION can be stated only as a coincidence of two unrelated claims, and the SUBFIELD half cannot be stated at all.

CONTEXT. `Field requires Numeric[T]` was fixed on 2026-09-06 to `requires Ring[T]` + `requires PartialEq[T]` (stdlib/anthill/prelude/field.anthill), which removed the spurious ORDER obligation and made every field a ring. `algebra_spec_test::a_field_extension_is_a_vector_space_over_the_base_field` now writes `L = F_5[t]/(t^2 - 2)` over `K = F_5` and drives it: `t^2 = 2` and `vec_scale(3, t) = 3t` both evaluate. THAT TEST IS ALSO THE EVIDENCE FOR THIS TICKET, and its own comment says so: what it measures is that L is a K-VECTOR SPACE, which is the DIMENSION half of an extension. It does not measure, and the tower cannot state, that K is a SUBFIELD of L.

WHAT IS MISSING, precisely, and each item is a thing the standard definition states.

1. NO HOMOMORPHISM NOTION. `provides` and `requires` relate a CARRIER to a SPEC. Nothing relates a carrier to ANOTHER CARRIER. A field extension L/K is an injective ring homomorphism K -> L; a characteristic is a homomorphism Z -> K; an isomorphism, a kernel, a quotient and a Galois group are all morphism vocabulary. None of it is expressible.

2. THE EMBEDDING IS AN ORDINARY OPERATION AND NOTHING KNOWS IT. In the test fixture `operation inject(c: F5) -> L = lv(a: c, b: F5.zero())` is written, and it is inert: no clause says it is additive, multiplicative, injective, or that it sends `F5.one` to `L.one`. Rename it, or return `zero` for every input, and the suite stays green.

3. THE COHERENCE LAW CANNOT BE WRITTEN. What makes L a K-ALGEBRA rather than merely a K-module is `vec_scale(c, x) = mul(inject(c), x)` — the scalar action agrees with L's own multiplication. That equation reads operations of THREE different specs over TWO carriers, and there is no scope in which it can be stated.

4. THE MULTIPLICATIVE GROUP IS OVER `F \ {0}` AND THERE IS NO WAY TO NAME THAT CARRIER. The standard definition says the non-zero elements form an abelian group under multiplication; anthill says `recip(a: T) -> T` carrying a guarded `Error[DivisionByZero] :- eq(a, 0)`. The encoding is faithful and is NOT what this ticket asks to change — it is recorded because a general fix for 1-3 (a sub-structure relation) is the same machinery that would let `F \ {0}` be named, and a design that closes 1-3 while leaving this unsayable should say why.

WHAT THIS IS NOT. It is NOT a request to rename `Additive`/`Multiplicative` to `AdditiveGroup`/`MultiplicativeGroup`, and `arithmetic.anthill`'s header argues that case already: operator-carrier names were chosen deliberately over a standard tower nothing else in the prelude has. The names are not what blocks an extension; the absence of a carrier-to-carrier relation is. A design that concludes the standard tower IS wanted should reopen that header's argument explicitly rather than around it.

SIZE, and why this is a ticket rather than an inline change. A carrier-to-carrier relation is a new kind of clause in the spec system, with its own load-time backing check (is the claimed homomorphism actually additive and multiplicative?), its own scoping question (where does a law over two carriers live?), and its own interaction with `provides`/`requires` chaining and with the cross-namespace leak WI-20260825-N2865 left open on `requires`. Nothing about it is one file.

ACCEPTANCE. A degree-2 extension states that its base is a SUBFIELD, and a candidate that violates the claim is a LOAD ERROR naming it: an `inject` that is not additive, or does not carry `one` to `one`, must be refused rather than loading inert. The coherence law `vec_scale(c, x) = mul(inject(c), x)` is written somewhere the loader reads it. CONTROLS, each of which must still hold: `algebra_spec_test::a_field_needs_no_order` and `a_field_extension_is_a_vector_space_over_the_base_field` both still pass and still DRIVE their arithmetic; `float_provides_ring_and_vec3_provides_vector_space` unchanged; `ring_polynom_test` green; and the F_5 carriers still provide no order surface.

