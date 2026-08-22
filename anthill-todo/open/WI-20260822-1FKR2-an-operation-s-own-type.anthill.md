## Attributes

- id: WI-20260822-1FKR2-an-operation-s-own-type
- created: 2026-08-22T12:29:21Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T12:29:21Z

- acceptance: cargo-test

## Description

AN OPERATION'S OWN TYPE VARIABLE DOES NOT THREAD THROUGH A CALL WHEN THE CALLER IS GENERIC IN IT, so no generic operation can be implemented in terms of another generic operation. Every one must be a primitive.

MINIMAL REPRODUCTION: docs/measurements/op-type-var-does-not-thread.anthill. Twelve lines, no specs, no dispatch, no information flow -- the identity delegating to the identity.

  namespace tv1
    operation idv(x: ?t) -> ?t
    operation via_bare(x: ?t) -> ?t = idv(x)
  end

  error: type mismatch in via_bare.return (op-return): expected ?t, got ?t
         (these render alike but are not the same type -- the difference is in
          a component this diagnostic does not print; please report it)

The diagnostic asks to be reported, which is a fair description of the state: the two types PRINT identically and compare unequal, so the difference is in a component the renderer drops.

THE NESTED FORM is the same defect one level in, and its message is the informative one:

  operation id(b: Box[?t]) -> Box[?t]
  operation via(b: Box[?t]) -> Box[?t] = id(b)

  error: expected Box[T = ?t], got Box[T = b.T]

"b.T" is the tell. The callee's variable is being resolved to a PROJECTION -- "the T of the argument b" -- rather than unified with the variable the CALLER declared. Whether the bare and nested cases share a root is the first thing to establish; the bare one prints no projection, which may mean the same mechanism with the rendering lost, or may mean two defects.

CONTROL, in the same file. The identical delegation with a GROUND caller loads clean:

  operation via_ground(b: Box[Int64]) -> Box[Int64] = id(b)

So the failure is about the CALLER's own polymorphism -- not about delegation, not arity, not the sort. Measured 2026-08-22: exactly the two marked cases fail and the control passes, which is what makes the two failures mean something.

WHERE IT WAS FOUND, AND WHY IT MATTERS BEYOND GENERICS-FOR-THEIR-OWN-SAKE. examples/guardians types information flow by putting a label in a type parameter, so the load-bearing shape is an operation that PRESERVES a label: f(x: T[L = ?l]) -> T[L = ?l]. That works at the EDGES, where a call site supplies a concrete label, and it is what makes the article's exfiltration a type error. It does not work in the MIDDLE: a library operation that is itself label-preserving and delegates to another cannot be written. So the property composes through the type checker but not through user-written library code, which is what any real pipeline is made of. `guardians.summarize` had to be narrowed from "?l in, ?l out" to monomorphic at Untrusted for exactly this reason -- a narrowing forced by this defect, not chosen.

RELATED, POSSIBLY THE SAME ROOT: WI-20260822-RKMD4 (an argument whose SORT differs from a parameter type containing a type variable is accepted silently, leaving the variable unbound). Both are a type variable in a parameter position failing to bind through a call; one is silent and one is loud. Establishing whether they are one defect is worth doing FIRST -- if they are, it is one fix.

SUPERSEDES a ticket filed earlier the same day under the framing "two label-polymorphic operations do not compose". That framing was too narrow -- this has nothing to do with labels -- and it carried a supporting claim that measurement disproved: it said the label slot is invariant and an n-point lattice needs O(n^2) coercions. anthill HAS variance, declared as facts (Covariant / Contravariant, stdlib/anthill/reflect/typing.anthill), and type_compatible has a "provides" arm, so a provides-chain lattice with a covariant parameter gives the ordering directly: widening loads, the dangerous direction is refused, and deleting the Covariant fact refuses the widening too (the third being what shows covariance is doing the work). docs/design/measured.md C4 carries the same wrong claim and needs the same correction.

ACCEPTANCE: both marked cases in docs/measurements/op-type-var-does-not-thread.anthill load. CONTROLS: the ground case in that file still loads; guardians' docs/measurements/guardians/d2g_leak.anthill is still REFUSED (the label must still be ENFORCED, not merely threaded); and guardians.summarize can be restored to "?t in, ?t out" with examples/guardians still refusing fixtures/agent/rejected/leak.anthill.

