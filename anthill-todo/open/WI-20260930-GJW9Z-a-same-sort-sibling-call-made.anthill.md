## Attributes

- id: WI-20260930-GJW9Z-a-same-sort-sibling-call-made
- created: 2026-09-30T12:27:37Z

- status: Open
- status_agent: user
- status_at: 2026-09-30T12:27:37Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SAME-SORT SIBLING CALL MADE THROUGH THE SPEC OPERATION THREADS THE CARRIER'S CANONICAL VARIABLE WHERE THE QUALIFIED CALL THREADS THE ENCLOSING INSTANCE'S RIGID. `sort Sp { sort T = ?; effects E = ?; operation pick(x: T, s: Sp) -> Option[T = Pair[A = s.T, B = Sp[T = s.T, E = s.E]]] effects s.E }`, `sort Car { sort V = ?; effects EC = ?; entity car(v: V); provides Sp[T = Car, E = {EC}]; operation pick(x: Car, s: Car) -> Option[T = Pair[A = x.V, B = Car[V = x.V, EC = {Modify[s]}]]] effects {EC} = let r: Option[T = Pair[A = V, B = Car[V = V, EC = {Modify[x]}]]] = Sp.pick(s, x); none }` is refused "expected Option[T = Pair[A = V, …]], got Option[T = Pair[A = ?V, …]]": the call reaches `Car.pick` through the WI-606 fallback (typing/build.rs `concrete_override_threaded`), whose sigma starts empty, while `check_apply_iter`'s WI-424 step seeds a same-sort sibling callee's canonical parameter variables with `env.enclosing_instance_param_rigids()` before unifying the arguments — so `Car.pick(s, x)` threads the rigid `V`, and the spec spelling leaks the carrier's canonical `?V` into the caller's types. MEASURED identically before WI-20260929-0RP29 (the fallback never seeded); FOUND writing that ticket's rotated-self-call row. NOT A DROP-IN: seeding also changes a sibling call at a DIFFERENT instance, where the qualified path's rigid wins and the conflict is exempt from the §3 tie (the WI-374 exemption) — decide whether the fallback follows it there too. FIX: seed the fallback's sigma as the qualified call does (same sort: `impl_parent_of_op(impl_op)` against `env.enclosing_sort()`), handing it what it needs from the `TypingEnv`. ACCEPTANCE: the annotated call above loads; a spec-op sibling call and its qualified twin thread the same type, at the enclosing instance and at another; full workspace green via rustland/scripts/test.sh.

