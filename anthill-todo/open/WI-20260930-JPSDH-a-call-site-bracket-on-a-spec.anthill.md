## Attributes

- id: WI-20260930-JPSDH-a-call-site-bracket-on-a-spec
- created: 2026-09-30T16:25:29Z

- status: Open
- status_agent: user
- status_at: 2026-09-30T16:25:29Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CALL-SITE BRACKET ON A SPEC OPERATION DOES NOT REACH THE WI-606 FALLBACK, SO A CALL ITS QUALIFIED TWIN ADMITS IS REFUSED. `sort Sp { sort T = ?; effects E = ?; operation pick2[W](x: T, s: Sp) -> Option[T = Pair[A = s.T, B = W]] effects s.E }`, `sort Car { sort V = ?; effects EC = ?; entity car(v: V); provides Sp[T = Car, E = {EC}]; operation pick2[W, U, R](x: Car[V = U, EC = R], s: Car) -> Option[T = Pair[A = V, B = W]] effects {EC} = none }`; inside `use[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R])`, `Car.pick2[W = Int64](a, b)` loads and runs (the none arm answers), while `Sp.pick2[W = Int64](a, b)` is refused 'expected a well-formed type projection, got type Car has no member E'. The spec's s.E does not eliminate, so the call reaches the fallback (typing/build.rs concrete_override_threaded), whose σ is built from the ARGUMENTS alone: the override's W, bound only by the bracket, stays unbound in σ and is named by the return, so the fallback declines (WI-20260929-0RP29's rule) and the refusal stands. MEASURED the same on the pre-0RP29 binary. CONTROL, measured: with W bound by an argument instead (`pick2[W](x: T, s: Sp, w: W)` on both, `Sp.pick2(a, b, 3)`) the fallback threads and the program runs — the pre-0RP29 binary refused that one as well. A REFUSAL, NOT AN UNSOUND ACCEPT: the fallback declines what its σ cannot decide. THE ROOT, shared with WI-20260930-GJW9Z (the fallback's σ is not seeded with the enclosing instance's rigids): the fallback re-derives part of check_apply_iter's argument typing instead of running it — no seed_op_type_args (this bracket), no join_repeated_type_params (two arguments binding one override parameter at joinable types decline where the qualified call joins; not measured), no check_unconstrained_type_params. FIX: type the fallback's call against the override with check_apply_iter's own argument block, factored into one function both paths run, so GJW9Z's seeding comes with it. Open design point: a bracket names the SPEC operation's type parameters, and the override's correspond to them only through the two declarations (the override may add its own, as U and R here) — relate them by unifying the declarations position by position, as member_narrower_than_spec relates the parameters, never by name. FOUND by WI-20260929-0RP29's third /code-review. ACCEPTANCE: Sp.pick2[W = Int64](a, b) above loads and runs as its qualified twin does; a bracket contradicting the arguments is refused on both spellings; full workspace green via rustland/scripts/test.sh.

