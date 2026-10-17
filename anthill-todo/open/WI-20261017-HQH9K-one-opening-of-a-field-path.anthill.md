## Attributes

- id: WI-20261017-HQH9K-one-opening-of-a-field-path
- created: 2026-10-17T16:09:51Z

- status: Open
- status_agent: user
- status_at: 2026-10-17T16:09:51Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261003-P1PVT-a-field-read-s-existential

- tags: typing

## Description

ONE OPENING OF A FIELD PATH PER BODY, AND OF A NON-PATH ARGUMENT PER CALL — WI-20261003-P1PVT's three stated limits. P1PVT names a field path's TOP-LEVEL existential slots by the path (`h.s` over `s: Strm[T = Int64, E = ?]` is `Strm[T = Int64, E = h.s.E]`, `typing/elaborate.rs` `open_existentials`), and three spellings of one value still open apart, each refusing a correct program — none admits a wrong one (MEASURED on P1PVT's tree): (1) a slot NESTED inside a written binding (`s: Strm[T = List[T = ?]]`) takes a fresh rigid at every read and at every elimination of a written projection, so `f(h: Hold3, x: h.s.T, y: h.s.T) = same_list(x, y)` over `same_list[A](x: A, y: A)` is refused, "no common type for type parameter `A` …: List[T = ?T] (x), List[T = ?T] (y)"; (2) a pattern binder over a stable scrutinee is named by the binder, not the path: in `use(h: Hold, g: (x: Int64) -> Bool @ {Error[String], -h.s.E})`, `match h case hold(s) -> Strm.each(s, g)` is refused (`-s.E` against `-h.s.E`) where `Strm.each(h.s, g)` loads; (3) at a call whose argument is no path, each reading of the call (the callback hint, the parameter check) opens its own rigid, so `pick(hold2(s: strm(t: "a")), lambda (x) -> 42)` over `pick(h: Hold2, f: (x: h.s.T) -> Int64)` is refused, "expected ?T -> Int64, got ?T -> Int64", while the same call with the holder bound by `let` runs — pinned by `wi_p1pvt_field_path_existential_test::a_lambda_at_a_call_whose_argument_is_no_path_waits_for_a_name`, which this ticket turns. FIX (the altitude finding of P1PVT's review): record each stable path's opened field type ONCE — per body, beside `TypingEnv::receiver_aliases`, for the read, a written receiver and a pattern binder over a path scrutinee (the binder aliased to `h.s` as a `let` is); per call, for an argument that is no path, shared by the call's hint, parameter, return and effect readings — and have each consult it, so a nested slot is one rigid per path and every spelling agrees. A rigid must not outlive its body check (`value_contains_rigid`'s invariant). ACCEPTANCE: the three programs above load, and the runnable ones run to their values; `same(h.s, k.s)`, `same(mk().s, mk().s)`, `takes_pure(h.s)` and P1PVT's self-recursive `run2(mk_int(), v, n - 1)` stay refused; P1PVT's rows pass, the lambda row turned; spec §8.1 "A field read off a path is named by the path" updated where it states these limits; full workspace green via rustland/scripts/test.sh, scaland testFull.

