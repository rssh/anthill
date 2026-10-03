## Attributes

- id: WI-20261003-P1PVT-a-field-read-s-existential
- created: 2026-10-03T12:31:54Z

- status: Open
- status_agent: user
- status_at: 2026-10-03T12:31:54Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A FIELD READ'S EXISTENTIAL SLOT IS A FRESH RIGID PER READ, NOT ITS PATH'S PROJECTION, SO TWO SPELLINGS OF ONE PATH DISAGREE. `sort Strm { sort T = ?; effects E = ?; entity strm(t: T); operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {EffP, -s.E}) -> Bool effects {EffP} = f(1) }`, `sort Hold { entity hold(s: Strm[T = Int64, E = ?]) }`, `operation use(h: Hold, g: (x: Int64) -> Bool @ {Error[String], -h.s.E}) -> Bool effects {Error[String]} = Strm.each(h.s, g)`, with `pure1(x: Int64) -> Bool = true` and a main declaring `effects {Error[String]}` that calls `use(hold(s: strm(t: 1)), pure1)` and answers 42: refused "each.f (op-arg): expected callback for parameter `f` of `Strm.each` to lack the row `?E` (its `-…` lacks-constraint), which is the enclosing operation's own and unknown here, got the callback `g` …" on the tree WI-20260929-0RP29's eighth review saw and after the tenth pass's /simplify; ran to 42 on the tree before the ticket, and on the tenth pass before its /simplify only through the defect its part 122 closed — a field read's written `?` left flexible, which also passed `takes_pure(h.s)` a holder's stream for a pure one (MEASURED). The read `h.s` opens the field's `E = ?` to a FRESH rigid per read (WI-1063's existential opening — `open_existential_return` over `field_access`'s reduced return), so the call's `s.E`, eliminated against the read's type, is that rigid, while `g`'s declared `-h.s.E` is the path's projection: one value's row spelled two ways. A stable path read twice denotes one value, so its existential is ONE, and the path's own projection names it (`h.s.E`, a neutral — WI-400's path identity). FIX: where a field read's receiver is a stable value path (`stable_receiver_path`), open the field's existential slots to that path's projections instead of fresh rigids; a read off something that is no path (a call's result) keeps the fresh rigid. ACCEPTANCE: the program runs to 42; `takes_pure(h.s)` over `takes_pure(s: Stream[T = Int64, E = {}])` still refused — `h.s.E` is no `{}` — as `wi_0rp29_review9_regressions_test`'s `a_declared_fields_written_wildcard_is_opened` pins; two reads of one path agree (`same(h.s, h.s)` over `same(a: Strm, b: Strm[E = a.E])` loads) and reads of two paths do not (`same(h.s, k.s)` refused); a read off a call's result still opens a fresh rigid; full workspace green via rustland/scripts/test.sh.

