## Attributes

- id: WI-20261013-2HX69-068-d1c-the-unfold-threads
- created: 2026-10-13T08:03:43Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:03:43Z

- acceptance: cargo-test

- depends_on: WI-20261013-DEY66-068-d1b-the-per-consumer

- tags: proposal-068

## Description

068 D1c — THE UNFOLD THREADS DICTIONARIES (068 §8 step 4; items 3 and 4 of WI-20260926-DSEXA): `unfold_eq_operand` reads OTHER through WI-20260926-K4JGC's strategy and threads dictionaries as clause conditions, as P7VP4 does for rule-body calls, instead of declining every operation with `requires`; WI-20260827-XBHX3's gate goes. ROWS: XBHX3's three — `C.bpick(?c) = box(v: C.tag(red()))` answers `?c = red` definite; `C.pick(?c) = C.mk(red())` (custom `Eq`, WI-20260827-P1TPE) is never a wrong refutation; `append(?a, [3]) = append(?b, [4])` terminates; and over `sign[A](x: A, y: A) requires WeakOrd[T = A]`, `rule lit(?c) :- ?c = Util.sign(1, 5)` answers -1 as `?c <=> Util.sign(1, 5)` does, where it is one undecided row today (DSEXA note 2026-10-08). With it, kernel-language §5.3 ('what the gate still declines') and §8.1's rule-body typing sentence. ACCEPTANCE (cargo-test, driven, back-outs at their sites). CONTROLS: P7VP4's and SHED7's rows unchanged; classic-mini unchanged. WI-20260827-XBHX3 waits on this part.

