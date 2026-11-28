## Attributes

- id: WI-20260929-QA700-boundedlattice-s-less-bottom
- created: 2026-09-29T07:21:14Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-28T08:59:21Z

- acceptance: cargo-test

- tags: proposal-068

## Description

`BoundedLattice`'S `less_bottom` / `less_top` CLAUSES SHADOW A CARRIER'S `less` AND MATCH ONLY THE UNEVALUATED `bottom` / `top` — `Lattice.less(lo(), hi())` answers nothing where the carrier's own `less` is true, and `not(...)` over it proves a falsehood.

MEASURED on main at 145457c7, with a two-point lattice `Lv` (entities lo, hi) providing Lattice and BoundedLattice, `bottom() = lo()`, `top() = hi()`, and `less` a match body (lo ≤ everything, hi ≤ hi). (total, definite):
  Lattice.less(BoundedLattice.bottom(), hi())   (1, 1)   the clause less_bottom matched the TERM `bottom`
  Lattice.less(lo(), hi())                      (0, 0)   truth 1 — the same value, written as a value
  not(Lattice.less(lo(), hi()))                 (1, 1)   NAF proves a falsehood
  Lattice.less(hi(), hi())                      (0, 0)   truth 1
  Lattice.less(hi(), BoundedLattice.top())      (1, 1)   the clause less_top matched the TERM `top`
  Lv.less(lo(), hi())                           (1, 1)   control: the carrier's own implementation, called directly

WHY. `less_bottom: less(bottom, ?a) :- true` and `less_top: less(?a, top) :- true` (stdlib/anthill/prelude/lattice.anthill:44–45) are relational CLAUSES of the spec operation `Lattice.less`. A functor with hand-written clauses resolves through them ("rules win while both exist", abstract-interpreter design §3.3), so a `Lattice.less` goal never reaches the carrier's `less` — and the two clauses match the unevaluated TERM `bottom` / `top` and nothing else. Proposal 068 makes it worse: once a goal's arguments are evaluated (068 §1.1 / D3, WI-20260926-K4JGC), `bottom()` reaches the discrimination tree as `lo()`, and the clauses stop matching even the spelling that answers today. Found by 068's census (docs/design/068-implementation.md §1.3); `Set`'s heads are the sibling case (WI-20260926-QCJ0B).

DECIDE WITH THE USER what the two rules are:
 (a) LAWS about every bounded lattice, for the verifier — then they are equations (`less(bottom, ?a) <=> true`), which do not resolve goals, and a `Lattice.less` goal reaches the carrier's `less`;
 (b) a DEFAULT for a carrier that supplies no `less` of its own — then they belong in `less`'s default body, which runs only where the carrier has none;
 (c) both.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven): the rows above answer their truth — `Lattice.less(lo(), hi())` 1, `not(Lattice.less(lo(), hi()))` 0, `Lattice.less(hi(), hi())` 1, and `Lattice.less(hi(), lo())` 0 — and keep answering it once goal arguments are evaluated (K4JGC); the laws' readers (simp, the verifier) still see them in the form the decision gives. CONTROL, stated at its site: `Lv.less(lo(), hi())` answers 1 either way.

## Changes

### 2026-11-28T08:53:20Z — feedback — user

DECIDED (user, 2026-11-28): (a), the two are LAWS. Re-measured on HEAD 9dc7f6164 first: Lattice.less(lo(), hi()) (0, 0), not(...) (1, 1), Lattice.less(hi(), hi()) (0, 0), Lattice.less(Lv.bottom(), hi()) (0, 0) (K4JGC evaluates the argument, so the clause no longer matched even that spelling), Lattice.less(lo(), ?x) answered ?x = top (the unevaluated term, definite); the control Lv.less(lo(), hi()) (1, 1). (b) has no audience: a carrier that provides Lattice and supplies no less is refused at load ('backs no operation ... no default on Lattice'). Deleting the two was the alternative weighed: they follow from less_lub, lub_comm, bottom_lub / top_lub and eq_refl; kept as equations, which give z3 the fact directly.

### 2026-11-28T08:59:19Z — feedback — user

DELIVERED in d966f9e2a (2026-11-28). stdlib/anthill/prelude/lattice.anthill: less_bottom: less(bottom, ?a) <=> true, less_top: less(?a, top) <=> true — laws, which resolve no goal, so a Lattice.less goal reaches the carrier's less (body_less_dispatchable admits an operation with no clause of its own); the verifier lowers both (16 of BoundedLattice's 16 laws; 2 were left out and named). Every acceptance row answers its truth: Lattice.less(lo(), hi()) 1, not(...) 0, Lattice.less(hi(), hi()) 1, Lattice.less(hi(), lo()) 0 and not(...) over it 1; with evaluated arguments (K4JGC) Lattice.less(BoundedLattice[T = Lv].bottom(), hi()) 1 and Lattice.less(hi(), BoundedLattice[T = Lv].top()) 1; Lattice.less(lo(), ?x) no longer binds ?x to the term top. CONTROL Lv.less(lo(), hi()) 1 either way. Tests: wi_qa700_lattice_less_reaches_the_carrier_test (wi_tests), 7 rows, 5 fail with the two written :- true again, 2 pass either way by design. wi_zz7ph_law_lowering_test: the BoundedLattice row asserts 16 of 16 and the two laws' lines; the relation-headed refusal moved to a_relation_headed_law_is_left_out over a spec of its own. Simp: untagged, inert, as every other law of the sort. /code-review high: 5 nits, all fixed. Gate 13016 / 0 / 26; scaland testFull 863 rows green.

