# Future proposals

Forward-looking design sketches that are **not yet on the committed roadmap** —
ideas captured so they aren't lost, but deliberately **unnumbered**: a
main-sequence number (`docs/proposals/NNN-….md`) implies a committed, ordered
proposal, and these aren't there yet. Distinct from the parent directory
(committed kernel-language proposals, numbered) and `library/` (stdlib-library
proposals).

**Promotion.** When a future sketch becomes committed work, assign it the next
main-sequence number and move it to `docs/proposals/NNN-….md` (updating
back-references).

## Index

- [unification-framework.md](unification-framework.md) — unification as a
  framework of per-sort registered algorithms; the substrate for WI-010
  (resolver-as-type-checker).
- [first-class-operations.md](first-class-operations.md) — a bare operation name
  as a first-class function value (`Value::OpRef`), `()` as uniform application;
  the operation half deferred from proposal 039 (term-level constants).
- [bilateral-refutation.md](bilateral-refutation.md) — two-sided type theory
  (Li & Ramsay) read against anthill. Mostly a **negative** result: the `Eq`
  use-site question is answered positively by 058 §3.10, so no `refutes`
  channel is warranted on one instance. What survives is `NonEq` as the
  checkable shadow of a law that is never discharged, plus three concrete gaps
  behind `ProofResult.Disproved`.
