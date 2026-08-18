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

**Demotion.** The other direction — a *numbered* proposal deferred past the
current release — moves here **keeping its number in the filename**
(`future/NNN-….md`), and the number is retired rather than reused. Proposals are
cited by number from the spec, from each other, and from work-item descriptions,
so a number that changed meaning would silently falsify text nobody re-reads.
A proposal *declined* rather than deferred goes to
[`../rejected/`](../rejected/README.md), under the same number rule; that file
documents what a rejection has to say.

A sketch that was never numbered has nothing to retire, and promotion above is
its only move.

## Index

- [unification-framework.md](unification-framework.md) — unification as a
  framework of per-sort registered algorithms; the substrate for WI-010
  (resolver-as-type-checker).
- [first-class-operations.md](first-class-operations.md) — a bare operation name
  as a first-class function value (`Value::OpRef`), `()` as uniform application;
  the operation half deferred from proposal 039 (term-level constants).
- [associated-relations.md](associated-relations.md) — relations as
  per-instance-dispatched spec members, deferred from proposal 052's
  relations-as-values design.
- [bilateral-refutation.md](bilateral-refutation.md) — two-sided type theory
  (Li & Ramsay) read against anthill. Mostly a **negative** result: the `Eq`
  use-site question is answered positively by 058 §3.10, so no `refutes`
  channel is warranted on one instance. What survives is `NonEq` as the
  checkable shadow of a law that is never discharged, plus three concrete gaps
  behind `ProofResult.Disproved`.
