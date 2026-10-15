## Attributes

- id: WI-20261015-169VS-proposal-050-1-stage-4-the
- created: 2026-10-15T13:47:49Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T13:47:49Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261015-X57XR-proposal-050-1-stage-3-the

- tags: proposal-050.1, typing

## Description

Proposal 050.1, stage 4: the kill, by regions, and the two cases — a write kills the Γ facts over the places connected to what it writes, keeps those over separate places, and keeps the rest under the hypothesis that decides them; Γ holds facts with a condition.

PROGRAMS (docs/proposals/050.1-memory-alias-and-maybe-connected.md §1.2, §5.3):
- f(p: Cell[V = Int64], q: Cell[V = Int64]) effects Modify[p] = let v = Cell.get(q), Cell.set(p, 5), then Cell.get(q) - v. Γ assumes v ≡ Cell.get(q) for the pure call and keeps it across the write: 050's call rule has no kill (docs/design/abstract-interpreter-and-rules.md §6.1's open hole). No ticket held the kill; this one does.
- let x = p, let v = Cell.get(p), Cell.set(x, 5): a kill by the syntactic occurrence of the written name (§6.3's first cut) would keep v ≡ Cell.get(p) — unsound under aliasing.

EXPECTED:
- 050's call rule gains its kill, before the callee's ensures is assumed (abstract-interpreter §6.1–6.3), with "depends on" read through the regions (§5.3): a write through x removes the facts over places connected to x, keeps those over places separate from it, and keeps each other fact guarded by not memory_maybe_connected(r, s) for the unknown pairs it involves (§1.2). A fact carries only the hypotheses it needs; the ways n parameters can share are not enumerated.
- A postcondition the body shows under a hypothesis is guarded the same way, and a call discharges the guard from the caller's Γ as it refutes an effect's guard (048): proved, the fact holds; refuted, it is dropped; over the caller's own parameters, it is re-keyed and stays the caller's hypothesis. The bridge reads a guarded fact as a clause whose body is its hypotheses.
- requires not memory_maybe_connected(p, q) — separation logic's p * q — is held at calls like any requires.
- Cell.set's postcondition Cell.get(c) ≡ value (written if the stdlib lacks it) holds of every alias of c (§5.4).

ROWS: f's v ≡ Cell.get(q) kept under not memory_maybe_connected(p, q), holding at f(c, d) over two fresh cells and dropped at f(c, c); the aliased spelling killed; a separation requires refused at f(c, c) and met at f(c, d).

