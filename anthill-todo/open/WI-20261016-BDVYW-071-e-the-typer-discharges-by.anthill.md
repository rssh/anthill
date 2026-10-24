## Attributes

- id: WI-20261016-BDVYW-071-e-the-typer-discharges-by
- created: 2026-10-16T14:51:37Z

- status: Open
- status_agent: claude
- status_at: 2026-10-16T14:51:37Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261016-SQZPQ-071-b-typepattern-and, WI-20261016-5CDN5-071-d-a-raise-carries-its-type

- tags: proposal-071

## Description

071 (e): THE TYPER DISCHARGES BY THE SAME TEST, AND BUILDS PATTERN EVIDENCE AT AN OPEN SLOT. Proposal 071 §1.5, §1.6.
THE CHANGE: the typer's discharge of an `Error` label at a boundary reads the one predicate `admits` reads, so the row and the run cannot disagree (today `payload_matches` reads `sort_sym_compatible` on head sorts and the discharge `labels_match_by_subsumption`, exact on type arguments). Pattern evidence for a `T1` with an open slot (`Boom[Reason = ?]`) is built by the typer from `T1`'s term at the call — an open slot a wildcard, a rigid parameter the caller's evidence, a sort application its derived instance — not found by instance search, where a goal with an unbound slot matches every instance. Decide 071's open question 1 (WI-20261015-D2KZ5: what an unwritten `T1` over several labels binds) here or before.
MEASURED (2026-10-16): `caughtWide(n) -> Result[E = Boom, T = Int64] = Error.reify(lambda () -> both(n))`, over a thunk raising `Boom[Reason = String]` and `Boom[Reason = Int64]`, is refused at load: "undeclared effect: `Error[T = Boom[Reason = Int64]]`".
ACCEPTANCE (cargo-test via rustland/scripts/test.sh, scaland sbt testFull): `caughtWide` loads and catches both `boom("s")` and `boom(5)`; a boundary at `Boom[Reason = String]` still leaves `Error[Boom[Reason = Int64]]` to its caller, at load and at run time; families green (`scripts/families.sh`).

## Changes

### 2026-10-23T19:54:36Z — feedback — user

2026-10-23 (user, in WI-20261016-YM8HD's review): a pattern with an open slot is safe for a boundary only where the typer discharges exactly what it admits. An unknown T1 read as `?` (catch every payload) is sound where the thunk's row holds no Error label but T1 and no open tail that could carry one (`lambda () -> Error.raise(?p)`), and unsound otherwise (`raiseEither` over {Error[P], Error[Other]}: the `Other` its row leaves to the caller would be caught inside a Result[E = P]). The user's direction for the general case is a catch whose pattern is written at the call, `Error.catch(pattern, body)`, the typer discharging the labels the written pattern admits — proposal 071 §7 open question 5. Decide here, or before, whether stage (e) builds evidence for an inferred open T1 at all or leaves that to catch.

