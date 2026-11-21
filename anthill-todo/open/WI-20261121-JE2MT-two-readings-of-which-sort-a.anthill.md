## Attributes

- id: WI-20261121-JE2MT-two-readings-of-which-sort-a
- created: 2026-11-21T18:04:53Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T18:04:53Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

TWO READINGS OF WHICH SORT A PROVISION IS ABOUT, which disagree for a spec whose carrier parameter no operation of the spec receives — `Eq`, which declares none (filed with the user 2026-11-21, beside WI-20261121-TV0PA). `typing::witness_dispatch_carrier` (kb/typing/coherence.rs) reads `spec_carrier_param`, the parameter an operation receives on, and answers `None` for such a spec, so `sort W { provides Eq[T = C] }` is read as about `W`. `typing::provisions_about` (kb/typing/provision.rs) reads `spec_carrier_param_or_sole`, the sole parameter too, and answers `C`.

TV0PA moved the equality derivation's `spoken_for` to the second reading — MEASURED there: on the first, `C` derived its own equality beside the witness's and `eq(c(v: 1), c(v: 2))` answered 0, `W.eq` never called. The equality-closure record (`eq_derive::equality_signatures`), the later-load check and `EqualityReachesNoEq` read the second as well.

STILL ON THE FIRST: `provision_carriers_of_spec` (kb/sort_domain_derive.rs:66, kb/type_value_derive.rs:107 and :167), and `witness_dispatch_carrier` / `witness_dispatch_carrier_value` at fourteen call sites — dispatch (`provision_supplier`, which the eq-dispatch index's `Eq` sweep reads, so an `Eq`-only witness's `eq` is filed under the witness until the forwarded `PartialEq` row exists; WI-20261121-DBR8V's (b) is one consequence), the coherence grouping, the member-signature checks (typing/signature.rs), typing/subtype.rs, typing/projection.rs, typing/candidates.rs, typing/rule_requirements.rs, typing/carrier.rs.

NOT MEASURED: whether any of those answers wrongly for a witness of such a spec today. For dispatch the receiving reading may be the right one — a spec no operation of which receives on its parameter has nothing to dispatch there, and its operations arrive through a forwarded row of a spec that does.

TO DO: measure each reader with a witness of a spec whose carrier parameter no operation receives (`Eq`, and a user marker spec of one parameter); then either one owner for "about" that every reader shares, or each reader that keeps the receiving reading says why at its site.

ACCEPTANCE: a row per reader that answered wrongly, driven, with its back-out; the readers left on the receiving reading named with their reason; families green; full workspace green via rustland/scripts/test.sh; scaland testFull.

