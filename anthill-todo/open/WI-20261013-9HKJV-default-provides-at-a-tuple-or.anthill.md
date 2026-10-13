## Attributes

- id: WI-20261013-9HKJV-default-provides-at-a-tuple-or
- created: 2026-10-13T18:11:16Z

- status: Open
- status_agent: user
- status_at: 2026-10-13T18:11:16Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

`default provides` AT A TUPLE OR AN ARROW IS ACCEPTED AND ARBITRATES NOTHING, AND TWO DEFAULTS THERE ARE NOT REFUSED. `sort Apply { sort F = ?  operation run(f: F) -> Int64 }`, `sort P1 { default provides Apply[F = (Int64, Int64)]  operation run(f: (Int64, Int64)) -> Int64 = 10 }`, `sort P2 { provides Apply[F = (Int64, Int64)]  operation run(f: (Int64, Int64)) -> Int64 = 30 }`, `operation via(f: (Int64, Int64)) -> Int64 = Apply.run(f)`: refused, "ambiguous dispatch of `Apply.run`: 2 instances provide `Apply` (P1, P2) and the call selects none" - the mark the author wrote for exactly this call is read by nothing. MEASURED on f4827d68: (1) the program above; (2) the same at an arrow, `F = (Int64, Int64) -> Int64`; (3) the default declared by reference, `fact anthill.prelude.DefaultProvider(spec: Apply, provider: P1)`, at the tuple: the same refusal; (4) BOTH providers marked `default` at the tuple: the call is refused as the same tie and no "ambiguous default" is raised, and with no call written the program loads clean. CONTROLS, measured: at a carrier that is a sort the mark answers - `F = Box[T = Int64]` and `F = Int64` both run `P1` (10) - and two marks there are a load error with or without a call, "ambiguous default: carrier 'Box[T = Int64]' has 2 default providers of 'Apply' ('P1' at carrier 'Box[T = Int64]' (declared); 'P2' ... (declared))". MECHANISM, from code reading: a default row is keyed at its carrier's BASE SORT. `default_provider_for` (kb/defaults.rs) reads the goal's carrier through `typing::carrier_view_base`, which answers only for an applied sort or a bare name, so at a tuple or an arrow it has no bucket and the rung declines. On the declaring side `carriers_provided_by` asks `witness_dispatch_carrier_view` for the provision's carrier and takes its `None` for 'the provider IS the carrier', so a witness at a tuple is filed as a default at carrier `P1` - a row no goal asks for - and `one_default` compares that row with nothing. Found while WI-20261013-0GYW1's programs were run; not a regression of it (the same on a730f11b). TO DECIDE FIRST: a default may be declared at a tuple or an arrow, and the index holds such a row - keyed how, given that two arrows are one carrier when their parameter lists pair by position, the names lining up or one list written without names (kernel-language 5.2), and that pairing is no equivalence (`arrow_part_pairs`' doc); or the mark is refused where it is written, naming the carrier as one that takes no default. Either way the row at the provider's own name must not be filed for a witness whose carrier is no sort. ACCEPTANCE: by the decision, (1)-(3) answer by `P1` (10) and (4) is a load error naming both providers and the tuple, with or without a call - or each of (1)-(4) is refused at the mark; the controls stay; a provider at a tuple with no mark is not reported; full workspace green via rustland/scripts/test.sh.

