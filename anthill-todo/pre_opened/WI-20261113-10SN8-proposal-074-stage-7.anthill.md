## Attributes

- id: WI-20261113-10SN8-proposal-074-stage-7
- created: 2026-11-13T23:02:10Z

- status: PreOpened
- status_agent: claude
- status_at: 2026-11-13T23:02:24Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1, WI-20261113-64272-proposal-074-stage-8-specs

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 7 — DICTIONARIES IN THE C++ AND RUST GENERATORS (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§1.4; parked, filed PreOpened). Group one, a dictionary built at load, emitted as a constant; group two passed where a template cannot unroll it (polymorphic recursion, T8); group three, a value with its dictionary (T9), as the host's own form of a value beside its table. Rows: T2, T4, T7, T8 and T9 generated, compiled and run in each. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

## Changes

### 2026-11-25T19:46:57Z — feedback — user

Kept parked, decided with the user 2026-11-25, after stage 8 was delivered. The C++ generator's one real program, lf1 (examples/webots-modelling/lf1, generated and compiled by wi_zw6n5_lf1_scaffold_test), needs no passed dictionary: it calls spec operations only at concrete types (Additive.add and sub, Multiplicative.mul, PartialOrd.lt and gt, PartialEq.eq, IndexedSeq.nth at List[Waypoint]), each answered at load and emitted as a direct call (074 §1.4's group one), and it declares no operation with a type parameter, a requires, a parameter typed at a spec, an x.T or a Dictionary.instance; its one provision, Modifiable[T = Self] on the device handles, is about Modify effects. What would need a dictionary in a generator: a value carrying its provider, such as a list of vehicles of different sorts typed at one spec (T9, group three), or polymorphic recursion (T8, group two). A controller generic over a spec, requires Vehicle[T = V], is a C++ template while its instantiations are finite. Promote this ticket when a program of that shape is written.

