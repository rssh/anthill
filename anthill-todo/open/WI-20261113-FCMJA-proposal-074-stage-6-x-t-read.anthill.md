## Attributes

- id: WI-20261113-FCMJA-proposal-074-stage-6-x-t-read
- created: 2026-11-13T23:01:52Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T23:01:52Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 6 — `X.T` READ AS A VALUE IS 065'S DISPATCH (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§3; T10). In value position `x.T` is `TypeValue.type_value[T = x.T]()`, as a type parameter is: under `requires TypeValue[x.T]`, `tOf(x: Additive) -> Type requires TypeValue[x.T] = x.T` answers `Int64` and `Float`; without the clause it is refused at load, naming the clause to add, as for `X`, over `Num` as well (it loads today). Where `x`'s spec states `requires TypeValue[T = T]`, the clause is supplied from `x`'s dictionary, and the list of T10 answers `[Int64, Float]` (refused today at `map(tOf)`); over `Additive` that `map` is refused. Depends on stage 1, whose spelling its rows write. Spec: §8.2 and proposal 065's rule, which today name a type parameter only. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

