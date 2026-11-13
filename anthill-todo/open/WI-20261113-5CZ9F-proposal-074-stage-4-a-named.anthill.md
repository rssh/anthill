## Attributes

- id: WI-20261113-5CZ9F-proposal-074-stage-4-a-named
- created: 2026-11-13T23:01:35Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T23:01:35Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1, WI-20261113-0FTHQ-proposal-074-stage-9-a-call

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 4 — A NAMED PROVIDER FIXES ITS PARAMETERS (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§2, "A provider named"; T11). `Dictionary.instance[Additive[T = Meters], Additive = ProjAdditive[X = Int64, Y = Meters]]()`, and the call's bracket `Additive.add[Additive = ProjAdditive[X = Int64, Y = Meters]](m(v: 2), m(v: 3))`, answer `m(v: 5)`: the named provider's type arguments fix `X`, after which its construction is `Int64`'s `Additive` and `MetersIso`, finite. Today refused: "construction is cyclic". Rows (§2, "A provider named"): the bracket `ProjAdditive[X = Int64]`, its positional `ProjAdditive[Int64]`, and `ProjAdditive[Int64, Meters]` answer `m(v: 5)`, `Y` fixed by the call's type where unwritten; the bare `Additive = ProjAdditive` is refused, naming `X` to write; the unnamed `m(v: 2) + m(v: 3)`, with `ProjAdditive` the only provider at `Meters`, is refused as no provider chosen there, its message naming `ProjAdditive` and the bracket that chooses it; `Additive.add(true, false)` is refused about `Bool`, not as a cycle; a cycle among provisions that fix every parameter keeps its message, "no type written at a use changes that". `sumM(d: Additive[T = Meters], a: Meters, b: Meters) = a + b`, handed the named dictionary, answers `m(v: 5)` (stage 1's rule). What is new to build (from review): a witness's plain type arguments are discarded today by design — `selection_witness_sym` (`kb/typing/slots.rs`) keeps the head, the witness's parameters being instantiated at the goal's bindings — so the selection keeps them, and they enter `InstanceSelection`, the key of `resolve_cache`, beside WI-870's `slots`; a row: two sites naming `ProjAdditive` at two `X` (an `Iso` from `Int64` to `Meters` and one from another carrier) each answer through their own. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

## Changes

### 2026-11-13T23:23:54Z — feedback — claude

FROM THE THIRD REVIEW (proposal 074 §5, with the user 2026-11-13): first, a census — every provider whose provides leaves one of its parameters unbound, in the standard library, the examples and the fixtures, and every call §8.7's order now passes it over at. Build notes: a witness's plain type arguments are discarded today (selection_witness_sym keeps the head), so the selection keeps them and they enter InstanceSelection, the resolve_cache key, beside WI-870's slots; two sites naming ProjAdditive at two X each answer through their own. Depends on stage 9 (WI-20261113-0FTHQ) too: the sumM row reads a handed dictionary.

