## Attributes

- id: WI-20261113-5CZ9F-proposal-074-stage-4-a-named
- created: 2026-11-13T23:01:35Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-24T17:18:01Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1, WI-20261113-0FTHQ-proposal-074-stage-9-a-call

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 4 — A NAMED PROVIDER FIXES ITS PARAMETERS (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§2, "A provider named"; T11). `Dictionary.instance[Additive[T = Meters], Additive = ProjAdditive[X = Int64, Y = Meters]]()`, and the call's bracket `Additive.add[Additive = ProjAdditive[X = Int64, Y = Meters]](m(v: 2), m(v: 3))`, answer `m(v: 5)`: the named provider's type arguments fix `X`, after which its construction is `Int64`'s `Additive` and `MetersIso`, finite. Today refused: "construction is cyclic". Rows (§2, "A provider named"): the bracket `ProjAdditive[X = Int64]`, its positional `ProjAdditive[Int64]`, and `ProjAdditive[Int64, Meters]` answer `m(v: 5)`, `Y` fixed by the call's type where unwritten; the bare `Additive = ProjAdditive` is refused, naming `X` to write; the unnamed `m(v: 2) + m(v: 3)`, with `ProjAdditive` the only provider at `Meters`, is refused as no provider chosen there, its message naming `ProjAdditive` and the bracket that chooses it; `Additive.add(true, false)` is refused about `Bool`, not as a cycle; a cycle among provisions that fix every parameter keeps its message, "no type written at a use changes that". `sumM(d: Additive[T = Meters], a: Meters, b: Meters) = a + b`, handed the named dictionary, answers `m(v: 5)` (stage 1's rule). What is new to build (from review): a witness's plain type arguments are discarded today by design — `selection_witness_sym` (`kb/typing/slots.rs`) keeps the head, the witness's parameters being instantiated at the goal's bindings — so the selection keeps them, and they enter `InstanceSelection`, the key of `resolve_cache`, beside WI-870's `slots`; a row: two sites naming `ProjAdditive` at two `X` (an `Iso` from `Int64` to `Meters` and one from another carrier) each answer through their own. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

## Changes

### 2026-11-13T23:23:54Z — feedback — claude

FROM THE THIRD REVIEW (proposal 074 §5, with the user 2026-11-13): first, a census — every provider whose provides leaves one of its parameters unbound, in the standard library, the examples and the fixtures, and every call §8.7's order now passes it over at. Build notes: a witness's plain type arguments are discarded today (selection_witness_sym keeps the head), so the selection keeps them and they enter InstanceSelection, the resolve_cache key, beside WI-870's slots; two sites naming ProjAdditive at two X each answer through their own. Depends on stage 9 (WI-20261113-0FTHQ) too: the sumM row reads a handed dictionary.

### 2026-11-24T17:17:57Z — feedback — user

CENSUS AND DECISIONS (2026-11-24, with the user). Measured first: every T11 row refused 'construction is cyclic', named or not, and m(v: 2) + m(v: 3) and Additive.add(true, false) too. Census by a traced full gate (12700 / 0) of the providers §8.7's order chose whose provides leaves a parameter unbound: named requirement slots (OA, OB, OI; 79 providers) are none, a sub-goal or a bracket's value position answering them; the stdlib and the examples meet none of the rest; among the fixtures, a parameter the requires read in a provider with no values of its own is ProjAdditive's X and wi822's Ghost.U (a refusal row) alone; ~12 fixtures leave a parameter nothing reads (ownparam.P.B, n3w68 MidA, bd56.cyc); two providers with values of their own (wiekwdc's and gnpg7's Mid) leave one their value's type fixes. Decided: the narrow reading -- passed over only where the requires or conditions read the open parameter and the provider has no values of its own -- and proposal 074 §2's sentence amended (the user: 'we can add to sentence'). The witness's type arguments ride the selection as values hashed by their structural fingerprint (the user: 'we have hash on values'), not lowered to terms.

### 2026-11-24T17:17:59Z — feedback — user

DELIVERED (2026-11-24, ee630e14c): a bracket naming a provider, and Dictionary.instance's key, may write the provider's type parameters (by name or position); they fix what the goal leaves free (a conflicting one refused), key resolve_cache, and §8.7's order passes over a provider that leaves open a parameter its requires read. Acceptance: rows driven (wi_5cz9f_named_provider_test, 9: T11 via the dictionary and the bracket m(v: 5), the spellings m(v: 5), two sites at two X m(v: 5) / m(v: 50), the bare bracket refused naming X, the unnamed goal refused naming ProjAdditive and its bracket, Bool refused about Bool, a true cycle keeps its message, a parameter nothing reads leaves its provider chosen, a conflicting bracket refused); 7 parts backed out by a temporary switch over all of anthill-core (11626 rows, control clean), every part failing named rows; /code-review (xhigh) found a conflicting bracket argument ignored in silence, fixed with a row. Gate 12709 / 0; families green on both carriers; scaland testFull 811 + 51 (2 skipped) + 1. kernel-language 8.7 and proposal 074 agreed with the user.

