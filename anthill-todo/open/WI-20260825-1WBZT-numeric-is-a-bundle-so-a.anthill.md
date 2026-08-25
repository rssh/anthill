## Attributes

- id: WI-20260825-1WBZT-numeric-is-a-bundle-so-a
- created: 2026-08-25T17:15:42Z

- status: Open
- status_agent: claude
- status_at: 2026-08-25T17:15:42Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`Numeric` IS A BUNDLE, SO A CARRIER THAT ONLY ADDS MUST CLAIM MULTIPLICATION AND AN ORDER TO GET `+`. Split `Additive` out from under it, the way WI-20260824-VT8CF split `Divisible` / `EuclideanDomain` / `Field` out from under a single `div`. Found by driving a `Money` carrier as an example for that ticket; the numbers below are that program.

THE COST, COUNTED. To give a user sort a working `+`, it must assert `fact Numeric[T = C]`, and `Numeric` declares `add`, `sub`, `mul`, `neg`, `zero-val` and `requires PartialOrd[T]`, which declares `gt`, `gte`, `lt`, `lte`. NINE operations for one operator. For `Money(cents: Int64)`:

  add / sub          MEANINGFUL — money adds and subtracts
  neg / zero-val     MEANINGFUL — a debt, and nothing
  gt / gte / lt / lte MEANINGFUL — money orders
  mul                MEANINGLESS — cents times cents is cents-squared, which is not money

So `Money` must either implement a `mul` that is a lie, or omit it. DRIVEN: omitting it LOADS AND RUNS CLEAN — `Money(700) + Money(25)` answers 725 with no `mul` declared anywhere — and `Money * Money` then dies at RUN TIME with "expected matching Int, BigInt, or Float, got Entity", because the call falls through to the host builtin registered on the spec op. The choice a carrier author faces today is IMPLEMENT A LIE OR SHIP A SILENT HOLE, and nothing at load time says which was chosen.

WHAT THE SPLIT LOOKS LIKE. `Additive` owns the additive-monoid surface and, unlike `Divisible`, it is NOT law-free — `Numeric` already carries `add_comm`, `add_assoc` and `add_identity`, and those are exactly additive-commutative-monoid laws that belong on the floor that declares `add`:

  Additive       add, zero-val, neg;  add_comm / add_assoc / add_identity / neg_def
    +-- Numeric  provides Additive;   + sub, mul;  requires PartialOrd[T]

`sub` is a judgement call and should be measured rather than assumed: it is derivable (`sub(a,b) = add(a, neg(b))`) and every current carrier has it, so it may belong on `Additive` with a default body instead of on `Numeric`. Whether `requires PartialOrd[T]` stays on `Numeric` or moves is a second one — WI-644's note says `Numeric` itself uses no ordering op and the requirement is "the comparison surface consumers rely on", which is an argument for it being a consumer's `requires` rather than the spec's.

NAMING. `Additive` follows `Divisible`'s precedent — an operator-carrier name, legible without an algebra course — and the prelude has no algebraic tower to borrow from: `Semigroup`, `Monoid`, `Group`, `AbelianGroup`, `CommutativeRing`, `IntegralDomain`, `EuclideanDomain` and `GCDDomain` are ZERO hits across every `.anthill` and `.md` in the tree (censused under VT8CF), and `Monoid` exists only as a test fixture. The standard name for what this sort IS would be `CommutativeMonoid` (additive), or `AbelianGroup` once `neg` is in it; either would be the first rung of a tower nothing else in the library has, which is the same argument VT8CF used to prefer a plain name for the base and a standard one (`EuclideanDomain`) only where the LAW was standard. If the laws below are the real content, the standard name may be the right one here — that is this ticket's naming question rather than a settled point.

WHAT IT BUYS, beyond `Money`. `provides Additive[T = C]` becomes a claim a carrier can make TRUTHFULLY when it has no multiplication: durations, positions/offsets, counts with a unit, vectors (`anthill.geometry.Vec3` already declares `vec_add` / `vec_sub` / `vec_zero` and provides `VectorSpace` precisely because it could not say "additive" any other way), and the accumulator of any fold. Today each of those either over-claims `Numeric` or invents its own operation name and loses `+`.

WHAT IT COSTS. `Numeric` has FOUR provider sites (`anthill-stl` int64 / bigint / float, `anthill-cpp-gen` int64) and `provides Additive[T = T]` on `Numeric` carries the base to all of them with no per-carrier row — the same one-row-per-carrier property `EuclideanDomain provides Divisible` has. The stdlib's own bare `add` sites resolve through the implicit tier, which points at `anthill.prelude.Numeric.add`; that entry would have to move to `Additive.add` exactly as VT8CF moved `div` and `mod`, and `wi_bfb9a_rival_spec_operation_test::the_refusal_population_is_the_twelve_spec_operations` is the row that records it.

RELATED, AND POSSIBLY A REASON TO WAIT: WI-20260825-KD9SW would delete that tier entry altogether by making a minted `+` name its target outright. If it lands first, this ticket's tier hop is a one-line change to a constant instead of a table edit — and if this lands first, KD9SW's twelve-name census moves by one. They do not conflict, but doing KD9SW first is cheaper.

NOT DRIVEN: everything after "WHAT THE SPLIT LOOKS LIKE" is design. The cost paragraph IS driven — the nine operations, the clean load without `mul`, the 725, and the run-time death on `Money * Money` are all measured on the built tree.

CONTROL, when it is done: a `Money` carrier declaring ONLY `add` / `neg` / `zero-val` and asserting `fact Additive[T = Money]` — no `mul`, no `sub`, no comparison surface, and no `fact Numeric` — loads clean and answers `Money(700) + Money(25) = Money(725)` through a minted `+`. That row cannot pass today: `fact Additive` names nothing, and `fact Numeric` without `mul` passes the loader but is the silent hole this ticket exists to remove. `wi_vt8cf_division_tower_test::a_user_carrier_gets_plus_but_cannot_yet_provide_the_division_tower` is the existing row that drives the nine-operation version, and it should keep passing unchanged — a carrier may still claim the whole bundle.

ACCEPTANCE: a carrier providing `Additive` alone gets a working minted `+`; `Numeric provides Additive[T = T]` so its four existing providers need no new row; the additive laws sit with the operation that declares `add`; full workspace green via rustland/scripts/test.sh and scaland sbt test.

## Changes

### 2026-08-25T17:22:58Z — feedback — claude

ORDER THIS BEFORE WI-20260825-KD9SW, and the reason is stronger than the one in that ticket's body. KD9SW would have a minted `+` name its target by ADDRESS, and the address must be the sort that DECLARES `add` — `..anthill.prelude.Numeric.add` today, `..anthill.prelude.Additive.add` after this ticket, because the split leaves ONE declaration per short name (two would be `ordered.anthill`'s `sort_ops` HashMap coin flip). Land KD9SW first and every `+` in the corpus has to be re-minted when this one moves the declaration. It fails LOUDLY — 5W3RJ's address mechanism surfaces a rename at the use site — but a loud failure across every `+` is still a migration, and ordering avoids it. KD9SW's body currently advises the opposite ordering; a feedback there corrects it.

A CLARIFICATION THE SAME QUESTION EARNED, recorded because it is the natural worry and the answer is not obvious: a carrier does NOT have to provide `Numeric` for `+` to reach it, and will not have to provide `Additive` either in any address-specific sense. The mint names the SPEC op, the spec op is what DISPATCHES, and the carrier never appears in the address. Driven today: `Money(700) + Money(25)` = 725 through `Money.add`, off one `fact Numeric[T = Money]`, with the name resolved via the implicit tier to `Numeric.add`. After this split the same call would route `..Additive.add` -> dispatch -> `Money.add` with a `fact Additive[T = Money]` and NO `mul`, which is this ticket's whole point.

