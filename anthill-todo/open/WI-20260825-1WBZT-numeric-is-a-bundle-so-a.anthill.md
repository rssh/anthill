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

### 2026-08-25T18:42:52Z — feedback — claude

WIDENED, AND SETTLED ON TWO POINTS: this is not one split but a RULE — every operator gets a SYNTAX CATEGORY, a spec owning exactly the operation that operator mints — and `Numeric` reaches them by `provides`, not `requires`.

THE RULE. `Divisible` is the shipped prototype and this ticket generalizes it: WI-20260824-VT8CF gave `/` a spec whose only content is `div`, for a resolution reason (one short name, one qualified target), and the same shape answers this ticket's claim-size problem for free. A carrier claims the categories whose operations it can honestly back, and nothing more.

  operator   category            owns                     status
  `=` `!=`   PartialEq           eq, neq                  EXISTS, already minimal
  `<` etc.   PartialOrd          lt, lte, gt, gte         EXISTS, already minimal
  `+` `-`    Additive            add, sub, neg, <zero>    NEW — this ticket
  `*`        Multiplicative      mul, <one>               NEW
  `/`        Divisible           div                      SHIPPED (VT8CF)
  `%`        EuclideanDomain     mod, rem                  SHIPPED (VT8CF)
  `^`        —                    pow                       NONE, deliberately (see below)
  `|` `&` `!` —                   or, and, not              WI-20260825-P9Y67's question

`Numeric` THEN BECOMES WHAT IT ALREADY CALLS ITSELF. `algebra.anthill` describes it as "Ring + Ord bundled into one spec for primitive arithmetic types" — a convenience bundle beside the algebra rather than in it. Under this rule that stops being an apology and becomes its job: `Numeric` provides `Additive`, `Multiplicative`, `Divisible`-or-not, and requires `PartialOrd`. Its four existing providers (`anthill-stl` int64 / bigint / float, `anthill-cpp-gen` int64) keep their one row and get every category by the chain — no per-carrier edit anywhere.

`provides`, NOT `requires`, AND THE DIRECTION WAS MEASURED. `Numeric provides Additive[T = T]`. The opposite spelling means a carrier must write BOTH rows and be trusted to keep them consistent; the `provides` form gives one row and one operation. WI-1109/WI-1110 measured exactly this choice on `Eq`/`PartialEq` and recorded both wrong answers: `requires` + `provides` fails 1867 of 2849 tests with "construction is cyclic: PartialEq[X] -> PartialEq[X]" because the provision is filed as a PROVIDER of the floor; `provides` alone under the wrong filing fails 32 with "unresolved import 'anthill.prelude.Eq.eq'". Filed as a CONVERSION in the chain it is correct, and it brings the scope with it, which is why `Eq.eq` still resolves to the inherited `PartialEq.eq`. Copy that filing.

THE TYPER REMAP IS NOT NEEDED FOR THIS, and should not be built for it. Minting `Additive.add` and letting the typer fall back to `Numeric.add` "when Numeric has add but does not provide Additive" trades a ONE-LINE declaration for a typer rule, and the rule is ambiguous in the CURRENT stdlib: `anthill-stl/anthill/float.anthill` writes both `provides Numeric[T = Float]` and `provides Ring[Float]`, and BOTH `Numeric` and `Ring` declare `add`, so "the spec has a same-named member" has two answers and no tie-break — the `sort_ops` coin flip `ordered.anthill` refuses, relocated into the typer. It also makes `provides` optional, which is a hole in proposal 058's model rather than a part of it: no provision, no condition, nothing for a coherence check to read. Recorded because the idea is reasonable-sounding and will be reached for again.

TWO THINGS THE GENERALIZATION TURNS UP, both pre-existing:

  * THE ADDITIVE IDENTITY HAS TWO NAMES. `numeric.anthill` declares `zero-val()` and `algebra.anthill`'s `Ring` declares `zero()` — same value, two spellings, and `Ring` also has `one()` with no `Numeric` counterpart. A category that owns the additive identity must own ONE of them, and every carrier providing both specs today would otherwise get two `sort_ops` entries for one concept under different names (not the coin flip — worse, because nothing collides and so nothing complains). Deciding the name is part of this ticket; `zero` is shorter and matches `one`, `zero-val` is what the four current carriers implement.
  * `^` STAYS WITHOUT A CATEGORY, and this rule is the reason to restate that rather than to change it. `pow` is declared on `Float` alone, `Int64` has none, and there are ZERO uses of `^` as an operator in the tree — so a `Power` category would assert a structure exactly one carrier satisfies. VT8CF decided that and wrote it at kernel-language.md §6.6; the generalization does not overturn it, because the rule is "a category per operator that HAS one", not "invent a spec so the table is uniform".

WHAT THIS DOES TO WI-20260825-KD9SW. Each operator would mint its own category's address (`..anthill.prelude.Additive.add`, `..anthill.prelude.Multiplicative.mul`), which is the same one-line-per-operator change either way — but it makes the ORDERING argument on that ticket sharper rather than weaker: every category this ticket creates MOVES a declaration, so all of them must land before any address is baked. Do the categories first.

CONTROL, unchanged in shape from the body's: a `Money` declaring ONLY `add` / `neg` / `zero` and asserting `fact Additive[T = Money]` — no `mul`, no comparison surface, no `fact Numeric` — loads clean and answers `Money(700) + Money(25) = Money(725)` through a minted `+`. Add a second row for the rule: `Int64` keeps its single `provides Numeric[T = Int64]` and `1 + 2`, `7 / 2`, `7 % 2`, `1 < 2` all still answer, which is what proves the bundle still bundles.

### 2026-08-25T18:48:34Z — feedback — claude

THE DIAMOND THIS CREATES IS THE BENIGN ONE, MEASURED — and the check that keeps it benign does not exist. Filed as WI-20260825-EBMG8.

The syntax-category rule makes `Numeric` and `Ring` both provide `Additive`, and `anthill-stl/anthill/float.anthill` already writes both `provides Numeric[T = Float]` and `provides Ring[Float]` — so `Float` reaches `Additive` by TWO paths. Driven on user sorts: that shape (base declares the operation ONCE, both branches only provide) LOADS CLEAN and is benign, because implementation is CARRIER-directed — both routes resolve to the carrier's own member by the short-name join, so there is no 'which parent's method' question to answer.

IT REMOVES A LIVE DUPLICATION RATHER THAN ADDING ONE, which is the half worth stating first: today `Numeric.add` and `Ring.add` are two DIFFERENT operations under one spelling, and a bare `add` seeing both is ambiguous — driven under VT8CF's census as "`add` is a member of sorts Numeric, Ring, not in scope as a bare name here" — resolved only because the implicit tier deterministically answers `Numeric.add`. One `Additive.add` declaration is the fix.

WHAT EBMG8 OWNS: the rule `ordered.anthill` states in prose ("declaring them a second time gives a carrier two `sort_ops` entries for one short name, and which one wins is HashMap-iteration order — a coin flip, not a rule") and 058 §3.8 restates ("the derivation adds a provision ROW, never a second op declaration") is enforced NOWHERE. Driven: a spec redeclaring a provided base's operation loads clean; and with two such specs over one carrier the answer follows SOURCE ORDER — 22 with `sort L` first, 33 with `sort R` moved above it, stable across runs either way.

NOT A BLOCKER for this ticket — the categories land in the benign shape — but this ticket's safety rests ENTIRELY on a discipline nothing checks, so EBMG8 should land near it. Source order is worse than a coin flip for exactly the reason it looks safe: stable in tests, stable across machines, and it flips when someone reorders two declarations or renames a file.

