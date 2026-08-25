## Attributes

- id: WI-20260824-VT8CF-and-are-capturable-by-a-same
- created: 2026-08-24T12:55:39Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-25T16:13:41Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`/`, `%` AND `^` ARE CAPTURABLE BY A SAME-NAMED DECLARATION, and neither of the two mechanisms that protect the other minted operators reaches them. Found by /code-review on the WI-20260824-BFB9A diff; the obvious fix was attempted there and REFUTED by the corpus, which is the part worth reading before trying again.

THE GAP, DRIVEN. With `operation mod(a: Int64, b: Int64) -> Int64 = 99` in a namespace, a minted `7 % 2` written in that namespace reaches the local declaration and returns 99 instead of 1. No diagnostic is raised anywhere. `/` (`div`) behaves the same; `^` (`pow`) has no tier target at all, so there is nothing even to reclaim to.

WHY NEITHER MECHANISM COVERS THEM. Two guards protect minted operators and both decline these by design:
  - WI-BFB9A's rival REFUSAL only reaches a spec operation on a PARAMETRIC carrier (`typing::spec_op_parent_sort`). `Int64.div` / `Int64.mod` sit on `Int64`, which declares no `sort T = ?`, so there is no `provides Int64[T = …]` to prescribe and the refusal correctly stands down — see `check_rival_spec_operations`.
  - `reclaim_minted_operator` only reaches the POSITION-DIRECTED BOOLEANS (`or`, `not`, `and`), whose primitives are `anthill.kernel.*` / `Bool.and` and which no carrier re-implements.
So one minted-operator family has three treatments — bypass the ladder, reclaim after it, or nothing — and this ticket owns the third.

THE OBVIOUS FIX IS WRONG, MEASURED. `reclaim_minted_operator` was briefly widened from "the position-directed booleans" to "any minted operator whose primitive does not DISPATCH", spelled `spec_op_parent_sort(primitive).is_none()`. That reads correctly and is false: `Int64.div` IS a concrete operation and passes the predicate, but the OPERATOR `/` is carrier-polymorphic — `Float.div` exists — so reclaiming forced every minted `/` to the Int64 one. SIX corpus rows fell with `type mismatch in div.a (op-arg): expected Int64, got Float`: `eval_test::{m3_float_division, m3_float_division_by_zero_is_infinity, m3_float_nan_detection}` and `lf1_real_spec_test::{lf1_lower_violation_is_unsat, lf1_step_distance_bound_is_within_two_meters, lf1_upper_violation_is_unsat}`. THE LESSON IN ONE LINE: "the primitive has one meaning" is not "the operator has one target". The narrowness is now stated at the site with this measurement.

WHAT A REAL FIX HAS TO DO. Decide `/` by the CARRIER of its operands, which is what the ladder is doing today when it reaches `Float.div` — so the repair cannot be a resolution-time override keyed on the name alone. Candidates, none costed: (a) make `Int64.div`/`Float.div` a dispatched spec op on a parametric carrier, which would put them inside BFB9A's refusal and close this by construction — the largest change and the only one that removes the special case; (b) refuse a free-standing declaration of any name pratt mints an operator to, independently of whether the target dispatches, which is a rule about OPERATOR SPELLINGS rather than about spec ops and needs its own census of what that would break; (c) accept the gap and document it in kernel-language.md beside the operator table.

NOT DRIVEN: (a), (b) and (c) are code reads. FIRST STEP: census how many names pratt mints an operator to that are NOT already covered by the refusal or the reclaim — the answer decides whether this is three names or a family.

CONTROL, when it is fixed: `a_non_parametric_carriers_operation_is_not_a_spec_op` (wi_bfb9a_rival_spec_operation_test) currently RECORDS the gap — it asserts the local `mod` wins and returns 99, with a pointer here. That row inverts when this closes, and its inversion is the measurement. Drive it through an OPERATION BODY, not a rule: `:- eq(7 % 2, 1)` answers 0 definite solutions with or without the shadow, because `eq` never binds and the goal suspends, so it measures nothing.

ACCEPTANCE: a minted `%` / `/` means its carrier's operation whatever the enclosing namespace declares, or the divergence is documented at the operator table with this ticket's number; the float rows above stay green; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-08-25T07:27:51Z — feedback — claude

THE `reclaim_minted_operator` THIS TICKET IS WRITTEN AROUND IS NOT IN THE TREE, and that WIDENS this ticket rather than narrowing it. Read this before the ticket body.

WHAT HAPPENED. WI-20260824-BFB9A was withdrawn after two /code-reviews and re-implemented on 2026-08-25. The reclaim did not come back. It was scope creep on BFB9A's ask — refuse a free-standing rival of a spec operation — and its query-path half carried a live defect: a `goal_position_boolean(resolved, pos_args.len())` added to `convert_query_term_expecting`'s `Term::Fn` arm, which recurses into positional AND named args through itself, so it routed at every depth and on WRITTEN calls. Measured: a fact holding `or(true, false)` became unqueryable by ANY spelling, exit 0, no diagnostic. Its doc also carried a fabrication ("`and` is absent from `PRELUDE_QUALIFIED` where `or` / `not` are present" — `anthill.prelude.Bool.and` IS in that table, load.rs, and is the sole reason `&` was reclaimable at all).

WHAT THIS TICKET'S POPULATION IS NOW. Two treatments, not three: BYPASS THE LADDER (`minted_connective_symbol`, the carrier-agnostic connectives `<=>` / `===` — WI-888's line, which deliberately excludes `eq`) or NOTHING. So `or`, `not` and `and` join `/`, `%` and `^` in the population this ticket owns: a namespace-level `operation or(...)` captures a minted `|` exactly as `operation mod(...)` captures `%`. Whether they are one family or two is this ticket's first question rather than a settled point — the reclaim answered it "two" on a code read, and that answer left with it.

WHAT IS UNCHANGED. BFB9A's refusal reaches none of these, for the reason the ticket body already states and which is now written in kernel-language.md §5.1 with this ticket's number at it: `Bool.and`, `Int64.div`, `Int64.mod` sit on NON-PARAMETRIC carriers and `anthill.kernel.or` / `.not` on no carrier at all, so `typing::spec_op_parent_sort` answers `None` and there is no `provides` to prescribe. `check_rival_spec_operations` exists and is that leg.

THE "OBVIOUS FIX IS WRONG, MEASURED" PARAGRAPH STANDS AS A MEASUREMENT and no longer describes the tree: the six float rows really did fall under `spec_op_parent_sort(primitive).is_none()`, but the function that predicate lived in is gone, so re-reading it as "the narrowness is stated at the site" will find no site.

THE CONTROL THIS TICKET NAMES DOES EXIST: `wi_bfb9a_rival_spec_operation_test::a_non_parametric_carriers_operation_is_not_a_spec_op` records the gap — `operation mod(a, b) = 99` in a namespace, and `7 % 2` written in that namespace answers 99. Driven through an OPERATION BODY, as this ticket prescribes. That row inverts when this closes.

### 2026-08-25T14:55:30Z — feedback — claude

SPLIT, AND THE DESIGN IS DECIDED. This ticket is now the NUMERIC half alone — `/`, `%`, `^`. The boolean half the 2026-08-25 feedback folded in (`|`, `&`, `!` / `or`, `and`, `not`) is WI-20260825-P9Y67, filed with its own driven rows: the value-position capture inverts three rows, and a GOAL-position `operation or` re-reads `rule q(?x) :- p(?x) | p(99)` as a boolean value test — `?x` never binds and a definite `?x = 1` becomes a floundered conditional. Split because the two halves need DIFFERENT fixes: this one has a parametric spec to move to and that one has none.

WHAT WAS MEASURED HERE, on the built tree at b885f8a1, all through an operation body via `anthill run` unless said otherwise:

  `10.0 + 4.0`, no import                     works
  `10.0 / 4.0`, no import                     type mismatch in div.a (op-arg): expected Int64, got Float
  `2.0 ^ 3.0`, no import                      `pow` is a member of sort Float, not in scope as a bare name here
  `operation mod(a,b) = 99` + `7 % 2`         prints 99                              <- the gap
  `operation add(a,b) = 99` + `7 + 2`         REFUSED by check_rival_spec_operations <- the control

THE PREMISE THE TICKET BODY CARRIES IS WRONG IN ONE WORD, and correcting it is what decided the fix. There is no CARRIER-dependent resolution of `/` to correct — the resolution is SCOPE-dependent. The minted bare `div` goes down the ordinary ladder and bottoms out on `PRELUDE_QUALIFIED`'s `anthill.prelude.Int64.div` (kb/load.rs); Float division works ONLY because every float site in the corpus writes `import anthill.prelude.Float.{div}` — 7 such import sites in the tree, `eval_test::m3_float_division` among them. That is the SAME rung a local `operation mod` shadows. So the capture and the "float division needs an import" wart are one mechanism and one fix closes both.

`+` ALREADY IS WHAT `/` SHOULD BE, driven three ways. `add`/`sub`/`mul`/`neg` mint to body-less spec ops on the parametric `anthill.prelude.Numeric` (`sort T = ?`), and they dispatch:
  - `10.0 + 4.0` works with no import;
  - a user sort `Money` declaring its own `add` and asserting `fact Numeric[T = Money]` answers 777 for `Money(1) + Money(2)` — the carrier's op wins, found by the SHORT-NAME JOIN (`resolve_op_target`), with NO `operation_map` entry and no host registration;
  - `operation twice[T](x: T) -> T requires Numeric[T] = x + x` answers 777 for Money and 42 for 21 — one body, two carriers, a genuine runtime dictionary.
So "will a spec op dispatch" is answered YES, and the cost objection is answered too: a concrete carrier with its own impl is resolved by the TYPER (no runtime dictionary), a concrete carrier with none — Int64, Float, BigInt declare no `add` — falls through to the spec op where eval's single `numeric_add` registration switches on `Value::Int|BigInt|Float` (also no dictionary), and only genuinely generic code pays a lookup. Moving `/` onto a spec puts nothing in `7 / 2`'s path.

THE SPEC ALREADY PRESCRIBES THIS. kernel-language.md §6.6's operator table gives Origin `Numeric` for `/`, `%` AND `^`. No `Numeric.div`, `Numeric.mod` or `Numeric.pow` exists — three rows are aspirational. So candidate (c) from the body ("accept the gap and document it") would mean editing the SPEC DOWN to the code, and candidate (a) is the documented design rather than a new one.

WHICH PARAMETRIC SPEC OWNS `div` — THE QUESTION THAT ACTUALLY NEEDED DECIDING. `Field` already exists (`sort T = ?`, `requires Numeric[T]`, declares `div`/`recip`) and has ZERO providers in the whole tree, and `field.anthill`'s own header excludes Int64 on purpose: truncated integer division discards information, `mul(div(7,2), 2) = 6` and not 7. So `/` cannot mint to `Field.div`. And `Field.div` is not merely `Int64.div` with an extra law — its declaration comment defines it AS `a * inv(b)`. They are two different operations sharing a spelling.

AND THEY CANNOT SIMPLY BE DECLARED ON TWO SPECS. `ordered.anthill` states the mechanism, about why `gt`/`lt` are declared on `PartialOrd` and NOT re-declared on `WeakOrd` where their laws live: a carrier providing BOTH specs would get two `sort_ops` entries for one short name, and which one wins is HashMap-iteration order (`build_sort_ops_table` pass 2) — "a coin flip, not a rule". That refutes the Haskell-shaped `Integral.div` + `Fractional.div` split outright, on this implementation's own terms.

DECIDED, with the user: a LAW-FREE base spec — working name `Divisible` — declares `div` ONCE, and each branch adds only what is new.

  Divisible        div(a, b)                                     -- no law; the `/` slot
    +-- Euclidean  provides Divisible;  + mod, rem, Euclid law    -> Int64, BigInt
    +-- Field      provides Divisible;  + recip, inverse law      -> Float (approximately), Rational

`provides`, not `requires`, is the WI-1110 spelling: "hold a Field[T] and you can obtain a Divisible[T]", one row per carrier — the same shape as `Eq provides PartialEq[T = T]`.

WRITE THE JUSTIFICATION ON THE SORT, because `Divisible` is NOT the `PartialEq` -> `Eq` pattern and a later reader will assume it is. `Eq` adds a law to the SAME operation; these two branches pin down WHICH operation `div` is. `Divisible` is therefore an OPERATOR-CARRIER spec — Rust's `std::ops::Div`, not an algebraic structure — and its entire justification is that it gives `/` exactly one symbol to resolve to. Anything that later tries to give it laws is undoing the point.

WHY NOT NAME IT FROM ABSTRACT ALGEBRA: because the prelude has no algebra to name it from. Censused — `Semigroup`, `AbelianGroup`, `CommutativeRing`, `IntegralDomain`, `EuclideanDomain`, `GCDDomain`, `PrincipalIdealDomain`, `UniqueFactorizationDomain` are ZERO hits across every `.anthill` and `.md` in the tree; `Monoid` exists only as a test fixture (`anthill-testcases/fact-substitution/monoid.anthill`) and as reflection doc examples. What exists is `Ring` + `VectorSpace` (algebra.anthill), `Field` (unprovided), `Lattice`/`BoundedLattice`, and `Numeric` — whose own header calls it a pragmatic bundle, "Ring + Ord bundled for primitive arithmetic types", i.e. explicitly beside the tower and not in it. No library proposal covers the hierarchy either (001..007 are map, iteration, finite-collection, partial-vs-total eq/ord, stored refs, reflection schemas, weak-vs-strong ordering). `EuclideanDomain` IS the standard structure that owns `div` + `mod`, but naming it that would claim the rungs between `Ring` and it that this prelude does not have; `Euclidean` names the LAW it would actually carry (`a = b*div(a,b) + mod(a,b)`) without claiming the domain structure, which is why it is preferred over Haskell's carrier-shaped `Integral`.

`mod` GOES ON THE BRANCH, NOT THE BASE, and this is measured rather than aesthetic: Float has `div` and no `mod`, and a provider that OMITS a spec member LOADS AND RUNS CLEAN — driven by deleting `Money.mul` while keeping `fact Numeric[T = Money]`, which loads, runs, and then dies at run time on `Money(1) * Money(2)` with "expected matching Int, BigInt, or Float, got Entity". Putting `mod` on the base would plant exactly that on Float, silently.

THE RESOLVER ALREADY IMPLEMENTS THIS TOWER. `kb/resolve.rs` — `BuiltinTag::Div` computes on int, bigint AND float; `BuiltinTag::Mod` computes on int and bigint with the float slot already `None`. Divisible over three carriers, Euclidean over two. The only component that does not know is the name ladder, which pins both to `Int64`.

THE WORK, and every impl already exists with the right short name on the right carrier (the `Money.add` row is the precedent that the short-name join needs no wiring):
  1. `Divisible` + `Euclidean` in the prelude; `field.anthill` drops its `div` declaration and gains `provides Divisible[T = T]` — a 2-line edit, and `Field` has no providers so nothing else moves.
  2. Provider rows in the binding files — 4 sites total (`anthill-stl` int64/bigint/float, `anthill-cpp-gen` int64).
  3. `PRELUDE_QUALIFIED`: `Int64.div` / `Int64.mod` -> the two spec ops.
  4. `BuiltinTag::Div` / `Mod` keys move to the spec ops; the builtins themselves are already written for every carrier.
  5. BIGINT IS THE ONE REAL GAP — it declares no `div`/`mod` at all (its `operation_map` is the seven ordering ops). The resolver computes both; eval has neither. Two declarations plus two registrations.
  6. The 7 `import Float.{div}` lines become unnecessary (they keep working).
  7. Operator table §6.6: `/` Origin `Divisible`, `%` Origin `Euclidean`.

`^` IS OUT OF SCOPE AND SHOULD BE SAID SO RATHER THAN SOLVED. `pow` exists only as `Float.pow`, `Int64` has none, and there are ZERO uses of `^` as an operator anywhere in the tree. Today's error names the carrier and the repair, which is the right behaviour; the §6.6 row should say `Float` with this ticket's number rather than the `Numeric` it now claims.

THE CONTROL NAMED IN THE BODY LOSES ITS SUBJECT, and a replacement is part of the work. `wi_bfb9a_rival_spec_operation_test::a_non_parametric_carriers_operation_is_not_a_spec_op` uses `mod` PRECISELY because `Int64` is non-parametric. Once `mod` is a `Euclidean` member that row inverts — which is this ticket's stated measurement — but the exemption LEG of `check_rival_spec_operations` then has no test at all unless the row is re-subjected onto something still non-parametric. `anthill.prelude.Bool.and` and `anthill.prelude.BigInt.to_bigint` both remain, and §5.1 lists them.

### 2026-08-25T15:03:55Z — feedback — claude

CORRECTION TO THE PRECEDING FEEDBACK: THE EUCLIDEAN LAW IT NAMES CANNOT BE WRITTEN OVER `div` AND `mod`, because Int64 — the canonical Euclidean domain — REFUTES it. The branch sketch "Euclidean: provides Divisible; + mod, rem, Euclid law" stands as a shape; the LAW named in it does not.

DRIVEN, through an operation body on the built tree:

  div(-7, 2)  = -3     truncated toward zero      (matches its declaration)
  mod(-7, 2)  =  1     Euclidean, non-negative    (matches its declaration)
  rem(-7, 2)  = -1     truncated, sign follows dividend (matches its declaration)

  2*div(-7,2) + mod(-7,2) = -5     the division law a = b*q + r FAILS
  2*div(-7,2) + rem(-7,2) = -7     it holds for THIS pair

EACH OPERATION IS CORRECT AGAINST ITS OWN DECLARATION. The defect is that `div` and `mod` were taken from DIFFERENT CONVENTIONS — truncated quotient, Euclidean remainder — so the pair satisfies no division law at all. Stated crisply: the prelude has truncated `div`, truncated `rem`, and Euclidean `mod`, and NO floored or Euclidean QUOTIENT anywhere. `mod` is orphaned — it is the only one of the three with no quotient partner in the library.

WHY THE STANDARD STRUCTURE DOES NOT RESCUE THIS, and the reason the base stays law-free. A EUCLIDEAN DOMAIN is an integral domain R with a Euclidean function N on R\{0} such that for every a and every b != 0 there EXIST q, r with a = b*q + r and either r = 0 or N(r) < N(b). Two properties of that definition decide the design:

  - THE PAIR IS NOT UNIQUE. The definition asserts existence only. For -7 = 2q + r with |r| < 2, BOTH (-3, -1) and (-4, 1) qualify. So the algebra does not pin truncated vs floored vs Euclidean; a language must choose a convention, and that choice is EXTRA to the structure. This is precisely the choice the prelude made inconsistently.
  - FIELD IS A SUBSET OF EUCLIDEAN DOMAIN, not a sibling of it — every field is trivially Euclidean with r identically 0, since a nonzero b is invertible. So the mathematically standard nesting is the OPPOSITE of the branch sketch, and it is useless here: it would give Float a `mod` identically 0, where what `7.0 % 2.0` must answer is 1.0. Float's `%` is not a Euclidean-domain operation at all — it is "remainder after truncating the exact quotient", a Z-flavoured operation on a field.

So the standard structure EXISTS and DOES NOT FIT. That is an argument FOR the law-free `Divisible` base, not against it, and it is the sentence to put on the sort.

WHAT THE BRANCH SHOULD CARRY INSTEAD. The law goes over the pair that satisfies it — `div` and `rem`, not `div` and `mod`:

  rule add(mul(?b, div(?a, ?b)), rem(?a, ?b)) = ?a :- neq(?b, 0)

with `mod` characterized by its own RANGE (0 <= mod(a,b) < |b|, and a congruent to mod(a,b) modulo b) rather than by a quotient it has none for. Naming the branch `Euclidean` is then still right — it is the structure with division-with-remainder — but the law it states must be the true one.

THE ALTERNATIVE IS A DELIBERATE BEHAVIOUR CHANGE, not a cleanup, and it needs its own decision: make `div` FLOORED so that `(div, mod)` pairs up. That flips `-7 / 2` from -3 to -4, and `wi863_operator_arithmetic_test` pins the current answer explicitly ("-7 / 2 truncates to -3"). That test is the control for the change, in either direction.

CONSTRAINT NOTE: `int64.anthill`'s `constraint mod_positive: gt(?b, 0) :- mod(?_, ?b)` constrains the DIVISOR, not the dividend, so a negative dividend is in scope and the mismatch above is live rather than excluded by declaration.

### 2026-08-25T15:12:04Z — feedback — claude

THE BRANCH IS `EuclideanDomain`, AND THE REASON GIVEN AGAINST THAT NAME DOES NOT STAND. Two feedbacks up it was named `Euclidean` on the grounds that "naming it EuclideanDomain would claim the rungs between Ring and it that this prelude does not have". That objection is refuted by the prelude itself, and a second objection recorded there is refuted by a measurement.

THE PRELUDE ALREADY NAMES STRUCTURES APPROXIMATELY, so the missing rungs are not a new compromise. `anthill.prelude.Field` sits on `requires Numeric[T]` — there is no `IntegralDomain` and no `CommutativeRing` beneath it, because neither exists — and `algebra.anthill` states outright that "Float satisfies Ring via the prelude's Numeric ops", which rounding refutes at the boundary exactly as overflow refutes `Numeric`'s `add_assoc` for `Int64`. `EuclideanDomain requires Numeric[T]` is the SAME move `Field` already makes, at the same honesty level, and it tells a reader which laws to expect where `Euclidean` alone is a non-word. Int64's arithmetic is CHECKED — overflow raises rather than wraps — so it is morally restricted-Z, and "no zero divisors", which is the content of integral domain, holds.

FLOAT HAS NO `mod` — IT HAS `fmod`, and that voids the under-provision worry recorded in the preceding feedback. `float.anthill` declares `fmod(a: Float, b: Float) -> Float  -- IEEE remainder (sign follows a)`, host-mapped as `float_fmod`. There is NO `Float.mod` and no `Float.rem`. So `%` is not available on floats today, none is expected, and putting `mod` on the Euclidean branch under-provides nothing. The earlier argument that `mod` must go on the branch "because Float has div and no mod" reached the right placement through a wrong premise; the right premise is that `mod` is a Euclidean-domain operation and Float is not a Euclidean domain.

THE ONE TRUE OBJECTION IS CHEAP TO PAY. Mathematically Field is a SUBSET of EuclideanDomain — every field is trivially Euclidean with r identically 0 — so a reader may expect `Field provides EuclideanDomain[T = T]`, and the library deliberately will not write it. What that declines is a true but USELESS implication: the Euclidean structure on a field is degenerate and is not what any Float operation computes. Say so at the sort rather than leaving the divergence to be rediscovered.

THE BASE'S JUSTIFICATION WAS ALSO WRONG, and the correct one is the ticket's own subject. The preceding feedback justified a single base by `ordered.anthill`'s `sort_ops` coin flip — two specs declaring one short name giving a carrier that provides BOTH two entries, resolved by HashMap-iteration order. THAT HAZARD DOES NOT FIRE HERE: no carrier provides both `Field` and `EuclideanDomain`. The base is load-bearing for a different reason, and it is this ticket's own: `/` mints a BARE `div`, and the implicit tier maps one short name to exactly ONE qualified name, so a `div` that is a member of two specs leaves `PRELUDE_QUALIFIED` unable to point anywhere without choosing by operand carrier — which IS the carrier-dependent demangling this ticket exists to remove. THE SINGLE BASE SPEC IS THE ALTERNATIVE TO DEMANGLING. That sentence belongs on the sort; it is not an algebraic claim and must not be read as one.

  Divisible            div                                          -- one spec, so `/` has one symbol; NO law
    +-- EuclideanDomain  provides Divisible; + mod, rem, division law  -> Int64, BigInt
    +-- Field            provides Divisible; + recip, inverse law      -> Float

THE BASE CANNOT CARRY THE TRUNCATED LAW EITHER, checked rather than assumed. `a = b*div(a,b) + rem(a,b)` is TRUE for Int64 (driven: 2*(-3) + (-1) = -7) and FALSE for Float, whose `div` is exact: 2*(-3.5) + (-1.0) = -8.0, not -7.0. Float's `fmod` relates to Float's `div` by no division identity at all. So the base stays law-free on a measurement and not on taste.

A WART THIS TURNED UP, recorded rather than fixed: `Int64.rem` and `Float.fmod` are THE SAME OPERATION — truncated remainder, sign follows the dividend — under two names. `EuclideanDomain` cannot unify them because Float is not one, and the base cannot because the law does not hold there. Two names is the defensible outcome; it is not something this design closes.

WHO PROVIDES `Divisible` — THE CARRIERS, THROUGH THEIR BRANCH, AND NOT AN ARITHMETIC SPEC ABOVE THEM. Two shortcuts were considered and both are refused, each on its own ground.

`Ring provides Divisible` IS FALSE. `Ring` is precisely the structure WITHOUT division, and `algebra.anthill` says so in its own words: "Operations are total. Subtraction is defined... Division is NOT — that's a Field, a separate spec we'll add when needed." Matrices, Z/4 and polynomial rings are rings with no division, so the clause would make every future ring owe a `div` it does not have. It also buys nothing measurable: `Ring` has exactly ONE provider in the tree (`provides Ring[Float]`, anthill-stl/anthill/float.anthill) plus a test fixture's `fact Ring[Int64]`, and Float reaches `Divisible` through `Field` regardless.

NOTE THE DIRECTION, because the two readings are opposite. In this prelude `provides` is the CONVERSION direction — eq.anthill's WI-1110 note: "hold an `Eq[T]` and you can obtain a `PartialEq[T]`" — so the STRONGER spec provides the weaker. "Division needs a ring's `mul` beneath it" is therefore `Divisible requires Numeric[T]`, which is the same spelling `Field requires Numeric[T]` already uses, and it is right.

`Numeric provides Divisible` IS ALSO REFUSED, and this one is the tempting version because it would save every carrier a row. It is refused on a MEASUREMENT: of the three carriers that provide `Numeric`, BIGINT DECLARES NO `div` AT ALL (its own file declares seven ordering operations and the three conversions; `div` count is zero). A provider that omits a spec member LOADS AND RUNS CLEAN — driven by deleting `Money.mul` while keeping `fact Numeric[T = Money]`, which loads, runs, and then dies at run time on `Money(1) * Money(2)` with "expected matching Int, BigInt, or Float, got Entity". So the clause would plant a silent hole on BigInt and on every user carrier that has arithmetic and no division. Reaching `Divisible` through the BRANCH keeps BigInt's gap visible as work item 5 of the preceding feedback's list instead of hiding it inside a provision.

### 2026-08-25T16:13:08Z — feedback — claude

DELIVERED — `/` and `%` are carrier-agnostic, and the capture closes BY CONSTRUCTION with nothing added to `check_rival_spec_operations`.

WHAT SHIPPED. A three-sort division tower in a new `stdlib/anthill/prelude/division.anthill`, and the implicit tier repointed at it:

  Divisible          div                                  -- no law, no `requires`; the `/` slot
    +-- EuclideanDomain  provides Divisible; + mod, rem   -> Int64, BigInt
    +-- Field            provides Divisible; + recip      -> Float

  PRELUDE_QUALIFIED:  div -> anthill.prelude.Divisible.div
                      mod -> anthill.prelude.EuclideanDomain.mod

`Field` dropped its own `div` and gained `provides Divisible[T = T]`; `Int64` and `BigInt` gained `provides EuclideanDomain`, `Float` gained `provides Field`, in both the rust and the cpp bindings. Each carrier's existing operation is found by the SHORT-NAME JOIN, so no new implementations and no new `operation_map` entries were needed except BigInt's.

MEASURED, before -> after, every row through an operation body:

  `10.0 / 4.0`, no import        type mismatch: expected Int64, got Float   ->  2.5
  `operation mod(a,b)=99; 7 % 2` prints 99, no diagnostic                   ->  REFUSED at the declaration
  `operation div(a,b)=99; 7 / 2` prints 99, no diagnostic                   ->  REFUSED at the declaration
  `7 / 2`, `-7 / 2`, `7 % 2`, `-7 % 2`   3, -3, 1, 1                        ->  unchanged
  BigInt `100 / 7`, `100 % 7`, `-100 % 7`   no such operation               ->  14, 2, 5
  generic `f[T](x,y) requires EuclideanDomain[T] = x / y`   impossible      ->  runs over Int64 AND BigInt

The refusal is the SAME message `add` already got, from the same pass. `check_rival_spec_operations` was not touched: a tier name is refusable exactly when what it points at can be `provides`-ed, and division could not be until it had a spec.

BIGINT HAD NO DIVISION AT ALL and now does — `div`/`mod`/`rem` declared, host-mapped (`bigint_div` / `bigint_mod` / `bigint_rem` in `eval/builtins.rs`), and the sort was providing `Numeric` while declaring none of them. The RESOLVER computed all three already (the BigInt slots of `BuiltinTag::Div`/`Mod`), which is what made the hole invisible: a rule-body division answered while the same division in an operation body had nothing to dispatch to.

TWO THINGS THE WORK ITSELF FOUND, both fixed:

  1. THE GUARDED EFFECT BELONGS ON THE SPEC OP, and the ticket's design said the opposite. Written with no `effects` row on `Divisible.div` — on the argument that partiality is the carrier's property — FOUR carriers became load errors: "overrides ... but does not refine it: the override declares effect ... which is not covered by any effect the spec operation declares (effects must not widen)". An override NARROWS and never widens, so the spec must carry the permissive row and `Float.div` narrows it to nothing. That is why `1.0 / 0.0` is still `+Infinity`.

  2. THE DISPATCHED PATH NEVER DISCHARGED A GUARDED EFFECT — a general defect, previously unreachable for division. `check_apply_iter`'s op's-own-effect loop ran WI-067 discharge; `dispatched_impl_effects` — the row a dispatched spec-op call takes instead — did not, so the impl's guarded atom came back conservatively present after the spec op's identical one had just been discharged. MEASURED the moment `/` became a spec op: `Int64.div(n, 2)` loaded pure while `n / 2` and `Divisible.div(n, 2)` both demanded a declared `Error[DivisionByZero]`, for a divisor literal that refutes `eq(b, 0)` by ground evaluation. Fixed by extracting the discharge into ONE owner (`push_effect_with_guard_discharge`) and calling it from both, with `flow` threaded to the four `dispatched_impl_effects` sites. CONTROL: `n / 0` still carries the effect — the fix drops it only on a positive proof of the negated guard, never by NAF.

THREE DIVERGENCES RECORDED RATHER THAN CLOSED, each at its own site:

  * `%` OVER FLOAT moved from a LOAD error to a RUN-TIME raise. `Float` provides `Field`, not `EuclideanDomain`, so `7.5 % 2.0` has no implementation; it used to be refused by the type mismatch against `Int64.mod`. The cause is WI-325's deliberate concrete-`NoCandidates` pass-through ("host builtin / spec-derived rule may resolve at runtime"), which does the same for a carrier that provides `Numeric` without declaring `mul`. Narrowing that arm is a general typer change with its own census. PINNED by `float_has_no_minted_modulo_but_does_have_fmod`, which asserts both the load and the raise, so it is not silent.

  * SMT LOWERING REFUSES A BARE `/`. `SMT_BUILTINS` keys on the functor alone and has no operand sort at the emit site, and the two carriers need DIFFERENT operators (`div` is SMT-LIB integer division, `/` is Real) — so a `Divisible.div` row would be silently wrong for one of them, on a proof obligation. There is deliberately no row: a bare `/` fails loudly with "unhandled arithmetic op 'div'", and the repair is the `import anthill.prelude.Float.{div}` every in-tree spec already writes. The reason is now written at the table. NOT caught by the corpus — every smt-gen test imports `Float.div`, so the tests are green either way; found by censusing the readers of the old qualified name rather than by running them.

  * A BARE FLOAT `/` OVER-APPROXIMATES ITS EFFECT ROW. A dispatched call MERGES the impl's effects into the spec op's rather than replacing them, so with a SYMBOLIC divisor `a / b` over floats carries an `Error[DivisionByZero]` IEEE division can never raise, while `Float.div(a, b)` is pure. Sound, imprecise, and not specific to division — it is how every dispatched spec op with a guarded effect behaves. A literal divisor discharges on both spellings, so it is a wart and not a wall. PINNED by `a_bare_float_division_over_approximates_its_effect_row`, which asserts the SEPARATION (bare impure, qualified pure) rather than the answer we would prefer. WORTH ITS OWN TICKET: "does a resolved dispatched call take the impl's effect row or the union" is a typer semantics question affecting every dispatched spec op, and it needs a census rather than an inline change.

TESTS. New `wi_vt8cf_division_tower_test.rs`, ten rows, with the back-out stated in the file header (repoint the two `PRELUDE_QUALIFIED` entries at `Int64.{div,mod}` and move the builtin tags back): every row naming a non-`Int64` carrier fails, and the `Int64` rows pass either way BY DESIGN, pinning that the repair changed nothing for the carrier that already worked.

TWO EXISTING ROWS MOVED, both deliberately:
  * `a_non_parametric_carriers_operation_is_not_a_spec_op` INVERTED — it asserted `Int(99)` and pointed here; it now asserts the refusal, plus the unshadowed `7 % 2 = 1` on the same expression, because a program that does not load cannot show the value.
  * `the_refusal_population_is_the_ten_spec_operations` is now TWELVE — `div` and `mod` joining is the whole ticket read off one list. `rem` is deliberately absent: an `EuclideanDomain` member, so a spec operation, but no operator mints it and it is not a tier entry, so a free-standing `rem` shadows nothing.

THE EXEMPTION LEG WAS RE-SUBJECTED, as this ticket's own feedback required. `a_non_parametric_carriers_operation_is_still_not_a_spec_op` uses `BigInt.to_bigint`, and `a_spec_op_reached_only_by_import_is_a_rival_too` — the only row separating "the rule is about spec operations" from "the rule is about the tier's table" — was rebuilt on a spec DECLARED IN THE TEST rather than on `Field.div`, whose disappearance took its subject away. A row whose subject is a library accident expires when the library changes, and that one already did once.

SCALAND. `EmbeddedStdlib` reads the same `stdlib/` files from disk, so `division` had to join its list before `field`. Its `WI-1066 CORPUS CONTROL` gained two rows and they are the first carrying BOTH clause kinds on one sort — `Divisible` from a `provides` (is-a) and `Numeric` from a `requires` — and `EuclideanDomain`'s also mixes the two qualifications, bare for the same-file `Divisible` and `_root_`-qualified for `Numeric`.

DOCS. kernel-language.md §6.6's operator table had `/`, `%` and `^` at Origin `Numeric`, which was ASPIRATIONAL — no `Numeric.div`/`mod`/`pow` ever existed. Two rows are now true; `^` is `Float` with a paragraph saying why it has no spec and is not getting one. §5.1's non-parametric exemption list lost `Int64.div`/`Int64.mod` and gained a note that they left by the tier being repointed rather than by a new exemption — the escape was never a property of division.

`^` IS UNTOUCHED AND SAID SO. `pow` is declared on `Float` alone, `Int64` has none, and there are ZERO uses of `^` as an operator anywhere in the tree. Today's error names the carrier and the repair, which is the right behaviour; inventing a spec for one operation with no second carrier would assert a structure nothing satisfies.

WHAT `/code-review high` FOUND, all four fixed and each with its own row:

  1. THE NEW HELPER STOLE `dispatched_impl_effects`' DOC COMMENT. Inserted with no blank line between the existing WI-365 block and the `fn` line, so both merged onto `push_effect_with_guard_discharge` and the original function was left with none. Invisible to the compiler and to the suite. The displaced paragraph was the one stating the spec-vs-impl parameter-naming rule — i.e. the rule finding 2 says the code then broke.

  2. σ WAS PAIRED BY THE IMPL'S PARAMETER LABELS, AND THE CALLER WRITES THE SPEC'S. The first cut called `build_call_guard_sigma(kb, &impl_op.params, …)`, which matches a named argument's LABEL against the params it is handed — correct where the call was matched against those params, wrong here. An override may RENAME its parameters (they align positionally, not by name), so a named call left σ EMPTY, the guard never grounded, and a literal divisor that refutes it kept a spurious `undeclared effect` — the exact false positive the discharge fix exists to remove, reintroduced for named calls. The PERMUTED case is worse and unsound: label-matching binds the guard to the WRONG OPERAND, dropping an effect that is really incurred. Repaired by pairing off the `spec_params` map the same loop already computes. DRIVEN by `the_guard_sigma_pairs_by_the_spec_ops_labels`, whose back-out (swap `spec_params.get(i)` for `impl_op.params.get(i)`) was RUN and fails with exactly the predicted message.

  3. THE BIGINT ASSERTIONS COULD NOT FAIL. `drive` renders the `Debug` of an `Option[Int64]` — `Entity { functor: Symbol(37), pos: [], named: [(Symbol(171), Int(14))] }` — so `contains("2")` is satisfiable by a digit of an INTERNING ID, and the headline new capability was unmeasured under a different symbol numbering. Now `contains("Int({want})")`, which can only be the payload; the same flaw in the generic row is fixed with it.

  4. THE SMT NOTE TOLD HALF THE STORY. It framed the missing `Divisible.div` row as a float problem; the INTEGER half regressed too — a bare `a / b` over `Int64` used to emit SMT-LIB `div` and now needs an `import anthill.prelude.Int64.{div}` it never needed. Both halves are now stated, with the censused fact that no in-tree `.anthill` file is affected. The note also cited the wrong in-tree writer of the float import (`safety_common.anthill`; it is `examples/webots-modelling/lf1/safety_gps.anthill`).

The review separately confirmed clean: the three BigInt host fns match the resolver's slots exactly including the negative-divisor lift; the `check_apply_iter` extraction is byte-equivalent to the inlined code and all four call sites took the new `flow`; the pre-registration covers exactly the two names `register_builtin_tags` resolves; cpp-gen's `int64.anthill` maps all three operations so the new provision has implementations; and no carrier provides both branches, so there is no coherence overlap.

GREEN ON THE FINAL TREE: full workspace via `rustland/scripts/test.sh` — 36 suites, 5711 tests, 0 failed. `scaland` — 514 tests, 0 failed. Both re-run AFTER the review fixes, not before.

### 2026-08-25T16:13:40Z — feedback — claude

CORRECTION TO THE DELIVERY NOTE, ONE NUMBER: `wi_vt8cf_division_tower_test.rs` has TWELVE rows, not the ten the note says. The draft was written before the last two were added, and a row COUNT in this repo is a census someone will later diff against the file — so it is worth being right rather than approximately right.

The twelve, and what each is FOR, so the count is checkable rather than trusted:

  float_division_needs_no_import                              the wart closed; fails hardest on a back-out
  float_division_by_zero_is_still_infinity_not_an_effect      the carrier NARROWS the spec's guarded row
  int_division_and_modulo_are_unchanged                       PASSES BOTH WAYS by design; the negative row
                                                              would catch a switch to floored division
  bigint_division_now_exists                                  a capability that did not exist at all
  one_generic_body_divides_over_two_carriers                  the runtime dictionary; one body, two carriers
  the_division_identity_holds_for_rem_and_not_for_mod         the design decision, as the DISAGREEMENT
  the_tower_is_wired_as_two_branches_over_one_base            what the library WROTE (provision facts)
  float_has_no_minted_modulo_but_does_have_fmod               divergence 1, pinned: loads, then raises
  the_guard_sigma_pairs_by_the_spec_ops_labels                the /code-review finding 2 repair, with its
                                                              back-out RUN
  each_branch_reaches_the_base_and_neither_reaches_the_other  what the TYPER DOES with it — the separating
                                                              matrix, whose two REFUSALS are what make the
                                                              four positive rows evidence
  a_bare_float_division_over_approximates_its_effect_row      divergence 3, pinned as the separation
  the_implicit_tier_points_at_the_spec_operations             the mechanism the whole ticket rests on

TWO OF THEM ARE THE ANSWER TO ONE QUESTION ASKED TWO WAYS, deliberately. `the_tower_is_wired_as_two_branches_over_one_base` reads the `SortProvidesInfo` facts; `each_branch_reaches_the_base_and_neither_reaches_the_other` drives requirement DISCHARGE over six programs. The second is the stronger one and would have been enough on its own — a fact table can be right while the typer does something else with it — but the first localizes a failure to the library rather than the typer, which is worth one cheap row.

### 2026-08-25T17:16:03Z — feedback — claude

A USER CARRIER CANNOT PROVIDE THE DIVISION TOWER, and the delivery note did not say so. Found while building a `Money` example after delivery; recorded here because the tower now LOOKS extensible and the gap needs saying at the ticket that built it.

DRIVEN, five spellings of the same carrier, differing ONLY in the effects row on `Money.div`/`mod`/`rem` whose bodies divide `Int64` fields:

  effects Error[DivisionByZero]                  -> 'must not widen' (an UNGUARDED row is
                                                    wider than the spec's guarded one)
  effects { … :- eq(b, zero-val()) }             -> 'must not widen'
  effects { … :- eq(b, zero-val) }               -> 'must not widen'
  effects { … :- eq(b, Money(cents: 0)) }        -> 'must not widen'
  (no effects row)                               -> 'undeclared effect' from the body

A PINCER: declare it and the override widens, omit it and the body incurs it undeclared. The coverage check compares the guard STRUCTURALLY against `Divisible.div`'s `eq(b, 0)`, whose `0` is an `Int64` literal, and no spelling over a `Money` operand can match that. So `Int64`, `BigInt` and `Float` reach the tower because they are HOST carriers — exempt from the load-time backing check and declaring the guard in the spec's own vocabulary — not because a carrier in general can.

NOTHING REGRESSED: a user carrier could not divide before this ticket either, when `/` meant `Int64.div` outright. What is new is the appearance of extensibility. `each_branch_reaches_the_base_and_neither_reaches_the_other` exercises the three host carriers ONLY, and that is a narrower claim than it reads as.

PINNED, not left silent: `wi_vt8cf_division_tower_test::a_user_carrier_gets_plus_but_cannot_yet_provide_the_division_tower` drives all four refusals plus the ADDITIVE half that does work (`Money(700) + Money(25)` = 725 through the carrier's own `add`, one `fact Numeric[T = Money]` and no wiring). If the pincer ever closes, that row's negative arms invert and it should become the positive test it wants to be.

THE REPAIR IS NOT THIS TICKET'S. Either the coverage check learns that a guard over the carrier's own zero REFINES a guard over the literal `0` — which needs the carrier's `zero-val` and is a real typing question — or the tower's spec ops drop the guard and each carrier declares its own, which re-opens the widening problem from the other side. Both need their own census. WI-20260825-SKWTH is adjacent (it owns the merge-vs-replace question on the same effect rows) but is NOT the same defect and must not absorb this one.

ALSO SURFACED, and filed as WI-20260825-1WBZT: the ADDITIVE half costs nine operations. `Numeric` declares add/sub/mul/neg/zero-val and `requires PartialOrd[T]` (gt/gte/lt/lte), so a carrier that only adds must claim a multiplication it does not have — and omitting it loads clean, then dies at run time.

