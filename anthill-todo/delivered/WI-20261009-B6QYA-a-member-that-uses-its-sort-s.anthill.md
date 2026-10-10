## Attributes

- id: WI-20261009-B6QYA-a-member-that-uses-its-sort-s
- created: 2026-10-09T06:44:42Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-10T16:43:36Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261008-HZVQA-the-parameters-an-alias-fixes

- tags: typing

## Description

A MEMBER THAT USES ITS SORT'S PARAMETER COULD TAKE IT AS A TYPE PARAMETER OF ITS OWN, A CONSTRUCTOR INCLUDED — so the callee's bracket binds it on a constructor as it does on an operation. PROPOSED by the user 2026-10-09 while closing WI-20261008-HZVQA ("maybe we want to extend operations which accept V (types, defined in the enclosed sort), and not only operations, but constructors, migrate to operation type parameters. But this is an additional rule"). Not to be started without a design pass.

THE PROGRAM. Over `sort Box[V]` with `entity mk(v: V)` and `operation wrap(x: V) -> Self = mk(x)`:

  Box.wrap[V = Int64](5)      -- loads: the callee's bracket may name the sort's parameter
  Box[V = Int64].wrap(5)      -- loads
  Box[V = Int64].mk(5)        -- loads since HZVQA: a constructor reads its receiver
  Box.mk[V = Int64](5)        -- refused

TODAY (measured 2026-10-09). A callee's bracket key resolves among the operation's own parameters and its sort's (spec §5.4, "What a key may name"), for an operation. A constructor has no type-parameter list, so the bracket on it is a load error: "call-site type arguments `Box.mk[…](…)` are not supported here … an entity-constructor call … have no channel for it". The receiver's bracket and an alias bind the sort's parameter for a constructor (HZVQA), so two of the three spellings work for it and one does not.

THE PROPOSAL. A member whose signature uses a parameter of its enclosing sort — an operation's parameter or return, a constructor's field — has that parameter as a type parameter of its own. The callee's bracket on a constructor then binds by the operation rule and needs no rule of its own, and the receiver's bracket, an alias and the callee's bracket are three spellings of one binding for every member.

TO DECIDE WITH THE USER BEFORE IMPLEMENTING. (1) Whether only the parameters a member's signature uses migrate, or all of the sort's: today `Cell.empty[V = Int64]()` over `empty() -> Cell` binds a `V` the signature does not use, and loads. (2) What a positional bracket counts: today it counts the parameters the operation writes in its own bracket, so `Cell.empty[Int64]()` is refused and `Cell.pick[String](1, "s")` over `pick[W](x: V, y: W)` binds `W`. (3) Whether a member's own parameter and its sort's may share a name once both are the member's; today the collision is refused at the declaration. (4) How it meets WI-20261004-KEGNC's question (2), an operation's own parameter a call leaves unfixed: `Opt[T = Int64].make()` over `make[A]() -> Opt[T = A]` is refused for `A` today, in every spelling.

ACCEPTANCE. `Box.mk[V = Int64](5)` is a `Box[V = Int64]`; `Box.mk[V = Int64]("s")` is refused at `mk.v`, as `Box[V = Int64].mk("s")` is; the three spellings give one verdict at one site, for an operation and for a constructor; no program that loads before is refused after. Full workspace green via `rustland/scripts/test.sh`; scaland parity stated.

## Changes

### 2026-10-09T06:58:30Z — feedback — claude

PROMOTED TO OPEN 2026-10-09 on the user's word, the same day it was filed PreOpened: "Type parameter migration - it's relative small change, let make it open". The four points under TO DECIDE stand.

### 2026-10-10T16:43:29Z — feedback — claude

DELIVERED 2026-10-10. THE RULE AS BUILT. The bracket written on a constructor binds the parameters of its sort, through the reader an operation's bracket goes through. Over `sort Box[V]` with `entity mk(v: V)` and `entity hole`: `Box.mk[V = Int64](5)`, `mk[V = Int64](5)` and `Box.hole[V = Int64]()` are constructions at `Box[V = Int64]`; `Box.mk[V = Int64]("s")` is refused at `mk.v (entity-field): expected Int64, got String`, as `Box[V = Int64].mk("s")` and `CA.mk("s")` are. A receiver and the bracket binding one parameter differently are the two-bracket contradiction, in its words. A slot the sort names is bound and validated as on an operation; a spec's short name is no key of a constructor. In a rule body or a fact the applied bracket is refused as before. No operation's parameter list changed: a constructor's list is its sort's, which the spec already said of the constructor's type.

DECIDED WITH THE USER 2026-10-10 (the implemented reading was put to them and accepted, "Ok"). The four points: (1) every parameter of the sort, not only those a signature uses — `Pair.left[R = String](5)` over `left(l: L)` is a `Pair[L = Int64, R = String]`; (2) a positional on a constructor takes the sort's next parameter no key took, as in the type `Box.mk[Int64]`, and an operation's positional is unchanged (`Box.wrap[Int64](5)` stays refused); (3) the name collision is unchanged; (4) a parameter a call leaves unfixed is unchanged. And a bracket with no argument list, `Opt.non[T = Int64]`, is a load error advising `Opt.non[T = Int64]()`: its entries reach the loader as values, where a type parameter of the enclosing operation is a name and not the parameter.

AGAINST "NO PROGRAM THAT LOADS BEFORE IS REFUSED AFTER", two kinds that loaded are refused. The bracket with no argument list in a value definition, which loaded with the bracket read as the constructor's fields (`Box.mk[Zork = Int64]` loaded, `Box.mk[Int64]` was a box holding the type). And a positional that lands on a parameter a requirement names is held to the key's checks, on an operation as on a constructor: `pick[String, ConcOrd](…)` over `pick[T, O](…) requires O: WeakOrd[T]` is refused as `pick[T = String, O = ConcOrd](…)` is.

FOUND WHILE PROBING AND FIXED WITH IT (user, 2026-10-10: "let fix", "It was about found while probing not in change", and "Ok" to the fourth). (a) A parametric variant is its sort at the same arguments, in the subtype relation, the branch join, the variance read, the receiver's carrier, the provision match and the reading of a requirement's other elements. Before: `pass(x: Option.some[T = Int64]) -> Int64 = unwrap(x)` refused `expected Option[T = Int64], got some[T = Int64]`; `Box.unbox(x)` at `x: Box.mk[V = Int64]` refused "no impl provides Box"; `Desc.describe(x)` at `x: Both.one[V = Int64]` refused "`Both.one` provides no `Desc`"; `some[T = cat]` was no `some[T = Animal]`. (b) An argument's hint reads what the call's own bracket and receiver bind: `Hold.keep[V = (x: Int64) -> Int64](inc)` lifts `inc`, in every spelling, on an operation and on a constructor; `Box[V = Colour.red].mk(red(v: 1))` was refused "expected red, got Colour". (c) A constructor's type standing as an entry of a type value's bracket is a type value: `kind(Box[V = Pair.left[R = String]])` loaded and failed at run, `UnknownOperation`.

WHERE. `Expr::Constructor` has a `type_args` slot, carried at every rebuild site. The loader's `ApplyOrConstructor` frame reads it for an entity outside a rule's compound expression, refuses the bracket without arguments (`refuse_bracketed_constructor`) and classifies a bracket's entries (`bracket_entries`). `seed_constructor_type_args` and `seed_op_type_args` share `seed_bracket_bindings` (typing/slots.rs); `check_constructor_iter` holds a literal's constructor to it. The variant readings go through `KnowledgeBase::type_arg_owner`: `variant_at_its_sort`, `declared_variance` (typing/subtype.rs), `concrete_receiver_carrier`, `bind_clause_params_at_carrier` (typing/carrier.rs), `match_candidate_against_goal` (typing/candidates.rs). The hints: `call_site_bindings_for_hint`, `constructor_instance_for_hint`.

TWO WRONG TURNS, kept because each looked right in my first probes. Reading the coarse head of a per-call value at its sort in `dispatch_values_match` turned `TypeExtractor.EffectsRows` into `TypeExtractor`, and rows stopped matching rows — the standard library's own provisions failed on every load. Naming the sort for the constructor in `goal_carrier_sort` switched the refusal off: `x: Only.wrap[V = String]` with a provision only at `Only.wrap[V = Int64]` loaded. Both backed out; the second is a row.

UNCHANGED, each measured. A bracketed constructor in a clause's term position is unchecked: `fact holds(Box.mk[Zork = Int64])` and `rule r(?v) :- ?v <=> Box.mk[Zork = Int64]` load, plain and under an `if` — the user asked whether that is an error and was told it is not one today; no decision to change it. `x: Only[V = Int64]` with a provision only at `Only.wrap[V = Int64]` loads, as before. The paren-less dotted `Colour.red` is WI-20261008-R653S's.

CONTROLS. `wi_b6qya_constructor_bracket_test` (15 rows), `wi_b6qya_variant_at_its_sort_test` (6), `wi_b6qya_bracket_hints_test` (3); each header lists, per piece backed out, the rows that fail and the row that passes under every back-out. Changed row elsewhere: `wi839_call_bracket_channel_test::a_bracket_on_an_entity_constructor_call_is_read` (still refused, now for its unknown key).

REVIEW. `/code-review` at xhigh on the constructor-bracket change: three defects of the change, fixed with rows (a bracketed variant inside a type value was refused; a bracket on a literal's constructor was dropped; a positional on a named slot skipped the witness checks). The later fixes were reviewed by me and not by a second run of the skill.

GATE, on 75b7f5c4 with this change. `rustland/scripts/test.sh`, full: 36 binaries, 9062 passed, 0 failed, 14 ignored. `sbt -batch testFull`: 634 passed. `ANTHILL_TEST_NODE_CARRIER=1` over the bracket, variant and alias rows: 273 passed. scaland has no typer; its parser attaches the bracket and its loader reads it on no callee, an operation's included, so nothing mirrors this and no scaland file changed. Spec: §5.4 and §8.2.

