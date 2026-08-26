## Attributes

- id: WI-20260825-P9Y67-and-are-capturable-by-a-same
- created: 2026-08-25T14:54:29Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-26T16:59:26Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`|`, `&` AND `!` ARE CAPTURABLE BY A SAME-NAMED DECLARATION, and in GOAL position the capture changes what a rule MEANS. Split out of WI-20260824-VT8CF, which now owns the numeric half (`/`, `%`, `^`) alone. Same root — a minted operator resolves its bare functor down the ordinary name ladder, and the implicit tier is the lowest rung — but a different fix, because unlike `div`/`mod` these have NO parametric spec to move to.

THE GAP, DRIVEN. All rows measured on the built tree at b885f8a1 through an OPERATION BODY (`anthill run`) or a RULE BODY (`anthill query`), never through `eq` — each arm differs from its control in the local declaration alone.

VALUE POSITION — `let b = <expr>` then `if b then 1 else 0`, printed:

  expr             control   with a namespace-level declaration
  `false & false`     0      1   `operation and(a: Bool, b: Bool) -> Bool = true`
  `true | true`       1      0   `operation or(a: Bool, b: Bool) -> Bool = false`
  `!true`             0      1   `operation not(a: Bool) -> Bool = true`

Every row inverts. Loads clean, exit 0, no diagnostic.

GOAL POSITION — `fact p(1)` and `rule q(?x) :- p(?x) | p(99)`, queried as `q(?x)`:

  control                                    ?x = 1                     1 solution
  with `operation or(a: Bool, b: Bool) -> Bool = false`
                                             ?x = ?_                    1 conditional
                                             residual: eq(or(p(?_), p(99)), true)

THIS ONE IS WORSE THAN A WRONG NUMBER. The disjunction stops being a disjunction: the goal is re-read as a boolean VALUE expression, `?x` never binds, and a definite answer becomes a floundered conditional. A free-standing `operation or` therefore silently changes the LOGIC of every rule in reach, not just the result of a call.

WHY NO EXISTING GUARD REACHES THEM. Two treatments exist and both decline these by design:
  - WI-BFB9A's `check_rival_spec_operations` refuses a free-standing rival only of a spec operation on a PARAMETRIC carrier (`typing::spec_op_parent_sort`). `anthill.prelude.Bool.and` sits on `Bool`, which declares no `sort T = ?`; `anthill.kernel.or` / `anthill.kernel.not` sit on no carrier at all. So `spec_op_parent_sort` answers `None`, there is no `provides` to prescribe, and the refusal correctly stands down. kernel-language.md §5.1 lists exactly these names as the exemption.
  - `minted_connective_symbol` bypasses the ladder only for the carrier-agnostic connectives `<=>` / `===` (WI-888's line, which deliberately excludes `eq`).

WHAT THE TARGETS ACTUALLY ARE, so a fix does not restate them wrongly. `|` / word-`or` mints the functor `or`, resolved by the implicit tier to `anthill.kernel.or`, and is POSITION-DIRECTED: the kernel primitive in a goal position, `Bool.or` as a value expression in an operation body. `!` / word-`not` mints `not` → `anthill.kernel.not`, position-directed the same way. `&` / word-`and` mints `and` → `anthill.prelude.Bool.and` and is VALUE-ONLY: there is no `anthill.kernel.and` because conjunction is the comma, so it resolves to the dispatched Bool op in every position. All three are `PRELUDE_QUALIFIED` entries (kb/load.rs) — `anthill.prelude.Bool.and` INCLUDED, which is the sole reason `&` was ever reclaimable.

WHAT A REAL FIX HAS TO DECIDE. There is no `Numeric`-shaped move available: `and`/`or`/`not` are not carrier-polymorphic operations that happen to sit on the wrong sort, they ARE the boolean connectives. Candidates, none costed:
  (a) a parametric spec owning them — `BooleanAlgebra` / `Heyting`, with `Bool` providing it — which would put them inside `check_rival_spec_operations` by construction, the same route the numeric half takes. Needs a census of what ELSE would provide it and how it relates to the existing `Lattice` / `BoundedLattice` (which already own `lub`/`glb`/`top`/`bottom` on a parametric carrier and are the nearest thing in the prelude). It also has to answer what happens to the POSITION-DIRECTION: a goal-position `|` must stay `anthill.kernel.or`, so the spec would cover the value reading only.
  (b) extend `minted_connective_symbol` so `|` / `&` / `!` bypass the ladder as `<=>` does. THIS WAS ATTEMPTED AND WITHDRAWN — it shipped inside WI-20260824-BFB9A as `reclaim_minted_operator`, was scope creep on that ticket's ask, and its query-path half carried a live defect: a `goal_position_boolean(resolved, pos_args.len())` added to `convert_query_term_expecting`'s `Term::Fn` arm, which recurses into positional AND named args through itself, so it routed at every depth and on WRITTEN calls. MEASURED: a fact holding `or(true, false)` became unqueryable by ANY spelling, exit 0, no diagnostic. A retry must not route there.
  (c) refuse a free-standing declaration of any name pratt mints an operator to, independently of whether the target dispatches — a rule about OPERATOR SPELLINGS rather than about spec ops, needing its own census of what it would break. This covers both halves at once and is the only candidate that does.
  (d) accept the gap and document it at the operator table (kernel-language.md §6.6) with this ticket's number.

NOT DRIVEN: (a), (b), (c) and (d) are code reads. The six rows above ARE driven.

CONTROL, when it is fixed: the six rows above. Each inverts, and the inversion is the measurement — the value rows through an operation body, the goal row through a rule body. Do NOT restate them as `:- eq(...)`: `eq` never binds, the goal suspends, and such a row answers 0 definite solutions with or without the shadow, so it measures nothing.

ACCEPTANCE: a minted `|` / `&` / `!` means the connective whatever the enclosing namespace declares — in BOTH goal and value position — or the divergence is documented at the operator table with this ticket's number. Full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-08-26T15:49:14Z — feedback — claude

DELIVERED, BY A ROUTE THE TICKET LISTED AS NEITHER (a) NOR (b) — and the ticket's own analysis is what ruled the listed ones out.

WHAT LANDED. `|` / `&` / `!` carry an ABSOLUTE ADDRESS, exactly as WI-20260825-KD9SW's twelve do, and the address is the KERNEL CONNECTIVE: `..anthill.kernel.or` / `.and` / `.not` (`parse::pratt::CONNECTIVE_FUNCTORS`, kept a separate list from `SPEC_OP_FUNCTORS` because those are spec ops that dispatch and these are primitives that never do). `..` is unspellable by any identifier, so the capture is UNREPRESENTABLE rather than refused.

WHY NO LIBRARY MOVE HAD TO LAND FIRST, which is where the ticket's candidate (a) goes wrong. The body reasoned that a fix needed "a parametric spec owning them — BooleanAlgebra / Heyting" so they would fall inside `check_rival_spec_operations` by construction, plus a census of `Lattice` / `BoundedLattice`. That inherits an ordering from `+` that does not apply: `+` needed WI-20260825-1WBZT to split `Numeric` because THE ADDRESS NAMES WHERE THE OPERATION IS DECLARED and `Numeric.add` was a bundle no `Money` could claim honestly. These three already have exactly one honest declaration each — the resolver primitive. `|` IS disjunction, and disjunction is `push_choice`. There is no spec to split and none to invent. The `Lattice` census the body called for is not deferred; it is NOT NEEDED for this, and only becomes a question if someone later wants `|` to be carrier-polymorphic, which is a different ticket with its own cost (a goal-position `|` would still be `kernel.or` for every carrier, since a goal operand is a goal and there is nothing to dispatch on).

WHY IT IS NOT CANDIDATE (b) EITHER, though it looks adjacent. (b) was "extend `minted_connective_symbol` so the three bypass the ladder", and its withdrawn attempt (`reclaim_minted_operator`, scope creep on WI-20260824-BFB9A) added a `goal_position_boolean` call to `convert_query_term_expecting`'s `Term::Fn` arm, which recurses into positional AND named args through itself — so it routed at every depth and on WRITTEN calls, and a fact holding `or(true, false)` became unqueryable by any spelling, exit 0, no diagnostic. THIS CHANGE ADDS NO ROUTING ANYWHERE. Position-direction already runs on the RESOLVED symbol, downstream of the ladder: `Loader::redirect_op_body_boolean` maps `kernel.X` to `Bool.X` whenever `in_op_body_value`, so an addressed mint reaches the value op exactly as a tier-resolved short name did, and `route_body_goal_boolean` is simply a no-op on a functor already at the goal spelling. A written `or` carries no `..`, so (b)'s failure mode is unreachable here.

THE SIX ROWS, RE-DRIVEN. Confirmed still live at HEAD (72750c01) before the change — all six inverted exactly as the body describes, including the goal row's `?x = ?_` with residual `eq(or(p(?_), p(99)), true)`. After: every arm equals its control. Pinned in `wi_p9y67_connective_address_test.rs`, whose back-out (mutate the three constants to the short spellings) fails three of its four rows; the fourth pins the pre-declaration below and passes either way.

A STALE CLAIM IN THIS TICKET'S OWN BODY, corrected rather than worked around: "`&` ... is VALUE-ONLY: there is no `anthill.kernel.and` because conjunction is the comma". WI-20260822-J38JE added `push_and` and the rule lift, and `POSITION_DIRECTED_BOOLEANS` has carried three rows since. All three operators are position-directed and symmetric, which is why one uniform treatment covers them.

A LIVE DEFECT FOUND IN PASSING, and it is the more interesting half. `kernel.anthill` declares `and` ONLY as a rule head, and a rule head does not register a qualified name — so `anthill.kernel.and` was absent from `by_qualified_name`, `goal_position_boolean`'s lookup answered `None`, and J38JE's `POSITION_DIRECTED_BOOLEANS` row for `and` HAS NEVER FIRED. The conjunction reading worked anyway, by a different mechanism: `goal_arg_slots` and `is_goal_conjunction` both match the resolved symbol's LOCAL NAME (`"and"`), which `anthill.prelude.Bool.and` also answers. So the capability was real and its stated guard was not the one supplying it. It surfaced the moment `&` began carrying an address — `..anthill.kernel.and` reached the typer verbatim as "unknown functor". Fixed by pre-declaring `and` beside its peer `or` in `register_stdlib_scopes`; `push_choice` / `push_and` never needed it because `register_builtin_tag` defines a missing name rather than skipping it. The instrument that NAMED it was `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load`, extended here to walk `CONNECTIVE_FUNCTORS`.

ONE OBSERVABLE CHANGE BEYOND THE SIX ROWS, from that pre-declaration: a goal-position `&` now genuinely routes to `kernel.and` where it used to stay at `Bool.and` and be handled by the local-name match. Same bag, different search ORDER — `p(?x) & r(?x)` over two facts answered `1, 2` and now answers `2, 1`. Driven both ways.

THE `PRELUDE_QUALIFIED` ENTRIES STAY, where the twelve lost theirs. The stdlib writes bare `not(...)` in rule bodies throughout, and retiring the tier for these three is a migration rather than a repair. So KD9SW's split holds here too: the OPERATOR is uncapturable, the WRITTEN name is an ordinary name that still resolves by scope — pinned by `a_written_bare_connective_still_resolves_by_scope`, which holds both spellings against ONE declaration.

### 2026-08-26T16:47:53Z — feedback — claude

ADDENDUM AFTER /code-review — ONE FINDING WAS A REAL REGRESSION THIS TICKET SHIPPED, and the repair changes where the value reading is supplied.

THE DEFECT. The first cut added a "value-position mirror" to `build_body_atom_occurrence`: at a rule body's non-goal, non-wrapper `Fn` node, redirect `kernel.X` to `Bool.X`, on the ground that §6.6 calls a goal's ARGUMENT a value expression. It reproduced WI-20260824-BFB9A's defect from the other side. Fact heads, rule heads and query patterns build through `convert_term` and are NOT redirected, so a rule body came to spell the same source text differently from the fact it must match. DRIVEN, with an entity control in the same file:

  fact wrap(boxed(v: 1))       rule viaEntity :- wrap(boxed(v: 1))        1 solution  (control, green both ways)
  fact holdsN(not(true))       rule viaNot    :- holdsN(not(true))        0 solutions
  fact holdsO(or(true,false))  rule viaOr     :- holdsO(or(true,false))   0 solutions

Exit 0, no diagnostic. A DATA SLOT HOLDS A TERM and a term's spelling is its identity; normalizing one side of a match is never a repair (WI-756). The argument was already written down one coordinate over, in `typing::goal_form_proposition`: "the `b` in a fact `eq(x, not(b))` is a boolean VALUE, and rewriting it to the NAF primitive would change what the fact says."

THE REPAIR. The mirror is gone and the loader leaves data slots alone. The position knowledge moved to a CONSUMER that knows what it is reading: `anthill-smt-gen`'s `translate_condition` is only ever called on a condition, so its `bool_connective` table now carries both spellings. That table's `Bool.*`-only coverage was never a decision — a rule body reached those rows only when the fixture had written `import anthill.prelude.Bool.{not}` and the import CAPTURED the operator, which is exactly what this ticket removes. `wi680_ite_lowering_test` (9 rows, two of them z3-driven) is what made it visible and is green. Pinned by `a_data_slot_keeps_its_spelling_so_a_body_matches_a_fact`, whose entity row is the control.

A SECOND CLAIM OF MINE WAS WRONG, and the user caught it. I wrote that anthill-core cannot drive a rule-body value position because "a rule body reduces a bodied operation and a resolver builtin and nothing else" (quoting kernel-language.md). Both the quote and my use of it are false. MEASURED:

  :- Bool.and(true, true)         1     a host-backed op DOES reduce at a GOAL
  :- Bool.and(true, false)        0
  :- bodied() = true              1     `reduce_operand` (WI-482/483) DOES run on a VALUE slot
  :- bodiedF() = true             0
  :- viaHost() = true             1     a bodied body calling a host op reduces
  :- Bool.and(true, true) = true  0     THE GATE

Two evaluators run. What is declined is a BODY-LESS operation, via `reduce_operand`'s `dispatch_body_less: false` — and deliberately: an operand is a term a RULE WROTE, and a body-less spec op there may be symbolic algebra rather than a computation (`Set.insert` / `Set.empty` are the named case; dispatching them would reduce data). `Bool.and`/`or`/`not` are body-less host-backed and land in that class. The user's direction for the gap: reduce when the arguments are ground and concrete, DELAY when unground or abstract — the residual discipline the goal side already follows — rather than declining by declaration shape. kernel-language.md §5.2 now states this with the six rows; the paragraph had attributed the gap to host-backing (WI-20260822-ZJZS7) and to `a & b` being refused (lifted by J38JE).

SCALAND WAS NOT PORTED IN THE FIRST CUT, and this ticket's acceptance names `scaland-sbt-test`. `Pratt.scala` still minted short `or`/`and`/`not` while rustland minted addresses — the exact divergence that file's own doc names as the thing addresses exist to prevent ("the same source would parse to `add(a, b)` here and to `..anthill.prelude.Additive.add(a, b)` there"). Ported; one expectation updated; scaland 518/518 green.

FOUR STALE DOCS CORRECTED, all traceable to WI-20260822-J38JE landing `kernel.and` while the prose that justified the OLD behaviour stayed put — which is the pattern worth naming, not the individual lines. `kb::mod::goal_slot_readings` said "`and` is deliberately ABSENT … WI-1046 refuses it" while its own arm reads `("or" | "and", 2)`; `typing::goal_form_proposition` ended "`and` has no goal reading at all"; `redirect_op_body_boolean` said "`and`/`neg` need no entry"; kernel-language.md §5.2 said `a & b` in a goal "stays refused". Also DELETED (user-authorized): `LoadError::BooleanOperatorInGoalPosition`, its two render arms and its message — rendered in two places, CONSTRUCTED nowhere since J38JE lifted the refusal, and its text still told users the evaluator "cannot yet reduce a host-backed operation".

FINAL STATE: rustland 5813 passed / 0 failed across 36 binaries; scaland 518/518. `/code-review` findings 1-5 all addressed.

