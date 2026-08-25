## Attributes

- id: WI-20260825-P9Y67-and-are-capturable-by-a-same
- created: 2026-08-25T14:54:29Z

- status: Open
- status_agent: claude
- status_at: 2026-08-25T14:54:29Z

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

