## Attributes

- id: WI-20260904-02ERR-typechild-gains-a-var-carrier
- created: 2026-09-04T15:07:27Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T15:07:27Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260904-DTY3B-why-typechild-accept

## Description

A transient inference variable is interned. `TypeChild::Interned` holds a `TermId`, so
`type_check_node`'s rung 3 must launder a fresh `VarId` through the term store
(`Value::term(type_param_var_term(kb, Var::Global(vid)))`), leaving a refcounted
`Term::Var` nothing releases — against CLAUDE.md's rule that transient terms are not
interned. Background and both sides of the question: WI-20260904-DTY3B (the slot) and
WI-20260904-RB0Z5 (the value).

THE FIRST SHAPE PROPOSED WAS A THIRD `TypeChild` ARM, and it COLLIDES WITH A DOCUMENTED
INVARIANT — recorded before anyone builds it. `typing.rs`'s row-IR argument states, in one
breath and across four sites:

    the row builders (`make_effects_rows_type`, ...) all return `TermId`; the occurrence
    builders (`make_..._occ`) all return `Rc<NodeOccurrence>`. THERE IS NO THIRD: a row is
    minted as a term or as an occurrence

  ...plus the loader's `type_expr_to_value` being total over `TypeChild`, a LIVE
  `unreachable!("a param type is Term or Node")` in the `OperationInfo` emission, and
  `value_to_type_child` as the narrowing direction. That is an argued invariant, not an
  omission, so a third arm is not a small correction and must re-argue it.

THE BETTER SHAPE, AND IT RESPECTS THE INVARIANT. The `Node` carrier ALREADY MEANS
"identity-bearing, per-site, not shareable" — which is exactly what a fresh inference
variable is. So mint it as `TypeChild::Node`, not as a third `TypeChild` arm:
`value_to_type_child` maps `Value::Var(v)` to an occurrence instead of `debug_assert!`-ing
it a typer bug, and "a type is minted as a term or as an occurrence" still holds.

  WHAT THAT COSTS INSTEAD, AND IT IS NOT FREE EITHER: `TypeNode` has no `Var` variant
  (Denoted / Parameterized / EffectsRows / Arrow / NamedTuple / ExprCarried / PolyType),
  and its MEMBERSHIP RULE is why — "one arm per form that can sit on a `denoted` spine".
  A form earns an arm iff it can TRANSITIVELY CONTAIN a `denoted`. `sort_ref`, `nothing`
  and `type_var` are LEAVES, so no `denoted` can ever be beneath them; that is also the
  answer to "why is a `Ref` not a `Node`" — not a preference for interning, but that it
  can never NEED the other carrier.

  SO BOTH SHAPES RE-ARGUE AN INVARIANT, symmetrically, and neither is the free one this
  ticket first implied:

      TypeChild::Var   breaks "there is NO THIRD: a type is minted as a term or an
                       occurrence" (argued across 4 sites, one a live `unreachable!`)
      TypeNode::Var    breaks "one arm per form that can sit on a `denoted` spine" — a
                       VARIABLE IS A LEAF, so under the rule as written it has no arm

  `TypeNode`'s is the more defensible to EXTEND — provenance (identity + span) is a
  genuine SECOND reason to want an occurrence, and extending it does not change the
  carrier count — but it is an extension of a stated rule, not a gap in it. The rule and
  this consequence are now written AT the enum, so whoever builds either shape meets it
  before choosing.

THREADING THE OCCURRENCE IS THE THIRD REASON, and it is the one that shows up for users.
`Rc<NodeOccurrence>` carries SPAN and OWNER, so a transient type variable minted as a
`Node` knows WHICH BINDER PRODUCED IT. Rung 3 already holds that context — `occ.span` /
`occ.owner` on the lambda occurrence, the same pair `make_poly_type_occ` and
`make_named_tuple_occ` take today.

  WHAT IT BUYS, CONCRETELY: "type mismatch in make.return (op-return): expected String, got
  ??param" names a variable with NO LOCATION. In a file with several un-annotated lambdas
  the reader cannot tell which binder it is. With the occurrence threaded the variable can
  point at the binder that minted it. (Whether the current renderer READS a type value's
  span is a separate check — the carrier makes it possible, it does not make it happen.)

So the `Node` shape wins on three counts, not one: it RESPECTS the two-carrier invariant
instead of re-arguing it, it stops interning a term shareable with nothing, and it gives
the variable a provenance the `TermId` spelling throws away. A third `TypeChild` arm buys
only the second.

THE VIEW LAYER NEEDS NOTHING — the strongest evidence for the `Node` shape. `TermView` is
implemented for `Rc<NodeOccurrence>` (term_view.rs:2950), and `ViewHead` ALREADY HAS a
`Var(Var)` variant: "Logic variable of any kind — flex `Global`, `Rigid` skolem, or bound
`DeBruijn` (mirroring `Term::Var(Var)` / `Value::Var(Var)`)". So `type_node_head` returns
`ViewHead::Var(Var::Global(vid))` for the new variant and EVERY `TermView`-generic relation
already handles it, because a `Term::Var` produces that same head today. Only the CARRIER
is new; the consumers are already written for the head.

  SIZE, MEASURED: 170 `TypeNode::` references across 13 files, and ZERO adjacent `_ =>`
  arms — every match is exhaustive, so `cargo check` ENUMERATES the work and there is no
  silent-skip surface. That is the opposite of the risk profile a new variant usually has.

  THE HAZARD THAT COMES WITH IT, from the same `ViewHead::Var` doc: the DISCRIMINATION TREE
  reads the kind off that head and treats a flex `Global` as a WILDCARD EDGE matching any
  subterm. WI-20260904-50B2K listed this hazard for the interned spelling and never
  demonstrated it either way; it applies to this carrier too and is still owed a
  measurement. Do that BEFORE the 170 sites, not after — it is the one thing that could
  make the whole shape wrong.

THE POPULATION IS SMALL, AND NOT WHERE THIS TICKET FIRST SAID. "~110 `TypeChild` match
sites and their `_ =>` arms" was the wrong census: a match on `TypeChild` is EXHAUSTIVENESS-
CHECKED, so a new variant is caught by the compiler at every one of them, for free. The
places the compiler CANNOT help are exactly the stretch where the two-variant type is
laundered through the many-variant `Value` — which is also why the "invariant" reads as
four sites when it is ONE ENUM plus three restatements of what the enum already guarantees
(the `unreachable!`'s own comment says so: "`type_expr_to_value` yields only `Value::Term`
/ `Value::Node` (TypeChild has two variants)").

AND THE "INVARIANT" IS AN ARTIFACT — there is no rule being maintained. `type_expr_to_value`
is a PURE WIDENER; its whole body is

    match self.type_expr_to_child(ty, span, owner) {
        TypeChild::Interned(t) => Value::term(t),
        TypeChild::Node(n)     => Value::Node(n),
    }

and its own doc calls it "a thin wrapper over `Self::type_expr_to_child`". Nothing else
happens. So the guarantee is not being PRESERVED at four sites; it is DISCARDED at one and
re-asserted in prose at three.

THE OWNER IS THE STORED FIELD TYPE, not the wrapper: `OperationInfo.params` is
`Vec<(Symbol, Value)>` (op_info.rs:39, :102). The adapter exists because that field is
wider than its range. Typing those slots `TypeChild` would carry the guarantee and delete
the `unreachable!` — but the typer works over `Value` throughout (`TermView` is
carrier-agnostic), so every READ would convert. That is a tradeoff to weigh with a
measurement, not a cleanup to assume; it is recorded here because it is the same question
this ticket asks (which carrier, and who is allowed to forget it) one level up.

    NARROWING IN   10 call sites, ALL THROUGH ONE FUNCTION — `value_to_type_child`.
                   One edit covers all ten.
    WIDENING OUT   12 call sites of `type_expr_to_value`. THIS IS THE CENSUS. Exactly one
                   of them re-asserts the lost guarantee by hand today, as
                   `unreachable!("a param type is Term or Node")` (`load.rs:29304`) — so
                   that one is known, and the other eleven have not been read.

Read those twelve before estimating. The narrowing is already centralized, which is what
makes either shape cheaper than it looks.

AND IT FINISHES A HALF-LANDED RULE rather than adding a feature. WI-1079 made a bare
logical variable a legitimate TYPE at the reading end (`type_head`'s arm, and the
`FlexVar` / `Skolem` reflect forms `extract` had been reporting as `Error`) and never gave
the BUILDING path the matching arm — which is why `value_to_type_child` still calls a
`Var` in a type slot "a typer bug" while `type_head` two thousand lines away calls it
"perfectly well-formed". Read WI-1079 first, and check whether other builders were left
behind by the same half-landing: `value_to_type_child` was found by driving ONE mint, so
it is a lower bound on that population, not a census.

THE CONTAINER CASE FALLS OUT EITHER WAY. Every container's lowering already asks "is any
child NOT interned?" (spelled `any` / `any_node` because `Node` was the only non-interned
answer). Under either shape a variable child makes its container non-interned by the SAME
rule a `denoted` child does, so `(a: ?T, b: Int64)` — today interned variables and all, and
shareable with nothing since `?T` is unique per site — stops being interned with nobody
writing a special case.
