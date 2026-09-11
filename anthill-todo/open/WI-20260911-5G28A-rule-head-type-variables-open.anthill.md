## Attributes

- id: WI-20260911-5G28A-rule-head-type-variables-open
- created: 2026-09-11T12:28:49Z

- status: Open
- status_agent: claude
- status_at: 2026-09-11T12:28:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

RULE HEAD TYPE VARIABLES: open them per CITATION at the typer, read them off the VALUE at the
resolver, and mint them for UNWRITTEN parameters — so a rule can be read from an operation body
with the body's own (rigid) arguments and answer a typed result.

THE DRIVING CASE (user, 2026-09-11): `operation op(x: List, y: List)` reads `my_rule(x)` where
the rule ties a result column's element to `x`'s. Inside `op` the argument's type is the rigid
projection `List[T = x.T]` (kernel-language.md §8.1, WI-1059). MEASURED 2026-09-11 on a CLI
rebuilt from 1eb89144, body `my_rule(x).head.res`, return-type verdicts; the full table with
every spelling is on WI-20260910-6ARRN's feedback of 2026-09-11T12:20.

  head spelling                                  x: List[Int64] -> List[Int64]   -> List[String]   x: List, y: List -> List[T = x.T]   -> List[T = y.T]
  `x: List[T = ?t], res: List[T = ?t]`           refused                         refused           refused                              refused
                                                  "argument binding column `x` has an incompatible type", concrete and rigid alike
  `my_rule[T](x: List[T = T], res: List[T = T])` LOAD ERROR "WI-582: rule type-variable `T` has no bounding guard"
  `res: List[T = x.T]` (projection)              LOAD ERROR "unresolved name 'x.T'"; the citation still types `res` as the RULE's `x.T`
  `x: List[Int64], res: List[Int64]` (control)   accepted                        refused           refused at the citation: a rigid is not Int64 — correct

  RESOLVER, head spelling 1 queried directly: `my_rule([1, 2], ?r)` answers `?r = [1, 2]`
  CONDITIONAL with residual `domain([1, 2], List(T: ?t))` twice — the variable is opened per
  resolution but nothing reads it off the value, so the bound parks instead of deciding.

THE THREE GAPS, each at a named site (verify at the site before building — these were read
and driven, not fixed):
  (1) TYPER, the applied-citation checker (WI-714). `relation_clause_columns` (typing.rs ~9221)
      takes a typed head's bound VERBATIM from `rule_type_bounds`, so a `?t` inside `List[T =
      ?t]` reaches the checker (~7905) as the rule's own variable, which `types_compatible`
      cannot bind. The checker opens and correlates only a column whose WHOLE type is a
      variable (`resolved_var` → `bind_resolved`, the `rel(5, "s")` case, and the fresh var an
      untyped column gets). Nothing opens a head's type variables per citation.
  (2) RESOLVER, the typed-head domain goal. The goal carries the head's type variable as an
      OUTPUT to be guessed, so with the value bound and the type free it delays (residual
      above); with fresh variables it enumerates every derived domain instead (WT8WG item 7:
      `nest(?w: List[T = List])` 20 rows / 1 definite; WI-743's `bound_names_a_determinate_type`
      gate skips the goal silently for exactly this reason, typing.rs ~70379). The type is
      functionally determined by the value (`value_type_term`, WI-578, which `domain_leaf`
      already reaches through `type_bound_verdict_view`) — read it, (in, out) mode, instead of
      opening one choice point per derived domain (WT8WG item 8).
  (3) LOADER, the implicit introducer. An UNWRITTEN parameter of a parameterised sort in a rule
      head bound (`?x: List`, and `List` nested inside `List[T = List]`) should become a
      rule-scoped type variable per occurrence — WI-582's `[T]` introducer without writing it,
      RECURSIVE at every depth, opened fresh per resolution like every de Bruijn variable — the
      rule twin of §8.1's expansion. The self-reference stays its own rule keyed by declaration
      context (`repair_self_reference`: a bare `List` inside `List`'s OWN definition is the same
      element type, the recursion closes — type-parameter-scoping.md §3's twin).
  ONE PRINCIPLE, to record once in kernel-language.md §8.1 beside WI-1059 (RS2G4 plan §0): a
  sort parameter inside a member is a projection off the receiver's instance — an OPERATION
  reads it (Γ, input only; `x.T` and `y.T` are two projections), a RULE unifies it (σ, both
  directions). RS2G4 delivers the operation half; this ticket the rule half.

WHY THE VARIABLE SPELLING AND NOT THE PROJECTION: with (1) in place a concrete argument pins
`?t := Int64` and `res` resolves; a RIGID argument pins `?t := op.x.T` and `res` comes back
`List[T = op.x.T]`, so `-> List[T = x.T]` is accepted and `-> List[T = y.T]` refused by ordinary
σ-equality of one neutral. No receiver re-keying (path-dependent-types.md §4.1's deferred ζ
step) is needed, because the tie is a variable, not a path; in a rule `x.T` IS `?t`. A
projection in a rule-head bound is therefore OUT OF SCOPE here, and its load error stays.

ONE SMALL DECISION, to settle in the delivery note: the `[T]` head introducer today REQUIRES a
`:- Spec[T]` bound (WI-582). Either an unbounded introducer becomes the plain tie (spelling 2 =
spelling 1), or its message names the `?t` spelling as the repair. Decide by what WI-582's
bound is FOR (the guard grounds a requirement, proposal 060); do not widen it silently.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row DRIVES the capability):
  * spelling 1 × the four columns above reads accept / refuse / accept / refuse, and the
    accepted rigid row EVALUATES: `op4([a, b], [1])` with `op4(x: List, y: List) -> List[T =
    x.T] = my_rule(x).head.res` answers `[a, b]` by value.
  * `my_rule([1, 2], ?r)` answers DEFINITE, residual empty, with the domain goal PRESENT (assert
    the goal is generated — the WI-743 gate no longer skips a `?t` bound); `my_rule([1, 2],
    ["a"])` answers nothing.
  * nested: `rule nest(?w: List[T = List]) :- ?w <=> [[a()]]` answers 1 row, definite, with its
    domain goal PRESENT (today 1 all / 1 definite because the goal is skipped; 20 all / 1
    definite under fresh variables without (2) — WT8WG item 7's table); `anylist(?w: List) :-
    true` over a Letter-bearing KB (today 1 all / 0 definite) enumerates definite rows without
    an undecided tail up to the cap.
  * the (in, out) read is the control for (2): with it backed out and (3) in, the `nest` row
    reddens to 20 all / 1 definite — say so at the site.
  * CONTROLS, pass either way BY DESIGN: the exact-typed control row (accept / refuse / refuse);
    `wi714_applied_correlated_columns_reject_contradiction` and
    `wi714_applied_unconstrained_column_accepts_and_narrows` (whole-variable columns, already
    correlated); `wi743_finite_domain_test` keeps its counts; the projection-spelling load error
    is unchanged.
  * CENSUS the typed heads in the corpus (stdlib, examples, anthill-todo, the test fixtures)
    whose bound names a parameterised sort bare or carries a `?var`: today their domain goal is
    skipped; after (3) it is generated. Report how many, and which change their answer count.
  * scaland: check whether it has a typed-head twin (WI-582/WI-743 machinery) before claiming
    Rust-only; the acceptance field is set for both until that is answered.

REFERENCES: WI-20260910-6ARRN (the framing and the measured table; it keeps its own goal — the
reflect model following the typer), WI-20260911-RS2G4 (the operation half; plan §0 and §5),
WI-20260911-WT8WG items 6–8 (the resolver measurements), WI-743 (the gate and the derived
clauses), WI-714 (the applied citation), WI-582 (the introducer), proposal 060 (its §"domain"
clause already writes a shared head variable `List[T = ?T]`).

