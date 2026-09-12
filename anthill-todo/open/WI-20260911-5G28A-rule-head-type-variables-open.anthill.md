## Attributes

- id: WI-20260911-5G28A-rule-head-type-variables-open
- created: 2026-09-11T12:28:49Z

- status: Open
- status_agent: claude
- status_at: 2026-09-12T05:44:34Z

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

## Changes

### 2026-09-11T21:27:45Z — feedback — claude

SCOPE ADDITION (claude, 2026-09-11, agreed with user): THE RECEIVER BRACKET ON A RULE CITATION,
the rule half of RS2G4 that RS2G4's delivery note already assigns here and that this ticket's
text does not yet contain. Every acceptance row above is driven by an ARGUMENT (`my_rule(x)`,
`my_rule([1, 2], ?r)`) or a VALUE (`nest`, `anylist`); WT8WG's parameterised value face is
driven by NEITHER — `List[T = Letter].domain.takeN(5)` is mode (out) with the type as its only
INPUT, supplied by the bracket. MEASURED 2026-09-11 (tree 5856c5cc): inside `sort Wrap[T]`, a
written `rule dom(?x: Wrap[T = T]) :- true` cited as `Wrap[T = Colour].dom.takeN(5)` and as bare
`Wrap.dom.takeN(5)` both LOAD CLEAN — the bracket is validated (WI-839) and dropped, the bound
is a type variable so WI-743's gate skips the member goal, and the citation can only flounder at
the drain. A silent acceptance, and this ticket is where it is closed.

THE DESIGN QUESTION IT CARRIES, to settle in the delivery note before code: a rule has no frame
channel — its head is its only interface — so an enclosing sort's parameter must travel as a
HIDDEN HEAD SLOT that a bracketed citation fills and an unbracketed one leaves free (opened
fresh per firing like every de Bruijn variable). That is WI-743's "the type travels as an
argument", one level up: the kernel's `domain_member(?x, List[T = ?T])` already IS that shape.
`build_relation_value` (eval) and `relation_reference_type` (typer) are the two sites; RS2G4's
`bind_or_refine_member_param` is the operation-side precedent for reading the bracket.

ROWS ADDED TO ACCEPTANCE: (a) `List[T = Letter].domain.takeN(5)` answers 5 definite rows once
WT8WG has derived the value face (until then, the written twin `Wrap[T = Colour].dom.takeN(5)`
= 3); (b) bare `List.domain` / `Wrap.dom` stays REFUSED at load — it names no element type, and
enumerating "lists of something" is the 20-row type enumeration WI-743 measured; (c) the
refusal WT8WG installs for a parameterised sort's value face is LIFTED here, and the lifting
row is the control: with this ticket backed out that row is a load error, not a wrong count.

WT8WG delivers its non-parameterised half first (map-colouring, alphabet-words' Letter,
tiny-sat, 34 of the 37 all-nullary corpus sorts) and refuses the parameterised citation
loudly; nothing it derives is rework for this ticket — the derived clause for a parameterised
sort is exactly what the hidden-slot answer here decides, so WT8WG derives none.

### 2026-09-12T05:43:54Z — feedback — claude

IMPLEMENTED: gaps (1), (2) and (3), plus a representation prerequisite the ticket's own text
denies. The receiver-bracket row (the 2026-09-11T21:27 scope addition) is NOT delivered; its
design is settled and recorded below, and WT8WG stays blocked on it.

THE TICKET'S TEXT WAS WRONG ABOUT ONE THING, and it decided the shape of the work. Gap (2)
says "the variable is opened per resolution but nothing reads it off the value". It is NOT
opened: measured on b43d9670, `rule my_rule(?x: List[T = ?t], ?res: List[T = ?t])` had
`globals = [x, res]`, while the twin `rule p(?x) :- q(?x, ?y)` — whose `?y` is BODY-ONLY —
had `[x, y]`. A body-local variable was already a frame slot; a BOUND-local one was not, and
was a `Var::Global` shared by every firing of the rule. Nothing had ever bound one, so the
difference was invisible. Gap (2) is exactly what makes it a leak, and the CONTROL is a
driven row, not an argument: with the frame admission backed out and everything else in,
`rule two(?a, ?b) :- my_rule([1, 2], ?a), my_rule(["s"], ?b)` answers NO SOLUTIONS — the
first call's `?t := Int64` refutes the second call's `List[T = String]`.

WHAT LANDED, per gap:

(1) TYPER — `relation_reference_type_applied`. A column whose type MENTIONS a variable is
    CORRELATED; before, only a column that WAS one counted (`resolved_var`), and the nested
    case fell to `types_compatible`, a SUBTYPE test that does not bind. It does not merely
    fail to pin: a raw `Var::Global` is `TypeHead::FlexVar`, which has no dispatch tag, so it
    is not even the `type_var` WILDCARD and the structural arms REFUSE — which is why all
    four driving rows read "argument binding column `x` has an incompatible type", the
    concrete and the rigid alike. Such a column now UNIFIES through the citation's shared σ,
    and `relation_clause_columns` opens the clause's bounds PER CITATION so the tie reaches
    both columns.

(2) RESOLVER — `pin_bound_from_value`, mode (in, out). The match is ONE-WAY and purpose-built
    (`pin_type_vars`), NOT `unify_types`: a source-written bound lowers `?e` as an `Expr::Var`
    occurrence, which `resolved_var` reads as no variable at all — measured, the first cut
    answered 0 rows for WT8WG's own `varBound` fixture, turning a withheld verdict into a
    refutation.

(3) LOADER — `expand_rule_head_bound_type_params`. It runs AFTER
    `derive_domain_member_clauses`, not at `load_rule`: it needs the PARAMETER LIST of the
    sort a bound names, and that sort may be declared in a later file. Measured at the head's
    own conversion site the table is still empty and the expansion silently did nothing —
    `?w: List` stayed `Ref(List)` right through. The variables it mints join the frame there,
    which is why `extend_rule_frame_with_bounds` PREPENDS: a De Bruijn index is
    `len - 1 - position`, so inserting at the front leaves every existing index untouched.

WI-743'S DETERMINACY GATE IS LIFTED, and its reason moved rather than vanished. Both of the
gate's reasons are now owned elsewhere — the bare reference is no longer a shape a bound can
have (3), and the variable is no longer guessed (2) — so the member goal IS generated for a
`?t` bound. Mode (out) over a type that is still free then delays at the dispatch site
(`domain_member_goal_is_undetermined`) instead of enumerating. That is strictly louder than
the gate: a skipped goal said nothing at load; a delayed one residualizes and is loud at the
drain on WI-737's route. The guard asks about the TYPE alone, in BOTH modes — an earlier cut
asked about the value too, and `rule memberVar(?x) :- ?x <=> [a()], domain_member(?x,
List[T = ?e])` dispatched anyway at 204 rows / 1 definite for a goal with one answer.

A SORT's TYPE PARAMETER IS NOT A CLAUSE VARIABLE (`is_canonical_type_param_var`), and the
suite is what said so. Admitting bound variables to the frame blindly turned
`wi_pw9a0_rule_tvar_in_bound_test::a_guard_whose_functor_is_a_type_parameter_lowers_as_that_
parameter` red: `F` in `rule keep[T](?x: T, ?y) <=> ?y :- F[T]`, written inside
`sort Lib { sort F = ? }`, is a projection off the RECEIVER's instance, and opening it fresh
per firing would decouple the bound from the receiver — a bound that accepts anything. It
keeps its pre-ticket representation; reaching it from a citation is the half below.

ONE TEST MOVED, DELIBERATELY, and it is the only behaviour change outside this ticket's own
rows. `wi_wt8wg_domain_value_face_test::a_written_bound_carrying_a_type_variable_suspends`
asserted (1 total, 0 definite) for `domain(?x, List[T = ?e])` with `?x` bound — a WITHHELD
verdict, which was the only honest answer while nothing could determine `?e`. This ticket
determines it, so the row is now 1 DEFINITE and renamed
`..._is_read_off_the_value`. WI-067 is intact: nothing decided the open variable, it was
instantiated from its only determiner. Its two controls (ground bound = 1 definite, wrong
bound = 0) are unchanged and are what make the middle number readable.

DECISION A — THE `[T]` INTRODUCER'S UNBOUNDED CASE: KEEP THE REFUSAL, NAME THE REPAIR.
Read at the site rather than argued from the name: `rule_head_bound_alias` substitutes an
introducer inside a bound by the SPEC SYMBOL its `:- Spec[T]` guard named, so
`rule g[A](?a: A) :- Eq[A]` installs the NOMINAL bound `?a: Eq` and the check asks "does this
value's type PROVIDE Eq". That is 060 §3's anchor — the guard grounds a requirement. This
ticket's `?t` is a different question: a tie with nothing required of it, an ordinary
unification variable. Merging them would give ONE spelling two readings decided by whether a
guard happens to be written elsewhere in the clause, and ADDING a `:- Spec[A]` guard to a
working rule would change what its bound MEANS rather than narrowing it. So the refusal
stands and its message now names the `?t` spelling beside the `:- Spec[T]` one.

DECISION B — THE RECEIVER BRACKET: A HIDDEN HEAD SLOT. Settled, NOT built. A rule has no
frame channel — its head is its only interface — and a citation's query is built from the
clause HEAD ALONE (`eval::build_relation_value`), so a bound's variable is unreachable from
the call site. The cheaper mechanism was measured and does not work: conjoining a guard at
the citation (`guarded(pattern_query(dom(?x)), domain_member(?x, Wrap[T = Colour]))`)
restricts the right values but cannot pin the CLAUSE's own `?t` — they are different
variables — so `<Sort>.domain`'s own member goal still has a free element type and deadlocks
against the mode-(out) delay; and conjoining the GENERATOR form would make a bracket on a
non-domain rule enumerate its argument instead of restricting its type. The answer is one
head argument per enclosing-sort type parameter, filled by a bracketed citation and left free
by an unbracketed one, SHARED with the bound so pinning the slot pins the bound, and HIDDEN
(excluded from `rule_head_var_slots`) so it is not a column. That is WI-743's "the type
travels as an argument" one level up; the kernel's `domain_member(?x, List[T = ?T])` already
is that shape. Its cost is a head-shape change, which reaches the discrimination index, the
goal spelling a rule body writes, `resolve_relation_arg_columns`, and the derived
`<Sort>.domain` emission — a second feature, not a finishing touch, which is why it is not in
this commit.

SCALAND: NO TWIN, and that is an answer rather than an assumption. `Loader.scala:2466` strips
the `typed_var` marker and DROPS the bound — "scaland has no typer to enforce the bound, so we
DROP the type and keep only the bare variable". There is no WI-582 bound install, no WI-742 /
WI-743 domain-goal machinery and no relation-citation typing to port to. `scaland-sbt-test`
stays a no-regression check.

CORPUS CENSUS (acceptance: "how many, and which change their answer count"). Scanned 1574
`.anthill` / `.anthill.md` under stdlib, examples, anthill-todo and rustland. The LIVE typed
heads are `colouring(wa: Colour, …)` (Colour takes no parameters), `model(vs: List[T = Bit])`
and alphabet-words' three `List[T = Letter]` heads — every one writes its parameters in full
or names a non-parameterised sort. The derived `<Sort>.domain` clauses carry `Ref(<Sort>)`
for a non-parameterised sort only. SO THE POPULATION IS EMPTY: the expansion is a no-op over
the whole corpus and so is the gate lift, and NO corpus answer count moves. Asserted rather
than grepped by `the_shipped_corpus_has_no_unwritten_parameter_in_a_rule_head_bound`, which
is also the tripwire for the other direction.

ACCEPTANCE, ROW BY ROW (18 driving rows in `wi_5g28a_rule_head_type_variables_test.rs`;
full workspace suite 6931 passed / 0 failed):

  * spelling 1 x the four columns — MET. accept / refuse / accept / refuse, and the refusals
    now land at the OP-RETURN with the pin visible in the message ("expected List[T = String],
    got List[T = Int64]"; "expected List[T = y.T], got List[T = x.T]") where before this
    ticket all four read the same column-bind error. The accepted rigid row EVALUATES:
    `op4([a(), b()], [1])` answers the FIRST list by value.
  * `my_rule([1, 2], ?r)` DEFINITE with an empty residual, `my_rule([1, 2], ["a"])` nothing,
    and the member goal PRESENT on the clause — MET, the last asserted by reading the clause's
    body nodes for the `domain_member` functor rather than inferred from a count.
  * `nest` 1 row definite with its domain goal present — MET.
  * the (in, out) read is the control for (2) — MET and STATED at the site.
  * CONTROLS — the exact-typed rows, wi714's two whole-variable rows, wi743's counts and the
    projection-spelling load error: all unchanged.
  * `anylist(?w: List)` "enumerates definite rows without an undecided tail up to the cap" —
    NOT MET AS WRITTEN, and the row is reported rather than quietly redefined. It now answers
    ONE conditional row whose residual carries the member goal, where before the goal was not
    generated at all. Enumerating instead was BUILT and MEASURED: with the mode-(out) guard
    removed the query DOES NOT RETURN — `domain_member(?h, ?t)` with both free is a product of
    two infinite streams, whose fairness is WI-20260911-09E6M's and not this ticket's. Shipping
    the hang to satisfy the sentence would have been worse than saying so; the test row asserts
    what is true (it comes back, no definite row, the goal in the residual) and its module
    header records that this axis's back-out is a HANG, not a red.
  * the receiver-bracket rows (a)/(b)/(c) from the 2026-09-11T21:27 scope addition — NOT MET.
    Design settled (above), not built; WT8WG stays blocked on it and its refusal stands.

/code-review high RAN AND ITS EIGHT FINDINGS ARE APPLIED, and three of them were real defects
this ticket would otherwise have shipped:

  * TWO NAF-DECISIONS OF AN OPEN VARIABLE, which is precisely what the pin's own doc promised
    not to do. The gate `type_mentions_flex_var` asked `is_type_variable` — all THREE variable
    spellings — while the pin could bind only a `FlexVar`, so a `Skolem` or a reflect `TypeVar`
    bound fell out of the structural walk as `Refuted` where it used to SUSPEND. And a SORT's
    canonical type-parameter variable is a plain `Var::Global`, so the pin would have bound the
    RECEIVER's parameter from one value — the very thing `is_canonical_type_param_var` was
    added to prevent on the frame side, unasked on the pin side. Both now go through one
    predicate, `bindable_type_var`, which answers the pin's own question.
  * SUBTYPING LOST. `pin_type_vars`' structural descent is exact head-and-arity equality, where
    `type_bound_verdict_view` used `types_compatible` — so a value whose type is a strict
    subtype, or `Nothing`, came back `Refuted`. It now falls back to `types_compatible` when
    the structural match fails, pinning nothing on that path. The same reader is now used at
    the citation, which had the identical narrowing through `unify_types`.
  * `Fn{S}` REWRITTEN TO `Ref(S)`. The expansion's nullary arm minted a bare `Ref` and recursed
    unconditionally, so a sort with NO parameters had its bound replaced — and the two spellings
    are one only for THIS question: `Fn{S}` is the concrete spec identity, `Ref(S)` the dispatch
    wildcard `impl_param_ref` matches on. A WI-582 spec bound silently became a wildcard.

The rest: a false sentence in the justification for deleting WI-743's gate (it claimed `anylist`
"now comes back as rows"; it comes back as one conditional row, and that is now what the comment
says), a `HashMap<String,_>` resolve ahead of the functor test on the resolver's hot path
(screened by short name now), an unconditional frame mint in `relation_clause_columns` before
the bounds were even read, and the cross-batch coupling in the expansion sweep — which is now a
LOUD load error rather than an argument that it cannot happen, with `open_debruijn_node`'s
splice asserting that every index it opened was in range.

AND THE FIX FOR ONE FINDING BROKE THREE ROWS, which is the measurement worth keeping: routing the
citation through `pin_type_vars` felled both RIGID rows, because that walk matched named
parameters by `Symbol` IDENTITY while `parameterized_compatible_view` — the neighbour doing the
same job — matches by SHORT NAME. Two sides of one comparison reach their `T` through different
resolutions and carry two symbols for it; the concrete row passed only because its argument type
and its column type came from the same place. Fixed to the neighbour's rule. Two more rows were
TEST defects the fixes exposed: `expect_load_errors` pairs expected substrings to errors
positionally (three substrings demanded three errors), and the eval row asserted `contains('a')`
on a `Value::Node`'s DEBUG rendering — an occurrence tree of `Symbol(1234)` handles with no `a`,
`b` or `1` in it as content, so it had been passing on the word "Span". It renders through
`TermPrinter` now and asserts both halves: that the answer IS `x`'s list and is NOT `y`'s.

