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
### 2026-09-12T06:17:41Z — feedback — claude

IMPLEMENTATION PLAN FOR WHAT REMAINS (claude, 2026-09-12, session with user; revised the
same morning after the user's question "why can't B be an unfilled var?" — the earlier
version refused an unwritten parameter BY SPELLING, this one refuses it only when it is
still UNCONSTRAINED after typing, the rule an operation's own type parameter already has).
Everything below was read at the site or driven on 575683e5 (typing rows through `anthill
load` on the CLI built from that tree; eval rows through a direct-child scratch test,
deleted). Nothing was built.

0. WHAT REMAINS — a census of the acceptance against the delivery note of 05:43:
  * NOT BUILT: the receiver bracket on a rule citation — rows (a)/(b)/(c) of the
    2026-09-11T21:27 scope addition. Decision B settled the design (a hidden head slot);
    this plan makes it concrete. WT8WG stays blocked on it and lifts its refusal when it
    lands (its 03:35 note lists the three edits on its side).
  * NOT MET AS WRITTEN: the `anylist(?w: List) :- true` row ("enumerates definite rows
    without an undecided tail"). It answers ONE conditional row with the member goal in
    the residual; enumerating was built and did not return (both operands free is a
    product of two infinite streams — WI-20260911-09E6M's fairness). Decision (c) below.
  * A DOC LINK TO NOTHING: `load::emit_domain_value_face`'s doc names
    `typing::refuse_parameterised_rule_citation`, which does not exist — the refusal is
    `record_domain_value_face_declined` read by `typing::domain_value_face_refusal`. Fix
    when that function is edited (step W1).
  * Everything else in the acceptance is met (05:43 note, row by row). scaland: no twin.

1. MEASURED TODAY, on the written twin `sort Wrap[T] { entity wrap(v: T)
   rule dom(?x: Wrap[T = T]) :- true }` beside `sort Colour { red green blue }`:

    citation, in an operation body                       load               eval
    `Wrap[T = Colour].dom.takeN(5).length()`             clean              RAISES
    `Wrap[W = Colour].dom.takeN(5).length()`  (bogus W)  clean              —
    `Wrap[T = Colour].dom().takeN(5).length()` (applied) clean              RAISES
    `Wrap[W = Colour].dom().takeN(5)`         (bogus W)  refused: "has no type parameter named 'W'"
    `Wrap[T = Colour].dom().head.x` -> Wrap[T = Colour]  REFUSED: "expected Wrap[T = Colour], got Wrap[T = ?T]"
    `Wrap[T = Colour].dom().head.x` -> Wrap[T = Int64]   refused, same "got Wrap[T = ?T]"
    `Wrap.dom.head.x`               -> either            refused, same "got Wrap[T = ?T]"
    `Wrap[T = Colour].dom.head.x`   -> either            3 x "type mismatch in dom.name / head.name / x.name: expected resolved name, got unresolved"
    `dom.takeN(5).length()` inside a member of Wrap      clean              RAISES
    rule-body goals `Wrap.dom(?x)` outside, `dom(?y)` inside, `Wrap[T = Colour].dom(?x)`: all load clean
    `List[T = Letter].domain.takeN(5)`                   refused naming 5G28A (WT8WG's row)

  RAISES = `Err(Raised …)` at the first row, `takeN(1)` included: the appended member goal
  carries `Wrap[T = ?T]` with `?T` the sort's canonical variable, which `bindable_type_var`
  rightly refuses to pin from one value, so the goal delays and the drain flounders.

  THREE DIFFERENT DEFECTS, and the plan has to close all three, not one:
  (i)  the PAREN-LESS bracket is ERASED before any validation — `convert.rs`
       `collect_field_access_segments`' `application` arm ("bindings erased") for a dot
       CALL's receiver chain, so `Wrap[W = Colour].dom` loads clean; the APPLIED spelling
       reaches `build_recv_type` (the `recv_type` aux rides only a call's `Fn` node) and is
       validated, then DROPPED by the typer;
  (ii) the citation's column types at the sort's CANONICAL variable, which is neither a
       wildcard nor pinnable, so the agreeing instance is refused with the same message as
       the wrong one — a FALSE REFUSAL of a correct program, not a silent acceptance, in
       every position that reads the column type;
  (iii) a paren-less bracketed chain followed by a PROJECTION is not recognised as a
       citation at all: `field_access_dotted_name_of` needs a `Term::Ident` root and
       4NEKZ's `loader_chain_dotted_name` an `Expr::Ref` root, and a type application is
       neither, so it falls to the per-segment path WI-20260902-40KSW owns.

  CORPUS: a text census (stdlib, examples, anthill-todo, every test fixture) finds ZERO
  relational rules declared inside a parameterised sort body — the only rules inside one
  are wi383's two `CpsMonad` EQUATIONS. So the head-shape change below has an EMPTY corpus
  population; the clauses that gain a slot are the derived `<Sort>.domain` faces of the
  parameterised sorts that derive a domain, plus this ticket's fixtures. Asserted at
  delivery by a KB walk (the idiom of
  `the_shipped_corpus_has_no_unwritten_parameter_in_a_rule_head_bound`), which is also the
  tripwire for the day a corpus rule moves into a parameterised sort.

2. THE DESIGN, made concrete (Decision B):

    Wrap[T = τ].dom(?x)   ==   dom(?x, τ)        -- one trailing HIDDEN slot per parameter
    List[T = Letter].domain(?x) == anthill.kernel.domain_member(?x, List[T = Letter])

  * ONE TRAILING POSITIONAL SLOT PER ENCLOSING-SORT TYPE PARAMETER, in
    `type_param_syms_of(sort)` order — the parameter list `seed_receiver_type_args`
    already binds for an operation, so the two engines read one list. The slot holds the
    parameter's CANONICAL variable term (`published_param_var`), which is the very term the
    bound already carries: `assert_rule_debruijn_with_*` collects head variables into the
    frame, the bound then closes to the same De Bruijn index, and pinning the slot pins the
    bound with no second mechanism. The `is_canonical_type_param_var` exclusion at
    `load_rule_inner` and in the expansion sweep becomes REDUNDANT for a relational head
    (the variable is already in the frame from the head) and STAYS for an equation.
  * WHICH CLAUSES: every RELATIONAL clause whose declaring scope is a sort with type
    parameters, and the derived `<Sort>.domain` of a parameterised sort. An EQUATION — a
    rule whose head is an equality connective, `flatMap(pure(?x), ?f) <=> ?f(?x)` or
    `keep[T](?x: T, ?y) <=> ?y :- F[T] [simp]`, as opposed to a predicate head — is
    EXCLUDED (`is_equational_head`): its clauses index under the connective, it fires as a
    REWRITE in `apply_eq_rules` by matching a call at the arity the author wrote, and it
    cannot be cited as a `Relation`, so a slot would change the redex and nothing could
    fill it. The two `CpsMonad` equations above are the whole corpus population, and
    pw9a0's `keep_id` row (bound stays a canonical `Var::Global`) is the control that says
    equations were left alone. Uniform per predicate, which is what WI-6WVJB (one arity)
    and `relation_columns_across_clauses` (one head shape) require.
  * WHERE THE SLOT SPEC LIVES: derived from the GOAL SYMBOL's scope
    (`hidden_slot_params_of(goal) -> &[Symbol]`: the owner's `type_param_syms_of` when the
    owner is a parameterised sort, else empty), not stored per clause — one owner, no
    second table, and decidable at the two mint sites (`scan_rule_goal`,
    `mint_domain_value_face_name`) before any clause is asserted, so a body goal can be
    lowered with its slots before the rule that owns the predicate is loaded.
  * HIDDEN = excluded from `rule_head_var_slots`, the ONE enumeration the typer's schema
    and eval's `build_relation_value` share — so a hidden slot is never a column on either
    side by construction.
  * AT A CITATION THE SLOT IS A FRESH TYPE VARIABLE, exactly as an operation's own type
    parameter is at a call, and it is pinned by the same four sources or refused by the
    same rule. Sources: (1) the receiver bracket, seeded into the citation's σ by short
    name; (2) the EXPECTED type, arriving from any consumer up the chain — the op return
    in `operation g() -> List[T = Letter] = List.domain.head.x`, a `let` annotation, an
    argument slot; (3) an APPLIED argument — `Pair[A = Colour].domain(pair(red(), a()))`
    binds column `x`, whose type `Pair[A = ?a, B = ?b]` unifies with the argument's
    through the correlated-column unify this ticket's gap (1) already delivered; (4)
    inside the sort's own body, the enclosing instance (RS2G4's bare-sibling rule). A
    parameter STILL A VARIABLE when the walk ends is `TypeError::UnconstrainedTypeParam`
    — WI-270's "expected a type for 'B'" from `check_unconstrained_type_params`, whose
    doc states the rule: "every declared type-param must resolve to a non-Var term; an
    unresolved Var means the caller can't recover the return type's concrete shape".
    NOTHING ABOUT THE SPELLING DECIDES IT: `Pair[A = Colour].domain` with `B` pinned by
    the return is accepted, bare `List.domain` with `T` pinned by the return is accepted,
    `Wrap[T = Colour].dom.takeN(5).length()` is accepted, and `Wrap.dom.takeN(5).length()`
    is refused naming `T` because nothing in it can say what `T` is.
  * WHY A SLOT CANNOT STAY OPEN INTO EVAL, stated once: the resolver enumerates VALUES,
    never types. A free type argument makes every derived clause a candidate (WI-743's
    20-row measurement) and the mode-(out) guard turns that into a delay, which is the
    RAISES column of §1. A rule-BODY goal is the exception and stays one: there an open
    slot is the ordinary free variable of §8.1 and delays until a sibling binds it.
  * THE PIN TRAVELS TYPER -> EVAL ON THE EXISTING CHANNEL. The typer writes the pinned
    types to the citation occurrence with `set_resolved_type_args`, keyed by the PARAMETER
    SYMBOL — the sort half RS2G4 added at typing.rs ~19291 already keys by it and already
    skips a walk that lands on a bare variable. Eval's `build_relation_value` reads that
    channel for the hidden slots and NEVER reads the bracket: the typer is the bracket's
    only reader, as it is for an operation call, so the two engines cannot disagree about
    what the bracket meant. A KB typed by nothing (a hand-built fixture) has an empty
    channel, the slot opens as a fresh variable, and the goal delays — the same backstop
    `UnknownOperation` gives a typer-less apply.
  * WHY POSITIONAL AND TRAILING, stated because a named slot under a reserved key was the
    alternative: `domain_member(?x, T)` is already that shape, `rule_head_written_columns`
    and `resolve_relation_arg_columns` are positional-index readers (exclude "index >=
    written arity"), and a trailing slot leaves every written column's index untouched.
    THE COST is every `pos_arity` reader that means "written arity": the hand-written
    `domain` hook's 1-ary test (`arity_of` in `derive_domain_member_clauses`), the "arity
    {n} is not the member shape" decline in `emit_domain_value_face`, resolve.rs's
    `declared_arity` / `bare_bodied_bool_relation` check (~2079), and the load-time "a term
    a clause of `X` can match (k positional)" refusal — each must read `pos_arity -
    hidden`. That last one is a GIFT, not only a cost: with the head shape changed and
    nothing else, every rule-body goal the plan fails to convert is REFUSED AT LOAD by it,
    so the goal-site census is "build L1, run the suite, read the arity refusals".

3. SITES, in build order; each names the row that reddens when it is backed out.

  L1 LOADER, HEAD SHAPE. `load_rule_inner`, after `kb_heads` and before
     `assert_rule_debruijn_with_bound_vars`: for a relational head whose `domain` is a
     parameterised sort, append the canonical var terms. `emit_domain_value_face`: delete
     the `!job.params.is_empty()` early return; head `pos_fn(sym, [x, T1..Tn])` from
     `job.params`; the bound is the `self_type` already built (`domain_self_type`, the same
     term the kernel clause's head carries). VERIFY AT THE SITE (v1): that a written `T`
     inside `Wrap[T = T]` in a rule-head bound lowers to the canonical `Var::Global` and
     not to `Term::Ref(Wrap.T)` — pw9a0 asserts it for the guard-introduced form and the
     exclusion at `load_rule_inner:31527` presumes it, but the direct form runs through
     `convert_term` under `in_rule_head_bound`; if it is a `Ref`, the slot must carry the
     same spelling or `term_to_debruijn` closes nothing and the slot is inert. (v3): a
     NULLARY relational head inside a parameterised sort (`rule holds :- …`) becomes
     `holds(?T)`, a `Fn` where `alloc`'s WI-511 rewrite gave a `Ref` — check
     `rule_head_var_slots`' and `build_relation_value`'s `Term::Ref` arms.

  L2 LOADER, GOAL SPELLING. Every rule-body goal and query pattern naming a hidden-slot
     predicate is lowered WITH its slots: inside the sort's own scope, the canonical var
     term (the tie — the enclosing clause's own hidden slot is the same variable, so
     `Wrap[T = Colour].again` reaches `dom`'s slot through `again`'s); outside, one fresh
     variable per slot (a rule body's ordinary free case, §8.1); a BRACKETED body goal
     `Wrap[T = Colour].dom(?x)` takes the written binding. VERIFY (v2): where that body
     goal loses its bracket today (P6 loads clean and `check_unconsumed_recv_types` does
     not report it — that sweep only sees a call `Fn` node carrying the `recv_type` aux,
     so either the aux is absent for a goal or it is consumed by something that drops it);
     WI-839's rule is read-or-reported, so the outcome is read, never erased.

  L3 LOADER, THE CITATION. Lower a paren-less `Sort[…].rel` whose chain ROOT is a type
     application as `Expr::Apply { functor: rel, recv_type: Some(<the type value>),
     pos: [], named: [] }` — the zero-argument applied citation both engines already take
     (`start_relation_apply` with no args IS `build_relation_value`; typing.rs:17467 IS
     `relation_reference_type_applied`). One node for both spellings, so (iii) closes and
     (i)'s paren-less erasure closes with it. Two producer sites, because the bracket is
     lost at two places: `visit_load`'s `field_access` ladder (a rung before
     `try_qualified_rule_ref`, reading the application root the way `build_recv_type`
     reads the aux) and the dot-CALL receiver path where `convert.rs:843` erases the
     bindings — the converter must keep the application as the chain root (or attach the
     `recv_type` aux to the chain) so the loader can read it. `build_recv_type` validates
     parameter NAMES through `type_expr_to_child_inner` for free, which is row (e).

  T1 TYPER, THE SLOT VARIABLE AND ITS SOURCES. `rule_head_var_slots` excludes hidden
     slots. `relation_clause_columns` returns, beside the columns, the hidden slots'
     PER-CITATION fresh variables `(param, VarId)` (it already mints a fresh frame per
     citation for a clause with bounds, and a hidden-slot clause always has one); across
     clauses each clause's slot variable is unified with one citation-level variable per
     parameter. `relation_reference_type_applied` (and the bare arm, which becomes the
     same code path) seeds source (1): `call_recv_type_of(occ)` -> `sort_application_parts`
     -> per parameter BY SHORT NAME (the type-parameter-keys footgun: the bracket's keys
     are bare interns, the declared list is qualified — exactly `seed_receiver_type_args`'
     loop) -> `expand_written_bracket_value` -> unify with the slot variable in the walk's
     σ. Factor the name-matching into ONE helper shared with `seed_receiver_type_args`, so
     the two readers of a receiver bracket cannot drift. Sources (2) and (3) need no code:
     the slot variable is inside the column type `x: Wrap[T = ?s]`, so `expected` and an
     applied argument reach it through the unifications that already run. Source (4):
     inside the sort's own body (`env.enclosing_sort()` is the relation's sort) seed the
     slot with the enclosing instance's WI-424 body rigid, as a sibling operation call is.

  T2 TYPER, THE DISCHARGE. The check cannot run at the citation node: an operation call
     has `expected` threaded INTO `check_apply_iter`, so `check_unconstrained_type_params`
     runs with a complete σ there, but a citation's pin may arrive from a consumer ABOVE
     it (`.head.x` unified against the op return after the citation was typed). So the
     citation registers `(occ, [(param, VarId)])` on `WalkSolutions` — the deferral
     50B2K's `defer_abstract_dispatch` already uses, "held until the walk ends so the
     binder's own uses can answer it" — and at the walk's end, with the final σ: every
     variable bound -> `occ.set_resolved_type_args(pinned)` (walked and surfaced exactly as
     ~19291 does; a rigid from source (4) is SKIPPED there so eval inherits the frame, the
     rule that loop already states); any variable unbound ->
     `TypeError::UnconstrainedTypeParam { op: <the relation>, type_param }`. VERIFY (v5):
     `resolved_type_args` is written ONCE — `substitute_occurrence`'s `Apply` arm rewrites
     `type_args` and `recv_type` through σ but not this channel, and every rebuild path
     carries `resolved_type_args: _` — so writing the variable early and hoping a later
     pass replaces it would leave a variable in the channel; the write must be the
     deferred one.

  E1 EVAL, THE FILL. `build_relation_value` takes the citation occurrence (the bare leaf
     from `reduce_var`, the `Expr::Apply` from `start_relation_apply` — carried through
     `AwaitState::RelationArgs`) and fills each hidden slot from
     `occ.with_resolved_type_args` by parameter symbol; a parameter absent from the
     channel takes a fresh variable that is NOT pushed to `columns`. No `recv_type`
     plumbing at eval at all.

  E2 EVAL, THE ENCLOSING INSTANCE. A citation inside a member whose parameter the typer
     left off the channel (source (4), a rigid) fills the slot from the frame's
     type-argument channel — the entries `inherit_enclosing_sort_type_args` carries into a
     sibling's frame, keyed by the parameter symbol `hidden_slot_params_of` hands back.
     Row (f) is the only row that reddens under this axis alone.

  W1 WT8WG's LIFT: delete the parameterised arm of `domain_value_face_refusal` (and the
     dangling doc link), flip `a_parameterised_sorts_citation_names_its_owner` into an
     answering row with the unconstrained bare `List.domain` as its control, per its
     03:35 note.

  D1 DOCS: kernel-language.md §8.1 ("with one piece of the rule half still open …" —
     delivered; a citation's hidden slot is pinned as an operation's type parameter is,
     by the bracket, the expected type, an argument, or the enclosing instance, and
     refused by WI-270's rule otherwise) and §5.3 (the parameterised value face);
     proposal 060 §2.2's "no value face yet" paragraph; 052 §Naming (a receiver bracket
     on a citation binds the sort's parameters, the twin of proposal 035 form (3));
     060-implementation §7.1/§7.2. CLAUDE.md untouched.

4. ROWS (one file, `wi_5g28a_receiver_bracket_test.rs`; every row DRIVES; back-out axes
   [L1] [L2] [L3] [T1] [T2] [E1] [E2] [W1], each RUN not predicted, one mutation per axis):
  (a) `List[T = Letter].domain.takeN(5)` = 5 definite rows; `List[T = Letter].domain.head.x`
      accepted at `List[T = Letter]`, refused at `List[T = Int64]` with BOTH types in the
      message. Fails [W1], [L1], [T1], [E1].
  (b) PINNED WITHOUT A BRACKET: `operation g() -> Relation[T = (x: List[T = Letter]),
      E = {Error}] = List.domain`, driven as `g().takeN(5).length()` = 5 — the return
      pins `T`, the channel carries it, eval reads it. Fails [T2] (no deferred write: the
      slot opens free and the drain raises) and [E1].
  (c) UNCONSTRAINED: `Wrap.dom.takeN(5).length()` outside the sort, and
      `Pair[A = Colour].domain.takeN(6).length()`, refused at load naming `T` / `B` with
      WI-270's message. Fails [T2]: backed out, both load clean and RAISE at eval — §1's
      column, and WT8WG's control (c) in the form it now takes (with this ticket backed
      out the row is the 5G28A-naming load error, not a wrong count).
  (d) the written twin, BOTH spellings: `Wrap[T = Colour].dom.takeN(5)` = 3 and
      `Wrap[T = Colour].dom().takeN(5)` = 3 — one lowering. Paren-less fails [L3]; applied
      fails [T1]/[E1] only. And `Wrap[T = Colour].dom.head.x` -> `Wrap[T = Colour]`
      accepted, -> `Wrap[T = Int64]` refused naming both (today: three unresolved-name
      errors; applied form today: `?T`).
  (e) `Wrap[W = Colour].dom` (paren-less) refused "has no type parameter named 'W'" — today
      clean. Fails [L3].
  (f) inside the sort: `operation inside() = dom.takeN(5).length()`; `Wrap[T = Colour].inside()`
      = 3 and `Wrap[T = Letter].inside()` = 2 (`sort Letter { a b }`) — two instances, two
      counts, so a slot filled with the wrong instance or left free cannot pass. (Not
      `Int64`: a primitive derives no domain, so its member goal delays and the row would
      measure floundering, not the fill.) Fails [E2].
  (g) rule bodies: `rule outside(?x) :- Wrap.dom(?x)` answers ONE conditional row (slot
      free, the member goal delays — WI-737's route); `rule tied(?x) :- ?x <=> wrap(red()),
      Wrap.dom(?x)` = 1 definite — the value is bound FIRST, so `pin_bound_from_value`
      reads `T` off it into the bound's variable, which IS the slot's (the other goal
      order delays inside the callee and comes back conditional; assert that too, it is
      what makes the definite number readable); inside the sort `rule again(?y) :-
      dom(?y)`, cited `Wrap[T = Colour].again` = 3. Fails [L2] — LOUDLY, at load, by the
      arity refusal.
  (h) two parameters: `sort Pair[A, B] { entity pair(a: A, b: B) }`;
      `Pair[A = Colour, B = Letter].domain.takeN(6)` = 6 (slot ORDER and short-name
      matching, `B = …, A = …` written in the other order answers the same);
      PARTIALLY WRITTEN AND PINNED: `operation p() -> Pair[A = Colour, B = Letter] =
      Pair[A = Colour].domain.head.x` accepted and evaluates to `pair(red(), a())`;
      APPLIED ARGUMENT PINS: `Pair.domain(pair(red(), a()))` — no bracket at all — types
      `Relation[Unit]` and answers 1 row, both parameters read off the argument.
  (i) CONTROLS, pass either way BY DESIGN and say so: pw9a0's `keep_id` bound stays a
      canonical `Var::Global` (equations excluded); `wi743_finite_domain_test` counts;
      `wi_wt8wg` rows other than the flipped one; `wi714`'s rows (no sort, no slot);
      `wi_5g28a`'s 18 rows; WI-270's own `UnconstrainedTypeParam` rows for operations.
  (j) the corpus tripwire of §1: the set of relational clauses carrying a hidden slot in
      the shipped corpus is exactly the derived faces of the parameterised sorts that
      derive a domain — name the count.
  (k) PERSISTENCE ROUND TRIP: a hidden-slot rule printed by `TermPrinter` and re-loaded
      keeps ONE slot — the printer must omit hidden slots (or print the bracket form), or a
      re-load appends a second. Fails on the printer axis; it is a row because the
      failure is silent.

5. DECISIONS. Settled with the user 2026-09-12: an unwritten parameter of a citation is
   an ordinary fresh type variable, pinned by any of the four sources and refused only
   when still unconstrained after typing — WI-270's rule, not a spelling rule. Still open,
   each with my recommendation:
  (b) a bare citation INSIDE the sort: the enclosing instance fills the slot (T1 source
      (4) + E2; recommended — without it no member operation of `Wrap` can cite its own
      domain).
  (c) the `anylist` acceptance row: amend it to what ships (one conditional row, the
      member goal in the residual; enumeration is 09E6M's) — recommended — or leave it
      unmet and the ticket open on it after the bracket lands.
  (e) equations excluded from hidden slots (recommended; §2 says what an equation is and
      why; pw9a0 is the control).

6. ORDER AND SIZE: L1 -> run the suite, the arity refusals ARE the goal-site census ->
   L2 -> L3 -> T1/T2 -> E1/E2 -> W1 -> D1 -> corpus census -> `/code-review` on a
   restored tree. It is the "second feature" Decision B called it — comparable to RS2G4:
   two loader sites, two typer sites, two eval sites, a KB accessor, and the WT8WG lift.
   scaland: no twin (05:43 note), `sbt test` a no-regression check.

### 2026-09-12T07:14:48Z — feedback — claude

THE PLAN'S CORPUS CENSUS WAS WRONG, AND MEASURING IT REOPENED DECISION B. Session with the
user, 2026-09-12. L1 (the head-shape change) was BUILT and the head/bound wiring VERIFIED; it
is not committed, because the measurement it produced argues for a different mechanism.

1. THE CENSUS. §1 of the 06:17 plan says a text census "finds ZERO relational rules declared
   inside a parameterised sort body — the only rules inside one are wi383's two `CpsMonad`
   EQUATIONS". FALSE. Measured by building the append and instrumenting it on a stdlib load:
   SEVEN clauses under FOUR predicates, none of which carries a head bound at all.

     anthill.prelude.Set.eq/2         1 clause    in Set[T]
     anthill.prelude.Set.subset/2     2 clauses   in Set[T]
     anthill.prelude.Set.contains/2   2 clauses   in Set[T]
     anthill.prelude.Lattice.less/2   2 clauses   in BoundedLattice (`sort T = ?` spelling)

   Plus fixtures: `parameterized_provides_block_test`'s `Stack.is_full`, wi752's `Mid.rel`.
   13 tests red, and one group names the reach the plan's site list does not contain: wi616 /
   wi625 / wi939 drive `Set.eq` through the SPEC-OP DISPATCH bridge, which builds its goal at
   the WRITTEN arity. An in-band head slot changes arity, so every such site must be found.

2. L1 ITSELF WORKS, and the wiring the plan predicted is confirmed. Probe on `sort Wrap[T]
   { rule dom(?x: Wrap[T = T]) :- true }`: with the slot appended, `globals = [x, T]` and the
   stored bound is `Wrap[T = DeBruijn(0)]` — the bound closed to the SAME index as the slot,
   so pinning one pins the other with nothing in between, exactly as §2 claimed. A written `T`
   in a rule-head bound also lowers to the canonical `Var::Global`, not to `Term::Ref` (the
   plan's v1), so the slot can carry the same term.

3. AND FOUR BOUNDS ANSWER FOUR WAYS, which is a defect the ticket names and does not implement:

     rule (inside `sort Wrap[T]` unless noted)   stored bound         its `T` is
     `written(?x: Wrap[T = T])`                  Wrap[T = <db 0>]     the CANONICAL Wrap.T
     `bare(?x: Wrap)`                            Wrap[T = <db 2>]     a FRESH clause variable
     `other(?x: List)`                           List[T = <db 2>]     a FRESH clause variable
     `outside(?x: Wrap)` at top level            Wrap[T = <db 1>]     a FRESH clause variable

   `written` and `bare` MEAN DIFFERENT THINGS SILENTLY. Gap (3)'s own text says they should
   not — "the self-reference stays its own rule keyed by declaration context
   (`repair_self_reference`: a bare `List` inside `List`'s OWN definition is the same element
   type)" — but `expand_unwritten_type_params` has no such arm; it mints fresh unconditionally.
   That sentence is UNIMPLEMENTED for a rule-head bound, whichever mechanism ships.

4. THE USER'S QUESTION SETTLED ONE THING OUTRIGHT: "when we have p(x: List) :- … then we should
   have slot for T?" — NO. Gap (3), delivered, mints `List`'s `T` as an ordinary CLAUSE
   variable opened fresh per firing, and that is the right reading: `p(?x: List)` means "for
   any list, whatever its element type". A channel there would let a caller pin something `p`
   never promised. THE RECEIVER'S PARAMETER IS THE ONLY ONE IN QUESTION.

5. THE COMPARISON THE USER ASKED FOR — against the requires subtree — AND WHAT IT SAYS. Read
   at the sites, the requirement channel has four properties:
     * its SHAPE IS DECLARED, never inferred: `dict_layout` = `direct_requires_chain_rc(spec)`
       + `provider_dict_entries(provider)`, a structural recursion over declarations. There is
       no fixpoint over the call graph anywhere in it.
     * EVERY MEMBER CARRIES IT, read or not (`Frame::requirements`, populated on frame push).
     * A NESTED CALL GETS IT BY PROJECTING A SUBTREE: `Frame::child_context()` clones the
       channel wholesale into the child, and a nested dispatch walks `proj_path` with
       `dict.sub(k)`; `expand_dispatching_dict` hands the callee exactly its own half.
     * THE TWO ENDS ARE CHECKED AGAINST ONE PREDICTED SHAPE (`dict_layout` vs
       `DictLayout::from_halves`, `divergence_from`), loud on disagreement.
   The declared/inferred axis rules the FIXPOINT out: this codebase decides who carries a
   context channel from a DECLARATION, never from who-calls-whom. But the reason requires can
   afford "every member carries it" is that a dictionary is OUT OF BAND and PER-ACTIVATION — it
   changes no arity, no discrimination key, no call site. A hidden slot is IN BAND, which is
   precisely why the uniform rule went red on the dispatch bridge. The analogy transfers only
   if the type channel moves out of band too.

6. SO DECISION B'S PREMISE WAS RE-READ, AND IT IS THE CODEBASE'S OWN KNOWN-FALSE CLAIM.
   Decision B rests on "a rule has no frame channel — its head is its only interface".
   `resolve.rs:840` documents that sentence as a defect: the claim "a rule has no caller to
   thread a dictionary into a frame" is "written in `kb/typing.rs` and in
   `docs/design/requirement-dictionaries.md`, and FALSE … What this frame lacks is a
   requirement channel; it has callers, and it already threads a caller-inherited environment
   in `assumed_facts`." Decision B's own MEASUREMENT stands (`eval::build_relation_value` does
   build the query from the head alone) — but that is a fact about today's code path, not
   about what a rule can have.

7. AND THE OUT-OF-BAND ROUTE IS REACHABLE, verified at the sites:
     * THE BOUND IS ALREADY ENFORCED BY A BODY GOAL, not by a head match, on the SLD route:
       `install_typed_head_domain_goals` appends `domain(?x, Wrap[T = ?T])` with `?T` a frame
       slot. So `Wrap[T = Colour].dom` floundering today is exactly "nothing binds the opened
       `?T`" — not "the head cannot carry it".
     * THE GOAL IS IN SCOPE AT THE CLAUSE ACTIVATION: `step_choice_point` holds
       `original_goal: Value` and calls `kb.with_fresh_vars(rid, &tree_subst)` at resolve.rs
       ~4400.
     * THE PIN IS ALREADY BUILT: `pin_type_vars` (gap 2) is "match a determined type against a
       variable-bearing bound, binding what stands opposite each variable", and
       `typed_pattern_bounds_hold` already opens a stored bound with `term_from_debruijn(bound,
       fresh)`. Binding the clause's `?T` from a CALLER-supplied type is the same call with a
       different source.
     * WHAT IS NOT VERIFIED, said plainly: the citation's goal is a `Value::Entity` built by
       `build_relation_value` (`pattern_query(term: …)`), so it carries NO occurrence and no
       `resolved_type_args` today; that carrier would have to change. And `with_fresh_vars`
       returns `(fresh_nodes, answer_links)`, not the fresh frame, so the opened slot's VarId
       is not currently handed back.

8. THE TRANSITIVITY QUESTION SURVIVES BOTH MECHANISMS, and requires answers it. Acceptance row
   (g)'s `rule again(?y) :- dom(?y)` cited as `Wrap[T = Colour].again`: `again` has no bound,
   so out of band there is nothing to pin, exactly as in band there is no slot to fill. The
   requires analogue is `child_context()` — the channel is INHERITED by the body's goals, a
   dynamically-scoped type environment keyed by (sort, parameter), which the resolver frame
   already has the shape for (`assumed_facts`). That is a design choice, not a detail: it is
   dynamic scoping, and an inner goal's own bracket would have to shadow it.

NOTHING IS COMMITTED. The L1 tree (head append, `hidden_slot_params_of*`, the
`rule_head_var_slots` exclusion, `emit_domain_value_face`'s parameterised arm) exists in the
working tree as the measurement that produced §1–§3, and is to be kept or discarded by the
mechanism decision above.

### 2026-09-12T07:18:53Z — feedback — claude

DECISION C — THE TYPE RIDES BESIDE THE GOAL, NOT AS AN EXTRA HEAD ARGUMENT, AND IS RESOLVED
FROM THE FRAME AT EVALUATION. Settled with the user 2026-09-12, replacing Decision B (the
hidden head slot) of the 05:43 note. L1 is DISCARDED — reverted from the working tree, its
measurement kept in the feedback above.

THE ARGUMENT THAT DECIDED IT IS THE USER'S, and it is about WHEN the type is known, not about
cost. With the type baked in as a head argument the TYPER is what fills it, so inside

    operation g[T]() -> Int64 = List[T = T].domain.takeN(5).length()

the argument is pinned to `g`'s RIGID `T` and the goal reaching the resolver carries a rigid. A
rigid has no constructors, so the member goal cannot enumerate — it delays, and the program gets
the RAISES column §1 measured, this time for a CORRECT program. The real type is known only at
`g[Colour]()`, at RUN time, which is exactly where `Frame::type_args` holds it (WI-272,
`(declared-param-name, resolved-type-term)`) and where `inherit_enclosing_sort_type_args` already
carries a sort's parameters into a sibling's frame. Reading the frame at evaluation is native to
the beside-the-goal shape and bolted onto the head-argument one. The 06:17 plan half-saw this:
its E2 skips a rigid from the ENCLOSING SORT so "eval inherits the frame" — but an OPERATION's
own `[T]` is the same question and the plan does not cover it.

THE SHAPE, stated without the word "out-of-band" (my coinage, dropped):

    goal reaching SLD          dom(?x)              -- UNCHANGED, the written shape
    riding beside it           Wrap.T := <type>     -- resolved through Frame::type_args
    what the resolver does     opens the clause, then binds the clause's own bound variable
                               from it (`pin_type_vars`, gap 2, already built)

Nothing counts it as an argument, so NO arity change, NO discrimination-index change, NO body-goal
rewriting, NO `pos_arity` readers, NO printer round-trip, and NO spec-op dispatch-bridge cost —
the 13 red tests of the L1 measurement do not arise. THE SLOT RULE AND THE FIXPOINT QUESTION
DISSOLVE WITH IT: there is no head shape to be uniform about, so "which predicates get a slot" is
no longer a question. A clause whose bound mentions the receiver's parameter is pinned; one whose
bound does not has nothing to pin, and whether its bracket is meaningful is decided at the TYPER,
where the column types are.

SITES, in build order:
  R0 RESOLVER, THE CHANNEL. `ResolverFrame` gains a type-argument channel inherited on push the
     way `assumed_facts` is — which is the `Frame::child_context()` analogue and answers the
     transitivity question (acceptance row (g)'s `rule again(?y) :- dom(?y)` cited as
     `Wrap[T = Colour].again`): a body goal inherits its clause's channel, and a body goal that
     writes its OWN bracket shadows it. Keyed by (sort, parameter symbol).
  R1 RESOLVER, THE PIN. At the clause activation (`step_choice_point`, resolve.rs ~4400, where
     `original_goal` is in scope and `with_fresh_vars` is called): open the clause's stored
     bounds against the fresh frame — `term_from_debruijn(bound, fresh)`, which
     `typed_pattern_bounds_hold` already does — and `pin_type_vars` the caller's type against
     each, binding into the merged σ. VERIFY (v6): `with_fresh_vars` returns `(fresh_nodes,
     answer_links)` and NOT the fresh frame, so the opened variable's `VarId` is not currently
     reachable; a sibling that hands it back is needed.
  E1 EVAL, THE SUPPLY. `build_relation_value` attaches the citation's types to the query, each
     one walked through `Frame::type_args` FIRST so a rigid becomes the caller's real type.
     VERIFY (v7): the citation's goal is a bare `Value::Entity` inside `pattern_query(term: …)`
     and carries no occurrence, so it holds nothing today — decide between making it a
     `Value::Node` of the citation occurrence (reusing `resolved_type_args`, the channel the
     typer already writes) and a second field on `pattern_query`.
  T1/T2 TYPER. As the 06:17 plan's T1/T2, with one change: a RIGID pin is left OFF the channel
     deliberately, for E1 to resolve from the frame — the rule the plan stated for the enclosing
     sort, now the rule for every rigid.
  W1/D1 as before.

STILL TO SETTLE, and not settled here: whether an inherited channel (R0) is the right semantics
or whether a clause must write its own bound to be pinnable. R0 is the requires analogue and
makes row (g) work as written; the alternative is lexical and would amend row (g) to
`rule again(?y: Wrap[T = T]) :- dom(?y)`. Decide before building R0 — R1 and E1 do not depend
on it.

