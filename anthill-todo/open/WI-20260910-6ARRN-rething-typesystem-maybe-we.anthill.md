## Attributes

- id: WI-20260910-6ARRN-rething-typesystem-maybe-we
- created: 2026-09-10T17:02:10Z

- status: Open
- status_agent: user
- status_at: 2026-09-10T17:02:10Z

- acceptance: cargo-test, scaland-sbt-test

## Description

rething typesystem - maybe we need case for type-projection of expression.  motivation is p(x:Leaf, y:Leaf),  where x, y can have differrent substitutions in Leaf.  So, maybe we need type-projection over expr 

## Changes

### 2026-09-11T11:48:47Z — feedback — claude

CROSS-REFERENCE (claude, 2026-09-11, session with user). The operation/rule split this ticket
asks for was worked out while planning WI-20260911-RS2G4, and the plan there (feedback of
2026-09-11, §0 and §5) records it: a sort parameter inside a member is a projection off the
receiver's instance — an OPERATION reads it (Γ, input only; `x.T` and `y.T` are two projections,
already kernel-language.md §8.1 / WI-1059), a RULE unifies it (σ, both directions: `p(?x: List,
?y: List)` opened to `p(?x: List[T = ?v1], ?y: List[T = ?v2])` with rule-scoped variables, fresh
per resolution). RS2G4 delivers the operation half at the typer and at eval. The RULE half is
this ticket's, in three pieces: (i) the implicit per-occurrence introducer (WI-582's `[T]`
without writing it); (ii) the derived `domain_member` clause reading its type argument as an
INPUT off the value (WT8WG item 8 — without it a free type variable enumerates every derived
domain, WT8WG item 7); (iii) a citation bracket binding the head's variables in
`build_relation_value`. Nothing filed beyond this note.

### 2026-09-11T12:04:02Z — feedback — claude

NESTED (user's question, 2026-09-11): the implicit introducer must be RECURSIVE — a fresh
rule-scoped variable per unwritten slot at every depth, `List[List]` = `List[T = List[T = ?v2]]`
— and the (in, out) domain read must hold at every depth. Today the domain goal for such a bound
is SILENTLY SKIPPED (typing.rs, the `continue` at `bound_names_a_determinate_type`'s caller), so
`rule nest(?w: List[T = List]) :- ?w <=> [[a()]]` answers 1 / 1 without enumeration and 20 / 1
under fresh variables (WT8WG item 7); this ticket must make it 1 / 1 with the goal present. The
self-reference exception (`repair_self_reference`: a bare `List` inside `List`'s own definition
is the same element type) stays a separate rule keyed by declaration context. Measured rows in
RS2G4's addendum of 2026-09-11, §3.

### 2026-09-11T12:20:22Z — feedback — claude

RULE STREAM READ FROM A BODY WITH RIGID ARGUMENTS (user's question, 2026-09-11): `operation
op(x: List, y: List)` reading `my_rule(x)` where the head ties a result column's element to
`x`'s. MEASURED on a CLI rebuilt from the source at 1eb89144 (the earlier binary carried an
old probe print); every row is `anthill load` of a scratch file, all removed. Body of each op:
`my_rule(x).head.res`. Return-type verdicts only; the `.head` effect noise was separated out and
an exact-typed control loads clean with `effects {Error, Error[EmptyStream]}`.

  head spelling                                  op(x: List[Int64]) -> List[Int64]   -> List[String]        op(x: List, y: List) -> List[T = x.T]       -> List[T = y.T]
  A  `res: List[T = x.T]` (projection)          LOAD ERROR at the head: "unresolved name 'x.T'" — and the citation still types `res` as the RULE's `x.T`:
                                                 refused "got List[T = x.T]"        refused (same)         refused: "expected List[T = x.T], got List[T = x.T] (render alike, not the same type)"   refused
  B  `x: List[T = ?t], res: List[T = ?t]`       head LOADS; every citation refused: "argument binding column `x` has an incompatible type" — concrete and rigid alike
  C  `my_rule[T](x: List[T = T], res: …)`       LOAD ERROR: "WI-582: rule type-variable `T` has no bounding guard" — an introducer must be `:- Spec[T]`-bounded
  D  `x: List, res: List` (bare, no tie)        accepted arg, `res` comes back `List[T = ?T]` and the return check refuses it — the two columns are independent by design
  E  `x: List[T = Int64], res: List[T = Int64]`  ACCEPTED                            refused (correct)      refused at the citation: a rigid `x` is not `Int64` (correct)

SO: NO, in every spelling today. Three separate gaps, each at a named site:
  (1) a path projection is not readable in a RULE-HEAD bound (row A's load error) — the position
      S8CBV closed for a `requires` bracket is still open here; and the citation checker does not
      re-key a head projection to the argument (the ζ receiver re-keying path-dependent-types.md
      §4.1 defers) — row A's "render alike" is exactly two neutrals with different receivers.
  (2) TYPER: `relation_clause_columns` (typing.rs ~9221) takes a typed head's bound VERBATIM
      (`rule_type_bounds`), so a `?t` inside `List[T = ?t]` reaches the citation checker as the
      rule's own variable, which the checker's `types_compatible` (~7905) cannot bind — it opens
      and correlates only a column whose WHOLE type is a variable (`resolved_var` →
      `bind_resolved`, the `rel(5, "s")` case). Nothing opens a head's TYPE variables per
      citation.
  (3) RESOLVER: `anthill query 'my_rule([1, 2], ?r)'` on head B answers `?r = [1, 2]`
      CONDITIONAL, residual `domain([1, 2], List(T: ?t))` twice — the variable is opened per
      resolution, but nothing reads it off the value, so the typed bound parks instead of
      deciding (WT8WG item 8's missing (in, out) read).

WHAT MAKES THE USER'S CASE WORK, and it is this ticket's direction rather than row A's: spelling
B plus per-citation OPENING of the head's type variables at the typer — fresh flexible variables
threaded through the ONE shared substitution the checker already keeps. Then a concrete argument
pins `?t := Int64` and `res` resolves; a RIGID argument pins `?t := op.x.T` and `res` comes back
`List[T = op.x.T]`, so `-> List[T = x.T]` is accepted and `-> List[T = y.T]` refused by ordinary
σ-equality of one neutral — no projection re-keying needed, because the tie is a variable, not a
path. In a rule `x.T` IS `?t` (RS2G4 plan §5 (iv)); row A's spelling is the heavier route and is
not required. Acceptance rows for this ticket: B × the four columns above (accept / refuse /
accept / refuse), C either loads as a plain tie or its message says to write B, and the resolver
query above answers DEFINITE with the domain goal present.

### 2026-09-11T12:28:58Z — feedback — claude

SCOPE, settled with the user 2026-09-11: this ticket KEEPS ITS OWN GOAL — the reflect typing
model (`anthill.reflect.typing`, proposal 022 "typing as facts") following the typer's reality,
which today has an expression-carried projection (`x.T`, the typer's ExprCarried form, §8.1)
that the reflect model has no case for; `p(x: Leaf, y: Leaf)` with two different substitutions
is the motivating shape. The RULE-HALF DELIVERY my three notes above sketched (per-citation
opening of head type variables, the (in, out) read at the resolver, the recursive implicit
introducer) is NOT this ticket's: it is filed as WI-20260911-5G28A-rule-head-type-variables-open, which carries the measured table and
the acceptance rows. Read the notes above as measurements the reflect model must also be able
to state, not as this ticket's work list.

### 2026-09-20T18:56:29Z — feedback — user

also thibk - are we need some notion for unfilled rigid patameter '?'  (like unknown in typescript)  or have rigid type-var itself as type

### 2026-09-25T09:57:32Z — feedback — claude

UNKNOWN[e] — A THIRD KIND OF UNKNOWN TYPE (user's question, 2026-09-25; arose designing WI-20260911-5G28A S3b, proposal 060 §2.3 / 067). It answers this ticket's opening question — "type-projection over expr" — and the 2026-09-20 note above ("unfilled rigid parameter '?' like unknown in TypeScript, or the rigid type-var itself as a type"): there are THREE kinds, not two, and they answer differently.

  rule same(?a: T, ?b: T) :- true
  rule q(1) :- same([?h], [red()])          -- ?a pins T from its value; ?b says T = List[Colour]

  ?a's type            unified with List[Colour]                      q answers
  List[?]              `?` is FLEX, anonymous, unshared:              1, DEFINITE, ?h free — WRONG (?h must be a Colour)
                       unifies with Colour and forgets ?h
  List[X], X rigid     a RIGID (skolem, e.g. the caller's X inside    nothing — WRONG
                       countAt[X]) unifies only with itself: fails
  List[Unknown[?h]]    the type OF ?h: no type variable to bind or    1, CONDITIONAL until ?h binds — RIGHT
                       refuse; the unification becomes a CHECK on      (as Int64's domain check waits on its
                       the value ?h (it must be a Colour)              variable today)

So `Unknown[e]` is a type that DEPENDS ON A VALUE — neither flex `?` nor rigid. Where each belongs: `List[?]` for a value with no element (`[]`: nothing for it to be the type OF — proposal 060 §2.3 decides `[]` is a `List[?]`, whose element's SortDomain is the Fillable of any value); `List[Unknown[?h]]` for a value whose element is a FREE variable — the carried type of a partially bound value (WI-578's value_type_term would produce it). PRECEDENT: docs/design/constrained-term-substrate.md already defines `typeof(?x)` — "the CARRIED type of ?x's binding; for an unbound ?x, its constraint-store bound" — in the desugaring `head(…) :- conforms(typeof(?x), T), body`; `Unknown[e]` is `typeof` made a type. Not designed further; nothing filed.

### 2026-09-25T10:00:47Z — feedback — claude

REFINED THE SAME DAY (user, 2026-09-25), correcting the note above: proposal 060 §2.3 no longer makes an unnamed element "the Fillable of any value". A condition is resolved when `fill` READS it, and a read WAITS while its type is unpinned. `[]` never reads it (its `nil` case), so `Wrap.el([])` still answers 1 definitely; and in the `same([?h], [red()])` row the waiting element check resumes once `?b` pins the type to Colour, so `q` answers red, green — the RIGHT answer, which the "any" reading got wrong. So the waiting goal already carries the tie between a type and a value; `Unknown[e]` is the type-system form of it, for the typer and the reflect model, and not a prerequisite of 5G28A S3b.

