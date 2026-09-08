# 060 implementation notes — mechanisms, status, measurements

Companion to [proposal 060](../proposals/060-clause-level-requirements-and-typed-heads.md),
which states the surface and its rules, and to
[`requirement-channel.md`](./requirement-channel.md), which owns the dictionary
mechanics. This document maps each proposal section to the code that implements it,
records what is delivered, and carries the build order for what is not.

Measurements are against the Rust loader at `0c5e3621`, each with a stated back-out.

## 0. Section → owner → status

| proposal § | what | owner | status |
|---|---|---|---|
| §1 `require[X]` | dictionary into clause scope | WI-1040 | **delivered** — §1 below |
| §2 `?x: T` on a relational head | `domain(?x, T)` body goal | WI-742 | **delivered** — §3–§5 |
| §2.1 parameter form `p(x: T)` | sigil-free typed clause variable | WI-742 | **delivered** — §6 |
| §2.2 a sort defines its `domain` | mode-(out) enumeration | WI-743 | not started — §7 |
| §3 anchor (requirement half) | covered body call grounds the spec | WI-1040 | delivered |
| §3 anchor (typed-head half) | `?x: T` grounds the spec | **WI-20260908-VVM1R** | **not started** — §8 |
| §4 determinism | fetch, never choose | WI-855/857/860 | delivered (058) |
| C666A relaxation | admit the guarded non-enclosing join | WI-742 | **delivered** — §9 |

Everything delivered is driven and controlled in
`anthill-core/tests/include/wi742_typed_relational_head_test.rs`, whose header names
which rows fail per back-out.

`domain` in §2.2 is the **member relation a sort defines**, not a second name for the
§2 goal — they share the name because the goal *is* that member read through the type.
WI-742 builds the goal with no enumeration arm; WI-743 adds the arm. Nothing in §2
depends on §2.2 landing.

## 1. §1 — delivered, and what it established

`require[X]` / `requires(X)` lower in the **converter**
(`parse/convert.rs:3376-3381`) to the kernel relation
`anthill.kernel.find_dictionary`, with an `out` named argument present exactly when a
dictionary is consumed:

```
require[Eq[T]]        ⇒  find_dictionary(Eq, out: ?<fresh>)
?d = require[Eq[T]]   ⇒  find_dictionary(Eq, out: ?d)
requires(Eq[T])       ⇒  find_dictionary(Eq)
```

The **typing pass** then rewrites each such goal into its resolver-ready form and
weaves the covered calls (`typing.rs:69175 record_find_dictionary_grounding`, called
from `typing.rs:64808`), replacing the clause body wholesale through
`KnowledgeBase::set_rule_body_nodes` (`kb/mod.rs:6181`). The resolver reads the goal at
`resolve.rs:6221 builtin_find_dictionary`.

Three things this establishes, and WI-742 inherits all three:

- **A typing-pass sweep may rewrite a clause body.** `set_rule_body_nodes` is the
  supported edit, and `body_nodes` is the SOLE body representation
  (`kb/mod.rs:321` — the term-level `body: Vec<TermId>` was dropped in WI-246), so one
  write reaches the resolver, the typer and `simp_rewrite` alike.
- **The sweep runs after `type_rule_bodies`**, so `?x.op(?y)` is already dispatched to
  `Apply` form and per-argument `inferred_type` is stamped. A goal generated earlier
  would have to re-do both.
- **A generated goal is an ordinary goal.** Nothing in the resolver knows
  `find_dictionary` was written by the compiler rather than the author.

**The one constraint the edit imposes**: `set_rule_body_nodes` asserts that fact-ness
must not flip (`debug_assert_eq!` at `kb/mod.rs:6187`, guarding WI-812's
`bodied_rule_counts` gate). A sweep that PREPENDS a goal to a body-less clause would
trip it. See §5's body-less boundary.

## 2. What already exists for §2 — measured

The ticket's "HOW IT COMPILES" table is accurate; three of its four rows are built.

| step | site | state |
|---|---|---|
| head stripped to the bare `?x` | `parse/convert.rs:1114` mints a `typed_var` marker; `kb/load.rs:19670` strips it | **exists** (WI-582) |
| bound installed on the rule | `kb/mod.rs:7584 install_rule_type_bounds`, read back by `rule_type_bounds` | **exists** |
| column type from the bound | `typing.rs:9057` — `relation_clause_columns` reads `type_bounds` FIRST, then inference, then a fresh var | **exists** (WI-714/WI-741) |
| `domain(?x, T)` body goal | — | **the whole of the new work** |

**The refusal that stands between them** is `kb/load.rs:28639`: with any bound present,
a rule that is not `is_directional_equation` is refused as
`TypedPatternNotEnforced { reason: NotARewrite }` and the bound is **not installed**.

MEASURED 2026-09-08 (`anthill load`, three separate files so each shape is attributed):

| written | today |
|---|---|
| `rule f(?x: Colour) :- palette(c: ?x)` | refused — `WI-582: … enforced only where the resolver fires a directional rewrite` |
| `rule g(x: Colour) :- palette(c: x)` | head **loads** (`x: Colour` is an ordinary named argument passing the sort as a value, 055); the body's bare `x` is `type mismatch in x.name: expected resolved name, got unresolved` |
| `fact h(?x: Colour)` | refused **earlier and elsewhere** — `WI-582: a variable type annotation (?x: T) is only meaningful in a rule head pattern` (`load.rs:19756`), i.e. the `in_rule_head` flag is not set for a fact head |

The third row is the surprise and it is load-bearing for §5: the body-less case never
reaches the `NotARewrite` refusal at all, so lifting that refusal does **not** admit
`fact h(?x: T)`.

### 2.1 The three-valued read already exists, collapsed

`typing.rs:64430 typed_pattern_bounds_hold` computes exactly the §2 decision and then
throws two thirds of it away: `value_type_term` (WI-578) for the carried type,
`sort_functor_of_view` for "is it determined", `types_compatible` for conformance —
and returns `bool`, mapping *refuted*, *under-determined* and *slot did not match* all
to `false` ("don't fire"). That is right for a rewrite, whose only two outcomes are
fire and don't. The goal needs the split, so §4 factors the decision out and leaves
`typed_pattern_bounds_hold` as its boolean caller — one predicate, two readers, rather
than a second implementation that can drift.

## 3. Where the goal is produced — the site decision

Three sites are possible; take the third.

- **The converter** (where `require[X]` is lowered). Rejected: at convert time `T` is
  an unresolved parse-level name, and the bound's own resolution already happens in the
  loader — generating here would make the goal's `T` and the bound's `T` two
  resolutions of one annotation, which is exactly the one-name-two-questions defect.
- **The loader**, beside the bound install at `load.rs:28639`. Possible — the DeBruijn
  index and the resolved bound term are both in hand — but the body nodes at that point
  are pre-`type_rule_bodies`, so a generated goal would be walked by the dot-dispatch
  and type-collection passes as if the author had written it.
- **A typing sweep**, beside `record_find_dictionary_grounding` (§1). **Take this.**
  `rule_type_bounds` is installed, `rule_globals` gives the DeBruijn frame, the body is
  settled, and `set_rule_body_nodes` is the supported write. The goal is built from
  `(db_index, bound_tid)` — no new variable is allocated, because `?x` is a head
  variable that already owns a slot.

Ordering inside the typing pass: **after** `type_rule_bodies` and **before**
`check_rule_body_requirements`. The generated goal must be visible to the WI-642 static
requirement check for §8's anchor to be readable there, and it must not be visible to
`collect_rule_var_types` — the bound is that pass's *input*
(`relation_clause_columns:9057`), and a `domain(?x, T)` goal in the body it re-reads
would make the column type derive from the goal that derives from the column type.

## 4. The `domain` goal — a new delayable builtin

Model it on `resolve.rs:4879 builtin_is_entity_of`: walk both args, `delay()` on an
unbound operand, verdict otherwise. What differs is that the type read is the CARRIED
type, and that the middle outcome is a third value rather than a failure.

```
domain(?x, T)
  ?x unbound                      → BuiltinResult::delay()     -- rotation re-asks
  carried type under-determined   → BuiltinResult::delay()     -- WI-067: never NAF-decide
  conforms                        → Success
  refuted                         → Failure
```

- **The carried type is `value_type_term(kb, subst, &x)`** — the full stored term, never
  collapsed to a head symbol (proposal 060's rule, and the 2026-08-07 terminology
  correction on WI-742). Conformance is `types_compatible`; for a nominal sort bound
  that is subsort, for a spec bound it is `provides`. All three are the calls
  `typed_pattern_bounds_hold` already makes.
- **REORDERABLE** (`resolve.rs:9825 builtin_is_reorderable`). `domain(?x, T)` denotes a
  property of the VALUE, so "suspend now, re-ask after rotation" is equivalent to "ask
  now" — the `neq` side of WI-739's split, not the `nonvar`/`ground` side. Getting this
  wrong is measurable in exactly the way WI-739 records: a non-reorderable classification
  collapses `f(?x: Colour) :- palette(c: ?x)` from its rows to one floundered residual,
  because the whole rule delays before its own generator can bind `?x`.
  The default is reorderable (the predicate is a `!matches!` over three tags), so this
  is a decision to RECORD and drive, not code to add — and per the new-variant census
  rule, the negated `matches!` says YES to a new tag silently.
- **Still unbound at the end** is not the builtin's decision: an undischarged delayed
  goal residualizes, and the WI-737 route (`eval/effects.rs:731`) raises
  `Error[RelationFloundered]` when a floundered relation is drained. §2's "flounder
  loudly" is that existing route, reached because the goal is ordinary — it needs
  driving as acceptance, not new machinery.
- **Naming.** The goal is a kernel relation like `find_dictionary`
  (`parse/desugar_target.rs:198`), reached only by generation; `domain` as a *user*
  member relation (§2.2 / WI-743) resolves by the ordinary ladder. Two things, one name,
  and the plan is that WI-743 makes the builtin's (out) arm dispatch to the member —
  so the builtin must be registered under a desugar target the surface cannot reach
  bare, exactly as `find_dictionary` is (WI-909 removed it from the implicit prelude).

## 5. Lifting the WI-582 refusal — what stays refused

At `load.rs:28639` the `NotARewrite` arm becomes a three-way classification:

| head | today | after |
|---|---|---|
| directional equation (`[simp]`/`[unfold]`, bodyless) | bound installed, enforced at `apply_eq_rules` | **unchanged** |
| typer-fired dot rule | refused (`DotRule`, WI-903) | **unchanged** |
| untagged equation | refused (`NotARewrite`) | **unchanged** — no body to prepend to, no wakeup site |
| **relational head with a body** | refused (`NotARewrite`) | bound installed; §3 generates the goal |
| **relational head, body-less** (`fact h(?x: T)`, `rule h(?x: T)`) | refused at `load.rs:19756`, a different error | **unchanged** — see below |

The body-less relational case is refused today by the `in_rule_head` flag never being
set for a fact head, and it must STAY refused in WI-742: prepending to an empty body
flips fact-ness and trips `set_rule_body_nodes`' assertion (§1), and the shape's only
sound meaning — "h holds of every T" — is §2.2's enumeration, which is WI-743's. Its
message names a reason that will no longer be true once relational heads are typed
("only meaningful in a rule head pattern"), so it is reworded, not re-scoped, in this
change: *a body-less head has no body to carry the generated guard; give it a body, or
wait for the sort's `domain` (WI-743)*.

`NotARewrite`'s doc comment and `typed_pattern_refusal_detail`'s wording both name the
equational shape as the only admitted one; both are part of the change. So is
`docs/constrained-term-substrate.md:389`'s "*Enforcement scope (deliberate)*", which is
the sentence WI-742's premise correction reads as the whole justification.

## 6. §2.1 — the parameter form, classified by resolved category

The proposal's four steps map to one new decision in the loader's head conversion.

- **Parsing is unchanged.** `p: Person` already parses as a `named_arg`
  (`tree-sitter-anthill/grammar.js:1309`).
- **The discriminator is the resolved head functor**, never case. `subject_introduces` /
  `rule_introduced_functor_name` already answer "what does this head introduce"; where
  it is the rule's own defined predicate, each top-level `name: Type` argument becomes a
  typed clause-variable introduction; where it is an **entity constructor**, named args
  are untouched.
- **CENSUS, re-measured 2026-09-08** (depth-aware scan of top-level head arguments over
  `stdlib/`, `examples/`, `anthill-todo/`, `rustland/anthill-stl/` — the earlier
  2026-08-07 figure was a textual scan restricted to lowercase functors): **87** rule/fact
  heads carry a top-level `name: …` argument, and **all 87 resolve to an entity
  constructor** (`Covariant`, `TypeMapping`, `IncludeMapping`, `EffectMapping`,
  `NamingConvention`, `CppEnumValue`, `KnownContact`, `InMailbox`, `Module`,
  `StoreFormat`, the four webots bound facts, plus the two lowercase ones the earlier
  scan found, `palette` and `parent`). **The reclassified population is empty.** The
  loader-verified re-measurement still belongs AT the classification site — a textual
  scan cannot see a head whose functor resolves to a predicate in another file.
- **Everything else stays a named argument**, because a sort is a legal argument value
  (055): `f(kind: Int)` passes the type `Int` as data.
- **Bare `p(x, y)` is NOT an error, and must not become one** — see §10's third
  acceptance-row correction. It is a symbolic constant, which is a supported idiom, so
  this form's typo reads as a constant column rather than as a dead clause.
- **A `ParseAux` NAMED child is FILTERED**, with the same predicate the generic head
  conversion filters by (`visible_named`), so a head carrying the rule-level `[A]`
  type-variable introducer is reclassified like any other. Handing one to `convert_term`
  unfiltered reaches its `unreachable!` — MEASURED as a PANIC. A POSITIONAL `ParseAux`
  still declines, because the generic walk does not filter those either, so there is no
  pre-existing behaviour to match.

  **This replaces a blanket DECLINE** (WI-20260908-PW9A0), which was justified here as
  "filtering would silently drop the bracket the author wrote". It does not: the bracket
  is read by `collect_rule_tvar_names` BEFORE the head is converted, which marks the node
  consumed, and a bracket nothing consumes is still reported by the WI-839 sweep. The
  decline's own cost was the silent one: `rule g[A](a: A, …) :- one(a, …), Summable[A]`
  kept `a: A` a named argument and its body's `a` a constant, so it LOADED CLEAN and
  answered **0** where its sigil twin `?a: A` answered **1** — a dead clause, with no
  diagnostic anywhere, which is exactly what §2.1's "both spellings, one answer" exists
  to prevent. The decline's other premise — that a `[T]` introducer inside a
  parameterized bound is unsupported in the sigil spelling too — no longer holds either;
  see `kernel-language.md` §5.3, *An introduced type variable may be written anywhere
  inside a bound*.
- **The written type takes three spellings** — bare (`c: Colour`), qualified
  (`c: lib.Colour`) and applied (`xs: List[T = Int64]`) — because the `?x: T` spelling
  accepts all three and the two lower to one internal form. Only the bare one was
  reclassified on the first cut; the other two left a genuinely dead clause (the label
  is not a term the body can match), and that WAS found by `/code-review` rather than by
  the suite.

## 7. §2.2 — WI-743's arm, and the seam WI-742 must leave

WI-742 delivers modes (in) and *delay*. WI-743 adds: derive `domain` rows for an
all-nullary closed ADT, admit a hand-written `domain` member on any sort, and make the
builtin's unbound arm enumerate through it instead of delaying.

The seam is one branch in §4's builtin. What WI-742 must NOT do is make the unbound arm
*fail* or *succeed vacuously* — both would be answers, and both would have to be
un-answered later. Delay is the honest placeholder, and it is also the final behaviour
for a sort with no `domain`.

## 8. §3 — the typed head as the second anchor — NOT DELIVERED

**Owner: WI-20260908-VVM1R**, split out of WI-742 once the rest landed — 060's
work is partitioned by section, and this was the one section that would otherwise have
had no owner.

`requirement-channel.md` §"The anchor rule" names both anchors and, when it was written,
named WI-742 as the second one's owner. WI-742 lifted the FIRST of that shape's two
refusals (a typed relational head now loads); the anchor itself is still refused.

MEASURED 2026-09-08, after the rest of this work landed:

```anthill
rule anchored(?x: Colour, ?d) :- ?d = require[Desc[T = Colour]], seed(?x)
```

still reports *expected a body call to one of `Desc`'s operations … to ground the
requirement, got no such call in the rule body* — the same error its UNTYPED twin
reports, so the annotation buys nothing here yet.

**Why it is not one disjunct.** The refusal lives in
`record_find_dictionary_grounding`, but the refusal is not the mechanism: the rewritten
goal is `find_dictionary(spec_base, op_functor, witness_args…)`, and EVERY consumer
downstream is keyed on that `op_functor` —

- `simp_guard_holds_core` reads the op's `params` to learn which argument positions
  carry the spec (`param_is_spec_carrier` / `spec_self_represented_by`, WI-596's two
  shapes), and
- `witness_sort_goal` reads the same signature to learn which spec PARAMETER each
  argument's carried type binds.

A typed head has no op. Admitting it therefore needs a second grounding path — one that
maps the head's bound directly onto the spec's carrier parameter — or a synthetic
witness, which raises three questions each needing its own measurement: WHICH op stands
in (the choice must not change the answer), what fills its CONTENT parameter positions
(passing the carrier there would bind content params to the carrier's type), and how
WI-860's supplied-vs-derived agreement reads against a dictionary derived that way.

**And the surface has already thrown away what would replace the op.** The author writes
`require[Desc[T = Colour]]` — which NAMES the binding — but the converter strips a
spec's type arguments at the guard tier (`record_find_dictionary_grounding`'s own note:
"the guard tier strips the spec's type-args at convert time, so it cannot attribute WHICH
type-parameter each `requires` names", which is why two `requires` on one spec base are
refused). So the parameter-attribution the op supplies is not recoverable from the
surface either.

That note calls the repair "Tier B (WI-613)", and the CITATION IS STALE: WI-613 is
Delivered and the strip and its refusal are both still in place — so retaining the
bracket has no live owner. Whoever takes the anchor should re-read that comment rather
than trust its ticket number.

**The shape of the fix, for whoever takes it.** The grounding is STATIC: the bound is a
`TermId` at load, so `sort_provides(bound_sort, spec_sort)` is decidable at typing —
which is proposal 060's own rule (selection happens in the typing pass) and is a
stronger position than the witness path, not a weaker one. What is needed beside it is a
carrier-to-parameter map that does not come from an op: WI-596's two shapes answer it
differently (a self-representing spec names its carrier by the SORT, so the bound maps
straight onto it; a carrier-parameter typeclass names it by a type-parameter, which is
what the stripped bracket would have said). Deliver the type-argument retention first,
or restrict the first cut to the self-representing shape and say so.

**Acceptance, when it is taken.** `p(?x: T, ?y) :- ?d = require[Eq[T]], f(?x, ?y, ?d)`
loads and threads; the UNTYPED twin stays refused (the control that says the annotation
is what grounds it); and a typed head whose bound does NOT provide the spec stays
refused.

## 9. C666A — the guarded join

The interim gate is `load.rs:17455 unguarded_non_enclosing_predicate_join_target`,
called from the refusal loop at `load.rs:5089`. Both its doc and
`LoadError::UnguardedNonEnclosingPredicateJoin`'s already name WI-742 as the third
admitted case; the spec says the same at `kernel-language.md:2217`.

MEASURED 2026-09-08: the two-implementor program written with typed heads
(`rule p(?x: A)` in `sort A requires Spec`, `rule p(?x: B)` in `sort B requires Spec`)
reports **four** errors — two C666A refusals AND two WI-582 refusals. Both must lift
for the ticket's acceptance to run, and each is its own back-out.

**The structural obstacle**: `RuleHeadSite` (`load.rs:9481`) carries `file_idx, scope,
prefix, name, introduced_by, span` — no arguments — and the C666A loop runs inside
`scan_definitions`, BEFORE any rule is asserted, so `rule_type_bounds` does not exist
yet. The head's parse term IS in hand at the collection site
(`RuleHeadCollectPass::collect` holds `subject` and `parse_terms`,
`load.rs:9827-9836`), so the fix is a new `RuleHeadSite` field recording the head's
type annotations, resolved at the refusal loop (which already sets `asking_file` and
can resolve names).

**The admission is narrow, and stated as a predicate, not as "has an annotation"**: the
join is admitted when the generated guard selects the CONTRIBUTING carrier — the sort
whose `requires` / `provides` edge exposed the predicate, or, for a wildcard import,
nothing (a namespace is not a carrier, so a wildcard-import join has no carrier to
select and stays refused). Writing this as "any typed head may join" would admit
`rule p(?x: Int64)` inside `sort A requires Spec`, which selects nothing about `A` and
is precisely the silent-append C666A exists to stop.

## 10. Build order — what happened

Steps 1–7 landed as described; the notes below record where the plan was wrong.

**§5's body-less boundary was wrong, and measurement is what corrected it.** The plan
said a body-less relational head must keep a refusal, because prepending to an empty
body flips fact-ness under `set_rule_body_nodes`' assertion. Two measurements moved it:
`rule p(?x: T) :- true` folds to an EMPTY body (§6.1) and is nonetheless a CLAUSE — it
answers `p(5)` where the bare declaration `rule p(?x)` does not, the latter never
reaching an assert at all — and the ticket's own C666A acceptance is written in exactly
that spelling. So the flip is handled rather than forbidden, by
`KnowledgeBase::prepend_generated_body_goals`, which maintains the WI-812 gate;
`set_rule_body_nodes` keeps its 1:1 contract for its existing caller. The refusal
variant the plan called for was written, found unreachable, and deleted rather than left
as a branch nothing can drive.

**One acceptance row rested on a false premise, in the ticket rather than the code.**
WI-742's acceptance says `rule f(?x: String) :- eq(?x, "abe")` "MUST work and yield one
row". It does not, and not because of this feature: `eq` is a semantic equality TEST
that never binds (§8.3), so the UNTYPED twin residualizes identically — measured. The
capability the row means to pin is delay + rotation + re-ask, and its correct spelling
is `<=>`, which binds (proposal 049). Pinned that way, with the untyped control beside
it.

**A third acceptance row is false, and making it true would break a supported idiom.**
"An untyped bare head name remains a loud unresolved-name error" — it was not loud, and
it must not become loud. An unresolved bare name in a clause head is a SYMBOLIC
CONSTANT: `fact q(alpha, beta)` beside `rule p(alpha, ?y) :- q(alpha, ?y)` works because
both spellings of `alpha` intern to one unresolved `Ident` and UNIFY, which is exactly
what a refusal's wording ("it would ride as a term that unifies with nothing") denies.

The refusal was BUILT — censused first at zero across `stdlib/`, `examples/`,
`anthill-todo/`, `rustland/anthill-todo/anthill/` and `anthill-stl/` — and then measured
breaking three `parse_test` rows on `fact WorkItem(id: "WI-001", …, status: Open)`,
where `Open` is a `WorkStatus` variant the standalone fixture never declares and the
matching query spells identically. The corpus census was a LOWER BOUND: it covered
`.anthill` files and not the Rust fixtures, which are the second population and where
the idiom actually lives. Backed out; §2.1's typo therefore reads as a CONSTANT COLUMN
rather than as a variable, a different meaning rather than a dead clause.

Separating the typo from the idiom would need a whole-program "nothing ever matches this
constant" analysis, which a load check is not. Recorded at
`convert_rule_head_with_params`, pinned by
`an_unresolved_bare_head_name_stays_a_symbolic_constant`.

**What `/code-review` found, all fixed and pinned.** The parameter map was loader-scoped
rather than clause-scoped, so a later item's identically-spelled datum became the rule's
variable (`fact seen(name)` asserted a free variable); a qualified or parameterized
parameter type was not reclassified at all, leaving a genuinely dead clause where the
`?x: T` spelling worked; and the C666A admission read only the `typed_var` marker, so
the two spellings of one internal form diverged at that boundary.

## 10.1 The planned build order



Each step is separately measurable; the numbered order is a dependency order, not a
suggestion.

1. **Factor the three-valued decision** out of `typed_pattern_bounds_hold` (§2.1),
   leaving it as the boolean caller. No behaviour change — the control is that
   `wi582_typed_rule_pattern_test` passes unchanged.
2. **The `domain` builtin** (§4): desugar target, `BuiltinTag`, the four-outcome
   dispatch, reorderability recorded and driven. Not yet reachable from source —
   acceptance is a hand-built goal.
3. **Lift the refusal + generate the goal** (§5, §3). This is the step that makes
   `rule f(?x: Colour) :- palette(c: ?x)` load, filter, and type its column as
   `Colour`. The back-out that must fail: re-install the `NotARewrite` arm for a bodied
   relational head.
4. **Drive the column type** — `Relation[(x: Colour)]` through the already-wired
   `relation_clause_columns`, and the multi-clause disjoint-bound load error (052's LUB
   rule, no new machinery — assert it rather than assume it).
5. **§2.1 classification** (§6) with the loader-verified census at the site, plus the
   entity-constructor control and the bare-name control.
6. **§8 anchor** — one disjunct, two back-outs.
7. **§9 C666A** — the `RuleHeadSite` field, the carrier-selecting predicate, and the
   wildcard-import control that must STAY refused.
8. **Docs**: `kernel-language.md` §5.3 (:2152, :2174, :2217, :2304) and this file's §0
   table, for the delivered subset only. Proposal 060 keeps its text
   (`spec absorbs it, proposal keeps its text`).

## 11. Boundaries this plan does not cross

- **The map-colouring `Palette` wrapper is not retired here.** WI-742 stops the column
  TYPE depending on the entity field; the facts still generate. Retirement is WI-743.
- **A `[simp]`-tagged relational head** — proposal §2's open (4). The tag is meaningless
  on a `:-` head; today it is what the WI-582 guard DEMANDS, which is backwards. Decide
  and state it at step 3; do not leave the tag silently accepted-and-ignored.
- **`?x: T` in a rule BODY** stays refused (`load.rs:19756`'s other reader) — the
  annotation is a head-position declaration.
- **The typer-side enforcement gap** (`simp_rewrite.rs` skips a bound-carrying rule
  outright, WI-903) is not closed by this work and is not widened by it.
