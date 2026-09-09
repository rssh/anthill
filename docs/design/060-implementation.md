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
| §3 anchor (typed-head half) | `?x: T` grounds the spec | **WI-20260908-VVM1R** | **design settled, not built** — §8, mechanism at §8.2–§8.6 |
| channel §10 item 1 | retain the spec's type-args | **WI-20260908-VVM1R** | **settled, not built** — §8.6, taken inline |
| §3 anchor, CHECK tier | `requires(X)` under an anchor | **WI-20260909-QMFC5** | **delivered** — emits the same goal as the bind tier, §8.8 |
| channel §10 item 3 | op→rule dictionary channel (polytypes) | **WI-20260909-NAR1X** | **settled, not built** — §8.10 |
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

## 8. §3 — the typed head as the second anchor — DESIGN SETTLED, NOT BUILT

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

**The surface throws away what would replace the op — and that is what this ticket
removes.** The author writes `require[Desc[T = Colour]]`, which NAMES the binding, but
both producers (`lower_require`, `rewrite_requires_goal`) call `strip_spec_type_args`
(`convert.rs:3672`), which rebuilds the spec instance as a bare nullary `Fn`. Measured:
`require[Desc]` and `require[Desc[T = Leaf]]` are byte-identical after convert.

`record_find_dictionary_grounding`'s note calls the repair "Tier B (WI-613)", and the
CITATION IS STALE: WI-613 is Delivered. The live owner is `requirement-channel.md`
§10 item 1, and it is **taken by this ticket** (see "The un-strip" below).

## 8.1 MEASURED 2026-09-09 — the surfaces, before any change

`Desc` is a carrier-PARAMETER spec (`describe(x: T)`, no parameter typed `Desc`), `Leaf
provides Desc[T = Leaf]` supplying `7` against the default `1`.

| # | clause | today |
|---|---|---|
| a | `rule anchored(?x: Leaf, ?d) :- ?d = require[Desc[T = Leaf]], seed(?x)` | refused — "no body call to one of `Desc`'s operations" |
| b | the UNTYPED twin | refused, **identical message** |
| c | (a) + `Desc.describe(?x, ?r)` | loads, **7** — the witness path |
| d | `rule anchored[A](?x: A, ?d) :- ?d = require[Desc[T = A]], …` | refused TWICE — `WI-582: type-variable A has no bounding guard` **and** the grounding refusal |
| e | (d) + `Desc[A]` as the bounding guard | refused ONCE — grounding only |
| f | `rule anchored(?x: Leaf) :- requires(Desc[T = Leaf]), seed(?x)` | refused, same message — the CHECK tier needs the anchor too |
| i | `?x: Plain` (does not provide) + `require[Desc[T = Plain]]` | refused with the SAME message — right verdict, WRONG reason |
| j | `?d = require[Desc]` + typed head | refused, byte-identical to (a) |
| k | `rule anchored[A](?x: A) :- Desc[A], seed(?x)` then `Desc.describe(?x, ?r)` | **loads, 7** — dispatch already works with NO `require` |
| m | `rule anchored[A](?x: A) :- Sp[C = A], seed(?x)` | refused — `try_body_tvar_guard` takes only a single POSITIONAL arg |

Row (k) is the one to keep in view: a covered call under a typed head already
value-dispatches correctly with no dictionary anywhere. C666A is delivered and driven
(`wi742…::a_typed_head_may_join_the_predicate_its_carrier_exposes`), so §9's "both must
lift for the ticket's acceptance" was WI-742's own and is not inherited here.

## 8.2 The attribution is NOT missing — it has an owner

The paragraph this replaces said a carrier-to-parameter map "does not come from an op"
and had to be invented. **It exists.** `spec_carrier_param_or_sole` (`typing.rs:34990`,
WI-1102 over WI-1076's `spec_carrier_param`) answers WHICH type parameter of a spec the
carrier goes in, op-independently, on two rungs: the param some declared operation
*receives on* (first in the sort's declared order), else a SOLE parameter gated on
not-self-representing. Memoized; measured over stdlib + host bindings at its own site.

It is a DIFFERENT question from `param_is_spec_carrier` (WI-596), which classifies a
call's ARGUMENTS and answers a SET — `set(target: T, value: V)` says both. The anchor
needs the first.

**A new consumer owes the second gate**, and the predicate's own doc says so: it answers
"which parameter an operation takes", which is not by itself "which parameter names the
carrier" (measured there: `touch(c: Spec, x: P)` answers `P`, the accepted argument;
XZMGC's reader needed `composed_self_reference` beside it). The gate here is agreement
with the bound's own provision row — used as a CHECK, never as the producer, which would
be circular.

**Two rungs remain genuinely absent**: a self-representing spec (no param to pin — the
carrier is the sort, and `witness_sort_goal`'s self-representing branch already builds
`GoalCarrier` from the value's type and args), and a multi-parameter spec with no
receiving operation (`None` ⇒ located refusal).

## 8.3 The bound is TWO different things, and that is the discriminator

- **Concrete** (`?x: Leaf`, row a) — the bound IS the carrier. Test `sort_provides(bound,
  spec)`. This is also the C666A shape, `rule p(?x: A)` inside `sort A requires Spec`.
- **Introducer** (`rule p[A](?x: A) :- Desc[A]`, row e) — after WI-582's substitution the
  recorded bound IS THE SPEC (`load.rs:20262-20268`: `rule_head_bound_alias` returns the
  bound symbol, then `make_sort_ref`). Test `bound == spec`.

Opposite staging, one channel (`rule_type_bounds`), and the two tests do not overlap.

## 8.4 The transform — a compiled PROJECTION, not a compile-time dictionary

At `record_find_dictionary_grounding`, for a clause with a non-empty `rule_type_bounds`
whose witness scans all miss:

1. `p = spec_carrier_param_or_sole(kb, spec)` + the §8.2 gate. `None` + self-representing
   ⇒ no param to pin; `None` otherwise ⇒ located refusal.
2. Pick the anchoring head variable from `rule_type_bounds` by §8.3's test. ZERO ⇒ a
   located refusal naming sort, spec and the missing `provides` — row (i) is refused for
   the WRONG reason today, so the acceptance control does not discriminate until this
   exists.
3. Emit `find_dictionary(spec_base, ⟨carrier⟩, ?x, out: ?d)` — the carrier slot replacing
   `op_functor`.
4. Run time reads `typeof(?x)` through the same `value_type_term` the witness path uses,
   pins `p ↦ that type`, and X9PB4's wildcard loop fills the rest. `simp_guard_holds_core`
   collapses to a direct `sort_provides` — there are no op params to consult, so the
   op-keyed consumer is BYPASSED rather than generalized.

This is §2.1 exactly: the PROJECTION is compiled, the FETCH reads a carried type.

**THE BOUND IS NOT THE CARRIER, and step 4 reads `typeof(?x)` for that reason.** The
bound is an UPPER bound — `bare_sort_compatible` admits the sort, its
`sort_sym_compatible` relatives, and any sort that PROVIDES it — so the bound picks WHICH
head variable anchors the spec (step 2) and never stands in for the carrier value.
MEASURED, per shape:

- **spec bound** (the introducer form) — row (k): the recorded bound is `Desc`, the
  runtime carrier is `Leaf`. Different BY DESIGN; the clause is polymorphic over every
  `Desc` provider, and only a carried-type read names the one in hand.
- **data-sort bound** (`?x: Leaf`) — the gap is structurally closed, and loudly: a
  `provides` onto a constructor-declaring sort is refused — *"'Base' declares
  constructors, which makes it a DATA sort, and nothing is-a a data sort — a provision
  would let 'Sub' widen to it"*. So nothing can be narrower than the bound here.
- a bare PARAMETERIZED bound (`?x: List`) admits every instantiation, and a conditional
  provision follows the instantiation.

So a compile-time *dictionary* — splicing a constant instead of reading — is sound only
when ALL THREE hold: the bound is a data sort, fully applied, and its provision
unconditional. Narrow enough that it is recorded here as a boundary rather than planned
as an optimization; taking it would also have to answer WI-860 (the agreement check lives
in `read_dictionary_into`, which a spliced constant never reaches).

NOT monomorphization — specializing the clause per provider. Conditional provisions make
the family unbounded (`Pair provides Eq[Pair] :- Eq[A], Eq[B]`) and it changes the clause
population the discrimination tree indexes.

## 8.5 Two anchors are TWO dictionaries — the implicit-parameter reading

The annotated head variables ARE the implicit parameters: one dictionary per (spec,
anchor), each bound to its own variable, threaded into the calls that need THAT carrier.
This is the channel doc's own sentence — "the call site drives it; `require[X]` is only
the explicit form", which "simply pre-binds one of those variables" — with the anchor as
the slot source. So a clause with two typed head vars both providing one spec is NOT
refused; only attributing a WRITTEN `require` between them needs the bracket.

**DELIVERED by WI-20260909-96ZTM, and NOT by changing the weave.** Two `require`s on one
spec bind two dictionaries, each attributed by its own written bracket, ADMITTED where
every one of them is grounded by a TYPED HEAD ANCHOR — the only place the bracket is read.
Where one is grounded by a body call instead, the old refusal stands: a witness is chosen
by scan ORDER, so nothing there can say which dictionary a `require` names.

**The weave was NOT rewritten, and that reverses this section's earlier plan.** An attempt
that made `weave_covered_call` a single accumulating pass so one call could carry two
dictionaries was measured wrong twice over: it broke NESTED covered calls on a SINGLE
`require` (a panic in debug, the spec default in release), and the shape it enabled has no
reader — `dictionary_dispatch_target` destructures a one-element slice and eval rejects
more, because `requirements` answers "which instance does THIS CALL dispatch on" and one
call dispatches on one instance. The claim that "`apply_within` needs nothing — the list is
already a list" was false: the list exists, its consumers do not.

N dictionaries AT A CALL SITE already work, through a different channel: a callee's own
`requires` travel the SLOT-indexed `op_dicts` (`op_dict_entries` →
`build_op_scoped_dicts` → `push_op_scoped_slots`, WI-822), which is N-ary and has a
reader. Two `requires` on one sort already ship (`prelude/field.anthill`). That is a
different question and needs nothing from here.

So a call two dictionaries both claim is REFUSED, and carrier direction — which would have
picked one — was implemented and REMOVED when backing it out failed zero rows: a covered
call that names a carrier and is not itself a witness does not exist in this design.

## 8.6 The un-strip — DELIVERED by WI-20260909-51W18 (channel §10 item 1)

MEASURED 2026-09-09 by making `strip_spec_type_args` the identity:

| bracket | stripped (HEAD) | un-stripped |
|---|---|---|
| `require[Desc[T = Leaf]]` | loads, 7 | **loads, 7** |
| `require[Desc[Leaf]]` | loads, 7 | **loads, 7** |
| `require[Desc[T = T]]` | loads, 7 | `unresolved name 'T'` |
| `require[Desc[T]]` | loads, 7 | `unresolved name 'T'` |
| `requires(Desc[T])` | loads, 7 | `unresolved name 'T'` |
| `require[Desc]` | loads, 7 | loads, 7 |

**The split is CONCRETE vs VARIABLE, not named vs positional** — the named form breaks
too, so the `type_args` ParseAux channel is not already carrying it. A concrete bound
already survives un-stripping in BOTH spellings, which is the whole of what §8.3's
concrete arm needs.

**Blast radius: 33 of 4338 `wi_tests`, ZERO shipped programs.** `grep -rn 'requires(\|require\['`
over stdlib + examples + anthill-todo returns one hit, a rule NAMED `sort_requires`. All
33 are one cause — the free-tvar bracket — reported either as the raw `unresolved name`
or as the fixture's own expectation string (`wi642:116` `requires(Relatable[T])`,
`wi625:324` and `wi625:648` `requires(Eq[T])`).

**AS BUILT — and two predictions in this section were wrong, corrected here rather than
deleted.**

The channel is `Loader::build_require_spec_occurrence`, which resolves each binding value
through **`parse_arg_sort_symbol`** — the one owner of "does this name denote a sort", the
same one the §2.1 parameter form's bound reads. It is NOT `type_expr_to_child`'s
`TypeExpr::Simple` arm, which this section named: that arm takes a `TypeExpr`, and a
require bracket is a parse `Term::Fn` whose binding values are plain `Term::Ref` names
(measured: `Desc[T = Leaf]` → `Fn(Desc, named:[(T, Ref(Leaf))])`; `Desc[Leaf]` →
`Fn(Desc, pos:[Ref(Leaf)])`; `Desc` → `Ref(Desc)`).

**The head-introduced tvar rung needed no gate widening.** This section predicted it as
"the widening with the largest blast radius in this ticket", because
`rule_head_bound_alias` is gated on `in_rule_head_bound` and WI-20260908-PW9A0 narrowed
that deliberately. `parse_arg_sort_symbol` asks `rule_head_tvar` **unconditionally** — it
"must answer before any conversion happens" — so the rung came for free, and
`in_rule_head_bound` was not touched.

**A name denoting no sort is DROPPED, not lowered to a wildcard.** Equivalent in effect
and simpler: the binding is absent from the stored goal, which is byte-identical to what
the convert-time strip produced, so `witness_sort_goal`'s X9PB4 loop synthesizes the same
wildcard it always did. Nothing new constructs one. `requires(Eq[T])` — the canonical
typeclass spelling, whose whole point is that `T` is unconstrained — stays writable, and
the change is STRICTLY ADDITIVE.

**But the drop is sound only because POSITIONALS ARE PAIRED WITH THE SPEC'S DECLARED
PARAMS FIRST**, and that equivalence is exactly where a first cut was wrong. Keeping
positionals positional made a dropped one silently RE-INDEX the rest:
`requires(Desc[Zork, Leaf])` stored `Leaf` — the SECOND argument — at slot `#0`,
attributing it to the first type parameter, on a clean load with no diagnostic, in the
slot S2 is specified to read. Found by `/code-review`, driven, and fixed by paying the
attribution up front (`canonicalize_fact_binding_value`'s rule, applied not re-derived);
a named binding cannot shift. Pinned by
`a_dropped_positional_does_not_re_index_the_others`, whose control writes two sorts so
the SHIFT is what moves and not the count.

**Three more things `/code-review` found and this ticket fixed rather than deferred**: a
nested application whose head is a head-introduced type variable reported `unresolved
name` (the recursion's base fell to `remap_symbol_strict`, whose alias is gated on
`in_rule_head_bound` — two resolvers answering one question, now one); a written effect
row `Spec[E = {}]` was silently dropped (a `ParseAux` carrier, not a name, so the drop
rule never covered it — `lower_effect_row_aux_occ`, as the ordinary loop does); and this
slot bypassed the `check_sort_type_args` its sibling walk runs, so `Desc[Bogus = Leaf]`
and an over-application both loaded clean and stored the bogus binding.

**ONE WALK, NOT TWO.** A first cut also wrote the term-side lowering
(`convert_term_inner`'s `Term::Fn` arm), on WI-742 §2.1's precedent that a head rides one
walk and a body the other. MEASURED: the whole binary passes with that arm disabled,
because a rule BODY is stored as occurrences (WI-246 — "the term body is gone") and
`require[…]` is legal only as a body goal. It was deleted rather than kept undrivable.

**The rewrite carries the instance too.** `make_witness` used to re-mint slot 0 as a bare
`Expr::Ref(spec_base)`, which would have erased the retention one phase later — the two
spellings would still produce identical stored goals. It now pushes the instance whole;
every reader of that slot asks for the HEAD and an `Apply` answers it (`occ_head_symbol`,
and the resolver's `head_symbol` over `ViewHead::Functor`).

**Delivered controls**, measured by mutating each site: RETENTION 3 rows, THE DROP 3 rows
here + **33 elsewhere** (`wi1040` 9, `wi625` 7, `wi_x9pb4` 6, `wi1045` 5,
`kernel_mint_address` 3, `wi1098` 2, `wi642` 1), THE WHOLE ARM 4 rows — and notably NOT
the retention rows, because once the converter stops stripping the ordinary walk lowers a
CONCRETE binding correctly on its own. The arm's job is exactly the names that do not
resolve as values. Driven by
`anthill-core/tests/include/wi_51w18_require_spec_type_args_test.rs`.

Once a written binding exists, `witness_sort_goal` has two sources for one slot. Written
beats a synthesized wildcard; written against a DERIVED CONCRETE type that disagrees is a
new refusal (WI-860's shape, one tier down). ~~Nothing decides that today because nothing
can.~~ **DELIVERED for the anchor path by WI-20260909-QMFC5**, and it is the retention's
first real reader: `anchor_grounding` holds both the written bracket and the bound its
anchor selected, so `?x: Leaf` under `require[Desc[T = Other]]` — which loaded clean and
answered `7`, `Leaf`'s dictionary, ignoring the author's explicit `T = Other` — is now a
located refusal naming both. Only a CONCRETE disagreement refuses; a binding naming a type
variable was already dropped as a wildcard upstream.

STILL UNDECIDED ON THE WITNESS PATH, and the reason is a signature rather than a rule:
`fetch_dictionary` takes `(spec_sort, op_functor, arg_vals)` and never sees slot 0, so
`witness_sort_goal` still replaces a written binding with a synthesized wildcard. That is
what makes a self-representing spec whose provider pins a sibling concretely DELAY
(`a_self_representing_spec_whose_provider_pins_a_sibling_concretely_delays`) — the author
wrote `Cap[P = Int64]`, the provider binds `P = Int64`, and they never meet.

`try_body_tvar_guard`'s two limits (drops the guard's parameter position; refuses
`Sp[C = A]` — row m) become cosmetic once §8.2 supplies the attribution: they restrict
which SURFACES row (e) accepts, not whether the mechanism works.

## 8.7 Acceptance

The old acceptance spelled it `p(?x: T, ?y) :- ?d = require[Eq[T]], f(?x, ?y, ?d)`. **That
clause does not load, for a reason unrelated to this ticket** — row (d), `T` has no
bounding guard. Use the introducer form.

Row (e) LOADS and THREADS, and row (a) with it: the covered call dispatches through the
dictionary the annotation grounded, asserted BY VALUE. Controls, each stated at its site:

- the UNTYPED twin (row b) stays refused — what says the ANNOTATION is what grounds it;
- a bound that does NOT provide (row i) is refused with its OWN located message, not the
  grounding one;
- a clause with BOTH a typed head and a covered witness call answers exactly as today (row
  c/h: `7`) — the witness path is not displaced.

**The fixture must use a spec op that is COVERED but cannot be a WITNESS**
(`op_has_spec_carrier_param` false — a nullary / all-content op). Rows (c) and (h) show a
bodied `Desc.describe` call is simultaneously witness and covered call, so the obvious
fixture passes entirely on the existing witness path and never exercises the anchor.

## 8.8 The check tier — the anchor reaches it, and it emits the same goal

**`requires(X)` under a typed-head anchor gets the anchor** (user's call, 2026-09-09) and
is lowered to the **same runtime goal the bind tier emits, minus `out:`**.

### The first draft resolved it at LOAD, and that was wrong — three measurements

This section used to say the tier was "decided at LOAD, not lowered to a runtime goal",
on the argument that there is no residual runtime question in either shape: a data-sort
bound cannot be widened so the carrier IS the bound, and a spec bound has the
annotation's own `domain(?x, Spec)` goal. Both clauses are true. **The conclusion does not
follow**, and `/code-review` drove three counterexamples, each a program where the
load-time verdict said SATISFIED and the identical clause one spelling apart left a
residual:

| hole | fixture | check tier said | bind tier said |
|---|---|---|---|
| **conditional provision** | `Wrap provides Sh[T = Wrap] :- Sh[A]`, carrier `wrap(bad())` | `?r = 1`, definite | residual |
| **`sort_refines`** | `sort Sub { requires Leaf }`, provides nothing | `?r = 1`, 1 solution | no solutions |
| **witness-supplied provision** | `sort Rival provides Desc[T = Leaf]` | — | the anchor REFUSED at load |

The first two are the same mistake in two channels: `sort_provides` is a *base-level*,
*type-argument-blind* answer, and the bound is an UPPER bound on a sort HEAD. A structural
argument that reaches the head covers only the head — `Wrap[A = Good]` and `Wrap[A = Bad]`
are both `Wrap` and provide differently, and `sort_refines` is an edge
`bare_sort_compatible` walks that `sort_provides` never does.

**Each of the three has a different single-site repair, and every one leaves the other two
open.** That is the tell that the load-time verdict was the wrong SHAPE, not that its
predicate needed widening. The runtime goal gets all three right because it asks where the
carrier's actual type is known.

### And the arm could empty a rule body

`rule fe: f(?x: Leaf) <=> 1 :- requires(Desc[T = Leaf]) [simp]` has that goal as its ONLY
body atom. Dropping it left `new_body == []` and tripped `set_rule_body_nodes`'s fact-ness
assert; with `debug_assertions` off the assert vanishes, `is_equation` flips false→true,
and **a guarded rewrite silently becomes an unconditional law**. Every anchored fixture in
the test file was relational — and a relational typed head gets a prepended `domain(?x,
Leaf)` goal that keeps the body non-empty — so the whole suite shipped green over it.

### The stated objection was also wrong

"Emitting a goal would make the clause DELAY on something already decided" — the bind tier
emits this same goal in this same body position and resolves it by rotation. There was
never a delay to avoid.

### What emitting it buys

`requires(X)` IS the no-`out` case of one relation (WI-1040's "one form, one owner"). One
producer and one consumer is what makes the two spellings *unable* to disagree; a
load-time twin of the runtime verdict is a second implementation of the same predicate,
and it drifted from the original in three places before anyone read it. It also makes
`find_dictionary_guard`'s anchor branch reachable — under the load-time verdict no
anchor-form goal without `out` was ever stored, so that branch was dead code.

## 8.9 There is no "anchor with no `require`" — the real question

This section asked "automatic per anchor, or written-only?". **That dichotomy was wrong**
(user, 2026-09-09). Every dictionary need traces to a WRITTEN requirement; the only
question is WHERE it was written:

  (i) **in the rule body** — `require[X]` / `requires(X)`. This is what §8.4 grounds.
  (ii) **on an enclosing or callee declaration** — `sort S requires Desc[…]`, `operation
       f(…) requires Desc[T]`. A body call needing it is a USE of a requirement the
       author already wrote; nothing is being invented.

MEASURED 2026-09-09 for the ENCLOSING half:

| | clause | answers |
|---|---|---|
| I1 | a rule INSIDE `sort Holder { requires Desc[T = Plain] }`, body calls `Desc.describe(plain(), ?r)` | `1` — the spec DEFAULT |
| I2 | the same call with `requires(Desc[T = Plain])` written IN THE BODY | `[]` — the guard `DontFire`s, `Plain` provides no `Desc` |
| I3 | the same call, NOTHING declared anywhere | `1` |

**I1 ≡ I3**: the enclosing sort's `requires` has no effect on the clause. That is
`check_rule_body_requirements`' own documented rule — *"A Horn rule does NOT inherit its
enclosing sort's `requires` chain (that gates `[simp]`/`[unfold]` equations, not clause
bodies), so the in-body goal is the only declaration site"* — and I1 vs I2 is what it
costs: the correct spelling refuses to fire, the declared-on-the-sort spelling folds the
spec default and answers. Silently, and in the direction that produces a value.

The CALLEE half is the channel doc's *"the call site drives it; `require[X]` is only the
explicit form … the transformation reads the callee's dictionary chain
(`provider_dict_entries` / `synth_req_names`) and synthesizes one `find_dictionary` goal
per slot"*. NOT measured here — I1/I3's callee sort declares no `requires`, so that
fixture says nothing about it, and a claim either way would be unfounded.

**So the open question is: does a rule USE the requirement written on its enclosing (or
callee's) declaration?** It is a semantics change against a documented boundary, not a
gap to fill in passing, and it is DELIBERATELY not one of the filed stages — it needs a
decision first. Row (k) — a covered call under a typed head already answering `7` by
value-dispatch — is not an argument against it: value-direction happens to reach the same
answer at ONE supplier, and REFUSES at two (058 §4.9, WI-1040's two-supplier fixture),
which is exactly where inheriting would decide.

## 8.10 Build sequence — filed 2026-09-09, VVM1R as umbrella

| stage | ticket | what | depends |
|---|---|---|---|
| S1 | WI-20260909-51W18 | un-strip the spec's type-args (§8.6) — **delivered** | VVM1R |
| S2 | WI-20260909-QMFC5 | the anchor, BOTH tiers — one goal, one consumer (§8.2–§8.4, §8.8) — **delivered** | S1 |
| S4 | WI-20260909-96ZTM | two `require`s bind two dictionaries, attributed by the written bracket (§8.5) — **delivered**; the weave is NOT changed | S2 |
| S5 | WI-20260909-NAR1X | the op→rule channel for polytypes, channel doc §10 item 3 (`ResolveConfig` field seeded from `frame.requirements`) | S4 |
| S6 | WI-20260909-S8CBV | attribution by PROJECTION ROOT — the requirement channel learns to name `x.E`, and identity becomes δ/σ-conversion (`path-dependent-types.md` §4). REPLACES S4's sort-matching selector and lifts its anchored gate | S4 |

Tagged `vvm1r`. **S3 (the check tier) is FOLDED INTO S2** rather than filed, and was
delivered with it — there is no S3 ticket. The fold was justified as "a load-time verdict
riding on S2's steps 1–2, smaller than its own ticket"; **that reason is stale and the
fold is now better justified than it was**. The check tier is not a load-time verdict at
all (§8.8): it emits the same goal the bind tier does, so it is not a stage riding on S2 —
it is the SAME code path with `out:` absent, and giving it its own ticket would have
meant two owners for one relation. §8.9's question has no stage — see above.

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
