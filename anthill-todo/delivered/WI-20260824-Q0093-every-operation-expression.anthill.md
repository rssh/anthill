## Attributes

- id: WI-20260824-Q0093-every-operation-expression
- created: 2026-08-24T05:04:43Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-07T06:27:26Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260824-WAHB6-classify-a-nominal-type-once

- tags: proposal-055

## Description

EVERY OPERATION-EXPRESSION OCCURRENCE ADMITS A NOMINAL TYPE VALUE (proposal 055 umbrella A, step 2 -- the §3 matrix).

After WI-20260824-WAHB6 records the classification, make every child whose grammar/IR role is `ValueExpression` in an OPERATION EXPRESSION consume it, and pin the adjacent non-value role at each family. docs/design/055-implementation.md §3 owns the list; the fact / rule-body / metadata-of-declaration halves belong to umbrella B (WI-20260823-53W12), the dot receiver to its own ticket.

FAMILIES (each needs its own row): positional and named call/constructor arguments; operation result; `let` value and continuation; `if` condition, then, else; `match` scrutinee, branch guard, branch body; lambda body; collection, set and tuple element values including named-tuple values; parenthesized expression and infix/prefix operands; bounded-quantifier collection; `proof` conclude goal and continuation body; metadata values.

PER FAMILY, per design §9: (1) a DRIVING test that resolves or evaluates the expression and asserts the resulting `Type` value -- not that the file loads; (2) a negative destination (`String` / `Bool` where the family admits one) rejecting with `expected ..., got Type` naming the denoted sort; (3) a CONTROL pinning the adjacent non-value role -- head, callee, pattern, binder, label, member name, metadata key, `TypeExpr` child -- unchanged or loudly refused; (4) bare AND applied nominal variants; (5) at least one logical-variable argument where the type stays non-ground.

MEASURED, and it shapes the estimate: the typer walk is uniform. Bare names funnel through `check_bare_ref` at `typing.rs:10461` / `10473` / `10488` and a sort-headed application through the single Apply arm at `typing.rs:10512`, so the expectation is that this is mostly a TEST increment over WAHB6's record. ANY family that turns out to need a code arm of its own is the finding of this ticket and must be stated at that arm's site -- do not absorb it silently into "the matrix".

ACCEPTANCE (from the umbrella): `operation t() -> Type = Cell[Int64]` evaluates to the canonical type term; an unannotated `let` and a generic `id` infer `Type`; a collection of nominal types is driven and evaluated; a `String` / `Bool` destination rejects with `expected ..., got Type` naming the denoted sort; constructor, callee, head and binder controls retain their old meaning. Tests state which rows fail on back-out and which pass either way by design. Full Rust workspace via rustland/scripts/test.sh.

The matrix may ship in two commits if it runs long, but the ticket closes only with every family covered -- a partial matrix reads as "covered everything" to the next reader, so any family deliberately left out must be named in the delivery note with its reason.

## Changes

### 2026-08-24T05:55:30Z — feedback — user

SCOPE NOTE FROM WI-20260824-WAHB6's DELIVERY -- read its feedback before starting.

The widening does NOT arrive family by family. WAHB6 classifies at the loader, unconditionally, so every ValueExpression position stopped depending on the expected sort at once. This ticket therefore PINS the widening per family rather than delivering it: the driving test, the negative destination and the adjacent-role control are the deliverable, and a family that needs a CODE arm of its own is the finding to report at that arm's site.

ALREADY COVERED by `wi_wahb6_type_value_classification_test`, so do not re-file these as new rows: operation result (bare and applied), `let` value and continuation (unannotated -- the position with no expected sort at all), a type ARGUMENT inside a type application, the eponymous-constructor control, and the local-shadows-a-sort control. Everything else in design §3's operation-expression list is open.

ONE MEASURED ASYMMETRY TO CARRY: a bare STANDALONE ENTITY is deliberately still on its old arms (`check_bare_ref`'s `is_free_standing_entity` arm and its eval twin) -- see `bare_name_denotes_type`'s doc for why the predicate cannot be asked at load time. Its rows belong here, and if the matrix needs it classified, moving it needs a point that can answer `is_free_standing_entity` reliably.

### 2026-09-07T06:27:26Z — feedback — user

DELIVERED — design 055 §3's occurrence matrix PINNED per family (24 rows in
`rustland/anthill-core/tests/include/wi_q0093_type_value_occurrence_matrix_test.rs`), three CODE
ARMS produced by this ticket's own instruction ("any family that needs a code arm of its own is
the finding"), and two gaps reported rather than repaired.

THE ROWS. Every §3 operation-expression family is DRIVEN — evaluated, with the resulting `Type`
term asserted, in the bare AND applied face: positional and named call arguments; constructor
field values (read back through the field); both `if` branches; `match` scrutinee and branch
body; lambda body; list, set and named-tuple elements; parenthesized expression and both infix
operands; `proof` conclude goal and continuation; operation metadata values; the
bounded-quantifier collection; and a type argument that is an operation PARAMETER, non-ground
where written and decided by the call. Adjacent-role controls: pattern binder, lambda binder,
field label + member name, metadata key, constructor head, and a genuine `TypeExpr` annotation.

CODE ARM 1 — THE `if` CONDITION AND THE `match` GUARD HAD NO DESTINATION CHECK AT ALL. §3
admitted a type value there on the strength of "ordinary typing rejects `Type` as a Boolean
condition"; measured, it rejected nothing — `if Cell then …` loaded, and so did `if "x" then …`,
`if 1 then …` and `case x | "y" -> …`, which is the control saying the hole was never about type
values. `typing.rs::boolean_position_error` checks both slots through the predicate an ARGUMENT
gets, reporting `if.condition` / `match.guard`. It refuses nothing that loaded before (full
workspace green, measured both ways).

CODE ARM 2 — THE WRONG-DESTINATION DIAGNOSTIC NAMES THE DENOTED SORT, which §8 asks for and this
ticket's acceptance requires: `expected String, got Type` became `expected String, got Type
(Cell[V = Int64])`. `TypeError::TypeMismatch.denoted` carries the SURFACE (printed by
`TermPrinter`, so the message quotes text that would load back as what was written), filled by
`conformance_error` — the one renderer the op-argument / entity-field / let-annotation /
op-return channels share — and by the branch join for the `if` / `match` arm families. It
descends the two wrappers whose type is already their child's (`let`, in-body `proof`), and no
others.

CODE ARM 3 — THE CLASSIFIER ASKED THE PRIMARY KIND. `bare_name_denotes_type`'s own doc asked this
ticket for a row separating `kind_of` from `has_kind`. The row: `namespace Box … end` before
`sort Box … end` left `operation f() -> Type = Box` NOT LOADING, while the same two declarations
in the other order loaded and evaluated — the source-order dependence WI-926's category SET
exists to remove. Both faces ask `has_kind` now (the bare one and `build_load`'s `is_type_value`,
because they are one question about one name and keyed apart they would answer differently about
`Box` and `Box[V = Int64]`). The population the old note feared is excluded by the predicate's
own second conjunct — an eponymous constructor and a free-standing entity are both
`is_entity_constructor` — and a rule head spelled like a sort adds no kind at all (measured).

REPORTED, NOT REPAIRED — two gaps, each pinned in both directions so the report cannot rot:
(a) A COLLECTION LITERAL'S ELEMENTS ARE NOT ELEMENT-TYPE CHECKED. `List[T = String] = ["a", Cell]`
    loads, and so does `["a", 1]` — the control that says this is a missing collection-literal
    check and not a type value escaping one. The `literals` family's list and set halves
    therefore have no negative destination to drive; the tuple half does and is driven.
(b) THE INTERPRETER NEVER EVALUATES A `match` ARM GUARD. `MatchDispatch` clones `branch.guard`
    and then picks the first arm whose PATTERN matches: `match n case x | eq(x, 1) -> "one" case
    _ -> "other"` answers `"one"` for EVERY n, with no type value in the fixture. The guard
    family's RUNTIME half is therefore undrivable by anyone; its type value is driven at LOAD
    instead (`Cell[W = Int64]` inside a guard is refused naming the parameter `Cell` declares,
    `Cell[V = Int64]` loads). The typer's own Γ machinery already treats a guarded arm as
    conditional (WI-537), so the two layers disagree about what a guard does.

BACK-OUTS, MEASURED one at a time over the file's 24 rows: both loader predicates forced `false`
(WAHB6's own back-out) → 15 fail; `boolean_position_error` → `None` → 2 fail;
`denoted_type_value` → `None` → 2 fail; both classifiers reverted to `kind_of` → 2 fail;
`check_sort_type_args`'s own gate reverted to `kind_of` → 1 fails. The 9
that survive the first back-out are the 4 adjacent-role controls, plus the two rows that ask
about a `Relation`/rigid `?T` and about a sort sharing its name with a rule head (green in both
worlds by design)
and THREE ROWS WHOSE CARRIER IS NOT THE OPERATION-EXPRESSION PATH — metadata values, the
bounded-quantifier collection and the guard's load-time check are lowered by `convert_term`,
whose own `is_type_app` gate (WI-927) classified them before this umbrella existed. That is
umbrella B's (WI-20260823-53W12) boundary showing up exactly where this ticket said those halves
belong.

SPEC / DESIGN SYNC: kernel-language.md §4.8 states the two Boolean positions; design
055-implementation.md §3 records that its "ordinary typing rejects `Type` as a Boolean condition"
was false when written, what supplied it, and the collection-literal gap beside it.

/code-review (high) FOUND FIVE THINGS; three are repaired here and two are answered with a
measurement:
 * HIGH, REPAIRED: `check_sort_type_args` still gated on `kind_of`, so widening the
   classifier silently SKIPPED the WI-709 type-argument check for exactly the names the
   widening newly admitted — `Box[Zork = String, Zork = Bool, Int64, String]` loaded clean
   beside a plain sort that refused it. Both gates ask `has_kind` now, with the pairing
   stated at the gate ("the classifier decides which applications REACH this check").
   Pinned by `a_newly_classified_head_still_has_its_type_arguments_checked`.
 * MEDIUM, ANSWERED AND DOCUMENTED: the new `Bool` check refuses a relation-valued
   condition/guard, a reflect-`Term` one, and a rigid type parameter. Measured with the
   check backed out: the first two LOADED and then failed at EVAL (`EvalError::TypeMismatch
   { expected: "Bool", got: "Relation" }`), so the check is the runtime's own rule one phase
   earlier with a span; the third ran when instantiated at `Bool`, and is refused exactly as
   the same value in an ARGUMENT slot is (`expected Bool, got ?T`) — §8.1's rule for a body
   that pins a parameter its signature quantified. Both are driven by
   `the_boolean_destination_is_the_arguments_predicate_not_a_second_opinion`, and the two
   inaccurate sub-claims in the arm's doc (the `Term` tolerance is one-directional; a rigid
   var is DETERMINED, not deferred) are corrected there.
 * LOW, REPAIRED: `make_sort_ref_by_name` would have minted a phantom `Bool` in a KB with no
   prelude (`expected Bool, got Bool`); the check now uses `try_` and says loudly that it has
   no destination to check against.
 * LOW/MEDIUM, NOT REPRODUCED: the finding that a rule head spelled like a sort gives
   `[Goal, Sort]` and flips a bare reference's reading. Measured in BOTH orders and for the
   body-less form: a rule head that RESOLVES mints no kind (pass 1 defines every sort before
   pass 3 reads a head), so `kinds == [Sort]` either way and `kind_of`/`has_kind` agree; the
   body-less DECLARATION form is refused outright when a sort holds the name. The review's
   own comparison varied whether the SORT exists, not which classifier runs. Pinned by
   `a_sort_sharing_its_name_with_a_rule_head_is_unmoved_by_the_widening`, and the doc's
   one-sided measurement is replaced by both orders plus a corpus census (0 of 239 stdlib
   sorts have a non-`Sort` primary kind).
 * LOW, DECLINED WITH A REASON: `LoadError::TypeMismatch.actual_type` now carries the
   denotation suffix. It was never a bare type spelling — `TypeError::Other` routes through
   the same field with a whole clause in it, and `AmbiguousConstrainedParamMember` with a
   paragraph — so the field is documented as rendered message text, with the structured pair
   left where a consumer should read it (`TypeError::TypeMismatch`).

ACCEPTANCE: full Rust workspace via `rustland/scripts/test.sh` — 6556 passed, 0 failed. scaland
`sbt test` — 537 passed, 2 failed, both PRE-EXISTING and unrelated: `BootstrapTest` cannot emit
`stdlib/anthill/prelude/field.anthill`'s `requires Ring` (introduced by cb875e77, "Field requires
Ring, not Numeric"); this change touches no file under `scaland/` or `stdlib/`.

