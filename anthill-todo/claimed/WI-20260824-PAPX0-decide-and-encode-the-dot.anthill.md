## Attributes

- id: WI-20260824-PAPX0-decide-and-encode-the-dot
- created: 2026-08-24T05:05:04Z

- status: Claimed
- status_agent: claude
- status_at: 2026-09-13T21:52:33Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260824-WAHB6-classify-a-nominal-type-once

- tags: proposal-055

## Description

DECIDE AND ENCODE THE DOT-RECEIVER SPLIT: SORT COMPANION VERSUS `Type`-VALUE MEMBER (proposal 055 umbrella A, step 4).

docs/design/055-implementation.md §4. A type-shaped receiver participates in two different mechanisms and they must not be separated by whichever lookup happens to run first:

  Map[K = String].empty()   -- sort companion / static lookup
  Cell[Int64].name          -- potentially a member of the `Type` VALUE

DELIVERABLE: preserve the distinction in the resolved receiver / projection node rather than re-deriving it downstream -- design §4 sketches `ResolvedReceiver::{Value, TypeValue, SortCompanion}`; the exact owner may differ, the invariant may not. Existing companion syntax and lookup remain authoritative. Where a surface can name BOTH a companion member and a `Type` member and no existing rule orders them, refuse the ambiguity naming BOTH routes (design §8) -- never a lookup-order fallback, and never a retry of a failed lookup as the other kind.

CODEBASE SITE: the `DotApply` work-frame in `typing.rs` and the `lowered_receiver` channel on `NodeKind::Expr` (`node_occurrence.rs`, WI-762) -- that channel already exists so a consumer that must SPLICE the receiver reads the lowered form instead of re-deriving it, which is the same discipline this ticket needs for the receiver's KIND. Check whether it is the right carrier before adding a second one; a receiver kind and a lowered receiver are two questions, so if it is reused the reason must be written at the site.

WHY ITS OWN TICKET: this is a DECISION, not the mechanics of steps 1--2. Settled inside the occurrence matrix it would get no control of its own, and an ambiguity refusal that nothing drives is indistinguishable from an ambiguity that never arises.

CONTROL: (1) a companion call that resolves today still resolves and reaches the same member; (2) a `Type`-member read on a type value is DRIVEN -- evaluate it and assert the value, not that it loads; (3) a surface that names both is refused with a diagnostic naming both routes, and the test asserts the distinguishing tokens of both, not merely that some diagnostic mentioning the sort was raised. State which rows fail on back-out and which pass either way.

ACCEPTANCE: full Rust workspace via rustland/scripts/test.sh.

## Changes

### 2026-09-13T17:36:27Z — feedback — claude

DECISION SET BY THE USER (2026-09-13): option B -- THE DENOTATION DECIDES.

A receiver whose type is `Type` and whose denotation is a known sort resolves
`.m` in THAT SORT's scope, however the receiver was spelled. One meaning, one
rule, independent of syntax.

MEASURED BEFORE THE DECISION, so the ticket's premise is on the record as a
fact rather than a reading of the code. Three spellings of one value, driven
(`anthill query` over a local `sort Box[V]` with `operation tag() -> Int64 = 7`):

  Box.tag()                                 -> 7
  Box[V = Int64].tag()                      -> 7
  let t = Box[V = Int64] ... t.tag()        -> REFUSED,
      "type mismatch in anthill.prelude.Type.tag: expected operation declared
       on the receiver's sort, got no such member (dot dispatch)"

THE SWITCH IS ONE PREDICATE: `field_access_root_is_value` (kb/load.rs:24597).
It walks to the root `Term::Ident` and asks `dot_receiver_binder(name)` -- IS
THE ROOT A LOCAL BINDER? Yes -> value receiver (`Expr::DotApply`); no -> the
static name path, where `collect_field_access_segments` flattens
`Box[V = Int64].tag` to the segments `Box.tag` and the bracket rides the
separate `recv_type` aux channel (`build_recv_type`, load.rs:25872). So the
split is keyed on the receiver's SPELLING -- specifically on whether its root
happens to be let-bound -- and WI-20260824-WAHB6 made all three spellings
denote the same classified `TypeValue` without the two routes converging.

WHAT B COMMITS TO, stated so a later ticket cannot claim it was unforeseen:
`Type` gets NO dot-reachable member API. `sort Type = ?` declares no members
today, which is what makes B cheap now; the moment `Type` would gain one
(design 055 sec 4's own example is `Cell[Int64].name`, and `name` would be a
`Type` member), it is unreachable by dot on a denoted-sort receiver. If that
API is wanted later, the reopening is option C (look up BOTH, always both, and
refuse a two-hit naming both routes) -- NOT a fallback, which sec 8 bans.

WHAT B FORCES, and it is most of the implementation cost: the decision now
needs the receiver's DENOTATION and the MEMBER's resolution together, and the
loader has neither. So the loader must stop flattening `Box[...].m` into a
static name path and instead RECORD a receiver kind for the typer to consume.
Option A (syntax decides) would not have forced this; B and C both do.

THE AMBIGUITY REFUSAL sec 4 asks for keeps a driveable trigger under B -- it
fires when a sort declares a member whose name `Type` also declares. That set
is EMPTY today, so control (3) must CONSTRUCT it rather than find it; a
refusal nothing drives is what this ticket exists to avoid.

CARRIER -- ANSWERED FROM EVIDENCE, not open: `lowered_receiver` is NOT it.
Its own doc (node_occurrence.rs:789, :1141) says it is a `Weak`, same-pass-only
twin that must NOT be carried across rebuilds ("carrying it would alias a stale
receiver"), and a dropped twin answering `None` is deliberate. A receiver KIND
is a classification and has to survive every rebuild site -- which is WI-20260824-WAHB6's
own stated discipline (`Expr::Constructor.from_projection`: a field INSIDE the
`Expr` makes every rebuild site a compile error, because `substitute_occurrence`
/ `term_view` / `resolve` / `body_specialize` all mint replacement nodes and a
missed one is silent). Two lifetimes, two questions; add the second carrier.

NOT YET DONE: nothing in this ticket is implemented. This entry records the
decision and the measurement only.

### 2026-09-13T18:10:23Z — feedback — claude

CORRECTION TO THE ENTRY ABOVE, from a user question ("what is Cell[Int64].name?").
That entry cited design 055 sec 4's `Cell[Int64].name` as a REAL cost of option B
-- "the moment `Type` would gain one ... it is unreachable by dot". MEASURED, and
that framing is WRONG: the example resolves to nothing on either half.

  * `Cell` is not a stdlib sort. It occurs only as a TEST FIXTURE
    (`wi_x9rrn_provided_member_address_test.rs:94`) and as an illustrative name
    in comments (`reflect.anthill:370`).
  * There is no `operation name` anywhere in stdlib. Every `name` hit is a FIELD
    of a reflect record -- `OperationInfo.name: Symbol` (reflect.anthill:870),
    `SortRef(name: Symbol)` / `Parameterized(base: Symbol, ...)` (sort.anthill:415/482).
  * The one running-text `.name` in proposal 055 (line 254) is the OPPOSITE of a
    `Type` member: it is a quoted BAD DIAGNOSTIC, `type mismatch in Int64.name:
    expected resolved name, got unresolved`, where `Int64.name` is the FLATTENED
    static-path functor `collect_field_access_segments` produces. It is evidence
    of the companion route, not of a member API.

WHAT sec 4's `.name` ALMOST CERTAINLY MEANT. `sort.anthill:9` states the design in
as many words: "There is NO stored deep ADT inside `Type`; its structure is
REIFIED on demand by `anthill.reflect.extract(t) -> TypeExtractor`", and
"`Type` is a bare `sort Type = ?` -- an opaque handle like `Term` / `Symbol`".
A type's name is read off the REIFIED form:

    match extract(t)
      case Parameterized(base, bindings) -> base
      case SortRef(name) -> name

So `Cell[Int64].name` is a sketch of `SortRef.name` / `Parameterized.base` written
as a dot on the UNREIFIED handle. Two different objects.

CONSEQUENCE 1 -- B COSTS NOTHING REAL. The "what B commits to" paragraph above
weighed B against a `Type` member API that does not exist and that the stdlib has
already decided against. B is CONSISTENT with `Type`'s existing documented design,
not a trade against it. The "if that API is wanted later, the reopening is option
C" hedge stands only if the opaque-handle decision is itself reversed, which is a
different ticket than this one.

CONSEQUENCE 2 -- AND THIS CHANGES CONTROL (3). The ambiguity refusal's trigger is
empty BY DESIGN, not merely empty today: it requires `Type` to declare a member,
and `sort Type = ?` forbids that by construction. So control (3) has exactly two
honest shapes, and the implementer must pick one and say which:

  (a) CONSTRUCT the collision in a fixture -- declare a member on `Type` locally,
      contradicting the stdlib's opaque-handle decision inside the test only, and
      drive the refusal there; or
  (b) STATE THAT THE REFUSAL IS UNREACHABLE under B and do not ship a guard, since
      "an ambiguity refusal that nothing drives is indistinguishable from an
      ambiguity that never arises" is this ticket's own words.

Do NOT ship a refusal with no driving row and call control (3) satisfied.

### 2026-09-13T18:48:17Z — feedback — claude

RETRACTION OF FOUR CLAIMS IN THE TWO ENTRIES ABOVE (/code-review, verified by me
against the tree). READ THIS ENTRY BEFORE EITHER OF THOSE. The DECISION -- option
B, the denotation decides -- is unaffected and stands; what follows are wrong
FACTS I attached to it, three of them stated as "MEASURED".

(1) "`Cell` is not a stdlib sort ... only a TEST FIXTURE" -- FALSE.
    `sort anthill.prelude.Cell` is declared at stdlib/anthill/prelude/cell.anthill:6,
    with `sort V = ?`, `operation new/get/set` (:20/:24/:29), `provides
    Modifiable[T = Cell]` (:33) and `provides ModifyRuntime` (:39); it has a
    runtime (eval/cell_arena.rs) and ~150 references across .anthill files,
    including this CLI's own `main.anthill:19`. My census ran `grep "sort Cell"`,
    which cannot match a QUALIFIED declaration `sort anthill.prelude.Cell`.
    DRIVEN since: `let c = Cell[V = Int64].new(5)` then `c.get()` answers 5.
    So design 055 sec 4's `Cell[Int64].name` contrasts a REAL sort's companion
    route against a hypothetical `Type` member -- the `Cell` half is live, and
    `Cell[V = ...].new(...)` is a dot-on-a-denoted-sort call option B must keep
    working. I removed a live case from consideration.

(2) "THE SWITCH IS ONE PREDICATE: `field_access_root_is_value` (load.rs:24597)"
    -- FALSE, and it inverts the pass order. That function's own doc (load.rs:24590-24595)
    reads: "The load-time peer of the converter's `is_value_receiver` root walk --
    only NAME-rooted receivers reach the loader as `field_access` (a value-rooted
    one already became `dot_apply` in the converter)". `is_value_receiver` is
    parse/convert.rs:1668 and runs FIRST. So the one spelling this ticket exists
    to fix -- `let t = Box[V = Int64] ... t.tag()`, value-rooted -- NEVER REACHES
    the predicate I named. Further: all three spellings I measured are CALLS, and
    calls are decided by `dot_call_receiver_chain` (load.rs:24409), whose first
    rung is the qualified name, outranking the binder test. And the field-access
    side is a deliberate two-variant LADDER whose doc (load.rs:24540-24545) says
    "The two are deliberately NOT one widened gate ... Widening this into a single
    condition would reintroduce that ordering bug -- add a new admission as a new
    `DotFieldPass` variant placed explicitly in that ladder instead." My "one
    predicate" framing argued for exactly the change that comment forbids.

(3) "the LOADER must stop flattening `Box[...].m` into a static name path" --
    WRONG PASS. `collect_field_access_segments` is a PARSE-TIME converter function,
    parse/convert.rs:843 (the sole definition; kb/load.rs names it only in a doc
    comment at :25882), reached from `convert_name` at convert.rs:805. The
    paragraph I called "most of the implementation cost" pointed at a file with
    nothing to change. Also: `build_recv_type` is load.rs:25890, not :25872.

(4) "empty BY DESIGN, not merely empty today ... `sort Type = ?` forbids that by
    construction" -- UNMEASURED ESCALATION of my own earlier, correct "declares no
    members TODAY". `sort Type = ?` is a one-line opaque declaration
    (prelude/sort.anthill:26); giving it members is a source edit, not a language
    impossibility, and kernel-language.md:4266's only statement on this axis is
    about FIELDS ("field access is ill-formed (no fields)"), not members.

CONSEQUENCE -- WITHDRAW OPTION (b). The previous entry's control-(3) option (b)
("state that the refusal is unreachable under B and do not ship a guard") was
licensed ONLY by (4). Under the evidenced "empty today" it means shipping B with a
REACHABLE ambiguity and no refusal, which design 055 sec 4:131-132 and sec 8:217
still require and this ticket's own Description forbids. Control (3) keeps its
original meaning: CONSTRUCT the collision and drive the refusal.

CONSEQUENCE -- THE PASS QUESTION IS REOPENED, NOT ANSWERED. Which pass owns the
receiver-kind record is now an OPEN question for the implementer, not something
these entries settled. The honest starting points are convert.rs:1668
(`is_value_receiver`), convert.rs:843 (`collect_field_access_segments`),
load.rs:24409 (`dot_call_receiver_chain`) and the `DotFieldPass` ladder at
load.rs:24540 -- and the ladder's doc says to ADD A VARIANT, not widen a gate.

WHAT SURVIVES, because it was driven rather than read: the three spellings and
their answers. `Box.tag()` -> 7, `Box[V = Int64].tag()` -> 7, and
`let t = Box[V = Int64] ... t.tag()` -> REFUSED with "type mismatch in
anthill.prelude.Type.tag: expected operation declared on the receiver's sort, got
no such member (dot dispatch)". The asymmetry this ticket must resolve is real;
my account of the machinery behind it was not.

### 2026-09-13T21:54:38Z — feedback — claude

THE PASS MAP, REBUILT AND DRIVEN. Supersedes the mechanism account in entries 1
and 2 (entry 3 retracted those). BOTH my "one predicate in the loader" AND the
review's "the converter already made it a dot_apply" are wrong for the third
spelling. Read from the CST (`npx tree-sitter parse`) plus the two deciders.

CST SHAPES -- this is what neither earlier account checked:

  Box[V = Int64].tag()  ->  field_access { object: application{Box,V,Int64},
                                           field: tag }
  Box.tag()             ->  ONE `name` node: (name (identifier Box)(identifier tag))
  t.tag()               ->  ONE `name` node: (name (identifier t)(identifier tag))

`Box.tag()` and `t.tag()` are THE SAME CST SHAPE. The grammar folds a dotted name
into one `name` node, so there is no `field_access` for either -- and
`is_value_receiver` (parse/convert.rs:1668) is only ever called from
`push_field_access`. It therefore NEVER RUNS for `t.tag()`. The review's reading
("value-rooted, so it became `dot_apply` in the converter") does not apply here;
mine ("`field_access_root_is_value` is the switch") named the zero-arg peer.

WHO ACTUALLY DECIDES, per spelling:

  Box[V = Int64].tag()  converter `is_value_receiver`: root is `application`
                        -> "name" arm -> NOT a value -> name/companion route,
                        bracket erased to segments + `recv_type` side channel.
  Box.tag()             loader `dot_call_receiver_chain` (load.rs:24409) RUNG 1:
                        `qualified_name_resolves("Box.tag")` is true -> return
                        None -> no decomposition -> static/companion route.
  t.tag()               same function, rung 1 FAILS (`t.tag` resolves to
                        nothing), RUNG 2 `dot_receiver_binder("t")` hits ->
                        decompose -> `Expr::DotApply` -> typer.

RUNG 1 OUTRANKS RUNG 2 BY DESIGN, and its comment names three regressions that
rung ordering fixed. Any change here must ADD a rung, not widen one -- the
field-access ladder's own doc (load.rs:24540-24545) says the same in as many
words for its side.

CONSEQUENCE FOR THE IMPLEMENTATION -- AND IT IS THE OPPOSITE OF WHAT ENTRY 1
SAID. The loader is NOT wrong and must NOT stop flattening. It routes `t.tag()`
to `DotApply` correctly: `t` IS a value receiver. What is wrong is downstream --
the typer then reads the receiver's SORT (`anthill.prelude.Type`, via
`sort_functor_of_view`) and dispatches on `Type`'s members, when under option B
it must read the receiver's DENOTATION and resolve in THAT sort's scope. So the
change lives at the `DotApply` build frame (typing.rs:14342), not in any pass
that runs before it.

WHY "B-STATIC NARROW" WOULD HAVE HAD NO SURFACE, measured. A receiver that is
SYNTACTICALLY a type reaches the dot as a NAME, never as a `DotApply` -- both
name-route spellings above bypass the typer's dot frame entirely. So the only way
to reach the `DotApply` frame with a `Type` receiver is through a BINDER or an
operation RESULT. Narrow B-static (denotation syntactically on the receiver)
would have had essentially nothing to act on. Let-propagation is not an optional
extra here; it is the whole route.

THE SCOPE BOUNDARY, stated as three driven rows:

  let t = Box[V = Int64]          t.tag()  -> IN SCOPE. Propagate the let.
  let t = id_ty(Box[V = Int64])   t.tag()  -> OUT. Denotation is lost through
                                     the call; recovering it needs a Type that
                                     CARRIES its head (the third option, not
                                     this ticket). Today: "no such member".
  operation f(t: Type) = t.tag()           -> OUT, permanently. No denotation
                                     exists. Must be a clear refusal.

SIDE FINDING, not this ticket and not yet filed: `(Box[V = Int64]).tag()` LOSES
ITS RECEIVER. It reports "`tag` is a member of sort Box, not in scope as a bare
name here" -- the parenthesized receiver is dropped rather than routed, where
`is_value_receiver` descends through `paren_expr` and should reach the same
`application` arm the unparenthesized form does. Raise before filing.

### 2026-09-13T23:57:49Z — feedback — claude

IMPLEMENTED — option B, scoped "B-static + let propagation" by the user.

WHAT SHIPPED, three pieces plus a guard:

  1. `TypingEnv.type_denotations` — binder -> the `Expr::TypeValue` occurrence it
     was bound to. A SECOND channel beside `receiver_aliases`, not a widening:
     that one maps a binder to another VALUE PATH so a type projection off it
     canonicalizes to the same receiver; this maps a binder to a DENOTED SORT.
     `stable_receiver_path` answers None for a `TypeValue`, so reusing the alias
     map would mean inventing a path meaning "not a path, a denotation".
  2. Bound at the let site, storing the NODE rather than the head alone — the
     type ARGUMENTS are part of the denotation, and the synthesized call carries
     them as `recv_type` exactly as the written `Box[V = Int64].tag()` does.
  3. A branch at the `DotApply` build frame (typing.rs), BEFORE the `[simp]` rung
     and the default fallback, because it decides WHICH SORT the member is looked
     up in; running it after would let a member keyed on `Type` win by position.
     It synthesizes the COMPANION shape -- args UNSHIFTED -- because a companion
     member has no receiver parameter and the default fallback's
     `m(receiver, args)` would build `tag(t)`, an arity error. That asymmetry is
     why design §4 asks for three receiver variants rather than a wider dispatch.
  4. THE AMBIGUITY REFUSAL (control 3), which the first cut MISSED. `Type`
     declares no members today but is an ordinary sort a program CAN REOPEN --
     measured, a fixture adding `operation tag(t: Type)` to `anthill.prelude.Type`
     loads clean. With `tag` on BOTH routes the first cut answered 7 and never
     said the other existed: the lookup-order settlement §4 forbids. Both lookups
     now ALWAYS run and a two-hit refuses naming both routes. That is not §8's
     banned fallback, which is retrying one route AFTER the other fails; no answer
     here depends on which question was asked first.

DRIVEN (not "loads clean"):
  let t = Box[V = Int64]; t.tag()        -> 7      (was a LOAD ERROR)
  let t = Box[V = Int64]; t.wrap(5)      -> 5
  let t = Box[V = Int64]; t.wrap("s")    -> refused at Int64, IDENTICALLY to the
                                            written `Box[V = Int64].wrap("s")`
                                            -- so the instantiation really rides
  `tag` on Box AND on Type               -> refused naming `Box.tag` and `Type.tag`
  a member only on Type                  -> still reaches Type's ordinary dispatch

CONTROLS, measured per row. Backing out the frame branch fails exactly
`a_let_bound_type_receiver_resolves_in_the_denoted_sort`,
`the_denoted_sorts_type_arguments_ride_the_call`,
`a_missing_member_names_the_denoted_sort_not_type` (and, separately, the
ambiguity row answers 7 again), while the three fences stay green.

TWO CORRECTIONS TO MY OWN TEST WORK, recorded because both were measured rather
than noticed:
  * `the_two_name_route_spellings_are_unchanged` FAILED on back-out at first --
    not because a name route moved, but because it shared the arms' fixture, and
    once `via_binder` stopped LOADING the whole KB died so `bare_name` could not
    be called. Given its own source. A control that shares a fixture with what it
    controls measures the fixture.
  * I claimed the shadowing row drives the `clear_type_denotation` arm. MEASURED
    FALSE: removing that arm leaves every row green, because `let t = 1` mints a
    FRESH binder symbol (WI-550) so a `Symbol`-keyed map cannot collide, and a
    lambda binder shadowing a let does not inherit the denotation either (its
    receiver types as `<unresolved receiver>`). NOTHING DRIVES THAT ARM. Kept as
    the pairing `clear_receiver_alias` already has, and said so at both the code
    site and the test header instead of crediting it with a control.

SCOPE BOUNDARY, pinned by a row rather than left to be discovered:
  let t = id_ty(Box[V = Int64]); t.tag()  -> STILL REFUSED. The denotation does
      not survive an operation call; `Type` is opaque and carries no head.
      Recovering it needs a `Type` that CARRIES its instantiation -- the third
      option weighed in this ticket, and a different ticket to do.
  operation f(t: Type) = t.tag()          -> refused, permanently. No denotation
      exists at all.

ACCEPTANCE: full Rust workspace via rustland/scripts/test.sh -- 36 suites, 7027
passed, 0 failed, exit 0. SEE THE NEXT ENTRY: this increment closes less than
the Description asks, and the first cut was net-negative until /code-review.

### 2026-09-13T23:57:53Z — feedback — claude

KNOWN GAPS AFTER THE FIRST INCREMENT — open, measured, and NOT delivered. Listed
because a reader of the code would not find them, and because the increment that
ships closes less than the ticket's Description asks for.

WHAT THE FIRST CUT GOT WRONG, kept on the record because the shape repeats:
the new arm RETURNED instead of being a RUNG. That made `try_fire_dot_rule`,
`find_spec_op_for_provided_sort`, `find_spec_op_for_required_sort`, the JSFHG
parent rung, field access and relation projection all UNREACHABLE for a
`Type`-typed receiver. `prelude/sort.anthill` declares `fact Eq[T = Type]`,
`PartialEq`, `Lattice` -- so `t.eq(u)` HAD WORKED through the spec route and
stopped loading, while the same call with the denotation lost still loaded beside
it. Driven against a back-out in both directions. A new admission is a RUNG.
The same cut also took an INSTANCE member with args unshifted, silently DROPPING
the receiver: `t.combine(p, q)` became `combine(p, q)` and LOADED. Both repaired
and pinned by rows.

STILL OPEN:

 1. THE AMBIGUITY CHECK SEES ONE ROUTE OF SIX. `type_route` asks only
    `find_operation_in_scope(Type, m)`, i.e. members declared directly inside
    `sort Type`. A member reachable through `find_spec_op_for_provided_sort`
    (`Lattice[T = Type]`'s `lub`, say) is invisible, so a companion still wins by
    position. The block's comment claims "BOTH lookups always run"; that is true
    of the two RUNG-1 lookups and false of the rest. DRIVEN.

 2. NO CALL-SHAPE FILTER. The guard compares member NAMES only, so
    `Type.describe(t: Type)` (0 user args) beside `Box.describe(a, b)` (2) makes
    `t.describe()` refused as reachable by two routes when it fits only one. The
    sibling `find_spec_op_for_constrained_param` takes a `call_shape` for exactly
    this reason.

 3. THE REFUSAL FIRES AT ONE SPELLING OF THREE. `Box[V = Int64].tag()` and
    `Box.tag()` never enter the typer's dot frame, so the same collision is still
    settled silently by lookup order there. The decision recorded on this ticket
    is "one meaning, one rule, independent of syntax"; a once-per-sort LOAD-TIME
    coherence check would be spelling-free and is the honest shape for this.

 4. THE COMPANION RUNG SKIPS `dot_member_dispatch_decision`. The two sibling
    `find_operation_in_scope` callers in the same arm both route through it
    (WI-1035's supplier-set question plus WI-861's `DispatchByValue` reroute), and
    `docs/kernel-language.md` §5.4 states it as language. So a denoted sort whose
    companion backs a spec it provides refuses through the value spelling and
    resolves silently through the type spelling.

 5. ENTITY CONSTRUCTORS ARE NOT ADMITTED. `find_operation_in_scope` scans
    `OperationInfo` facts only, so `t.mk(5)` cannot resolve though `Box.mk(5)`
    does. The terminal refusal now declines to name the denoted sort in that case
    (it would otherwise say "no such member of `Box`" about a member that is right
    there -- a FALSE sentence where the old one was merely about the wrong sort),
    but the three-spellings asymmetry this ticket exists to remove SURVIVES for
    constructors.

 6. POSITIONAL BRACKETS ARE REFUSED, NOT SUPPORTED. `recv_type` is read
    downstream by `term_backed_bindings`, which consults named keys only, so a
    `Box[Int64]` denotation arrived with NO bindings and `t.wrap("s")` LOADED
    where the written form refuses. The rung now stands down for a positional
    bracket rather than accept it falsely. Admitting them means naming the
    positionals against `type_params_of_sort` when the denotation term is built.

 7. A RIGID TYPE PARAMETER IN THE BRACKET DIVERGES FROM THE NAME ROUTE.
    `Box[V = T].wrap(y)` written out loads; `let t = Box[V = T]; t.wrap(y)`
    reports `expected ?T, got T`. Holds for `V = Int64`, fails for `V = T`.
    No row covers it and no scope boundary was stated for it.

 8. `docs/kernel-language.md` §5.4 AND `prelude/sort.anthill`'s `Type` DOC BLOCK
    ARE UNTOUCHED. CLAUDE.md requires the spec to track the implementation. §5.4
    now reads false for a `Type`-typed receiver on both halves, and the new
    "names BOTH ... no rule orders them" load error is documented nowhere.

ALSO OPEN, against the ALREADY-COMMITTED `anthill-todo` graph guard (502d4e0c),
both driven by /code-review:
 9. The guard bounds path DEPTH, not path COUNT. One acyclic root over a
    mutually-depending clique still explodes: 8 items -> 82,202 lines; 9 items
    killed at 121 s after 484,625 lines. The commit's stated guarantee ("a
    corrupt cyclic store must not hang the CLI") holds at 3 nodes, not at 10.
10. `graph` on a store with NO acyclic root prints NOTHING and exits 0.
    `find_roots` keeps only rows with `depends: nil()`; a pure cycle has none, so
    `print_roots` hits its `nil()` case and `cmd_graph`'s only empty-guard
    (`count_rows == 0`) does not fire. `list` on the same store prints both items.

