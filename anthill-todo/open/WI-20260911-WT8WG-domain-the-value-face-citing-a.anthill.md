## Attributes

- id: WI-20260911-WT8WG-domain-the-value-face-citing-a
- created: 2026-09-11T10:03:05Z

- status: Open
- status_agent: claude
- status_at: 2026-09-11T21:34:01Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260911-RS2G4-type-args-a-call-site-bracket

## Description

DOMAIN: the VALUE face — citing a sort's domain as a relation value.

WI-743 delivers §2.2's GOAL face only: a typed relational head reads the derived
`anthill.kernel.domain_member` relation as an appended body goal, and an explicitly built
goal answers the same rows (pinned by
`wi743_finite_domain_test::an_explicit_member_goal_answers_what_the_typed_head_does`).
What it does NOT deliver is the VALUE face — `Colour.domain` cited BY NAME as a
`Relation[…]`, the way WI-714 lets a rule be cited and `takeN`/`where`-d.

THE BOUNDARY WAS STATED DELIBERATELY, not skipped: the 2026-09-11 implementation review
records that `Colour.domain` over ground facts would type as `Relation[Unit]`, not
`Relation[Colour]`, and warned against delivering the value face BY ACCIDENT through a
rule-shaped derivation, which reopens the typed-column and self-call questions. WI-743
derives CLAUSES under ONE kernel functor rather than per-sort `<Sort>.domain` relations,
so there is no `Colour.domain` name to cite at all today — the citation has to be
designed, not merely enabled.

THREE QUESTIONS TO SETTLE FIRST, none of which WI-743 answers:
  1. WHAT IS CITED. A per-sort name (`Colour.domain`) is what §2.2's prose suggests and
     what WI-714's dotted machinery already resolves, but the derivation is deliberately
     ONE clause set on one functor — that is what lets `domain_member(?h, ?T)` inside the
     `List` clause dispatch on whatever `?T` binds to. A per-sort face would be a
     projection of it, not a second definition.
  2. WHAT IT TYPES AS. `Relation[(x: Colour)]`, presumably — and for a PARAMETERISED sort
     the citation has to carry the type argument (`List[T = Letter].domain`?), which is a
     surface question 052 has not been asked.
  3. WHAT IT DOES WHEN THE DOMAIN IS INFINITE. `takeN` is fine; draining raises. That is
     WI-737's existing route and needs driving, not building.

ACCEPTANCE: `let c = Colour.domain` (or whatever (1) settles) types as a Relation over
Colour and `c.takeN(5)` answers 3 rows; the same citation over `List[T = Letter]` answers
its cap and does not hang; a full drain of an infinite domain raises
`Error[RelationFloundered]` rather than materializing a row. The GOAL face is unchanged —
`wi743_finite_domain_test` keeps its counts.

## Changes

### 2026-09-11T11:12:10Z — feedback — claude

MEASURED 2026-09-11 (session with user), on the delivered tree at 1eb89144. Nothing built; every
number below is from a probe that was then reverted.

1. THE THREE ACCEPTANCE BEHAVIOURS ALREADY WORK AT THE GOAL FACE, so this ticket is about a NAME,
not about new resolution. Hand-write the projection this ticket would derive and cite it:

    sort Colour { entity red, entity green, entity blue
                  rule dom(?x: Colour) :- true }
    operation howMany() -> Int64 effects Error = length(Colour.dom.takeN(5))

  `Colour.dom.takeN(5)` = 3; `Colour.dom.head.x` TYPES as `Colour`; the same shape over
  `List[T = Letter]` answers its cap (5 of 5) and does not hang; over `String` (no derived domain)
  the drain RAISES `Error[RelationFloundered]` — WI-737's route, driven, not built. So question (3)
  is answered: nothing to build.

2. THE TYPE MUST TRAVEL AS AN **OPERATION** TYPE ARGUMENT, and that is a measurement, not a
preference. Two channels were tested:
  * an OPERATION type parameter is readable as a VALUE in the body at run time — WI-708's channel,
    still live;
  * a SORT type parameter is NOT. `sort Box[T] { operation selfType() -> Type = Box[T = T] }` called
    as `Box[T = Letter].selfType()` returns the dangling `Box[T = Box.T]`, not `Box[T = Letter]`.
  So a per-sort derived MEMBER (rule or operation) cannot serve a parameterised sort, whatever it is
  named. This kills the cheap shape and answers questions (1) and (2) together.

3. A PER-SORT DERIVED RULE CANNOT CARRY THE TYPE EITHER, for a second, independent reason: a rule
citation's query is built from the clause HEAD alone (`eval::build_relation_value` →
`pattern_query(head(fresh cols))`), and the generated member goal is fixed at TYPING time. Bracket
type args on a citation parse and are validated (WI-839) but reach no clause. So `List[T = Letter].domain`
has no channel even if the generator were emitted.

4. THE GENERIC-OPERATION SHAPE TYPES TODAY WITH ZERO TYPER CHANGES. Declared and loaded clean:

    operation dom[T]() -> Relation[T = (x: T), E = {Error}]
    length(dom[Letter]().takeN(5))                          -- List[T = Letter]
    dom[T = List[T = Letter]]().head.x                      -- List[T = Letter]

  Both the named (`dom[T = X]()`) and positional (`dom[X]()`) spellings load. The runtime seam is the
  established `where`/`where_run`, `project`/`project_run` split: a host-backed
  `domainOfType[R](t: Type) -> Relation[T = R, E = {Error}]` taking the type as a VALUE, with
  `operation domain[T]() -> Relation[T = (x: T), E = {Error}] = domainOfType(T)` reading `T` back
  through WI-708. Measured to load clean; the builtin itself is ~20 lines over
  `build_logical_query_value("pattern_query", domain_member(?x, t))`.
  TRAP: a member of `Relation` may NOT name its type parameter `T` — it collides with the sort's own
  and is a loud load error naming 058 §4.2 rule 1.

5. NAMING IS STILL OPEN, and the spec constrains it: kernel-language.md §5.3 already says a `domain`
in a sort's scope that is not a 2-ary relation of the member shape — "a field named `domain`, an
OPERATION" — is NOT the sort's domain. So a per-sort member spelled `domain` would contradict §2.2 as
written, and `<Sort>.domain` is already taken by the hand-written 2-ary hook. Options left open:
`Relation.domain[Of = Colour]()` alone, or that plus a loader arm making `Colour.domain` /
`List[T = Letter].domain` sugar for it (today both are a loud error in a VALUE position, and the
LOGICAL position keeps the name unchanged per WI-20260901-719FJ, so the arm is purely additive).

6. A WI-743 FINDING, FOUND WHILE ANSWERING THIS TICKET'S QUESTION (2) — `bound_names_a_determinate_type`
(typing.rs) STATES ONE REASON FOR THREE ARMS AND IT FITS ONLY ONE.
  Its doc says "TWO ways it cannot, and they are one defect: the goal would carry an UNBOUND type,
  which unifies with every derived clause head and enumerates types." CENSUS, by instrumenting each
  false return: across the whole `wi743_finite_domain_test` suite only the `Term::Ref` arm ever fires —
  8 times, always `anthill.prelude.List`. The `Term::Var` arm and the nullary-`Fn` arm fire ZERO times
  there, and zero across full loads of classic-mini, github-todo and anthill-todo. And the arm that
  does fire has the OTHER failure mode: `domain_member(?w, Ref(List))` matches no derived head
  (`List[T = ?T]`) and `domain_leaf` refuses because `has_domain_member(List)` — so the goal FAILS and
  a row is LOST, which is what `a_bare_parameterised_bound_still_answers_its_bound_value` measured.
  The "enumerates types" reason belongs to the RECURSIVE arm (`List[T = List]`) alone.

7. AND THE FRESH-TYPE-VARIABLE REPAIR RE-MEASURED — the user's direction, BUILT and run rather than
inherited from WI-743's rejection. Bare parameterised sort references in the bound re-applied with
fresh vars at every depth (`List` becomes `List[T = ?fresh]`):

    clause                                        today          fresh vars
    anylist(?w: List) :- true                     1 all / 0 def  20 / 2   (cap; 200 at cap 200)
    nest(?w: List[T = List]) :- ?w <=> [[a()]]    1 / 1          20 / 1
    sig_bare(?w: List) :- ?w <=> [a()]            1 / 1          20 / 1   (178 at cap 200)
    par_bare(w: List) :- w <=> [a()]              1 / 1          20 / 1
    parm(?w: List[T = Letter]) — control          1 / 1          1 / 1

  THE SHAPE IS NOT WHAT THE RECORDED REJECTION IMPLIES, and that is the part worth keeping. It is not
  20 wrong rows. Row 0 is `definite=true, residual=[]` — THE CORRECT ANSWER, and the fresh var IS set
  from the body: `?w <=> [a()]` binds the element, the `Letter` clause head binds `?fresh := Letter`,
  decided, nothing pending. What follows is an UNDECIDED TAIL, and the residuals name its cause:

    row 1  residual=[domain_leaf(a, ?_)]
    row 2  residual=[unify(a, ho_apply[predicate = ?_, args = nil, …]), domain_leaf(?_, Term)]
    row 3  residual=[… , domain_leaf(?_, Term)]
    row 5  residual=[… , domain_leaf(?_, Term), domain_leaf(?_, Symbol), domain_leaf(?_, Term)]

  A FREE TYPE ARGUMENT MAKES EVERY DERIVED CLAUSE IN THE KB A CANDIDATE. After the right branch
  succeeds, backtracking enters the catch-all (`domain_leaf(a, ?_)`, `?T` still free → delay) and then
  every OTHER sort's derived domain — the stdlib's `Term`, `Symbol`, `String` are named in the
  residuals by their own constructors (`ho_apply`). Those alternatives do not FAIL, they PARK. The
  tail is therefore bounded by the KB's derived-domain population, not infinite: `sig_bare` — a clause
  whose body binds its one variable outright and can have AT MOST ONE row — terminates at 178
  solutions, 1 definite and 177 undecided. Under `Relation` that means `takeN(1)` is right and
  `takeN(2)` RAISES.
  RULED OUT as the cause: the catch-all's delay is not it on its own. Making `domain_leaf` return
  `Failure` instead of `delay()` for an unbound `?T` leaves the count at 20/1 — measured.

8. SO THE REPAIR THE FRESH-VAR DIRECTION NEEDS IS A GUARD ON THE DERIVED CLAUSES' **TYPE ARGUMENT** —
the type is an INPUT, not an OUTPUT — with the (in, out) mode READING it instead of choosing it: where
the value is bound and the type is free, the type is functionally determined by `value_type_term`
(WI-578, which `domain_leaf` already calls through `type_bound_verdict_view`), so it should be bound
deterministically rather than guessed by opening one choice point per derived domain. With that,
`bound_names_a_determinate_type` could shrink to one honest rule instead of three arms with one
reason. NOT IN THIS TICKET's scope — it is WI-743's — and it does NOT unblock this one either:
even with fresh variables `List.domain` cited paren-less means "lists of SOMETHING", never
`List[T = Letter]`, because of (3).

### 2026-09-11T11:18:27Z — feedback — claude

CORRECTION to items 2, 4 and 5 of the entry above, from the user (2026-09-11): "we should have no
one type argument for all, we should have zero type arguments for Colour, one for List, two for
Stream or Pair."

THE SINGLE-`[T]` OPERATION IS THE WRONG ARITY, and that is the point. `Relation.domain[Of = X]()`
takes ONE type argument whatever the sort is, because it passes the WHOLE type as that argument. The
domain of a sort takes the SORT'S OWN parameters: none for `Colour`, one for `List`, two for `Pair` /
`Stream`. Written with the receiver's own brackets that arity is right BY CONSTRUCTION and no new
naming rule is invented:

    Colour.domain                 -- Relation[(x: Colour)]
    List[T = Letter].domain       -- Relation[(x: List[T = Letter])]
    Pair[A = X, B = Y].domain     -- Relation[(x: Pair[A = X, B = Y])]

MY EARLIER CONCLUSION (item 2, "this kills the cheap shape") WAS WRONG. A sort type parameter not
reaching the body does not kill the per-sort member — it NAMES A MISSING CAPABILITY, and the
capability is general rather than anything to do with `domain`.

MEASURED 2026-09-11, the gap in both halves:

  * TYPING. A receiver bracket on a sort-member call is parsed and VALIDATED against the sort's
    declared parameters, and then IGNORED.

        sort Box[T] { entity box(v: T)
                      operation empty() -> Option[T = T] = none() }

        operation p8() -> Option[T = Letter] = Box[T = Int64].empty()   -- LOADS CLEAN
        operation p9() -> Option[T = Letter] = Box[W = Int64].empty()   -- LOUD: "`Box` has no type
                                                                        --   parameter named 'W'"

    So the bracket's VALUE is dropped: with nothing else carrying `T`, the return type's `T` is
    pinned by the EXPECTED type instead, and `Box[T = Letter].empty()` types as whatever the context
    wants. CONTROLS, both run: with an ARGUMENT carrying the parameter the pin does happen
    (`Box.mine(b)` with `b: Box[T = Letter]` is refused against a declared `Box[T = Int64]` return
    WITH NO BRACKET AT ALL — so the pin in that case is the argument's, not the bracket's), and a
    bracket CONFLICTING with such an argument is refused loudly. The bracket is therefore read where
    something else already decides, and dropped where it is the only source — which is exactly the
    nullary case a derived `domain` would be.

  * EVAL. The frame type-arg channel (WI-272/WI-708) is written ONLY for the OPERATION's own type
    params — `typing.rs`'s `set_resolved_type_args` is guarded by `if !op.type_params.is_empty()`
    and keys each entry by the op-scoped `<ns>.<op>.T`. A SORT parameter is never written, so a body
    read of it gets a dangling `Ref(Box.T)`: `Box[T = Letter].selfType()` with
    `operation selfType() -> Type = Box[T = T]` returns `Box[T = Box.T]`, measured.

058 §4.2 RULE 1 ALREADY STATES THE RULE — "a call-site bracket binds BOTH scopes" — and the loader
enforces only its COLLISION half: an operation type parameter that shadows its enclosing sort's is a
loud load error naming that rule. The BINDING half is not delivered for the sort scope, at either
level. So this is one capability with two sites, owed independently of `domain`.

WHAT THE VALUE FACE THEN IS, with that capability in hand: derive per sort, beside the
`domain_member` clause and in the `<Sort>.induction` idiom (a symbol scoped to the sort, `load.rs`'s
`emit_induction_rule`), an OPERATION

    <Sort>.domain() -> Relation[T = (x: <SelfType>), E = {Error}] = domainOfType(<SelfType>)

where `<SelfType>` is `Colour` for a non-parameterised sort and `Box[T = T]` for a parameterised one
— the same term `load::domain_self_type` already builds for the derived clause head, so the two
readings of one parameter list cannot disagree. `domainOfType(t: Type)` is the host seam (the
established `where`/`where_run`, `project`/`project_run` split), building
`pattern_query(domain_member(?x, t))` with one column `x`. It must be an OPERATION and not a rule,
for item 3's reason: a rule citation's query is built from the clause head alone and no type
argument reaches a clause.

SPEC CONSEQUENCE TO SETTLE: kernel-language.md §5.3 currently says a `domain` in a sort's scope that
is not the 2-ary member relation — "a field named `domain`, an OPERATION" — is NOT the sort's domain.
That sentence was written to exclude a USER's unrelated operation; a DERIVED `<Sort>.domain()`
operation is the value face of the very relation it describes, so the sentence needs rewording rather
than the design changing. Flagged, not decided.

### 2026-09-11T21:18:38Z — feedback — claude

IMPLEMENTATION PLAN (claude, 2026-09-11, session with user). Supersedes the two entries above
where they differ; every "today" figure below was driven on the current tree (5856c5cc) with the
built CLI, and nothing was built. The user's rule that governs the whole plan: THE AUTHOR WRITES
NO DOMAIN EXPRESSION, EVER. The author writes a sort; the loader derives its domain; a typed head
reads it (goal face, WI-743); and a citation reads it (value face, this ticket). Both faces are
generated. The operation-plus-host-builtin direction of the two entries above is DECLINED: it is
not what proposal 060 specifies (a MEMBER RELATION named `domain`), it is not what 052 cites (a
rule reference IS a `Relation`), and it needed the author to meet a builtin.

0. THE SHAPE, IN ONE EQUATION (the user's, 2026-09-11):

    Colour.domain(?x)  ==  anthill.kernel.domain_member(?x, Colour)

  The kernel relation is 2-ary and type-indexed: one clause per sort, the type as the second
  argument (WI-743). A sort's `domain` is the 1-ary PROJECTION of it at that sort, and it is a
  MEMBER RELATION of the sort, so 052 cites it by name and the whole Stream API follows:

    sort Colour { entity red  entity green  entity blue }     -- the author writes THIS
    Colour.domain            -- Relation[T = (x: Colour), E = {Error}]   (derived, not written)
    Colour.domain.takeN(5)   -- 3 rows, every one definite

  The loader derives, in the sort's own scope and at the same drain that emits the kernel
  clause, exactly the clause a typed head would have been: `domain(?x) :- true` with the bound
  `x: Colour` installed. From there NOTHING IS NEW: the typer sweep already prepends the
  conformance goal and appends the member goal to every bound clause
  (`install_typed_head_domain_goals`), and the 052 arm already resolves `Sort.rule` on a sort
  symbol to a relation value (`check_bare_ref` -> `relation_reference_type`, eval
  `build_relation_value`). MEASURED on the delivered tree with a WRITTEN twin named `dom`
  (entry of 11:12 above, item 1): `Colour.dom.takeN(5)` = 3, `Colour.dom.head.x` types as
  `Colour`. The plan makes the loader write that twin, under the name 060 gives it.

1. WHAT PROPOSAL 060 §2.2 ALREADY SPECIFIES, AND THIS PLAN KEEPS UNCHANGED:
  * derived for any sort with constructors, one clause, type as the second argument;
    finiteness decides only whether the stream ends; base constructors first, recursive
    positions first — all delivered by WI-743 and untouched here;
  * conformance goal prepended, member goal appended (untouched);
  * domain-defining, not a generator hint: both modes read a sort's domain (kept — the value
    face reads the SAME clauses through the same appended goal, so the three readers — mode
    in, mode out, citation — cannot disagree);
  * a sort with no constructors keeps §2's ladder (kept; see 3.4);
  * abstract T does not enumerate (untouched; NAR1X);
  * `Bool` (5TK6B) and two-recursive-position fairness (09E6M) stay where they are.

2. CHANGES TO PROPOSAL 060 — TO DECIDE WITH THE USER BEFORE BUILDING. Each is a text change
   plus the code that makes the text true; my recommendation is stated with each.

  (A) THE GENERATED GOALS HAVE NO SURFACE SPELLING, AND THE KERNEL DECLARES THEM IN SOURCE.
      §2.2 says "`domain(?x, T)` dispatches to a member relation T defines, named `domain`",
      and its delivery note records "one notion, two functors" (`anthill.kernel.domain` the
      conformance builtin, `anthill.kernel.domain_member` the relation). MEASURED TODAY, and
      this is the inconsistency to close: after `import anthill.kernel.*`, `domain`,
      `domain_leaf`, `find_dictionary` and `push_and` all RESOLVE from a user rule body, while
      `domain_member` "names nothing" — not by policy but by WHEN it is minted
      (`domain_member_symbol`, defined at the end of the load batch in
      `derive_domain_member_clauses`, after every body in the batch has resolved; the CLI
      loads stdlib and user files as ONE batch). And a hand-written `domain(?x, Colour)`
      goal is worse than reachable: in mode (out) it answers a conditional residual (the
      builtin cannot generate), and in mode (in) — `r(red)` — it trips
      `debug_assert!(false, "the bound operand is not a type term")` at resolve.rs:6064,
      an ABORT in a debug build and a resolver Error in release. So the writable name is the
      half that cannot generate, and it crashes.
      RECOMMENDED TEXT: "`domain_member` and the conformance goal are the compiled form of a
      typed head. Neither has a surface spelling: a source goal on either functor is a load
      error. The only surfaces are the annotation `?x: T` (input) and `<Sort>.domain`
      (output)." RECOMMENDED CODE: (i) declare `rule domain_member(?x, ?t)` body-less in
      `stdlib/anthill/kernel/kernel.anthill` — 061's declaration form, so the predicate exists
      from the stdlib's pass 1 and the derivation CONTRIBUTES CLAUSES to a declared predicate
      instead of minting a name at the drain (the user's question "why late minting"; the
      answer WI-743 gave — "a surface declaration would let code capture the name" — was not
      applied to `domain` or `domain_leaf`, so it protected nothing); delete
      `domain_member_symbol`. (ii) Refuse, at the rule-body goal resolution site
      (`undefined_rule_body_goal_message`'s neighbour in load.rs), a SOURCE goal whose functor
      is one of the three generated-only kernel functors, with a message naming the typed
      head as the spelling. A three-entry set on the KB, populated at bootstrap; the typer's
      generated nodes never pass through that site. (iii) The resolve.rs:6064 assert becomes
      unreachable from source and stays an internal invariant. ALTERNATIVE, if you prefer the
      goals writable: leave (ii) out and make 6064 a plain Error — but then 060 must say the
      goals ARE writable, and the mode-(out) residual of a written `domain(?x, T)` becomes a
      documented trap. I recommend the refusal.

  (B) THE HAND-WRITTEN OVERRIDE TAKES THE VALUE FACE'S SHAPE: 1-ARY, `domain(?x)` IN THE SORT
      BODY. §2.2 today: "a relation `domain(?x, T)` in the sort's body". With a derived 1-ary
      `<Sort>.domain`, a sort that also writes the 2-ary form would hold two arities under one
      name — 052's citation builds its query from the FIRST clause's head shape and would
      answer through whichever loaded first, and one-arity-per-predicate (WI-6WVJB) would
      later refuse it. RECOMMENDED TEXT: "Any sort may write its own domain as a 1-ary
      relation `domain(?x)` in its body; it then IS the sort's domain — the value face is that
      relation, and the kernel's `domain_member(?x, S)` forwards to it." A 2-ary `domain` in a
      sort body becomes a LOUD load error naming the 1-ary spelling (it was WI-743's own
      spelling for one day; three test fixtures write it, no corpus file does). The
      parameterised hand-written domain stays refused (unchanged). Cost: the loader hook's
      arity filter (`pos_arity: 2` -> 1), the forwarding clause (`domain_member(?x, S) :-
      S.domain(?x)`), the "second argument is neither" refusal retired, and one sweep rule (3.3).

  (C) PARAMETERISED SORTS: THE VALUE FACE IS REFUSED UNTIL WI-5G28A, LOUDLY, AT LOAD.
      `List[T = Letter].domain` needs the citation's type argument to reach the clause. A rule
      citation's query is built from the clause head alone (`build_relation_value`), and
      RS2G4 delivered the receiver-bracket binding for OPERATION members only; the rule half is
      5G28A. MEASURED TODAY: a written `rule dom(?x: Wrap[T = T]) :- true` inside
      `sort Wrap[T]` cited as `Wrap[T = Colour].dom.takeN(5)` AND as bare `Wrap.dom.takeN(5)`
      both LOAD CLEAN — the bracket is validated and dropped, the bound is a type variable so
      the sweep skips the member goal, and the citation can only flounder at the drain. That
      is a silent typing acceptance. RECOMMENDED: derive NO value face for a parameterised
      sort, and make the citation a load error that names 5G28A; add to 5G28A's acceptance
      "lifting this refusal: `List[T = Letter].domain.takeN(5)` answers 5, bare `List.domain`
      stays refused (names no element type)". The goal face for parameterised sorts is
      unchanged (WI-743's `List[T = Letter]` rows keep their counts). ALTERNATIVE: make this
      ticket depend on 5G28A and deliver both halves at once. I recommend delivering the
      non-parameterised half now: it is the whole of map-colouring, alphabet-words' `Letter`,
      tiny-sat, and 34 of the 37 all-nullary corpus sorts.

  (D) kernel-language.md §5.3's sentence "A `domain` in a sort's scope that is not a relation
      of that shape — a field named `domain`, an operation — is not the sort's domain" stays
      TRUE and is re-anchored on the 1-ary shape. Its field case is live: `guardians.Address`,
      `github-todo.FactRef` and `FactHolds` each carry a FIELD named `domain` (census: those
      three). For them the loader derives NO value face (the name is taken), records the
      reason (the `domain_member_decline_reason` idiom), and the goal face is unaffected. A
      later author who wants both renames the field. Recommended: state it in §5.3 as the one
      case where a sort has a domain and no `.domain`.

3. THE MECHANISM — four edits, each at a site that exists.

  3.1 LOADER, the value face (`derive_domain_member_clauses`, pass 2, beside the kernel
      clause). For each job that got a kernel clause (structural or forwarded), when
      `job.params.is_empty()` and `<sort_qn>.domain` is not already bound in the sort's scope
      and no hand-written domain exists: define the Goal symbol `domain` SCOPED TO THE SORT
      (copy `emit_induction_rule`'s idiom, including its comment on why the scope is the sort
      and not `<global>` — the short name registered once in `<global>` makes every later
      sort's member unreachable), assert `domain(?x) :- true` (empty body) with
      `assert_rule_debruijn_with_nodes` into `job.domain`, then
      `install_rule_type_bounds(rid, &[(x, self_type)])` — the same installer the typed-head
      path uses at load.rs:31164 — and `set_rule_head_span(rid, <the sort's declaration
      span>)`. THE SPAN IS LOAD-BEARING: the sweep anchors a body-less clause's generated goals
      on `rule_head_span` and hits `debug_assert!(false, "a type bound on a body-less clause
      with no source head span")` without one — so `DomainMemberJob` gains the sort's span,
      collected in `exit_sort_with_body` where the parsed sort is in hand. The re-load guard is
      the existing `has_domain_member` skip: one place, both clauses.
  3.2 LOADER, the override hook (decision B): arity 1; forward as `domain_member(?x, S) :-
      S.domain(?x)`; install the bound `x: S` on every clause of a hand-written `S.domain`
      (so its citation is typed like the derived one); record S in a KB set
      `sort_domain_is_written` — read by 3.3; refuse a 2-ary `domain` in a sort body with the
      migration message; keep the parameterised refusal.
  3.3 TYPER, one rule at the sweep's existing "THE SELF-CALL TRAP has no arm here" site in
      `install_typed_head_domain_goals`: a clause of `S.domain` where S is in
      `sort_domain_is_written` gets the conformance goal and NOT the member goal — a written
      domain is never generated FROM, which is the loop the loader refuses today one level up.
      The derived `domain(?x: S) :- true` is NOT in that set and keeps its member goal, which
      is its whole body. Nothing here keys on a name the typer reads; the loader's shape
      decision is what the set records.
  3.4 KERNEL SOURCE + REACHABILITY (decision A): `rule domain_member(?x, ?t)` declared in
      `kernel.anthill`; `domain_member_symbol` deleted; the three-functor refusal at the
      rule-body goal site; the parameterised-citation refusal of (C) at the 052 arm
      (`relation_reference_type`, where the cited Goal is a sort member whose sort has
      parameters — the receiver bracket is already parsed there, RS2G4). Constructor-less
      sorts (`String`, primitives, specs) derive no `.domain` and the citation is the ordinary
      unknown-member error, which is LOUD AT LOAD where a derived-but-floundering member would
      be loud only at the drain.

4. ROWS — `tests/include/wi_wt8wg_domain_value_face_test.rs`, header naming which rows fail
   per back-out (RUN each back-out, not predicted — WI-743's header guessed three of six).
   Axes: [a] the value-face derivation (3.1); [b] the bound + span on the derived clause;
   [c] the 1-ary hook and forwarding (3.2); [d] the sweep exclusion (3.3); [e] the kernel
   declaration and the three-functor refusal (3.4); [f] the parameterised refusal; [g] the
   name-collision decline.
   (1) `Colour.domain.takeN(5)` = 3 definite rows AND a return-type row: `Colour.domain.head.x`
       accepted at `Colour`, refused at `Int64` — fails [a] (no member) and [b] (untyped
       column, or a debug abort at the anchor); (2) one-constructor sort = 1; (3) a recursive
       non-parameterised sort `Nat { z, s(p: Nat) }`: `Nat.domain.takeN(4)` = 4, and the rows
       are `z`, `s(z)`, `s(s(z))`, `s(s(s(z)))` IN THAT ORDER (asserts the value face inherits
       WI-743's fairness; a count alone passes with the order reversed); (4) hand-written
       1-ary `domain` with 2 rows on a 3-constructor sort: `S.domain.takeN(5)` = 2, the typed
       head `rule pick(?x: S) :- true` = 2, and mode (in) REFUTES the third constructor —
       fails [c]; a typed hand-written clause `domain(?x: S)` loads and answers the same 2
       (does not loop) — fails [d] by non-termination, so the row runs under a solution cap;
       (5) 052 algebra over the derived face: `Colour.domain.where(lambda c -> eq(c.x, red()))`
       = 1 — shows a real `Relation`, not a special case; (6) explicit vs derived agree:
       the 060 §2.2 colouring rule's 6 rows equal a join over six `Colour.domain` citations
       filtered by the nine inequalities — or, cheaper, `wi743_finite_domain_test` keeps every
       count (the goal face is untouched; state it in the header as passing either way BY
       DESIGN); (7) a source goal `domain(?x, Colour)` / `domain_member(?x, Colour)` after
       `import anthill.kernel.*` is a LOAD ERROR naming the typed head — fails [e]; this row
       is the control for the resolve.rs:6064 abort, which is unreachable once it passes;
       (8) `List[T = Letter].domain` and bare `List.domain` are load errors naming 5G28A —
       fails [f] (loads clean today, measured); (9) a sort with a field named `domain`:
       no member derived, decline reason readable, the field still resolves as a field,
       goal face over that sort still enumerates — fails [g] by a merged-kind symbol (the
       WI-926 `define` merge); (10) `String.domain` is a load error (unknown member);
       (11) re-loading the same file into a KB does not duplicate `Colour.domain`'s clauses
       (`Colour.domain.takeN(9)` still 3). Plus the three wi743 hand-written fixtures
       rewritten to the 1-ary spelling, and `map-colouring`'s `main` gaining one line that
       cites `Colour.domain` (README sentence: the sort is the domain, and the domain is a
       value).
   Acceptance: full workspace suite green via `rustland/scripts/test.sh`; `/code-review` run
   on a restored tree; scaland: no `Relation` surface exists there (grep: nothing), so
   `sbt test` must simply stay green — nothing to port.

5. DOCS. Proposal 060 §2.2: the value-face bullet (the equation in §0, "derived, never
   written"), decisions A–D as adopted, the delivery note's "two functors" reworded as
   internal; §5.3 of kernel-language.md: the `<Sort>.domain` member beside `induction` under
   the sort's derived members, the reworded "not the sort's domain" sentence, the no-surface-
   spelling rule; `docs/design/060-implementation.md` §0 row and §7 ("The VALUE face" moves
   from NOT delivered to delivered, with the parameterised residue named 5G28A); proposal 052
   §Naming one sentence (a derived member relation is cited like any rule; OQ2's bare
   `Sort.rule` arm is what serves it) and OQ4 (a declaration/derived relation does not join
   the dispatch surface — confirmed by this: it is a rule); this ticket's acceptance line
   "a full drain of an infinite domain raises `Error[RelationFloundered]`" is CORRECTED: an
   infinite derived domain is a lazy stream and a `Relation` has no full drain (no `collect`,
   052); floundering belongs to a constructor-less sort, which under this plan has no
   `.domain` to drain.

6. NOT IN SCOPE, each with its owner: the parameterised value face (5G28A, decision C);
   `Bool.domain` (5TK6B); fairness for two recursive positions (09E6M); abstract T (NAR1X);
   the general "receiver bracket on a rule citation" binding (5G28A) — this plan only
   REFUSES it where it would otherwise be silent.

7. MEASUREMENTS THIS PLAN RESTS ON, all today, all reverted: the five-name resolution table
   in (A); the mode-(out) residual and the mode-(in) abort of a written `domain(?x, Colour)`;
   `anthill.kernel.domain_member` unreachable bare, qualified, by named import, by wildcard
   import and as a rule-body goal; `Wrap[T = Colour].dom` and `Wrap.dom` loading clean; the
   field-named-`domain` census (3 sorts); `Colour.dom.takeN(5)` = 3 typed `Colour` (entry of
   11:12, item 1, on 1eb89144); `rule_ids_by_qn` / `cites_a_relation` serving a derived
   sort-scoped Goal exactly as they serve `<Sort>.induction`.

