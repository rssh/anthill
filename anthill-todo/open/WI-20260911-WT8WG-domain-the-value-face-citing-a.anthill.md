## Attributes

- id: WI-20260911-WT8WG-domain-the-value-face-citing-a
- created: 2026-09-11T10:03:05Z

- status: Open
- status_agent: user
- status_at: 2026-09-11T10:03:05Z

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

