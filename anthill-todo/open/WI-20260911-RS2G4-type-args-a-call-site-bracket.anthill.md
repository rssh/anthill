## Attributes

- id: WI-20260911-RS2G4-type-args-a-call-site-bracket
- created: 2026-09-11T11:21:45Z

- status: Open
- status_agent: user
- status_at: 2026-09-11T11:21:45Z

- acceptance: cargo-test

## Description

TYPE ARGS: a call-site bracket must BIND the sort's type parameters, not only be validated
against them — 058 §4.2 rule 1's binding half, at the typer and at eval.

058 §4.2 rule 1 says a call-site bracket binds BOTH scopes — the operation's own type parameters
and its enclosing sort's. The loader enforces only the COLLISION half, and says so in its own
message: `operation dom[T]()` inside `sort Box[T]` is refused with "type parameter `T` collides
with the type parameter `T` of its enclosing sort `Box`. A call-site bracket binds BOTH scopes
(proposal 058 §4.2 rule 1), so `Box.dom[T = …](…)` would have two targets". The BINDING half is
not delivered for the sort scope, at either level.

MEASURED 2026-09-11 on 1eb89144, both halves.

(1) TYPING — THE BRACKET IS VALIDATED AND THEN IGNORED, which is a SILENT WRONG ANSWER rather
than a missing feature.

    sort Box[T]
      entity box(v: T)
      operation empty() -> Option[T = T] = none()
    end

    operation p8() -> Option[T = Letter] = Box[T = Int64].empty()   -- LOADS CLEAN
    operation p9() -> Option[T = Letter] = Box[W = Int64].empty()   -- LOUD: "`Box` has no type
                                                                    --   parameter named 'W'"

  The bracket's VALUE is dropped: with nothing else carrying `T`, the return type's `T` is pinned
  by the EXPECTED type instead, so `Box[T = Letter].empty()` types as whatever the context wants.

  TWO CONTROLS, both run, which say where the pin comes from today:
    * `operation mine(b: Box) -> Box[T = T] = b`, called as `Box.mine(b)` with `b: Box[T = Letter]`
      against a declared `Box[T = Int64]` return — refused naming `Box[T = Letter]` WITH NO BRACKET
      AT ALL. So an ARGUMENT pins the sort parameter and the bracket contributes nothing there.
    * `Box[T = Int64].mine(b)` with `b: Box[T = Letter]` — refused loudly. So a bracket that
      CONFLICTS with an argument IS heard.
  Together: the bracket is read where something else already decides, and dropped where it is the
  only source — which is exactly the nullary member case.

(2) EVAL — THE FRAME CHANNEL CARRIES OPERATION PARAMETERS ONLY. `typing.rs`'s
`set_resolved_type_args` is guarded by `if !op.type_params.is_empty()` and keys each entry by the
op-scoped `<ns>.<op>.T` (WI-708's rule: the key is the symbol a BODY reference resolves to). A SORT
parameter is never written, so a body read of one gets a dangling `Ref(Box.T)`:
`operation selfType() -> Type = Box[T = T]` called as `Box[T = Letter].selfType()` returns
`Box[T = Box.T]`, measured.

WORK, two sites, one rule.
  * TYPER. At the sort-member dispatch, seed the SORT's type-parameter vars from the receiver's
    bracket bindings BEFORE the return type is resolved, so `Option[T = T]` resolves to
    `Option[T = Letter]` instead of unifying with `expected`. The argument-carried pin must keep
    AGREEING with it; the conflicting case is already loud and must stay loud, with a message that
    still names which source said what.
  * EVAL. Write the SORT's parameters into `resolved_type_args` alongside the operation's, keyed
    the way a BODY reference to them resolves — WI-708's rule one level up, so the SORT-scoped
    symbol (`<ns>.<Sort>.T`), which is precisely what the dangling `Box[T = Box.T]` above shows a
    body read resolving to. `op.type_params` itself cannot be re-keyed (`seed_op_type_args` matches
    call-site labels against the bare-interned names); only the eval channel is translated, and the
    sort half needs the same treatment.

BLAST RADIUS — MEASURE IT, do not assume it. This changes what `Box[T = X].op()` MEANS for every
parameterised sort member in the corpus, not only nullary ones: a call whose bracket disagreed with
its context loaded clean before and must be refused after. The delivery must CENSUS the corpus for
such calls and report how many change verdict, in BOTH directions (newly refused, and newly pinned
where the old answer was a free variable).

ACCEPTANCE.
  * `Box[T = Int64].empty()` in an `Option[T = Letter]` position is a LOUD refusal naming both
    types; the matching `Box[T = Letter].empty()` loads, and a `let`-bound value of it types as
    `Option[T = Letter]`.
  * `Box[T = Letter].selfType()` with `operation selfType() -> Type = Box[T = T]` EVALUATES to
    `Box[T = Letter]` — the dangling `Box[T = Box.T]` is gone.
  * TWO-PARAMETER ARITY IS DRIVEN, not only one: a member of `Pair[A, B]` called as
    `Pair[A = X, B = Y].member()` reads BOTH parameters. A one-parameter fixture cannot tell a
    correct implementation from one that binds only the first.
  * The two controls above keep their verdicts, and the test header says they pass either way BY
    DESIGN: the argument-carried pin, and the conflicting-bracket refusal.
  * The 058 §4.2 COLLISION refusal is unchanged — it is the other half of the same rule, and a
    change that lifted it would be a different ticket.
  * cargo-test green via rustland/scripts/test.sh.

RUST-ONLY: scaland loads no operations, so there is no twin to keep in step.

REFERENCE: 058 §4.2 rule 1 (the rule, both halves); WI-708 (the operation half of the eval channel,
and the keying rule this must copy); WI-272 (the channel itself); WI-709/WI-710 (the validation
that already fires on the bracket). CLIENT: WI-20260911-WT8WG — the `domain` VALUE face is a
derived per-sort `<Sort>.domain()` whose type-argument arity IS the sort's own (none for `Colour`,
one for `List`, two for `Pair`), which is unbuildable until a receiver bracket binds those
parameters. Found while measuring WT8WG's question (1).

## Changes

### 2026-09-11T11:48:38Z — feedback — claude

IMPLEMENTATION PLAN (claude, 2026-09-11, session with user) — refined against the user's
operation/rule framing (2026-09-11, see WI-20260910-6ARRN) and MEASURED at 1eb89144. Typing rows
were driven through CLI `anthill load`; eval rows through a scratch direct-child test calling
`interp.call` on the wrapper operations below. Every probe was then removed.

0. THE FRAME (user's direction). A sort's type parameter read inside a member is a PROJECTION off
the receiver's instance, and the two engines read it differently:
  * OPERATION. `p(x: List, y: List)` at namespace level gives `x.T` and `y.T` — two projections,
    one per value, INPUT-ONLY: Γ decides at the call, the body sees a rigid. This is already the
    rule — kernel-language.md §8.1 "How the slot is named (WI-1059)": the skolem an unwritten
    slot takes is the projection off the value that carries it; and inside the sort's own
    definition the bare self reference is the parametricity tie instead
    (type-parameter-scoping.md §3, WI-1082). A member with NO value to project off —
    `Box[T = X].empty()` — has the receiver bracket as the instance, and that is this ticket.
  * RULE. `p(?x: List, ?y: List)` is `p(?x: List[T = ?v1], ?y: List[T = ?v2])`: the unwritten
    parameters become rule-scoped variables, de Bruijn-bound like value variables and opened
    fresh per resolution, and they flow BOTH ways — from a value's runtime type, from a body
    goal, from a citation's bracket. That is the WI-582 `[T]` head introducer made implicit per
    occurrence, plus the two readers it lacks. It is 6ARRN's half (§5 below), not this ticket's.
  One principle, to be recorded once in the spec (§8.1, beside WI-1059): a sort parameter
  inside a member is a projection off the receiver's instance — an operation READS it (Γ,
  input only, rigid in the body), a rule UNIFIES it (σ, both directions). RS2G4 = the OPERATION
  half, at both sites.

1. MEASURED — the gap is narrower at the typer and wider at eval than the ticket says.
  TYPING (`sort Box[T] { entity box(v: T); operation empty() -> Option[T = T] = none() }`):
    `operation p8() -> Option[T = Letter] = Box[T = Int64].empty()`        loads clean (the row)
    `operation p8c() -> Option[T = Letter] = Box.empty[T = Int64]()`       REFUSED: "type
        mismatch in p8c.return (op-return): expected Option[T = Letter], got Option[T = Int64]"
    `let v: Option[T = Int64] = Box[T = Letter].empty()`                    loads clean
    `Box[T = Letter].empty[T = Int64]()` in the `Letter` position           refused only through
        the return ("got Option[T = Int64]"): the callee bracket won, the receiver was dropped,
        and two written brackets disagreeing is itself reported nowhere
    `Map.size[K = Bool, V = Bool](put(Map.empty(), "a", 1))`               REFUSED: "size.type_args
        (op-type-params): expected consistent bindings for the sort's shared type parameter
        (first bound to Bool), got String"
    `Map[K = Bool, V = Bool].size(put(Map.empty(), "a", 1))`               loads clean — and is
        PINNED clean by wi_w6jh0_companion_receiver_bracket_test::
        a_receiver_bracket_on_a_non_constructor_callee_is_left_alone and by kernel-language.md's
        W6JH0 paragraph ("A callee returning some other type … is untouched")
    `Map.put[V = Bool](Map.empty(), "a", 1)`                                "put.value (op-arg):
        expected Bool, got Int64"
    `Map[V = Bool].put(Map.empty(), "a", 1)`                                "put.return
        (op-return): expected Map[V = Bool], got Map[K = String, V = Int64]" (W6JH0's late arm)
  So THE BINDING HALF ALREADY EXISTS FOR THE CALLEE-BRACKET SPELLING: `call_bracket_scopes`
  (WI-841, "058 rule 1") spans the enclosing sort's params, `seed_op_type_args` binds the sort's
  CANONICAL var in `subst`, and `Option[T = T]` sees it. What is missing is one writer: the
  RECEIVER bracket (`recv_type`, W6JH0) never reaches that seeding — it is read once, late, and
  only when the declared return is the receiver's own sort.
  EVAL (`operation selfType() -> Type = Box[T = T]`, `operation viaSibling() -> Type =
  selfType()` inside Box; `sort Pair[A, B] { … operation both() -> Type = Pair[A = A, B = B] }`;
  `operation ty[U]() -> Type = Box[T = U]`):
    `Box[T = Letter].selfType()`            => Box[T = Box.T]      (the ticket's row)
    `Box.selfType[T = Letter]()`            => Box[T = Box.T]      the CALLEE spelling dangles
                                                                    too, though the typer bound T
    `Pair[A = Letter, B = Int64].both()`    => Pair[A = Pair.A, B = Pair.B]
    `Box[T = Letter].viaSibling()`          => Box[T = Box.T]      a bare SIBLING call inside the
                                                                    member loses the instance
    `ty[U = Letter]()`                      => Box[T = Letter]     WI-708 control, reads fine
  The dangling symbol is the qualified `<ns>.Box.T` — the sort's own parameter symbol, i.e. the
  `(Symbol, TermId)` pairs `sort_type_params_as_pairs` already hands `call_bracket_scopes`. So
  the eval key is that symbol as is; no re-resolution in the WI-708 style is needed (assert the
  identity in the test anyway, as wi708 did).

2. WHERE THE TICKET'S TEXT NARROWS OR MISPLACES.
  * "Seed the SORT's type-parameter vars from the receiver's bracket" is not a new mechanism; it
    is routing `recv_type` into the seeding the callee bracket already has.
  * The eval half is owed for BOTH spellings and has a THIRD site — sibling inheritance —
    that neither spelling reaches.
  * "058 §4.2 rule 1": the proposal file's §4 has no §4.2. The rule is stated in
    docs/design/058-implementation.md line 15 ("Key resolution rule 1 spans the op's and the
    enclosing sort's type params … built as WI-841") and in `call_bracket_scopes`' doc. Cite
    those. Proposal 035 §"Surface form (3)" already says the receiver semantics outright:
    "desugars to `empty()` resolved within the scope of `Map`, with K and V bound at the call"
    (and commitment 1). W6JH0 delivered the RESULT consequence only, and kernel-language.md:2792
    wrote that narrowing down as the rule ("untouched", "it is the receiver that reaches the
    value") — that paragraph is what the delivery rewrites.

3. TYPER — one insertion, EARLY.
  SITE: `check_apply_iter`, operation path, immediately after `seed_op_type_args`
  (typing.rs ~17434) and BEFORE the WI-424 rigid fill and the WI-367 carrier pass.
  STEP: `if let Some(rt) = call_recv_type_of(occ)` and `impl_parent_sort_of_op(fn_sym)` is
  `Some(parent)` whose canonical sort is `rt`'s head: build the parent's self type at its
  canonical vars — `make_parameterized_type(make_sort_ref(parent), sort_type_params_as_pairs
  (parent))`, the term load.rs's `domain_self_type` already builds — and
  `unify_types(subst, self_type, rt)`. READ THE VERDICT: the only earlier writer is the callee
  bracket, so `false` means two written brackets bind one parameter differently — a new
  `TypeError` naming the parameter, the receiver's value and the callee bracket's value (the
  sibling of WI-839's `one_type_parameter_bound_twice_in_a_bracket_is_loud`, one spelling over).
  A receiver whose head is not the callee's parent sort is left to the W6JH0 arm as today; its
  parameter NAMES were already checked at load (`build_recv_type` → `type_expr_to_child_inner`).
  WHY EARLY and not at the W6JH0 arm: (a) form (3) then reads exactly as the callee bracket —
  the verdicts measured above for `Box.empty[…]()`, `Map.size[…](…)`, `Map.put[…](…)` become
  the receiver spelling's verdicts, one rule two spellings; (b) a WRITTEN receiver must beat
  WI-424's implicit rigid fill (WI-1082: a written slot is never rewritten), so a sibling call at
  another instance — `Box[T = Int64].empty()` inside `sort Box[T]` — types at `Int64` instead of
  being refused against the rigid; a late seeding would refuse it; (c) the W6JH0 arm stays as the
  RESULT rule for a bare self-sort return (`empty() -> Map`, WI-1082's untied return): it now
  finds `rt` already agreeing, reports nothing new, and its merge is untouched.
  WHAT MOVES — three rows of wi_w6jh0_companion_receiver_bracket_test.rs, each by design:
    (1) `a_receiver_bracket_on_a_non_constructor_callee_is_left_alone` FLIPS to loud: the
        receiver binds `K`, `m: Map` is tied to `Map[K = K, V = V]` (WI-1082), so `put(…"a"…)`
        contradicts it — with the callee-bracket message measured above. This is the ticket's
        "a call whose bracket disagreed with its context loaded clean before and must be refused
        after", and it is the row that separates this ticket from W6JH0.
    (2) `the_two_bracket_spelling_honours_the_receiver`: the disagreeing pair becomes ONE
        contradiction naming both brackets (today: receiver wins, two argument errors). The
        agreeing pair still loads — keep that half as the control.
    (3) `a_contradicting_partial_receiver_bracket_is_refused`: still exactly one error; the site
        moves from `put.return` to `put.value (op-arg): expected Bool, got Int64`, byte-identical
        to the callee spelling. Reword the assertion and its doc's "reported at the receiver".
  UNCHANGED, and the delivery says so: `the_callee_bracket_still_does_not_reach_the_result`
  (bare return, WI-1082 untouched), `a_true_partial_receiver_bracket_keeps_the_inferred_slots`,
  `form_one_and_form_three_agree`, `a_contradictory_receiver_bracket_is_a_located_error`
  (argument-located already), the unread-bracket sweep, the name checks.
  THE TICKET'S ROWS under this placement: p8 refused at `p8.return` naming both `Option[T =
  Letter]` and `Option[T = Int64]`; the `let` row refused at the let; `Box[T = Int64].mine(b)`
  with `b: Box[T = Letter]` refused at `mine.b` (expected `Box[T = Int64]`, got `Box[T =
  Letter]`) — still loud, site moves from the return to the argument; the bracket-less
  `Box.mine(b)` control is untouched.
  SPEC: rewrite kernel-language.md:2792 — a companion receiver's bracket BINDS the sort's
  parameters for the call (rule 1's sort half, every member), result typing is one consequence
  of it; the `size` example becomes "checked against `m`"; two brackets disagreeing on one name
  is a contradiction, not "the receiver wins"; the sentence that the callee bracket does not
  reach a BARE self-sort return stays. Add the receiver spelling to 058-implementation.md line
  15's list of writers of the same key. One sentence beside WI-1059 in §8.1 for the principle
  in §0 (both engines), and cross-reference type-parameter-scoping.md §3.

4. EVAL — two sites.
  SITE 1, the writer: typing.rs ~19020 (`set_resolved_type_args`). After the `op.type_params`
  loop, for each `(sym, var_term)` of `sort_type_params_as_pairs(parent)` with `parent =
  impl_parent_sort_of_op(fn_sym)`: walk through `subst` exactly as the op loop does
  (`walk_type_deep` + `surface_node_binding_to_term`), key = `sym` unchanged (measured: it is the
  symbol a body reference resolves to). SKIP an entry whose walk lands on one of
  `env.enclosing_instance_param_rigids()` — a rigid is the body's name for "the enclosing
  instance", which has no type-time value; it is the eval's to forward (site 2). Replace the
  `!op.type_params.is_empty()` guard by "either list non-empty", so a bracket-less namespace op
  still writes nothing. Key distinctness: op-scoped `<ns>.<op>.T` and sort-scoped `<ns>.<Sort>.T`
  are different symbols and WI-840 refuses equal SHORT names, so `find_type_arg`'s last-wins
  order cannot matter; say so at the site. `simp_rewrite.rs` 1404/1739 preserve or drop the
  whole `resolved_type_args` Vec, so the sort entries ride the same rules — check neither site
  assumes the Vec is empty for a `[]`-less op.
  SITE 2, inheritance: eval.rs `enter_operation` (~3196), where the callee frame's `type_args`
  is installed. When the callee's parent sort equals the CALLER frame's operation's parent sort
  and the callee's channel lacks a sort-scoped key the caller frame holds, inherit the caller's
  entry — `start_apply_same_sort`'s WI-841 rule ("same-sort inherit, unless the call site chose
  explicitly") applied to the type-arg channel. ONE place, the frame install, not per dispatch
  route: dictionaries differ per route, type arguments do not. Measured need: `viaSibling`
  above, and every bare sibling call inside a member body (`Box[T]` has no `requires`, so it is
  a plain apply and never sees `start_apply_same_sort`).

5. THE RULE HALF — 6ARRN's, NOT this ticket's, sketched so the two do not drift:
  (i) implicit introducer: an unwritten parameter of a parameterised sort in a rule head bound
      (`?x: List`) becomes a rule-scoped type variable per occurrence — WI-582's `[T]` without
      writing it, opened fresh per resolution like every de Bruijn variable; the loader site is
      `collect_rule_tvar_names` / `rule_head_tvar`, and `bound_names_a_determinate_type`'s
      `Term::Var` arm is the refusal that would stop being needed;
  (ii) the derived `domain_member` clause takes its TYPE ARGUMENT AS AN INPUT read off the
      value (`value_type_term`; WT8WG item 8) — without it a free type variable makes every
      derived clause a candidate (WT8WG item 7's undecided tail, 20 rows / 1 definite);
  (iii) a citation bracket (`p[T = Letter]`, `List[T = Letter].p`) binds the head's variables
      in `build_relation_value`'s query — today WI-839 refuses it as "not an operation", and
      WT8WG item 3 measured that no type argument reaches a clause;
  (iv) no new body surface: inside the rule the projection IS `?v1`, so a body writes it as any
      variable; whether `?x.T` should also be spellable is a surface question for 6ARRN.
  Not filed as delivery; ask before splitting 6ARRN.

6. ACCEPTANCE (the ticket's, sharpened by the measurements).
  TYPING: p8 refused naming both types; `Box[T = Letter].empty()` loads and a let-bound value
  types `Option[T = Letter]`; the two-bracket contradiction is loud naming both brackets while
  the agreeing pair loads; `Map[K = Bool, V = Bool].size(…String…)` refused with the message
  the callee spelling gives; the `Pair[A = X, B = Y].member()` return read at BOTH parameters.
  EVAL: `Box[T = Letter].selfType()` AND `Box.selfType[T = Letter]()` evaluate to
  `Box[T = Letter]`; `Pair[A = Letter, B = Int64].both()` to both; `Box[T = Letter].viaSibling()`
  to `Box[T = Letter]`; WI-708's `ty[U = Letter]()` unchanged.
  CONTROLS, with the back-out each measures, stated at the site:
    typer site backed out → p8 loads clean, the `size` row loads clean, the two-bracket pair is
      two argument errors (W6JH0's old verdicts); the callee-spelling rows (`Box.empty[T =
      Int64]()`, `Map.size[…](…)`) pass EITHER WAY BY DESIGN — WI-841 delivered them;
    eval site 1 backed out → the four sort-param eval rows dangle, the WI-708 control passes;
    eval site 2 backed out → only `viaSibling` dangles, the direct rows pass. A single "all off"
      run credits one site for the other's rows — run the three back-outs separately.
  CENSUS: static grep for `Sort[…].member(` (a LOWER bound — nested brackets escape the regex)
  finds 0 in stdlib, 0 in examples, 0 in loaded anthill-todo code (its 40 hits are ticket
  prose), 61 in nine anthill-core test files: map_builtins_test, parse_test, wi1025, wi843,
  wi_2nxac, wi_bad3v, wi_fcz3n, wi_h054k, wi_w6jh0. Dynamic census at delivery: a counter at the
  new seeding site over the full suite plus `anthill load` of the three corpora, reporting
  newly-refused and newly-pinned SEPARATELY; every corpus flip must land in one of those files.
  WI-840's collision refusal unchanged; scaland untouched.

7. ORDER: (1) typer site + the three W6JH0 rows + the spec paragraph; (2) eval site 1 + its
rows; (3) eval site 2 + the sibling row; (4) census + delivery note; (5) WT8WG's derived
`<Sort>.domain()` needs (1)+(2) and unblocks then.

### 2026-09-11T12:03:51Z — feedback — claude

ADDENDUM — NESTED UNWRITTEN PARAMETERS (`List[List]`, `List[List[T]]`), the user's question of
2026-09-11. MEASURED at 1eb89144 with the same probe routes as the plan above; all removed.
The nested case changes §3 of the plan: as written, the early receiver seeding would IMPORT an
existing hole of the callee-bracket spelling into the receiver spelling.

1. TYPING — a bracket VALUE with a bare inner sort ERASES what an argument says about the inner
element, TODAY, in the callee spelling. Fixture: `sort Box[T] { entity box(v: T); operation
mine(b: Box) -> Option[T = T] = none(); operation empty() -> Option[T = T] = none() }`, declared
return `Option[T = List[T = String]]`, argument `box(v: [1])` — a `Box[T = List[T = Int64]]`:
    (1) `Box.mine(box(v: [1]))`                         REFUSED "expected Option[T = List[T =
                                                         String]], got Option[T = List[T = Int64]]"
                                                         — the control: the argument's inner type
                                                         reaches the result
    (2) `Box.mine[T = List](box(v: [1]))`               LOADS CLEAN — the hole
    (3) `Box.mine[T = List[T = Int64]](box(v: [1]))`    REFUSED (written inner slot)
    (4) `Box.empty[T = List]()`                         loads clean — nothing else determines the
                                                         inner slot and the context completes it,
                                                         the partial-annotation reading. Fine.
    (5) `Box[T = List].mine(box(v: [1]))`               REFUSED today — ONLY because the receiver
                                                         is dropped, so the argument decides
    (6) `let v: Option[T = List[T = String]] = Box.mine[T = List](box(v: [1]))`   loads clean —
                                                         the same hole through a let
  CAUSE: `seed_op_type_args` unifies the sort's canonical var with the value AS WRITTEN —
  `?T := Ref(List)` — and unification width-ignores an absent slot (WI-1082's exploit shape,
  re-entered through a bracket VALUE). The argument's `Int64` binds a transient expansion
  variable inside `unify_parameterized_with_sort_ref` and reaches nothing. Under the plan's §3
  early seeding, row (5) becomes row (2).
  FIX, at the same site, BOTH spellings: EXPAND the bracket value's unwritten slots to fresh
  FLEXIBLE variables, one per slot at every depth, BEFORE `unify_types` — the WI-374 call-site
  expansion `expand_foreign_sort_application` (typing.rs ~17345), which already does exactly
  this to the callee's PARAMETERS, run on the written value. Then `Box[T = List]` seeds `?T :=
  List[T = ?f]`, the argument binds `?f := Int64`, the result carries it, rows (2), (5), (6)
  refuse, and row (4) keeps loading because its `?f` is bound by the context. A self-sort VALUE
  written inside the sort's own member body (`Box[T = Box]…` inside `sort Box`) is for the
  delivery to measure: the WI-374 expansion exempts the callee's own sort in a SIGNATURE, for
  the §3 tie; a written bracket value is not a signature, so the exemption should not apply.
  CENSUS WIDENS: callee-bracket calls whose value names a parameterised sort bare are newly
  refused wherever an argument or the context contradicts the slot they erased. The dynamic
  counter must classify them as their own kind ("callee bracket, bare value"), separately from
  the receiver-bracket kinds in the plan.
  ACCEPTANCE ROWS ADDED: (2), (5), (6) refused naming both inner types; (3) unchanged; (4) loads
  and passes either way BY DESIGN. Back-outs: the expansion alone backed out → (2) and (6) load
  clean again while (5) stays refused; (5) loads clean only when the receiver seeding is ALSO
  backed out. Two axes, two back-outs.

2. EVAL — nested reads and nested values already travel; only the carrier of a bare inner
value needs pinning.
    `operation tyn[U]() -> Type = List[T = List[T = U]]`, `tyn[U = Letter]()`
                                             => List[T = List[T = Letter]]   a nested BODY read
                                                substitutes — nested `SortTypeArgs` frames each
                                                consult the channel, WI-708's mechanism recurses
    `operation tyb[U]() -> Type = Box[T = U]`, `tyb[U = List[T = Letter]]()`
                                             => Box[T = List[T = Letter]]   a nested WRITTEN value
                                                survives the channel; the walk is deep
    `tyb[U = List]()`                        => Box[T = List]               a bare inner value
                                                arrives BARE
    `Box[T = List[T = Letter]].nestedSelf()` with `nestedSelf() -> Type = List[T = List[T = T]]`
                                             => List[T = List[T = T]]       dangling today, the
                                                plan's sort-scope gap at depth
  So `List[List[T]]` in a member body needs no new mechanism: add it as an acceptance row, both
  spellings, expected `List[T = List[T = List[T = Letter]]]`. With the fix in (1) a bare inner
  value arrives as `List[T = ?f]` — an unbound variable term when nothing bound `?f` — instead
  of `Ref(List)`. DECIDE ONCE and PIN what the channel carries for it; both are honest ("a list
  of something") and `bound_names_a_determinate_type` already refuses both shapes (its
  `Term::Ref` arm and its `Term::Var` arm). The CONSUMER owns the verdict: WT8WG's
  `domainOfType(t)` must apply that predicate at the value face and RAISE, never answer zero
  rows — `domain_member(?x, Ref(List))` matches no derived head (WT8WG item 6), so an unguarded
  value face is a silent empty relation. That is WT8WG's row; named here so RS2G4's channel test
  pins the carrier WT8WG will read.

3. RULES (6ARRN) — the gate is recursive, and today a SILENT SKIP of the domain goal.
`bound_names_a_determinate_type` walks every child, and its caller `continue`s on false
(typing.rs ~70379: "SKIPPED, not repaired — WI-742's reading of such an annotation stands
unchanged — conformance, then the delay/flounder ladder"). So `rule p(?w: List[T = List])` gets
conformance but no enumeration, and nothing says so. 6ARRN's implicit introducer must therefore
be RECURSIVE — a fresh rule-scoped variable per unwritten slot at every depth, `List[T = List[T =
?v2]]` — and the (in, out) domain read must hold at every depth. WT8WG item 7's `rule nest(?w:
List[T = List]) :- ?w <=> [[a()]]` IS the nested row: 20 rows / 1 definite under fresh
variables, 1 / 1 under today's skip; 6ARRN must make it 1 / 1 WITH the goal present. The
self-reference exception stays separate and keyed by declaration context: `repair_self_reference`
reads a bare `List` inside `List`'s OWN definition as the same element type, so the recursion
closes — the rule twin of type-parameter-scoping.md §3 — while a bare inner `List` written
OUTSIDE `List` is fresh.

4. `List[List[T]]` with `T` the enclosing sort's parameter or a head `[T]` introducer: nested
position is no different from top level. The typer's deep walk, eval's nested `SortTypeArgs`
frames (§2's first row) and a head variable at depth are one variable, and WI-840's collision
refusal keeps an operation's own `[T]` from shadowing the sort's, so there is no second reading
to choose between.

