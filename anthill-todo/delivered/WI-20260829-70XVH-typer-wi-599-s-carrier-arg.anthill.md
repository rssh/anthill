## Attributes

- id: WI-20260829-70XVH-typer-wi-599-s-carrier-arg
- created: 2026-08-29T19:02:25Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-30T12:38:06Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPER: WI-599's `carrier_arg_provision_projection` covers the SPEC-METHOD shape ONLY, and the FREE-OP shape it excluded has NO TICKET.

WI-599 IS DELIVERED — this is not unfinished work inside it, it is a scope boundary its own
delivery note draws and that nothing tracks:

  'Binding source = carrier_provision_short_bindings: the SPEC-METHOD case only
   (op(c:C,..) ON the spec) ... FREE-OP requires case (the WI repro tmap) NOT supported:
   op.rigidify not on env, requires-entry Refs don't resolve to body rigids -> would break
   the sibling field; documented, returns None -> original leak error.'

`grep -rl carrier_arg_provision_projection anthill-todo/{open,claimed,pre_opened}` is EMPTY.
WI-599 recommended splitting its OTHER gaps into their own WIs; this exclusion never got one,
so it exists only as prose inside a delivered item — which is how it was reachable again.

MEASURED while delivering WI-20260829-X13YV, which wanted exactly this shape. A free
operation on a DATA sort, generic over the source carrier, with an op-level `requires`:

  operation map[Sc, S, Dst, EffS, EffP](s: Sc, f: (x: S) -> Dst @ {EffP, -Modify[x]})
    -> MappedStream[Source = Sc, Src = S, T = Dst, ES = EffS, EF = EffP]
    requires Iterable[C = Sc, Element = S, E = EffS] =
    mapped(s, f)

  REFUSED -- type mismatch in anthill.prelude.MappedStream.map.type_arg:
      expected a type for 'S', got unconstrained — use `map[S = …](…)`

The element `S` does not ground from the argument's own provision though the `requires`
binds it. THE SORT-PARAM VARIANT IS NOT AN ESCAPE either — typing the input as the sort's own
`Source` param, covered by the sort-level `requires Iterable[C = Source, ...]`, fails
DIFFERENTLY: `Dst` goes unconstrained (the callback's return cannot be read off an argument
whose element type comes from a sort param rather than from the argument) and the effect row
leaks 'undeclared effect: ?_'. Both were measured; neither route is available.

WHAT THE ABSENCE COST X13YV: `MappedStream.map` / `FilteredStream.filter` had to be re-typed
onto their OWN carrier as receiver methods rather than staying general over any Iterable
source. That works and is driven — see `x13yv_map_map_chain_test` — but it NARROWED the two
operations: they no longer accept a bare `List`, which is why `wi439_iterable_filter_test`'s
parity op moved to `Iterable.filter`. Closing this gap would let them be general again, which
is the only reason to want it — so weigh that against the typer cost before claiming.

ACCEPTANCE: the free-op form above loads and grounds `S` and `Dst` from the argument's own
provision; `wi599_carrier_arg_provision_test` gains the free-op row beside its spec-method
one; state at the site which rows fail when it is backed out, and which pass either way.

## Changes

### 2026-08-30T12:38:00Z — feedback — claude

DELIVERED. The exclusion WI-599 documented is closed on BOTH sides, and the stdlib
generalization the ticket names as "the only reason to want it" landed with it.

WHAT THE TICKET NAMED vs WHAT WAS MEASURED. The title and the WI-599 quote point at
`carrier_arg_provision_projection`'s free-op face — a BODY question. The error the ticket
actually reports (`map.type_arg: expected a type for 'S', got unconstrained`) is a CALL SITE
question, and they are different mechanisms. Measured on the ticket's own free-op form:
  * its DECLARATION already loaded, because the return is spelled as the constructed carrier
    and `expected` then seeds every param the field loops left free (kept as the control
    `free_op_carrier_return_is_pinned_by_expected`);
  * routing the return through the carrier's PROVISION instead exposed the body gap —
    `got MappedStream[Source = ??_, ES = ??_, ...]`, the WI-599 exclusion exactly;
  * an ordinary CALL was refused `'S' unconstrained`, which no body-side threading reaches.
Both are the same unread clause, so both are delivered.

(1) BODY — `op_requires_provision_bindings`, the third face beside `carrier_provision_short_-
bindings` (spec METHOD) and `enclosing_requires_provision_bindings` (enclosing SORT). WI-599's
stated reason for excluding it ("op.rigidify not on env, requires-entry Refs don't resolve to
body rigids") expired with WI-942, which put the operation's own parameters in
`TypingEnv::param_rigids`; what was missing was wiring. Two reads differ from the sort faces:
`param_rigids` IN FULL (an op-level clause may name the operation's own parameters, which the
sort prefix excludes by construction), and the clause is decoded by
`op_requires_entry_carrier_map` — an op `requires` is stored as the bare `Fn{Spec, ...}`,
which `unwrap_spec_view_value` reads as the NO-BINDINGS case, so this face would have answered
for a clause it never read. The crossing to body rigids is identity-keyed
(`substitute_body_rigids`, joined on `type_param_global_var` against `param_rigids`), which is
why it needs no `param_leaves_belong_to_sort` twin: a foreign parameter is simply absent.

(2) CALL SITE — `bind_op_type_params_from_op_requires`, beside the WI-367/424 carrier
grounding (above the `expected` seeding, below `seed_op_type_args`). It reads the provision
exactly as `carrier_param_receiver` does; only WHICH variables the answer lands on differs —
the clause says which of the OPERATION's parameters each spec parameter is. Gated on the
callee declaring both brackets and a `requires`, so the >99% path pays two `is_empty()` reads.

A DESIGN BOUNDARY MEASURED BEFORE IT WAS DECIDED. This pass also makes a program load that
was refused before: with two witnesses disagreeing at one carrier it binds from the first.
WI-1091 says "neither may be picked for the author" — but about HOST-ENTRY dictionary
completion, a channel with no static receiver type. The typer's read of the SAME pair already
picks: with this pass neutralized, `Pair.combine(t)` grounds `F := Int64` from the first
witness and refuses a `-> Tag` return, through `bind_spec_params_from_carrier_param`. A
stricter rule here would make two readers of one question disagree by which declaration named
the spec, so it is stated at the site rather than special-cased.

STDLIB — `MappedStream.map` / `FilteredStream.filter` are GENERAL AGAIN (any `Iterable`
source, `Source = Sc` kept in the return). 4 lines each, whole workspace green including
X13YV's chain rows, so it landed inline rather than as a follow-up. The route is unchanged:
`.map` on a mapped stream still resolves to `MappedStream.map`, `MappedStreamFinite` still
recurses on `Source`, and a `.map` over an infinite source still loads while only its
consumption is refused.

/code-review (high) RAISED SIX, ALL ADDRESSED; one was a real drivable defect:
  * THE CARRIER GATE WAS TOO NARROW. `clause_named_op_type_param` was used for the clause's
    CARRIER as well as its targets, so a clause whose carrier names the ENCLOSING SORT's
    parameter — `wrap[El, ...](x: C, ...) requires Iterable[C = C, Element = El, ...]`, the
    ordinary shape for an operation on a parametric sort — was unreadable, and `El` stayed
    unconstrained while the function's doc claimed the opposite. Fixed by splitting the read:
    the CARRIER may name either scope (it only says which ARGUMENT the clause is about), the
    TARGET stays the operation's own (a sort parameter is the sort INSTANCE's, not this
    call's). New driving row `a_clause_whose_carrier_is_the_enclosing_sorts_parameter_still_-
    grounds`, with its own back-out.
  * `substitute_body_rigids` accepted ANY `Var::Rigid` verbatim while every other join is by
    VarId identity — now membership-tested, so "already this body's own skolem" is enforced
    rather than assumed.
  * the decline path interned a rebuild it discarded (`kb.alloc` increments on hit, and the
    store has a free list) — the child walk now short-circuits before rebuilding.
  * the argument-type lookup was a verbatim second copy of `carrier_param_receiver`'s — now
    one `supplied_arg_type`, since the two ask "which argument is the receiver" and "whose
    provision grounds the element" and must not drift.
  * the spec's-first-param carrier convention is now stated, as the sibling states it.
  * a control record named a back-out that no longer typechecks ("returning `false`" after
    the function was changed to report nothing) — corrected.

TESTS — `wi599_carrier_arg_provision_test` gains 8 rows beside its spec-method one, and the
file header carries SEVEN back-outs, each run over every row:
  1. body face returns `None`         -> `free_op_requires_clause_threads_the_field_specs_params`
  2. call face returns at entry       -> FOUR rows, including `the_stdlib_combinators_...`
                                         (the stdlib widening DEPENDS on this pass, which is
                                         why they are one commit)
  3. the already-bound skip removed   -> NOTHING (recorded as un-drivable, below)
  4. body "about this argument" gate widened -> `free_op_clause_about_another_param_...`
  5. call carrier search widened to arg 0    -> `a_clause_about_another_parameter_...`
  6. carrier read narrowed to the op's own   -> `a_clause_whose_carrier_is_the_...`
  7. either stdlib signature restored to X13YV form -> `the_stdlib_combinators_...`
`spec_method_bare_carrier_threads_source_and_effect` (the WI-599 row) and
`free_op_carrier_return_is_pinned_by_expected` pass under all seven, by design.
`the_stdlib_combinators_are_general_over_any_iterable_source` DRIVES to values
(2468 / 234 / 3579 / 23 / 68 / 4).

BACK-OUT 3 IS RECORDED AS UN-DRIVABLE rather than dressed up: `Substitution::bind_term`
already refuses to overwrite (it flags a contradiction instead), so removing the pass's own
already-bound skip leaves every row green. The skip is kept because "leave the author's
value" and "mark the substitution contradictory" are different behaviours and only one is
additive; both the site and the test say so.

ALSO UPDATED, each having carried a claim this ticket voided: `combinators.anthill`'s "WHAT
THE SHAPE COST" note, `x13yv_map_map_chain_test`'s header, and `wi439_iterable_filter_test`'s
"so it no longer accepts a List" (the parity partner stays `Iterable.filter` — that row
measures the ERASING spelling, which it is either way). `kernel-language.md` 5.2 gains a
paragraph: an op-scoped requirement DETERMINES as well as licenses, with its three limits.
`assert_refused_naming` moved to `common` — a control's value is that its token is the one a
back-out removes, and two copies could drift on what "refused" means.

UNRELATED BUT LANDED HERE because it was found by killing the machine three times mid-ticket:
`rustland/rustfmt.toml` now carries `ignore = ["src/kb/typing.rs"]`. rustfmt reaches ~15.3 GB
anon-RSS on that 3.7 MB file and is OOM-killed with the whole WSL VM; rustc/rust-lld/cargo
were killed zero times. Verified under `ulimit -v 4000000`: `cargo fmt -p anthill-core --
--check` now completes inside 4 GB with `typing.rs` untouched. Consequence stated in the file:
that one source is hand-formatted and nothing checks it. Filed WI-20260830-009H2 for the
file's SIZE, then pre-opened it — splitting would not fix rustfmt, only move the threshold.

ACCEPTANCE: cargo-test green — full workspace, 36 binaries, 6172 passed, 0 failed.
scaland-sbt-test green — 548 passed, 0 failed (relevant: `EmbeddedStdlib` reads the same
`combinators.anthill`, and this is the first op-level `requires` in the stdlib).

