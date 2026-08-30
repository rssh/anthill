## Attributes

- id: WI-20260829-W6JH0-typing-a-companion-receiver-s
- created: 2026-08-29T23:22:44Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-30T06:40:47Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPING: a companion receiver's type-arg bracket is INERT -- `Map[K = Bool, V = Bool].empty()` accepts a String key with no diagnostic.

SURFACED BY /code-review ON WI-20260829-BAD3V, which made the two-bracket spelling
`Map[K = String, V = Int64].empty[T = Int64](x)` newly writable and so put a read bracket
and a dropped one side by side. The REVIEW read the drop as introduced there; it is not,
and this ticket is the pre-existing half, filed rather than left in a test comment.

MEASURED, all three load with ZERO errors:

  operation build() -> Int64 = size(put(Map[K = String, V = Int64].empty(), "a", 1))
  operation build() -> Int64 = size(put(Map.empty(), "a", 1))
  operation build() -> Int64 = size(put(Map[K = Bool, V = Bool].empty(), "a", 1))   <-- !!

The third writes `K = Bool, V = Bool` and then puts a `String` key and an `Int64` value.
It is accepted. So the receiver's bracket is not merely dropped from the CALL -- it
constrains nothing at all, and does not even catch a direct contradiction with the
argument types it appears to annotate.

THE MECHANISM. `Map[…].empty` is a `field_access` whose object is an `application`.
`collect_field_access_segments` (parse/convert.rs) takes form (3) of proposal 035 and
flattens it to the segments `Map.empty` with, in its own words, "bindings erased" -- the
runtime call path wants the sort's NAME. Nothing downstream ever sees `K`/`V`, so the typer
infers them from the arguments and the written bindings are inert text.

WHY IT LOOKS DELIBERATE AND STILL IS NOT SETTLED. The erasure is what makes form (3) work
at all (`map_builtins_test::form_3_instantiation_receiver_parses_and_runs` drives it), and
a type-erased runtime does not need K/V. But an author writing them is making a claim, and
the language checks every other written type claim. Two coherent answers:

  (a) HONOUR THEM -- unify the receiver's bindings against the sort's params for the call,
      so the third program above is a located type error. This is the reading every other
      written binding gets.
  (b) REFUSE THEM -- if the receiver bracket cannot be honoured, a written one is a load
      error naming form (3) and telling the author to drop it or annotate the result.

Either is better than the present silence, and (b) is cheap if (a) is not wanted.

WHAT BAD3V CHANGED, so this is not re-derived: it made the CALLEE bracket readable on this
shape (`Map[…].empty[T = Int64]()` now carries type args on the same channel
`Map.empty[T = Int64]()` always did). It did not touch the receiver bracket. The two are
independent -- `Map[K = Bool].empty()` was already inert before BAD3V, which is the
measurement above.

ACCEPTANCE: `Map[K = Bool, V = Bool].empty()` with a String key is a LOCATED error (or the
bracket itself is refused, if (b) is chosen); the working form-(3) rows in
`map_builtins_test` stay green and are named as the controls that pass either way; and if
(a) is taken, say what happens when the receiver's bindings and the callee's bracket bind
the SAME name, since BAD3V's spelling now admits both at once.

## Changes

(a) HONOUR THEM -- but NOT by the mechanism the ticket proposed, and finding out why is
most of the work.

THE TICKET'S (a) WAS "unify the receiver's bindings against the sort's params for the
call". That is ALREADY WHAT THE CALLEE BRACKET DOES: `call_bracket_scopes` appends the
parent sort's params to the callee's own, so `Map.empty[K = Bool, V = Bool]()` reaches
`seed_op_type_args` and binds `Map.K`/`Map.V` in the call's substitution. MEASURED: it
still accepts a `String` key. The binding has nowhere to land, because `empty() -> Map`
returns the sort BARE and WI-1082 leaves a constructor's self-sort return untied on
purpose ("NO SELF PARAMETER, NO TIE ... a raw canonical var in `resolved_ret` is the
dangling-flex hazard"). So the receiver has to name the RESULT, not the substitution.

TWO INDEPENDENT GAPS, WHERE THE TICKET SAW ONE. The table it measured is right about the
receiver bracket and wrong about the callee one being the working channel:

  | spelling                         | bogus param name | contradiction with later args |
  | receiver `Map[K = Bool].empty()` | silent           | silent                        |
  | callee `Map.empty[K = Bool]()`   | LOCATED ERROR    | silent                        |
  | annotation `let m: Map[K = Bool]`| LOCATED ERROR    | LOCATED ERROR                 |

The second column is a SHARED gap, not a receiver one. Only the receiver half is closed
here; `the_callee_bracket_still_does_not_reach_the_result` pins the other as a control, and
closing it means reopening WI-1082 for every companion call returning its own sort.

(b) WAS NOT AVAILABLE. Proposal 035 lists form (3) beside forms (1) and (2) as three
spellings of one thing, and names it the REQUIRED disambiguator when nothing else
constrains the call ("the typer requires explicit form (3) or an annotation"). Refusing the
bracket would have deleted the third spelling. The reading implemented is 035's own
sentence -- "method dispatch on it produces values typed at those bindings".

THE SHAPE. Parse keeps the receiver's instantiation term as a `ParseAux::TypeExpr` -- the
SAME variant a `let m: T = ...` annotation rides, because under form (3) it means the same
thing about the same expression -- on the channel beside `type_args`. `Expr::Apply` gains
`recv_type: Option<Value>`, a field and not a merge into `type_args`, because the two
answer different questions and only one of them can be honoured today. The typer takes it
as the call's result when the declared return's base IS the receiver's sort.

THE NAME CHECK COSTS NOTHING AND WAS NOT WRITTEN. A first cut added its own
`check_sort_type_args` and reported the same fault TWICE; `type_expr_to_child_inner`'s
WI-709 check ("one written type cannot mean two things") already runs on every written
type, and the receiver bracket was unchecked only because it never reached a lowering at
all. Deleting my check was the fix. Kept as a note at the site -- the question "who
validates a written type" already had an owner.

THE COMPILER DID THE PRODUCER CENSUS. Adding the field flagged 10 destructuring sites; 6
are rebuilds that now thread it (DeBruijn open/close, sigma, body-specialize x2, spec-op
re-dispatch, functor re-pointing, smt-gen closing), 2 are macro-surface DECLINES joined to
the existing `type_args` decline, and 2 are deliberate drops with the reason at the site:
the TERM TWIN does not carry it (035 SS"Runtime: type erasure" -- carrying it would give
`Map[K = Bool].empty()` a different discrimination key for a distinction no resolver step
can act on), and the view head therefore does not count it. A SECOND PRODUCER the compiler
could NOT flag was found by testing: a rule body is lowered by its own walk
(`build_body_atom_occurrence`) that built an `Expr::Apply` with the field defaulted, so the
claim vanished there while being honoured one lowering over -- now red on back-out.

THE TICKET'S EXPLICIT QUESTION -- both brackets binding the SAME name. They do not compete:
the callee bracket binds the callee's params in the call's substitution (what it has always
done), the receiver names the RESULT. Where they disagree, the receiver reaches the value --
`Map[K = Bool].empty[K = String]()` refuses a `String` key. Deterministic, not a tie to
break. Making a disagreement itself loud would need the callee bracket to reach the result,
which is the half left alone.

BACK-OUT CONTROL: THREE AXES, THREE BACK-OUTS, because one "turn it all off" run credits
one mechanism for another's rows. (A) whole feature off: 8 of 14 red, 6 green. (B) the
unread-bracket sweep alone off: EXACTLY 1 red and nothing else moves. (C) the merge alone
off -- this change's own first cut: 3 red. Each is a MUTATION, never a deletion, so what is
measured is the capability and not whether the tree still builds. One test was also SPLIT
after the first back-out showed it mixed a control row with a mover -- asserting both, it
would have reported only the stronger half.

/code-review (high), FOUR FINDINGS, all measured by the reviewer, all reproduced, all
fixed. Two were HIGH and both were cases of the change being LESS true than its own
comments claimed:

  * ONE CLAIM, TWO VERDICTS BY ARGUMENT SPELLING. `reorder_named_args_in_apply` rewrites a
    named-argument call into positional form and rebinds the occurrence, and it rebuilt the
    `Expr::Apply` with `recv_type` defaulted -- BEFORE the read. So the bracket was inert on
    any call written with named args and honoured on the positional spelling of the same
    call. It patterns with `..`, so the compiler census could not flag it; the sibling
    `gather_spread_args_into_tuple` had the same drop after the read (corrupting only the
    stored node). Both thread it now, and the test asserts the two spellings AGREE rather
    than that the named one errors.
  * A TRUE CLAIM REMOVED A CHECK. The arm returned the receiver's type verbatim, which
    discards every slot it does not write -- and for a callee whose declared return is
    parameterized (`put(m, key, value) -> Map[K = K, V = V]`, WI-1082's self-tie) those
    slots hold what the ARGUMENTS just determined. `Map[K = String].put(Map.empty(), "a",
    1)` is a perfectly TRUE partial claim and it deleted the inferred `V = Int64`, taking a
    real error one call out with it: 1 error -> 0. The receiver is unified INTO the declared
    return now and the resolved return comes back; the receiver's own type is the result
    only where the declared return has no slots to carry, which is `empty()`. And the unify
    VERDICT is read: a contradicting bracket (`Map[V = Bool]` against an `Int64` value) used
    to load clean and is now a located error at the receiver, which is where the wrong claim
    is written.

The other two were ONE MECHANISM -- the new channel had no WI-839 "read or reported"
sweep, so every position that does not read it dropped the bracket in silence: an
ENTITY-CONSTRUCTOR callee, a fact head, and a `[simp]` rule head, all loading clean where
the `type_args` twin is a loud refusal. My own gate comment had asserted "the grammar
cannot produce a receiver bracket on either of those, so the gate never actually fires";
`Option[Bogus = Int64].some(1)` disproves it. The channel has its own sweep now. It is
called BESIDE the `type_args` sweep and not chained onto its tail, because that one returns
early when a file interned no `type_args` at all -- a file whose only bracket is a
receiver's would have swept nothing, which is how the first cut of the sweep measured as
doing nothing.

TESTS: rustland 35 binaries / 5895 passed / 0 failed (baseline 5881 + the 14 new). Not one
existing test moved -- the receiver bracket was inert, so only programs
writing form (3) can change. scaland 524 / 0: nothing to port, the Scala side has no typer
and the grammar is unchanged. kernel-language.md records the rule beside BAD3V's paragraph
on the same spelling.
