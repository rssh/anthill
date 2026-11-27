## Attributes

- id: WI-20260929-7XNSK-an-element-type-the-typer
- created: 2026-09-29T20:15:47Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-26T22:05:50Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN ELEMENT TYPE THE TYPER COULD NOT INFER DISPATCHES AS A WILDCARD, SO WHICH PROVIDER A CALL REACHES DEPENDS ON ARGUMENT ORDER. `sort Store2 { sort State = ?; operation peek2(s: State, t: State) -> Int64 }`, providers `CA` at `Buf[T = Int64, N = Bool]` (answers `s.v + 10`) and `CB` at `Buf[T = String, N = Bool]` (answers `s.v + 20`), `mkb[E](xs: List[T = E]) -> Buf[T = E, N = Bool] = buf(v: 1)` and `use(y: Buf[T = Int64, N = Bool])`: `Store2.peek2(mkb([]), y)` is refused "ambiguous dispatch … (CA, CB)" while `Store2.peek2(y, mkb([]))` runs CA (11); with CB alone, `peek2(mkb([]), y)` RUNS CB (21) although `y` pins `T = Int64`. MEASURED identically before and after WI-20260929-WBHTM; since WBHTM the value-in-type spelling (`N = 3`) reaches it too, where it used to be refused as "missing requires". MECHANISM: `[]`'s element type is the inert `TypeExtractor.TypeVar` marker (typing/constructor.rs ~407), σ binds the spec parameter from the FIRST argument and only checks the second against that binding, so the goal keeps the marker; `types_lesseq` treats `type_var` as compatible with anything (subtype.rs ~90), so `match_candidate_against_goal` accepts every provider on that element. FOUND by WI-20260929-WBHTM's /code-review (V5). ACCEPTANCE: the goal carries what a later argument pins (or the call is refused as under-determined), so the verdict does not depend on argument order — `peek2(mkb([]), y)` reaches CA with both providers and is refused with CB alone, in the typed and the value-in-type spelling; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-26T22:05:48Z — feedback — user

DONE (e00621b93). MEASURED on the parent (release CLI, `anthill run`): `Store2.peek2(mkb([]), y)` refused as ambiguous (CA, CB) while `peek2(y, mkb([]))` ran CA (11); beside CB alone the first order RAN CB (21); the `N = 3` spelling alike. WIDER THAN FILED: the named spelling in written order (`peek2(s: mkb([]), t: y)`), the receiver spelling (`mkb([]).peek2(y)`) and the bare open spelling (`peek2(Buf.empty(), y)`, refused "nothing here fixes T" where the other order ran) had the same split; and an operation's own `[X]` at an INVARIANT occurrence (`h[X](a: Cell[T = X], b: Cell[T = X]) requires Store2[State = X]`, `h(cell(c: mkb([])), cell(c: y))`) was refused as ambiguous and ran CB beside CB alone — `join_repeated_type_params` bound the first of the agreeing invariant occurrences, open slot and all.

WHAT WAS GOING ON: an open slot (the empty literal's element, or a slot left out) is admitted at every instance, and a spec's parameter is bound by the FIRST argument naming it (spec parameters are not joined, §8.1/§8.7), with every later argument only checked against it — so the goal kept the slot open and every provider matched there.

DONE: (1) `fill_open_spec_params` (join_instantiation.rs), asked in `check_apply_call` after the receiver / requires binders, for a sort the data-sort join does not instantiate: the first argument's contribution has its open slots written from the later ones (`open_slots_said_by`, the branch join's fill); nothing said is widened, a contribution with a walk variable keeps the parameter out of the pass, and where nothing is filled the loop decides as before. (2) the invariant arm of `join_repeated_type_params` fills the same way from the other invariant occurrences (not from covariant ones), and binds the filled occurrence even when a later one disagrees, so the site refuses the disagreeing one in either order (found by /code-review). No spec change: §5.4 already says an open slot takes the instance it meets, the parameter it is passed to.

ROWS: `tests/include/wi_7xnsk_open_slot_spec_param_test.rs`, 16. BACK-OUTS, MEASURED over the file: the spec fill off fails 9; the invariant fill off fails 3; the bind-despite-disagreement off fails 1; the other-order controls, two-open-arguments (still ambiguous) and the let-named value (closed at the name, §5.4) pass either way.

NOT IN THIS CHANGE, MEASURED: a RULE-BODY goal is order-independent already, but beside CB alone `rule rr(?r) :- Store2.peek2(mky(), mky(), ?r)` (`mky() -> Buf[T = Int64, N = Bool]`) answers 21 — a rule-body spec goal is not held to the provider's `T` at all; pre-existing, no empty literal involved, not ticketed (to discuss).

/code-review (high): two fixed (the invariant bind despite disagreement; §4.4 cited for §5.4's rule), two no change (a covariant fill takes the first said subtype, as a spec parameter's first said argument already decides; the rule-body route probed, above). Gate 12920 / 0; families green; scaland testFull 811 + 51 (2 skipped) + 1.

### 2026-11-27T05:09:20Z — feedback — user

The rule-body defect noted above (a rule-body spec goal not held to the provider's T) is filed, after discussion with the user, as WI-20261127-S4XD6.

