//! WI-1061 — an UNWRITTEN sort parameter is RIGID when NESTED inside a binding, not only at a
//! parameter's top level. And the RETURN position, which this ticket also owned, is PINNED
//! open here rather than left unrecorded: **WI-1063** owns it, and the last two tests are its
//! control.
//!
//! WI-1059 made the rule bite in one position and said so at its site: `s: Stream[T = Int64]`
//! is checked as `s: Stream[T = Int64, E = s.E]`, so a body may not assume the row. The same
//! soundness hole was still reachable through the two positions it left out. One of them
//! closes here; the other turned out to be a decision rather than a line.
//!
//! ## The nested position — what differs from WI-1059 is only the FILLER
//!
//! WI-1059's slot takes the projection off the value carrying it, because the language spells
//! that name and a signature writes it (`-> List[T = s.T]`). A nested slot has no such name —
//! nothing spells the inner row of `List[T = Stream]` — so it takes a fresh anonymous
//! `Var::Rigid`. The fear on record was that anonymity desynchronizes; it cannot here, because
//! nothing else names a nested slot, and the one nested thing that IS named elsewhere — a
//! SELF-sort reference — never reaches the anonymous arm.
//!
//! ## Why the return position is not closed here — MEASURED, not deferred on a hunch
//!
//! The walk works in the return: pass the return type through the same function and `widen`
//! below is refused at `widen.return`, `expected E = ?E`. It costs **40 tests across thirteen
//! delivered tickets** (WI-353/374/401/402/405/457/480/488/491/734/762/776/839, plus this
//! file's own two pins, which flip by design) — and it is the WRONG QUANTIFIER, which is the
//! reason it is held back rather than the cost alone.
//!
//! Read the polarity off the arrow. A PARAMETER's unwritten slot is negative-position and
//! UNIVERSAL — the caller instantiates it, so it is flexible at a call and rigid in the body,
//! which is what this file's other rows enforce. A RETURN's is positive-position and
//! EXISTENTIAL: `-> Stream[T = Int64]` is `∃E. Stream[T = Int64, E]`. The body PACKS a
//! witness, so `widen` below is CORRECT as written and must keep loading; each call OPENS,
//! minting a fresh skolem, so the CONSUMER is what should fail. Rigidifying the return in the
//! body check demands the body be good for every row — a universal in a positive position —
//! which is why its 40 failures are mostly correct programs refused for not being polymorphic
//! where only a witness was asked.
//!
//! `docs/design/type-parameter-scoping.md` §5's "erased" is that existential said without the
//! word, and two delivered tests already bet on it:
//! `wi374_expansion_test::foreign_bare_return_op_loads_and_narrows` pins `makeList() -> List =
//! cons(1, nil)` as LOADING (a body packing a witness), and `bare_value_stays_unusable`
//! refuses the CONSUMER of an erased value (the opening). The WI-401/402/457/480/488/491
//! escape gate is built on a bare abstract-spec return CONFORMING by provider upcast and only
//! then being refused with its own diagnostic — materialize the return and that gate stops
//! firing at all, so its fixtures cannot simply be updated.
//!
//! WI-1063 owns the fix, and it does not live where this ticket's walk lives: opening happens
//! at the USE (a fresh skolem per call, in `check_apply_iter`), not in the body check.
//!
//! ## What fails when each piece is backed out — DRIVEN, one revert each
//!
//! | test | nested recursion | arrow/tuple arms | effect-row gate | self tie at depth |
//! |---|---|---|---|---|
//! | `a_nested_unwritten_row_is_rigid` | **FAILS** | ok | ok | ok |
//! | `an_unwritten_row_in_a_callback_result_or_a_tuple_component_is_rigid` | ok | **FAILS** | ok | ok |
//! | `an_effect_row_binding_is_not_a_nested_type` | ok | ok | **FAILS** | ok |
//! | `a_self_reference_nested_in_a_binding_keeps_the_sort_tie` | ok | ok | ok | **FAILS** |
//! | `a_body_that_holds_for_every_instantiation_still_loads` | ok | ok | ok | ok — by design |
//! | `a_return_position_unwritten_row_is_not_yet_rigid` | ok | ok | ok | ok — pin |
//! | `an_effectful_stream_still_reaches_a_pure_slot_through_a_return` | ok | ok | ok | ok — pin |
//!
//! The reverts are: make the recursion into a written binding return `None`; delete the
//! `Arrow`/`NamedTuple` arms so those carriers fall to `_ => None`; drop the
//! `sort_param_is_effect_row` gate in front of the recursion; and narrow the self tie to the
//! top-level position (`is_self && !matches!(fill, UnwrittenFill::Anonymous)`). Each was run,
//! alone, on this file; every row above is a measurement, not a prediction. Each column fails
//! exactly ONE row — the corpus does not reach any of these mechanisms, so this file is their
//! only coverage and a wrong cell here would go unnoticed everywhere else.
//!
//! The arrow/tuple column is the review's finding on the first cut, and is worth its own line
//! because the shape that first shipped looked complete: the walk descended through
//! `Parameterized` bindings only, so every OTHER type carrier fell to `_ => None` and left its
//! slots flexible in silence.
//!
//! One earlier draft of this table was WRONG in that way and is worth recording: it claimed
//! the self-tie column also fails `a_body_that_holds_for_every_instantiation_still_loads`,
//! collaterally, because narrowing the tie costs the STDLIB 4 errors. It does — but only when
//! the RETURN is walked too, which is the shape this file no longer ships. With parameters
//! alone the stdlib loads clean under that revert, so the row above is right and the earlier
//! prose was measuring the other configuration.
//!
//! REFERENCE: WI-1059 (the parameter-position half); WI-1063 (the return position); WI-1056
//! (the four spellings, kept in lockstep); WI-942/WI-392 (the two rigid families before);
//! WI-594/WI-320 (the effect-row kind anchor the gate reads).

use crate::wi1012_static_supplier_tie_test::refusal;

/// The NESTED-position program. `feed`'s parameter writes `List`'s `T` and leaves the
/// `Stream` inside it bare, so the row it hands on is one nothing in the signature named.
const NESTED: &str = "namespace test.wi1061.nested\n\
    \x20 import anthill.prelude.{Int64, Stream, List, Error}\n\
    \x20 operation takes_pure(l: List[T = Stream[T = Int64, E = {}]]) -> Int64\n\
    \x20 operation feed(l: List[T = Stream[T = Int64]]) -> Int64 = takes_pure(l)\n\
    \x20 operation caller(l: List[T = Stream[T = Int64, E = {Error}]]) -> Int64 = feed(l)\n\
    end\n";

/// The RETURN-position program, PINNED as it loads today. `widen` is handed an effectful
/// stream and declares a return whose row it does not write.
const WIDEN: &str = "namespace test.wi1061.ret\n\
    \x20 import anthill.prelude.{Int64, Stream, Error}\n\
    \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
    \x20 operation widen(s: Stream[T = Int64, E = {Error}]) -> Stream[T = Int64] = s\n\
    \x20 operation exploit(s: Stream[T = Int64, E = {Error}]) -> Int64 = takes_pure(widen(s))\n\
    end\n";

/// THE HEADLINE — a slot NESTED inside a written binding is unwritten in exactly the same
/// sense as one left off the end, and nothing in the signature names it.
///
/// Refused where the body is wrong (`feed`'s call on `takes_pure`), not at `caller` — asserted
/// rather than left to "it is refused somewhere", because refusing at the caller would read as
/// a caller mistake and make every legitimately row-polymorphic signature unusable. Asserted
/// on `E = ?E` too: the anonymous rigid is what the nested slot is filled with, and a refusal
/// that did not carry it would mean the nested type had been rebuilt with something else.
///
/// CONTROL: on main the whole three-operation chain loads, and an effectful stream reaches a
/// slot that declared it wanted none — one level down instead of at the top.
#[test]
fn a_nested_unwritten_row_is_rigid() {
    let msg = refusal(NESTED);
    assert!(
        msg.contains("takes_pure.l") && !msg.contains("caller"),
        "the refusal belongs at `feed`'s body — the call on takes_pure — and NOT at the \
         caller that hands `feed` an effectful list: {msg}",
    );
    assert!(
        msg.contains("E = ?E") && msg.contains("E = {empty_row}"),
        "the refusal must name the nested row it cannot assume and the row it was handed \
         to: {msg}",
    );
}

/// THE EFFECT-ROW GATE, and the defect it was written for rather than a hypothetical. An
/// effect-row binding is structurally indistinguishable from a nested data type — `E = Error`
/// in `Stream[T = Solution, E = Error]` is a `SortRef` whose sort declares a parameter, just
/// like `T = Stream` is — but it is a ROW, and its labels are compared by structural identity
/// against the effects a body INCURS. Materializing `Error`'s own `T` makes the two spellings
/// of one label unequal and the operation is refused against its own declaration.
///
/// This is the anthill-todo program's shape, reduced. `sort_param_is_effect_row` (WI-594,
/// reading the WI-320 kind anchor) is the only thing that separates the two.
///
/// THE BODY MUST INCUR THE ROW, and the first draft of this test did not — it was
/// `= 1`, which loads with the gate AND without it, because a body that performs no effect
/// never reaches the declared-vs-incurred comparison where the two spellings of `Error` meet.
/// It is `splitFirst(s)` that pulls the parameter's row into the body's effects. Written down
/// because the vacuous version looked identical and passed.
///
/// CONTROL: drop the gate and this FAILS at `expected declared: [Error], got undeclared
/// effect: Error[T = ?T]` — verified by that revert, on this exact source. The same revert
/// breaks `rustland/anthill-todo/anthill` and takes 193 tests with it, so the CLI cannot even
/// print a work item; this row is the small one that says why.
#[test]
fn an_effect_row_binding_is_not_a_nested_type() {
    crate::common::load_kb_with(
        "namespace test.wi1061.effrow\n\
         \x20 import anthill.prelude.{Int64, Stream, Error}\n\
         \x20 operation drain(s: Stream[T = Int64, E = Error]) -> Int64 effects {Error} =\n\
         \x20   match Stream.splitFirst(s)\n\
         \x20     case none() -> 0\n\
         \x20     case some(p) -> 1\n\
         end\n",
    );
}

/// A SORT APPLICATION IS NOT THE ONLY CARRIER A PARAMETER TYPE CAN BE, and these two are the
/// review's finding on the first cut of this ticket: the recursion descended only through
/// `Parameterized` bindings, so the same unwritten row hid inside a callback's RESULT type
/// and inside a TUPLE COMPONENT, and both chains loaded clean.
///
/// They are the WI-1059 hole verbatim, one carrier further in. `feed` never writes the row of
/// the stream it gets back from `f(1)` — nor of the one it destructures out of `p` — and
/// hands it to a slot that declared `E = {}`; `caller` supplies `{Error}`. Both sit inside a
/// PARAMETER, the position WI-1063's two readings agree about, so they belong to this ticket
/// and not to that one.
///
/// THE CALLBACK'S OWN PARAMETER IS NOT WALKED, and that asymmetry is the measurement, not a
/// hedge — an unwritten slot in a callback's parameter says the callback accepts EVERY
/// instantiation, so the body may pass whatever it has. See the arm's own comment: walking it
/// failed 9 tests, all refusing a body for handing a good value to a callback that had
/// declared it takes any.
///
/// CONTROL: on main both chains load. With the recursion but without these two carriers —
/// the shape this ticket first shipped — they load too, which is what the review caught.
#[test]
fn an_unwritten_row_in_a_callback_result_or_a_tuple_component_is_rigid() {
    let arrow = refusal(
        "namespace test.wi1061.arrow\n\
         \x20 import anthill.prelude.{Int64, Stream, Error}\n\
         \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
         \x20 operation feed(f: (x: Int64) -> Stream[T = Int64]) -> Int64 = takes_pure(f(1))\n\
         \x20 operation caller(f: (x: Int64) -> Stream[T = Int64, E = {Error}]) -> Int64 = \
         feed(f)\n\
         end\n",
    );
    assert!(
        arrow.contains("takes_pure.s") && arrow.contains("E = ?E") && !arrow.contains("caller"),
        "a callback RESULT's unwritten row must be rigid in the body, refused at `feed`: \
         {arrow}",
    );
    let tuple = refusal(
        "namespace test.wi1061.tuple\n\
         \x20 import anthill.prelude.{Int64, Stream, Error}\n\
         \x20 operation takes_pure(p: (s: Stream[T = Int64, E = {}], n: Int64)) -> Int64\n\
         \x20 operation feed(p: (s: Stream[T = Int64], n: Int64)) -> Int64 = takes_pure(p)\n\
         \x20 operation caller(p: (s: Stream[T = Int64, E = {Error}], n: Int64)) -> Int64 = \
         feed(p)\n\
         end\n",
    );
    assert!(
        tuple.contains("takes_pure.p") && tuple.contains("E = ?E") && !tuple.contains("caller"),
        "a TUPLE COMPONENT's unwritten row must be rigid in the body, refused at `feed`: \
         {tuple}",
    );
}

/// THE POSITIVE CONTROL, and the reason the refusal above is a rule rather than a blanket
/// rejection: a body that genuinely holds for EVERY instantiation still loads. The two
/// signatures leave the same inner slot unwritten, and at a CALL an unwritten parameter is
/// FLEXIBLE again and binds from the argument — the asymmetry the whole rule rests on. Same
/// variable, two positions.
///
/// CONTROL: passes under every revert in the header table, BY DESIGN. It measures nothing on
/// its own; it is here so the refusal cannot be satisfied by a check that refuses every
/// unwritten slot, and it fails loudly if one ever is.
#[test]
fn a_body_that_holds_for_every_instantiation_still_loads() {
    crate::common::load_kb_with(
        "namespace test.wi1061.polymorphic\n\
         \x20 import anthill.prelude.{Int64, Stream, List}\n\
         \x20 operation takes_any(l: List[T = Stream[T = Int64]]) -> Int64\n\
         \x20 operation feed(l: List[T = Stream[T = Int64]]) -> Int64 = takes_any(l)\n\
         end\n",
    );
}

/// THE SELF TIE, which is the half of this ticket that is load-bearing for the corpus rather
/// than for the hole. Within a sort's own definition a bare self reference participates in the
/// parametricity tie (`docs/design/type-parameter-scoping.md` §3), so the `Wrap` nested in
/// `pack`'s parameter names THIS instance's `T` — the same one `w` carries — and the body
/// conforms.
///
/// The anonymous filler must therefore not reach a self reference at any DEPTH, only a foreign
/// one. Two unrelated skolems for one sort's parameter is precisely the desynchronization that
/// made the anonymous filler wrong at top level in WI-1059, and it is still wrong here; the
/// difference is that a foreign nested slot has no other name to desynchronize from.
///
/// CONTROL: narrow the self tie to the top-level position and this FAILS at
/// `expected Wrap[T = ?T], got Wrap[T = ?T] (these render alike but are not the same type)`.
/// It is the ONLY row that fails, and the stdlib loads clean under that revert — measured, so
/// that the tie is not mistaken for something the corpus is holding up. The corpus reaches a
/// nested self reference only in `MappedStream.splitFirst`'s RETURN, which nothing walks
/// today (WI-1063).
#[test]
fn a_self_reference_nested_in_a_binding_keeps_the_sort_tie() {
    crate::common::load_kb_with(
        "namespace test.wi1061.selftie\n\
         \x20 import anthill.prelude.{Int64, List}\n\
         \x20 sort Wrap\n\
         \x20   sort T = ?\n\
         \x20   entity Wrap(v: T)\n\
         \x20   operation pack(w: Wrap, l: List[T = Wrap]) -> List[T = Wrap] = \
         cons(head: w, tail: l)\n\
         \x20 end\n\
         end\n",
    );
}

/// THE RETURN POSITION, PINNED OPEN — **WI-1063**. This is not a passing capability test; it
/// records that the hole is still reachable, so that whoever closes it sees this row go red
/// and finds the decision written down instead of rediscovering it.
///
/// The program is the ticket's own: `widen` promises a stream of every row while holding one
/// with `{Error}` in it. The header says why enforcing this is a language decision and not a
/// line to add. `load_kb_with` panics on any load error, so this row also guards the reverse
/// mistake — a refusal arriving here from some UNRELATED change would fail just as loudly.
#[test]
fn a_return_position_unwritten_row_is_not_yet_rigid() {
    crate::common::load_kb_with(WIDEN);
}

/// The same pin read for its CONSEQUENCE rather than its shape, because "the declaration
/// loads" is the boring half. `exploit` hands `widen`'s result — whose row the type does not
/// carry — to a slot that declared `E = {}`, and the whole chain loads: an effectful stream
/// reaches a pure slot. That is the soundness statement WI-1063 owns, and it is asserted here
/// so the pin cannot be read as cosmetic.
///
/// Driven, not just loaded: `exploit` is resolved from the KB, so the row above cannot pass
/// on a program whose exploiting operation silently failed to be declared at all.
#[test]
fn an_effectful_stream_still_reaches_a_pure_slot_through_a_return() {
    let kb = crate::common::load_kb_with(WIDEN);
    assert!(
        kb.try_resolve_symbol("test.wi1061.ret.exploit").is_some(),
        "the exploiting operation must be declared — otherwise this pin measures nothing",
    );
}
