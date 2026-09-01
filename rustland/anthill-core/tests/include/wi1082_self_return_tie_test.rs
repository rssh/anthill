//! WI-1082 — §3's PARAMETRICITY TIE, WRITTEN DOWN. A declaration inside a sort's own body that
//! names that sort and leaves a parameter slot unwritten means *this* instance's parameter, so
//! `elaborate_self_ties` writes it as the sort's own parameter var before anything reads the
//! signature.
//!
//! ## The gap this closes
//!
//! WI-1063 made a RETURN's unwritten sort parameter existential and opened it to a fresh rigid
//! at every call — but only for a FOREIGN sort. It left the callee's OWN sort to the canonical
//! channel, and that channel binds nothing when the self reference is PARTIALLY written:
//! `unify_parameterized_view` width-IGNORES a slot the author elided, so nothing is claimed and
//! nothing refutes. WI-1063's headline exploit therefore survived verbatim as long as the
//! operation was declared INSIDE the sort its return names:
//!
//! ```text
//! operation widen(s: MyStream[T = Int64, E = {Error}]) -> MyStream[T = Int64] = s
//! operation use(s: MyStream[T = Int64, E = {Error}]) -> Int64 = takes_pure(MyStream.widen(s))
//! ```
//!
//! ## THREE positions, because §3 names three
//!
//! "`append(xs: List, ys: List)` ties both parameters **and the return** to *this* sort's `T`",
//! and "`cons(head: T, tail: List)` ⇒ `tail` is a `List` of *this* sort's `T`". So the rewrite
//! covers the return, the parameters and an entity's fields — and each of the three was
//! measured to be load-bearing separately (the table below). Doing only the return leaves the
//! exploit alive for every BODYLESS member ([`a_bodyless_member_cannot_launder_either`]); doing
//! only the signature leaves a destructured field with no element at all
//! ([`a_destructured_field_carries_the_instances_element`]).
//!
//! A BARE self parameter is the one thing deliberately left alone: it is already tied, by
//! `unify_parameterized_with_sort_ref`, and writing the tie in makes it strict enough that
//! WI-424's sibling-call seeding refuses `List.mapElems`' `reverse` at `Dst`
//! ([`a_bare_self_parameter_is_left_to_the_canonical_channel`]).
//!
//! ## Two producers, so the fix is at the DECLARATION
//!
//! The BODY check width-ignores the same slot — `widen`'s declaration was never checked against
//! what its body returns either ([`the_body_check_was_the_other_producer`]). A call-side-only
//! filler would therefore have the caller trust a claim nothing had verified. One rewrite of
//! the cached signature closes both, because both read it.
//!
//! ## The filler is the SORT'S parameter, not a receiver projection — measured, not chosen
//!
//! `-> List[T = c.T]` was built first and is the same type wherever both spellings can answer.
//! It reads ONE parameter where the tie pools ALL of them, and the suite found both ways that
//! matters: `put(empty(), "a", 1)` has no stable receiver to project off, and writing a
//! projection into `put`'s return flips `op_has_projection` on for the whole call, which then
//! failed `put`'s own PARAMETERS at `expected m.K, got Int64`. [`the_tie_pools_every_parameter`]
//! is that case as a row. The canonical var perturbs no call path — it is what the signature
//! already rides.
//!
//! ## Where the exploit fails depends on whether the member has a body, and both are refusals
//!
//! With a body, at the DECLARATION: inside a member body the sort's parameters are rigid
//! (WI-424 — the tie read as parametricity), so `widen`'s body must hold for EVERY `E`, and
//! `= s` — pinned to `{Error}` by its own parameter — does not. The message names
//! `widen.return`. The rule: **a member may not pin its own sort's parameter to a constant and
//! still elide it in the return.** Writing the return out is unaffected
//! ([`a_written_slot_is_never_touched`]). Without a body there is nothing to check, and the
//! refusal is at the CONSUMER, where the argument's row now reaches it. The ticket's acceptance
//! names the first as the other admissible verdict.
//!
//! ## What fails when this is backed out — one revert each, whole `anthill-core` suite
//!
//! | revert | cost |
//! |---|---|
//! | the whole pass (`elaborate_self_ties` returns immediately) | **7**: six rows here ([`the_headline_a_self_sort_return_no_longer_launders`], [`the_body_check_was_the_other_producer`], [`the_tie_pools_every_parameter`], [`a_bodyless_member_cannot_launder_either`], [`a_destructured_field_carries_the_instances_element`], [`a_self_returning_member_result_shares_the_receivers_parameter`]) plus `wi1078_…::a_self_sort_return_is_not_opened_in_either_spelling` |
//! | the PARAMETER half only | **1**: [`a_bodyless_member_cannot_launder_either`] |
//! | the ENTITY-FIELD half only | **2**: [`a_destructured_field_carries_the_instances_element`] and `wi1076_…::mplus_unifies_an_empty_stream_with_a_non_empty_one` |
//! | `unbound` ignored in a SIGNATURE position (only the anonymous spelling rewritten) | **2**: `wi1078_…::a_self_sort_return_is_not_opened_in_either_spelling`, whose halves then disagree, and `wi1076_…::mplus_…` |
//! | a FIELD position narrowed to the anonymous spelling too | **1**: `wi1076_…::mplus_…` |
//! | BARE self parameters rewritten as well | the stdlib stops loading (`expected List[T = ?T], got List[T = ?Dst]` in `List.mapElems`) — **40** `--lib` tests and all four corpus tiers |
//! | the `declares_self_param` gate dropped | **0**, and NOT for want of trying — see [`no_self_parameter_leaves_the_slot_open`] |
//!
//! Each was run alone against the whole `anthill-core` suite. Rows that pass either way, by
//! design, say so at their own site: [`a_written_slot_is_never_touched`],
//! [`a_foreign_return_still_opens_per_call`], [`an_elided_self_return_still_threads_the_element`],
//! [`the_field_tie_is_a_fixpoint`].
//!
//! REFERENCE: WI-1063 (the polarity rule, the four opening sites, the FOREIGN-only scope and
//! the two fillers it rejected at `SlotPosition::fill_self`), WI-1078 (the unbound-variable
//! classification this reuses), WI-1059/WI-1061 (the parameter side of the same walk), WI-374
//! + `docs/design/type-parameter-scoping.md` §3 (the tie, and the `cons(head: T, tail: List)`
//! example this implements literally), `docs/kernel-language.md` §8.1,
//! `docs/design/path-dependent-types.md` §4.1 (what this changed about a self-returning
//! member's result, and what it did not).

use anthill_core::eval::value::Value;

/// The refusals `src` raises, or an empty list when it loads.
fn errors_of(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

const STREAM: &str = "namespace test.wi1082.stream\n\
    \x20 import anthill.prelude.{Int64, Error}\n\
    \x20 sort MyStream\n\
    \x20   sort T = ?\n\
    \x20   effects E = ?\n\
    \x20   entity mystream\n\
    \x20   entity raising\n\
    \x20   BODY\n\
    \x20 end\n\
    \x20 operation takes_pure(s: MyStream[T = Int64, E = {}]) -> Int64\n\
    \x20 USE\n\
    end\n";

/// `STREAM` with its two holes filled.
fn stream(body: &str, use_site: &str) -> String {
    STREAM.replace("BODY", body).replace("USE", use_site)
}

/// THE HEADLINE. The ticket's five-line program, verbatim: a member whose declared return names
/// its own sort and elides `E`, handing `{Error}` to a parameter that declares `E = {}`. It
/// LOADED before this ticket.
///
/// Now `-> MyStream[T = Int64]` means "at THIS instance's `E`", the body must hold for every
/// `E`, and `= s` does not — refused at `widen.return`, the declaration.
///
/// CONTROL — THE SAME PROGRAM WITH THE OPERATION MOVED OUT of the sort, which is the only
/// difference the exploit ever turned on. There the two `MyStream` references are FOREIGN, so
/// WI-1063's existential opening applies unchanged and the refusal lands at the CONSUMER
/// (`takes_pure.s`) instead. Both halves refuse; that the SITES differ is what says the two
/// rules are distinct and that this ticket did not simply widen WI-1063.
///
/// BACK-OUT: the first half loads clean (the exploit), the second is unaffected.
#[test]
fn the_headline_a_self_sort_return_no_longer_launders() {
    let member = errors_of(&stream(
        "operation widen(s: MyStream[T = Int64, E = {Error}]) -> MyStream[T = Int64] = s",
        "operation use(s: MyStream[T = Int64, E = {Error}]) -> Int64 = \
         takes_pure(MyStream.widen(s))",
    ));
    assert!(
        member.iter().any(|e| e.contains("widen.return")),
        "the self-sort return is THIS instance's `E`, so a body pinned to {{Error}} is refused \
         at the DECLARATION: {member:?}",
    );

    let foreign = errors_of(
        "namespace test.wi1082.foreign\n\
         \x20 import anthill.prelude.{Int64, Error}\n\
         \x20 sort MyStream\n\
         \x20   sort T = ?\n\
         \x20   effects E = ?\n\
         \x20   entity mystream\n\
         \x20 end\n\
         \x20 operation widen(s: MyStream[T = Int64, E = {Error}]) -> MyStream[T = Int64] = s\n\
         \x20 operation takes_pure(s: MyStream[T = Int64, E = {}]) -> Int64\n\
         \x20 operation use(s: MyStream[T = Int64, E = {Error}]) -> Int64 = \
         takes_pure(widen(s))\n\
         end\n",
    );
    assert!(
        foreign.iter().any(|e| e.contains("takes_pure.s")),
        "moved OUT of the sort the references are foreign, so WI-1063 opens the slot and the \
         refusal is at the CONSUMER — a different rule, still in force: {foreign:?}",
    );
}

/// THE OTHER PRODUCER, and the reason the fix is at the declaration rather than at the call.
/// The BODY check width-ignores the return's unwritten slot too, so a member could return a
/// `{Error}`-carrying stream under a declared `-> MyStream[T = Int64]` and never be challenged.
/// A call-side-only filler would then hand the caller a claim nothing had verified.
///
/// Here the body is a DIFFERENT value (a call, not the receiver), so nothing about the
/// parameter can excuse it: the declared return promises this instance's `E` and the body
/// supplies `{Error}`.
///
/// BACK-OUT: loads clean — this exact program is what made a call-side fix insufficient.
#[test]
fn the_body_check_was_the_other_producer() {
    let errs = errors_of(&stream(
        "operation raiser(x: Int64) -> MyStream[T = Int64, E = {Error}] = raising\n\
         \x20   operation bad(s: MyStream[T = Int64, E = {}]) -> MyStream[T = Int64] = \
         MyStream.raiser(1)",
        "",
    ));
    assert!(
        errs.iter().any(|e| e.contains("bad.return")),
        "the declared return is checked against the body now, so a `{{Error}}` witness under an \
         elided slot is refused where it used to be width-ignored: {errs:?}",
    );
}

/// THE TIE POOLS EVERY PARAMETER — the row that decided the filler.
///
/// `Map.put(m: Map, key: K, value: V) -> Map` is called as `put(empty(), "a", 1)`: the receiver
/// argument is a CALL, so there is no stable value reference to project off (`param_to_arg_sym`
/// records nothing for `m`) and `m.K` could never be eliminated. The sort's own `K`/`V` are
/// bound by `key` and `value` instead, and the elided return reads the very same vars — so the
/// annotated `-> Map[String, Int64]` conforms.
///
/// AND IT IS A CLAIM, not a silence: the second half swaps one argument's type and is REFUSED.
/// Without the elaboration the return would be a bare `Map`, width-ignored against the
/// annotation, and both halves would load.
///
/// BACK-OUT: the first half loads either way (a bare `Map` is width-ignored against the
/// annotation); the SECOND half is what moves — it loads clean with the ticket backed out.
#[test]
fn the_tie_pools_every_parameter() {
    const SRC: &str = "namespace test.wi1082.pool\n\
        \x20 import anthill.prelude.{Map, String, Int64}\n\
        \x20 import anthill.prelude.Map.{empty, put}\n\
        \x20 operation built() -> Map[String, Int64] = put(empty(), \"a\", VALUE)\n\
        end\n";
    assert!(
        errors_of(&SRC.replace("VALUE", "1")).is_empty(),
        "`key` and `value` bind the sort's own K/V and the elided return reads them: {:?}",
        errors_of(&SRC.replace("VALUE", "1")),
    );
    let wrong = errors_of(&SRC.replace("VALUE", "\"b\""));
    assert!(
        wrong.iter().any(|e| e.contains("built.return")),
        "the elided return CLAIMS this instance's V, so a `String` value under a declared \
         `Map[String, Int64]` must be refused rather than width-ignored — and the refusal must \
         name the site, or a later stdlib rename would keep this row green while measuring \
         nothing: {wrong:?}",
    );
}

/// THE ENTITY-FIELD HALF, which `docs/design/type-parameter-scoping.md` §3 states literally:
/// "`cons(head: T, tail: List)` ⇒ `tail` is a `List` of *this* sort's `T`".
///
/// A pattern binds its fields at the DECLARED field type, so an untied `next: Box` handed the
/// body a field with no element at all — and because an absent binding is width-IGNORED, that
/// loss can only be seen where the element CONFLICTS. Hence the shape: `b : Box[T = Int64]` is
/// destructured and its `next` passed to an operation demanding `Box[T = String]`.
///
/// BACK-OUT (the field half alone): this program LOADS CLEAN — a false accept — and nothing
/// else in the suite or the corpus moves. That zero is the reason this row is written as a
/// refusal on a purpose-built fixture rather than left to the libraries: no corpus program
/// reads a destructured self-typed field at a conflicting element, so a green corpus says
/// nothing about this half either way.
///
/// THE POSITIVE HALF is [`an_elided_self_return_still_threads_the_element`]'s neighbour: the
/// same fixture with the demand at `Int64` must still LOAD, so the row is not simply "any
/// destructured field is now refused".
#[test]
fn a_destructured_field_carries_the_instances_element() {
    const SRC: &str = "namespace test.wi1082.field\n\
        \x20 import anthill.prelude.{Int64, String}\n\
        \x20 sort Box\n\
        \x20   sort T = ?\n\
        \x20   entity leaf(v: T)\n\
        \x20   entity node(next: Box)\n\
        \x20 end\n\
        \x20 operation want(b: Box[T = DEMAND]) -> Int64\n\
        \x20 operation use(b: Box[T = Int64]) -> Int64 =\n\
        \x20   match b\n\
        \x20     case leaf(v) -> 0\n\
        \x20     case node(n) -> want(n)\n\
        end\n";
    let conflicting = errors_of(&SRC.replace("DEMAND", "String"));
    assert!(
        conflicting.iter().any(|e| e.contains("want.b")),
        "`node(next: Box)` inside `sort Box` means a `Box` at THIS instance's `T`, so the \
         destructured `n` carries `Int64` and a `Box[T = String]` demand is refused: \
         {conflicting:?}",
    );
    assert!(
        errors_of(&SRC.replace("DEMAND", "Int64")).is_empty(),
        "the same destructure at the MATCHING element must still load — the tie names an \
         element, it does not refuse every destructured field",
    );
}

/// NO SELF PARAMETER, NO TIE — the residue, stated as behaviour rather than left implicit.
///
/// `List.empty() -> List` has no parameter mentioning its sort, so nothing at a call could bind
/// the sort's parameter; writing it into the return would stamp a raw, unbindable global into
/// the result (the dangling-flex hazard the WI-374 note names, and why WI-1063 rejected the
/// canonical var as a GENERAL filler). The slot therefore stays open and the caller's expected
/// type determines it — at two different elements in one program, which is the point.
///
/// This is the right answer for `empty`, whose body holds for every `T`, and the wrong one for
/// a hypothetical `mk() -> S[…]` whose body pins a row. Telling those apart needs the universal
/// spelling (`empty[T]() -> List[T = T]`), which is **WI-1083**'s `PolyType`.
///
/// BACK-OUT: **0**, and not for want of trying — this row records a guard I could not drive.
/// With the gate removed, the whole `anthill-core` suite stays green (this row included), all
/// four corpus tiers load with zero errors, and two purpose-built fixtures failed to reach the
/// hazard: `Box.mk() -> Box` bound twice in one body and consumed at `Int64` and `String`
/// loads either way, because each call gets a fresh `Substitution` and the raw var does not
/// alias across the two lets. So the gate is kept on the WI-1063/WI-374 argument alone — a
/// result type must not carry a global canonical var — and that argument is stated here rather
/// than dressed up as a measurement. If a later ticket reaches the hazard, this is the row to
/// rewrite; if one proves it unreachable by construction, the gate should go.
#[test]
fn no_self_parameter_leaves_the_slot_open() {
    assert!(
        errors_of(
            "namespace test.wi1082.empty\n\
             \x20 import anthill.prelude.{List, Int64, String}\n\
             \x20 import anthill.prelude.List.{empty}\n\
             \x20 operation ints() -> List[T = Int64] = empty()\n\
             \x20 operation strs() -> List[T = String] = empty()\n\
             end\n",
        )
        .is_empty(),
        "`empty` has no parameter to bind the sort's `T`, so its return stays open and each \
         caller's expected type determines it",
    );
}

/// A WRITTEN SLOT IS NEVER TOUCHED, which is what keeps the refused shape expressible: the same
/// `widen` that [`the_headline_a_self_sort_return_no_longer_launders`] rejects loads once the
/// author says what they meant. Only an ELIDED (or anonymous, or signature-unbound) slot is
/// filled — `written_slot_is_unwritten` decides, and it asks the same question at the
/// declaration that `SlotPosition::CallResult` asks at the call.
///
/// CONTROL: passes with the ticket backed out. It is the boundary of the rule, not the rule —
/// what it would catch is a future widening that starts rewriting slots the author wrote.
#[test]
fn a_written_slot_is_never_touched() {
    assert!(
        errors_of(&stream(
            "operation widen(s: MyStream[T = Int64, E = {Error}]) \
             -> MyStream[T = Int64, E = {}] = mystream",
            "operation use(s: MyStream[T = Int64, E = {Error}]) -> Int64 = \
             takes_pure(MyStream.widen(s))",
        ))
        .is_empty(),
        "writing the return out says something different from eliding it, and the elaboration \
         must leave it alone",
    );
}

/// THE FOREIGN SIDE IS UNCHANGED, asserted here because this ticket edits the walk both
/// polarities share and a `SlotPosition` arm added in the wrong place would silently retire
/// WI-1063. A foreign return's unwritten slot is still opened to a fresh rigid PER CALL, so two
/// calls do not relate — the freshness that is WI-1063's soundness.
///
/// CONTROL: passes with the ticket backed out (it is WI-1063's own behaviour). It fails if
/// `SlotPosition::Declared` ever answers `fill_foreign` — which would open the existential once
/// per DECLARATION and share one ρ across every call.
#[test]
fn a_foreign_return_still_opens_per_call() {
    let errs = errors_of(
        "namespace test.wi1082.foreignopen\n\
         \x20 import anthill.prelude.{Int64, Error}\n\
         \x20 sort Box\n\
         \x20   sort T = ?\n\
         \x20   entity box(n: Int64)\n\
         \x20 end\n\
         \x20 operation mk(n: Int64) -> Box\n\
         \x20 operation takes_int_box(b: Box[T = Int64]) -> Int64\n\
         \x20 operation use(n: Int64) -> Int64 = takes_int_box(mk(n))\n\
         end\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("takes_int_box.b")),
        "`mk` is declared OUTSIDE `Box`, so its unwritten `T` is the existential WI-1063 opens \
         at the call and a consumer demanding `Int64` is refused: {errs:?}",
    );
}

/// The tie is also what makes the ordinary elided member USABLE, which every row above tests
/// only through a refusal. `List.insert(c: List, elem: T) -> List` elides its element; the
/// result must come back at the receiver's, and this row runs it.
///
/// CONTROL: passes with the ticket backed out — a bare `List` is width-ignored against the
/// annotation and the value is the same. It is here because the refusal rows would all still
/// pass if the elaboration wrote the WRONG variable, and this one would not.
#[test]
fn an_elided_self_return_still_threads_the_element() {
    let mut interp = crate::common::interp_for(
        "namespace test.wi1082.thread\n\
         \x20 import anthill.prelude.{List, Int64}\n\
         \x20 import anthill.prelude.List.{cons, nil, insert, length}\n\
         \x20 operation grown() -> List[T = Int64] = insert(cons(head: 1, tail: nil), 7)\n\
         \x20 operation size() -> Int64 = length(grown())\n\
         end\n",
    );
    let size = interp.call("test.wi1082.thread.size", &[]).expect("length");
    assert!(
        matches!(size, Value::Int(2)),
        "the elided `-> List` is this instance's element, so the grown list is still a \
         `List[T = Int64]` and `length` runs on it; got {size:?}",
    );
}

/// THE PARAMETER HALF, and the hole that made it necessary. §3 bullet 1 ties "both parameters
/// AND the return"; writing only the return leaves a self parameter that ELIDES a slot claiming
/// nothing, so the call's argument never reaches the sort's parameter and the return's copy of
/// it stays a raw flexible var that unifies with anything.
///
/// The shape is the headline exploit with the body removed and the parameter's `E` elided
/// instead of pinned — and BODYLESS is the point: a member with a body is caught by the return
/// check ([`the_headline_a_self_sort_return_no_longer_launders`]), so the population that
/// survived is exactly the one with no body to check — spec operations, host-mapped members,
/// declaration-only members.
///
/// THE SECOND HALF is the worse form, where nothing is even about effects: `Box.pick(b: Box[T =
/// Int64]) -> Box` leaves `U` elided on both sides, so the result satisfied a `U = String`
/// demand and a `U = Int64` one alike. Now `U` comes from the argument.
///
/// BACK-OUT (the parameter half alone, keeping the return half): both halves load clean.
#[test]
fn a_bodyless_member_cannot_launder_either() {
    let effects = errors_of(&stream(
        "operation widen(s: MyStream[T = Int64]) -> MyStream",
        "operation use(s: MyStream[T = Int64, E = {Error}]) -> Int64 = \
         takes_pure(MyStream.widen(s))",
    ));
    assert!(
        effects.iter().any(|e| e.contains("takes_pure.s")),
        "a self parameter that elides `E` still names THIS instance's `E`, so the argument's \
         row reaches the return and a consumer declaring `E = {{}}` is refused: {effects:?}",
    );

    let data = errors_of(
        "namespace test.wi1082.twodemand\n\
         \x20 import anthill.prelude.{Int64, String}\n\
         \x20 sort Box\n\
         \x20   sort T = ?\n\
         \x20   sort U = ?\n\
         \x20   entity box(n: Int64)\n\
         \x20   operation pick(b: Box[T = Int64]) -> Box\n\
         \x20 end\n\
         \x20 operation want_str(b: Box[T = Int64, U = String]) -> Int64\n\
         \x20 operation both(b: Box[T = Int64, U = Int64]) -> Int64 = want_str(Box.pick(b))\n\
         end\n",
    );
    assert!(
        data.iter().any(|e| e.contains("want_str.b")),
        "`pick`'s elided `U` is the argument's `U`, so a `U = String` demand on the result of \
         picking from a `U = Int64` box is refused: {data:?}",
    );
}

/// A BARE self parameter is deliberately NOT rewritten, and this row is why that is a rule
/// rather than an oversight. `unify_parameterized_with_sort_ref` already binds the sort's
/// canonical vars whenever one side is a bare sort reference, so the tie is reached without
/// help — and writing it in makes the binding strict, at which point WI-424's seeding (which
/// pins a same-sort sibling call's canonical params to the ENCLOSING instance's rigids before
/// argument unification) refuses a sibling called at a different element.
///
/// `List.mapElems[Dst]` is exactly that call: it does `reverse(mapElemsOnto(xs, f, seed))`,
/// where `reverse(xs: List)` is a bare self parameter reached at `Dst`, not at the enclosing
/// `T`. This row runs it.
///
/// BACK-OUT (rewriting bare self parameters too): the stdlib stops loading at `expected List[T
/// = ?T], got List[T = ?Dst]`, and with it all four corpus tiers.
#[test]
fn a_bare_self_parameter_is_left_to_the_canonical_channel() {
    let mut interp = crate::common::interp_for(
        "namespace test.wi1082.mapped\n\
         \x20 import anthill.prelude.{List, Int64, String}\n\
         \x20 import anthill.prelude.List.{cons, nil, mapElems, length}\n\
         \x20 operation labels(xs: List[T = Int64]) -> List[T = String] = \
         mapElems(xs, lambda x -> \"n\")\n\
         \x20 operation n() -> Int64 = length(labels(cons(head: 1, tail: nil)))\n\
         end\n",
    );
    let n = interp
        .call("test.wi1082.mapped.n", &[])
        .expect("mapElems runs");
    assert!(
        matches!(n, Value::Int(1)),
        "`mapElems` reverses at `Dst`, a DIFFERENT element from its enclosing `T`; got {n:?}",
    );
}

/// THE FIELD REWRITE IS A FIXPOINT, which it has to be: unlike the signature cache — rebuilt
/// from the `OperationInfo` facts on every type-check — `entity_field_types` is mutated in
/// place, so a second type-check (what `load_all` into a live KB performs) reads this pass's own
/// output. An already-elaborated slot holds the sort's parameter, which is not a flexible
/// variable, so it is left alone.
///
/// BACK-OUT: passes either way — it pins an invariant of the implementation rather than the
/// rule. It fails if the field position's "unwritten" test ever widens to something that
/// matches its own fill.
#[test]
fn the_field_tie_is_a_fixpoint() {
    let mut kb = crate::common::load_kb_with(
        "namespace test.wi1082.fix\n\
         \x20 sort Box\n\
         \x20   sort T = ?\n\
         \x20   entity leaf(v: T)\n\
         \x20   entity node(next: Box)\n\
         \x20 end\n\
         end\n",
    );
    let ctor = kb
        .try_resolve_symbol("test.wi1082.fix.Box.node")
        .expect("the constructor is defined");
    let before = format!(
        "{:?}",
        kb.entity_field_types(ctor).expect("fields").to_vec()
    );
    let sorts: Vec<_> = kb
        .try_resolve_symbol("test.wi1082.fix.Box")
        .into_iter()
        .collect();
    let errs = anthill_core::kb::typing::type_check_sorts(&mut kb, &sorts);
    assert!(errs.is_empty(), "the re-check must stay clean: {errs:?}");
    let after = format!(
        "{:?}",
        kb.entity_field_types(ctor).expect("fields").to_vec()
    );
    assert_eq!(
        before, after,
        "a second type-check must leave an already-elaborated field type alone",
    );
}

/// A SELF-RETURNING MEMBER'S RESULT SHARES THE RECEIVER'S PARAMETER, asserted here because
/// WI-1082 changed it and a change nothing states is a change nobody can find. Before this
/// ticket `pick(p: DataProvider) -> DataProvider` declared inside the sort returned a
/// `DataProvider` whose `K` was related to `p`'s by nothing, so `y.K` and `p.K` were distinct
/// neutrals; now the return names this instance's `K` and the two are one type.
///
/// This does NOT retire §4.1's stability rule, and the second half is what says so: the rule
/// governs whether the two RECEIVERS canonicalize to one path, and a FOREIGN `pick` — declared
/// outside the sort — still gives `y` its own element, because §3 keeps two foreign references
/// apart and WI-1063 opens the return's elided slot to a fresh ρ.
/// `wi400_body_projection_test::let_unstable_value_does_not_alias` holds that half;
/// `docs/design/path-dependent-types.md` §4.1 carries the distinction.
///
/// The member half gives `pick` a BODY only to keep an unrelated diagnostic out of the way — a
/// body-less member of a user-defined, provider-less spec called on an abstract carrier is
/// `MissingRequiresForSpecOp`, which has nothing to do with this row. `let y = …` is a call
/// either way, which is all §4.1's stability rule looks at.
///
/// BACK-OUT: the member half is REFUSED (`y.K` ≢ `p.K`), the foreign half unchanged.
#[test]
fn a_self_returning_member_result_shares_the_receivers_parameter() {
    const SRC: &str = "namespace test.wi1082.pathdep\n\
        \x20 sort DataProvider\n\
        \x20   sort K = ?\n\
        \x20   MEMBER\n\
        \x20 end\n\
        \x20 FREE\n\
        \x20 operation g(p: DataProvider, k: p.K) -> p.K =\n\
        \x20   let y = CALL\n\
        \x20   let m: y.K = k\n\
        \x20   m\n\
        end\n";
    let member = SRC
        .replace(
            "MEMBER",
            "operation pick(p: DataProvider) -> DataProvider = p",
        )
        .replace("FREE", "")
        .replace("CALL", "DataProvider.pick(p)");
    assert!(
        errors_of(&member).is_empty(),
        "a member's return names THIS instance's `K`, so `y.K` IS `p.K` even though `y` is a \
         fresh value that records no alias: {:?}",
        errors_of(&member),
    );
    let free = SRC
        .replace("MEMBER", "")
        .replace("FREE", "operation pick(p: DataProvider) -> DataProvider")
        .replace("CALL", "pick(p)");
    assert!(
        !errors_of(&free).is_empty(),
        "declared OUTSIDE the sort the two references are foreign, so `y` keeps its own \
         element and the annotation is refused — §4.1's stability rule still decides that half",
    );
}
