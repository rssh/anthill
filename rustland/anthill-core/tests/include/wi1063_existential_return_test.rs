//! WI-1063 — an UNWRITTEN sort parameter in a RETURN is EXISTENTIAL: the body PACKS a witness,
//! every USE opens it to a fresh skolem.
//!
//! `operation widen(s: Stream[T = Int64, E = {Error}]) -> Stream[T = Int64]` declares
//! `∃E. Stream[T = Int64, E]`. Read the quantifier off the POLARITY of the arrow:
//!
//! * a PARAMETER's unwritten slot is NEGATIVE-position and UNIVERSAL — the caller instantiates
//!   it, so it is flexible at a call and rigid in the body. That is WI-1059/WI-1061, and
//!   §"Expansion during unification"'s "a signature written against a bare sort still threads
//!   bindings" is the same fact seen from the call.
//! * a RETURN's is POSITIVE-position and EXISTENTIAL — the body exhibits ONE witness, so it may
//!   be as specific as it likes, and no consumer may assume anything about it.
//!
//! One rule, two polarities. The delivered code is one walk
//! ([`rigidify_unwritten_sort_params`]) called from two [`SlotPosition`]s.
//!
//! ## What was leaking, and it was TWO things
//!
//! [`WIDEN`] is the bare/partial return: an effectful stream reached a slot that declared
//! `E = {}`. [`LAUNDER`] is the same unsoundness INSIDE A DELIVERED FEATURE — WI-402's
//! `-> C ensures KVStore[C]`, where the CARRIER is opened (`needs_mem(openOne(m))` is refused
//! at `expected MemStore, got KVStore`) but the MEMBERS never were, so `K = String` satisfied a
//! demand for `K = Int64`. Writing `ensures` bought nothing, which is why the fix could not be
//! confined to bare returns: the loader rewrites `-> C ensures Spec[C]` to a bare `-> Spec` and
//! the members then ride the ordinary path. Both close here, by the same three lines.
//!
//! ## Where the skolem is minted is the whole design
//!
//! NOT in the body check. That reading — rigidify the return where WI-1059 rigidifies the
//! parameters — is a UNIVERSAL in a positive position: it refuses `widen` itself, demanding a
//! body good for every row when only a witness was asked, and it costs 40 tests across
//! thirteen delivered tickets. It also silently retires the WI-401 escape gate, whose
//! `abstracting_return_error` sits in the `else` of `!conforms` and is unreachable once the
//! return no longer conforms. The decision and its measurement live at the body-check site in
//! `typing.rs` and in `wi1061_unwritten_slot_positions_test`'s header.
//!
//! AT EVERY USE. `open_existential_return`, and "every use" is FOUR sites, not the one the
//! first cut wired — see that function's doc. Two were found by review, each with the headline
//! exploit still running through it: a bare nullary name (`takes_pure(mk)`, no parentheses)
//! and the ETA lift (`apply_it(widen, s)`). Cost: THREE tests, all of which pinned the old
//! verdict (this file's two predecessors in `wi1061_…`, plus
//! `wi374_expansion_test::foreign_bare_return_op_loads_but_no_longer_narrows`, which had
//! pinned the ACCEPTING side of the same hole).
//!
//! ## THE CORPUS REACHES THIS ZERO TIMES — so this file is its only coverage
//!
//! Counted at the mint over all seven tiers (stdlib, `rustland/anthill-stl/anthill`,
//! `rustland/anthill-todo/anthill`, `rustland/anthill-cpp-gen/anthill`, `examples/`,
//! `anthill-todo/`, `anthill-testcases/`): every tier loads with zero errors and the opening
//! fires **zero** times. So "the corpus is clean" is evidence that nothing broke and NOT
//! evidence that anything works — exactly as it was for WI-1061's `Anonymous` arm. Every claim
//! below is driven here or it is not driven at all. The tier control is that `anthill load`
//! still reports the WI-1059 parameter-position refusal, which it does.
//!
//! ## What fails when each piece is backed out — DRIVEN, one revert each
//!
//! | revert | cost |
//! |---|---|
//! | `open_existential_return` returns `None` (all four call sites at once) | **15** rows: every test in this file except the three named both-ways-green below, plus `wi1061_…`'s two, `wi374_…`'s one and `wi402_…`'s new one |
//! | the eta opening alone (`operation_as_function_value` keeps `op.return_type`) | `the_eta_reading_opens_the_return_too`'s first half |
//! | REFUSING the eta lift instead of opening it | `typing_test::wi420_eta_of_curried_requires_op_is_loud_type_error` — a loud load error becomes a clean load that crashes at eval |
//! | the SELF gate (`SlotPosition::CallResult { callee_sort: None }`) | the PRELUDE stops loading (`cons.type_args`, "expected consistent bindings for the sort's shared type parameter") and **1590** tests fail |
//! | the call-side narrowing (`value_is_flex_var` at the call) | the stdlib reports `combinators.anthill:121` — `FilteredStream.splitFirst`'s own `Pair[A = Elem]` re-minted as an unrelated `Pair[A = ?A]` |
//!
//! THE NARROWING'S SHAPE CHANGED UNDER WI-1078 and its cost did not: it was "anonymous
//! carriers only", which exempted a NAMED variable and left this ticket's own exploit alive
//! under a two-character edit; it is now "anonymous, or a variable the SIGNATURE binds
//! nowhere". The last row's measurement still holds — what it protects is the op's own
//! `[Elem]`, which the signature binds — and `every_spelling_of_an_unbound_return_slot_opens`
//! carries the corrected verdict.
//!
//! Each was run alone, on the delivered tree. Three rows here pass under EVERY revert, by
//! design, and say so at their own sites: `the_ensures_carrier_is_still_abstract_at_the_-
//! consumer`, `the_wi401_escape_gate_still_fires` and
//! `an_unwritten_parameter_still_binds_from_the_argument`. They are the non-regressions the
//! rejected reading fails, not measurements of this one.
//!
//! REFERENCE: WI-1059 / WI-1061 (the parameter polarity, and this ticket's control);
//! WI-402 + `docs/design/path-dependent-types.md` §5 (the explicit `ensures Spec[C]`
//! existential — carrier enforced both halves, members neither); WI-401 (the escape gate);
//! WI-374 + `docs/design/type-parameter-scoping.md` §5 (erasure, which IS this existential
//! informally stated); `docs/kernel-language.md` §"Expansion during unification".

use crate::wi1012_static_supplier_tie_test::refusal;

/// The bare/partial-return witness. `widen` PACKS `{Error}` into a return that writes only `T`;
/// `exploit` hands the result to a slot that demands the empty row.
const WIDEN: &str = "namespace test.wi1063.widen\n\
    \x20 import anthill.prelude.{Int64, Stream, Error}\n\
    \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
    \x20 operation widen(s: Stream[T = Int64, E = {Error}]) -> Stream[T = Int64] = s\n\
    \x20 operation exploit(s: Stream[T = Int64, E = {Error}]) -> Int64 = takes_pure(widen(s))\n\
    end\n";

/// The `ensures`-form witness, inside the DELIVERED WI-402 feature. `openOne`'s real `K` is
/// `String` (from `MemStore`'s `provides`); `needs_int_key` demands `K = Int64`.
const LAUNDER: &str = "namespace test.wi1063.launder\n\
    \x20 import anthill.prelude.{Int64, String}\n\
    \x20 sort KVStore\n\
    \x20   sort K = ?\n\
    \x20   sort V = ?\n\
    \x20 end\n\
    \x20 sort MemStore\n\
    \x20   provides KVStore[K = String, V = String]\n\
    \x20   entity memStore\n\
    \x20 end\n\
    \x20 operation openOne(m: MemStore) -> C ensures KVStore[C] = m\n\
    \x20 operation needs_int_key(s: KVStore[K = Int64, V = String]) -> String\n\
    \x20 operation launder(m: MemStore) -> String = needs_int_key(openOne(m))\n\
    end\n";

/// THE HEADLINE, and both halves of the verdict in one assertion because either alone is
/// satisfiable by the wrong fix. The chain is REFUSED (the hole is closed) at `takes_pure`'s
/// parameter (the CONSUMER, where opening happens) and NOT at `widen.return` (the body packs a
/// witness and is correct as written — refusing it is the universal reading, which costs 40
/// tests and demands the wrong quantifier).
///
/// Asserted on `E = ?E` against `E = {}`: the `got` side must carry the skolem the
/// opening minted. Without that the assertion would also pass on a change that refused the
/// call for some unrelated reason.
///
/// CONTROL: on main the whole chain LOADS — `refusal` panics there, so this row fails on the
/// delivered tree for the plainest possible reason.
#[test]
fn a_bare_return_is_opened_at_the_consumer_and_the_producer_still_loads() {
    let msg = refusal(WIDEN);
    assert!(
        msg.contains("takes_pure.s") && !msg.contains("widen.return"),
        "the refusal belongs at the CONSUMER (`takes_pure`'s parameter), never at `widen`, \
         whose body packs a witness: {msg}",
    );
    assert!(
        msg.contains("E = ?E") && msg.contains("E = {}"),
        "the refusal must name the skolem the call opened and the row it was handed to: {msg}",
    );
}

/// THE SECOND WITNESS, and the one that says the fix could not be confined to bare returns:
/// the same laundering with `ensures` WRITTEN and the WI-401 gate satisfied. `openOne` is a
/// delivered, admitted WI-402 existential; the loader rewrites its return to a bare `KVStore`,
/// so before this ticket its MEMBERS rode the ordinary width-tolerant path and `K = String`
/// satisfied a demand for `K = Int64`.
///
/// This is the four-cell table WI-1063 completed. Carrier: declaration enforced (WI-401),
/// consumer enforced (`needs_mem` below). Member: declaration NOT enforced (correctly — the
/// body packs), consumer now enforced (here).
///
/// CONTROL: on main `launder` loads clean, driven.
#[test]
fn an_ensures_existentials_members_are_opened_too() {
    let msg = refusal(LAUNDER);
    assert!(
        msg.contains("needs_int_key.s") && msg.contains("K = ?K"),
        "the ensures form must open its MEMBERS at the consumer, not only its carrier: {msg}",
    );
}

/// THE CARRIER HALF, UNCHANGED — the delivered WI-402 behaviour this ticket had to leave
/// alone. `needs_mem(openOne(m))` is refused at `expected MemStore, got KVStore`: the witness
/// does not escape and the caller really does see the abstract carrier.
///
/// Here so that the member-opening row above cannot be satisfied by a change that broke the
/// carrier half instead — the two are different mechanisms (`strip_spec_carrier` DROPS the
/// carrier at load, so the carrier needs no opening code at all) and they must both hold.
///
/// CONTROL: passes on main too, BY DESIGN. It measures nothing on its own; it is the
/// non-regression half of the pair.
#[test]
fn the_ensures_carrier_is_still_abstract_at_the_consumer() {
    let msg = refusal(&LAUNDER.replace(
        " operation launder(m: MemStore) -> String = needs_int_key(openOne(m))\n",
        " operation needs_mem(m: MemStore) -> String\n\
         \x20 operation nolaunder(m: MemStore) -> String = needs_mem(openOne(m))\n",
    ));
    assert!(
        msg.contains("needs_mem.m") && msg.contains("expected MemStore"),
        "the WI-402 carrier must still be opened — `openOne`'s result is a KVStore, not the \
         MemStore that witnessed it: {msg}",
    );
}

/// FRESHNESS PER OPENING, which is the soundness and not an implementation detail: two calls
/// may genuinely return different rows, so one shared constant would relate them.
///
/// DRIVEN rather than asserted about the implementation. `takes_same[E]` demands its two
/// arguments carry the SAME row. Fed two separate openings of `mk`, it is REFUSED — which can
/// only happen if the two skolems are unrelated; a shared constant would unify and the program
/// would load. The rendered pair is `expected E = ?E, got E = ?E`: two things that print alike
/// and are not the same type, which is what an anonymous skolem looks like from the diagnostic
/// side.
///
/// ITS CONTROL IS THE ROW BELOW, not a comment — `f[E]` with ONE opening LOADS. Without that
/// pair this row would also pass if a skolem simply never bound anything.
#[test]
fn two_openings_of_one_operation_are_unrelated() {
    let msg = refusal(
        "namespace test.wi1063.fresh\n\
         \x20 import anthill.prelude.{Int64, Stream}\n\
         \x20 operation mk(n: Int64) -> Stream[T = Int64]\n\
         \x20 operation takes_same[E](x: Stream[T = Int64, E = E], y: Stream[T = Int64, E = E]) \
         -> Int64\n\
         \x20 operation two(a: Int64, b: Int64) -> Int64 = takes_same(mk(a), mk(b))\n\
         end\n",
    );
    assert!(
        msg.contains("takes_same.y"),
        "two openings must mint UNRELATED skolems, so the second argument cannot carry the row \
         the first bound: {msg}",
    );
}

/// A ROW-POLYMORPHIC CONSUMER STILL ACCEPTS ONE — a universal instantiates to anything,
/// including a rigid. This is the positive control for the row above, and it is NOT a
/// both-ways-green non-regression: on main this program is REFUSED, at `expected a type for
/// 'E', got unconstrained`, because a bare return gave `E` nothing to bind to. Opening the
/// return is what gives the inference something to solve — the same mechanism read from its
/// accepting side, exactly as WI-1059's `sink[X]` row reads the parameter half.
///
/// CONTROL: fails on main (for the opposite reason), and fails with the opening backed out.
#[test]
fn a_row_polymorphic_consumer_accepts_a_skolem() {
    crate::common::load_kb_with(
        "namespace test.wi1063.rowpoly\n\
         \x20 import anthill.prelude.{Int64, Stream}\n\
         \x20 operation mk(n: Int64) -> Stream[T = Int64]\n\
         \x20 operation f[E](s: Stream[T = Int64, E = E]) -> Int64\n\
         \x20 operation ok(a: Int64) -> Int64 = f(mk(a))\n\
         end\n",
    );
}

/// THE CALLEE'S OWN SORT IS NOT EXISTENTIAL IN ITS RETURN, and this row is the reason the
/// opening is keyed the way [`expand_foreign_sort_application`] keys the parameter side. A
/// self-sort return (`-> List` declared inside `sort List`) is the §3 parametricity tie: it
/// names THIS instance's parameter, which the call's own argument unification pins. Minting a
/// skolem there would refuse every self-returning member in the stdlib.
///
/// Both halves are driven together because the gate has two ways to be wrong: skip too much
/// (a FOREIGN partial return on a MEMBER operation left unopened — `Box.open_stream` here) or
/// skip too little (the self-sort return above).
///
/// CONTROL, driven per half. `Box.open_stream`'s chain LOADS on main. The `Wrap` half loads on
/// main and after (2597 facts, identical), and with the self gate dropped
/// (`SlotPosition::CallResult { callee_sort: None }`) it FAILS at `expected
/// List[T = Wrap[T = Int64]], got List[T = Wrap[T = ?T]]` — the sort's own parameter re-minted
/// as an unrelated skolem. That same revert costs the PRELUDE (`cons.type_args`) and 1590
/// tests, so this row is the small one that says what the gate is for.
#[test]
fn a_self_sort_return_is_not_opened_but_a_foreign_one_on_a_member_is() {
    crate::common::load_kb_with(
        "namespace test.wi1063.selfret\n\
         \x20 import anthill.prelude.{Int64, List}\n\
         \x20 import anthill.prelude.List.{cons, nil}\n\
         \x20 sort Wrap\n\
         \x20   sort T = ?\n\
         \x20   entity Wrap(v: T)\n\
         \x20   operation dup(w: Wrap) -> List[T = Wrap] = cons(head: w, tail: nil)\n\
         \x20 end\n\
         \x20 operation takes_ints(l: List[T = Wrap[T = Int64]]) -> Int64\n\
         \x20 operation use_it(w: Wrap[T = Int64]) -> Int64 = takes_ints(Wrap.dup(w))\n\
         end\n",
    );
    let member = refusal(
        "namespace test.wi1063.memberret\n\
         \x20 import anthill.prelude.{Int64, Stream}\n\
         \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
         \x20 sort Box\n\
         \x20   entity box(n: Int64)\n\
         \x20   operation open_stream(b: Box) -> Stream[T = Int64]\n\
         \x20 end\n\
         \x20 operation use_it(b: Box) -> Int64 = takes_pure(Box.open_stream(b))\n\
         end\n",
    );
    assert!(
        member.contains("takes_pure.s") && member.contains("E = ?E"),
        "a MEMBER operation's FOREIGN partial return is still existential — the self gate must \
         key on the base sort, not on the callee having a parent: {member}",
    );
}

/// ALL FOUR SPELLINGS OF ONE RETURN OPEN ALIKE — the WI-1056 measurement carried to the other
/// polarity. `E = ?` is an unwritten slot spelled out (§"Expansion during unification": the
/// ways mean the same thing), so it must open exactly as an omitted `E` does.
///
/// IT IS A DIFFERENT CARRIER FROM THE BODY'S, which is why it needs its own row rather than
/// riding the headline. In the body every remaining flexible variable IS an author's `?`, so
/// WI-1061 tests for one. At a call NOTHING has been rigidified — the op's own `[Elem]`, the
/// enclosing sort's parameters and an eliminated `s.T` are all still flexible, so the broad
/// test would skolemize slots this call is about to BIND. The corpus proved that necessary
/// rather than tidy: reading every flexible variable as unwritten re-minted
/// `FilteredStream.splitFirst`'s own `Pair[A = Elem]` as an unrelated skolem.
///
/// WHAT NARROWED IT WAS ONCE THE SPELLING, AND IS NOW THE SIGNATURE (WI-1078). This ticket
/// shipped `value_is_anonymous_wildcard` — anonymous carriers only — and the second half of
/// this row used to assert that `mk_named() -> Stream[T = Int64, E = ?A]` was therefore
/// exempt. It was the same hole under a two-character edit, and it is now REFUSED: a variable
/// the signature binds nowhere is the existential this section is about, whatever it is
/// spelled. What the narrowing protects is unchanged, and is a property of the DECLARATION
/// rather than of the carrier — see `wi1078_unbound_return_var_test`.
///
/// CONTROL: `?` LOADS on main (the fourth spelling of the hole, leaking); `?A` also loaded on
/// main, which is exactly what WI-1078 closed, so the second half fails on the tree this
/// ticket delivered.
#[test]
fn every_spelling_of_an_unbound_return_slot_opens() {
    let anon = refusal(
        "namespace test.wi1063.anon\n\
         \x20 import anthill.prelude.{Int64, Stream, Error}\n\
         \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
         \x20 operation widen_q(s: Stream[T = Int64, E = {Error}]) -> Stream[T = Int64, E = ?] \
         = s\n\
         \x20 operation exploit_q(s: Stream[T = Int64, E = {Error}]) -> Int64 = \
         takes_pure(widen_q(s))\n\
         end\n",
    );
    assert!(
        anon.contains("takes_pure.s") && !anon.contains("widen_q.return"),
        "`E = ?` in a return is the same existential as omitting it, opened at the same place: \
         {anon}",
    );
    let named = refusal(
        "namespace test.wi1063.named\n\
         \x20 import anthill.prelude.{Int64, Stream}\n\
         \x20 operation mk_named() -> Stream[T = Int64, E = ?A]\n\
         \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
         \x20 operation ok() -> Int64 = takes_pure(mk_named())\n\
         end\n",
    );
    assert!(
        named.contains("takes_pure.s") && named.contains("E = ?A"),
        "a NAMED variable the signature binds nowhere is the same existential (WI-1078): \
         {named}",
    );
}

/// A SKOLEM MAY NOT ESCAPE INTO A MANIFEST RETURN — the avoidance problem, one polarity over.
/// `escape` promises `KVStore[K = String, V = String]` and hands back a value whose members
/// are the constants `openOne`'s opening minted; naming them is precisely what the signature
/// cannot do. Refused at `escape.return`.
///
/// WHERE IT IS REFUSED IS RECORDED BECAUSE IT IS NOT WHERE THE TICKET PREDICTED. This is
/// ordinary return CONFORMANCE, not the WI-401 gate: `abstracting_return_error` runs only in
/// the `else` of `!conforms`, so a return that fails to conform never reaches it. That gate
/// keeps its own population — an abstracting return that DOES conform by provider upcast — and
/// [`the_wi401_escape_gate_still_fires`] holds it.
///
/// CONTROL: on main this loads clean, with `K = String` silently fabricated for a caller.
#[test]
fn an_escaping_skolem_is_refused() {
    let msg = refusal(&LAUNDER.replace(
        " operation needs_int_key(s: KVStore[K = Int64, V = String]) -> String\n\
         \x20 operation launder(m: MemStore) -> String = needs_int_key(openOne(m))\n",
        " operation escape(m: MemStore) -> KVStore[K = String, V = String] = openOne(m)\n",
    ));
    assert!(
        msg.contains("escape.return") && msg.contains("K = ?K"),
        "a skolem minted by an opening must not be nameable by the enclosing signature: {msg}",
    );
}

/// THE WI-401 ESCAPE GATE STILL FIRES, with its own diagnostic, byte-for-byte. This is the
/// requirement the rejected reading could not meet: rigidifying the return in the BODY makes
/// the return stop conforming, and the gate — which lives in the `else` of `!conforms` — goes
/// unreachable, taking the whole WI-401/402/457/480/488/491 diagnostic family with it in
/// silence. Opening at the CALL leaves the gate's precondition untouched, because the
/// declaration side is never rewritten at all.
///
/// CONTROL: passes on main, BY DESIGN — it is the non-regression that the rejected reading
/// fails. Driven both ways.
#[test]
fn the_wi401_escape_gate_still_fires() {
    let msg = refusal(&LAUNDER.replace(
        " operation openOne(m: MemStore) -> C ensures KVStore[C] = m\n\
         \x20 operation needs_int_key(s: KVStore[K = Int64, V = String]) -> String\n\
         \x20 operation launder(m: MemStore) -> String = needs_int_key(openOne(m))\n",
        " operation seal(m: MemStore) -> KVStore = m\n",
    ));
    assert!(
        msg.contains("seal.return")
            && msg.contains("an abstracting return")
            && msg.contains("would escape its scope (the avoidance problem)"),
        "the WI-401 gate's own diagnostic must survive — it is what the body-check reading \
         silently retires: {msg}",
    );
}

/// RE-PACKING DOES NOT LAUNDER. `reseal`'s own bare `-> KVStore` is itself an existential, so
/// its body legitimately packs the constants `openOne`'s opening minted (it LOADS, and must —
/// nothing escapes, because a caller of `reseal` opens its result afresh). What must not
/// happen is that the round trip through a second existential recovers the members: it does
/// not, and `needs_int_key(reseal(m))` is refused exactly as the direct call is.
///
/// Here because "closed at one hop" is the cheap version of this fix and looks identical on
/// the headline program.
///
/// CONTROL: on main the whole chain loads.
#[test]
fn repacking_through_a_second_existential_does_not_recover_the_members() {
    let msg = refusal(&LAUNDER.replace(
        " operation launder(m: MemStore) -> String = needs_int_key(openOne(m))\n",
        " operation reseal(m: MemStore) -> KVStore = openOne(m)\n\
         \x20 operation launder(m: MemStore) -> String = needs_int_key(reseal(m))\n",
    ));
    assert!(
        msg.contains("needs_int_key.s") && !msg.contains("reseal.return"),
        "`reseal` re-packs and must load; the members must still be unrecoverable one hop \
         later: {msg}",
    );
}

/// THE SKOLEM SURVIVES A `let`. The opening happens where the callee's return becomes the
/// call's result type, so binding that result to a local carries the constant with it rather
/// than laundering it through the local's inferred type.
///
/// A separate row because a `let` is a different path to the same demand
/// (`unroll_annotation_with_inferred` / let conformance rather than the op-arg check), and an
/// opening that only reached the direct-argument position would leave it open.
///
/// CONTROL: on main this loads.
#[test]
fn the_skolem_survives_a_let_binding() {
    let msg = refusal(
        "namespace test.wi1063.vialet\n\
         \x20 import anthill.prelude.{Int64, Stream, Error}\n\
         \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
         \x20 operation widen(s: Stream[T = Int64, E = {Error}]) -> Stream[T = Int64] = s\n\
         \x20 operation via_let(s: Stream[T = Int64, E = {Error}]) -> Int64 =\n\
         \x20   let w = widen(s)\n\
         \x20   takes_pure(w)\n\
         end\n",
    );
    assert!(
        msg.contains("takes_pure.s") && msg.contains("E = ?E"),
        "a `let` must not launder the opened row: {msg}",
    );
}

/// A ZERO-ARG CALL WRITTEN WITHOUT PARENTHESES IS STILL A CALL — the review's finding on the
/// first cut, and the reason the "one site owns this" claim in `open_existential_return`'s doc
/// is now a list of three. A bare nullary operation name denotes its return
/// ([`check_bare_ref`]'s zero-arg-call reading, which is NOT the eta reading — that one
/// returned an arrow type further up), and that site read the declared return verbatim. So the
/// headline exploit survived deleting two characters: `takes_pure(mk())` was refused and
/// `takes_pure(mk)` loaded clean, on the same two declarations.
///
/// The `mk_str` half is the control that makes the first half mean something. It proves the
/// bare-name site really does CHECK the type it produces — a wrong ELEMENT type was already
/// refused there before this ticket — so the row leaking was the row specifically, not the
/// whole position being unchecked.
///
/// CONTROL: on main the `mk` half LOADS and the `mk_str` half is refused, both driven; with
/// the opening backed out of `check_bare_ref` alone, the `mk` half loads again while every
/// other row in this file still passes.
#[test]
fn a_bare_nullary_operation_name_opens_too() {
    let leak = refusal(
        "namespace test.wi1063.bareref\n\
         \x20 import anthill.prelude.{Int64, Stream}\n\
         \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
         \x20 operation mk() -> Stream[T = Int64]\n\
         \x20 operation use_bare() -> Int64 = takes_pure(mk)\n\
         end\n",
    );
    assert!(
        leak.contains("takes_pure.s") && leak.contains("E = ?E"),
        "the parenthesis-free zero-arg call must open the same existential `mk()` does: \
         {leak}",
    );
    let elem = refusal(
        "namespace test.wi1063.barerefelem\n\
         \x20 import anthill.prelude.{Int64, String, Stream}\n\
         \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
         \x20 operation mk_str() -> Stream[T = String]\n\
         \x20 operation use_bare() -> Int64 = takes_pure(mk_str)\n\
         end\n",
    );
    assert!(
        elem.contains("T = String"),
        "the bare-name site checks the type it produces — without this the row above would \
         be measuring an unchecked position, not a closed hole: {elem}",
    );
}

/// THE ETA READING OPENS TOO — the review's second finding, and the one that says "each call
/// opens" was not yet true. Naming an operation where a FUNCTION is expected lifts it to its
/// arrow type, and that arrow's RESULT is a use of the declared return, so it must open like
/// any other. It did not, and the headline exploit survived one indirection: `apply_it(widen,
/// s)` put `{Error}` into a slot declaring `E = {}` with `widen` written exactly as in
/// [`WIDEN`].
///
/// THE SECOND HALF IS WHAT KEEPS IT FROM BEING "REFUSE EVERY LIFT". `pass_through`'s slot
/// leaves the row unwritten too — it never asked — so the lift still loads. Opening does not
/// reject; it stops the row being invented.
///
/// ONE SKOLEM PER LIFT, NOT PER APPLICATION, is the limit, stated at the site: an arrow type
/// has nowhere to write `∃`, so every application of one lifted value reads the same ρ. Sound
/// for the monomorphic arrow the lift builds (a type-parameterized op is refused a lift
/// outright, so the argument types are pinned and the result really is one type).
///
/// CONTROL: on main the `exploit` half LOADS. Refusing the lift instead of opening it — the
/// symmetric-looking alternative, since the site already refuses a type-parameterized op for
/// the sibling aliasing reason — is REFUTED: `Function` declares an effect row, so
/// `build(seed: Int64) -> Function[A = Int64, B = Bool]` is caught too, falls through to the
/// zero-arg-call reading, and `typing_test::wi420_eta_of_curried_requires_op_is_loud_type_-
/// error` turns from a loud load error into a clean load that crashes at eval. Driven, both
/// ways.
#[test]
fn the_eta_reading_opens_the_return_too() {
    let leak = refusal(
        "namespace test.wi1063.eta\n\
         \x20 import anthill.prelude.{Int64, Stream, Error}\n\
         \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
         \x20 operation widen(s: Stream[T = Int64, E = {Error}]) -> Stream[T = Int64] = s\n\
         \x20 operation apply_it(f: (s: Stream[T = Int64, E = {Error}]) -> \
         Stream[T = Int64, E = {}], s: Stream[T = Int64, E = {Error}]) -> Int64 = \
         takes_pure(f(s))\n\
         \x20 operation exploit(s: Stream[T = Int64, E = {Error}]) -> Int64 = \
         apply_it(widen, s)\n\
         end\n",
    );
    assert!(
        leak.contains("apply_it.f"),
        "the lifted arrow's result must open, so a slot that names the row refuses it: \
         {leak}",
    );
    crate::common::load_kb_with(
        "namespace test.wi1063.etaok\n\
         \x20 import anthill.prelude.{Int64, Stream, Error}\n\
         \x20 operation widen(s: Stream[T = Int64, E = {Error}]) -> Stream[T = Int64] = s\n\
         \x20 operation pass_through(f: (s: Stream[T = Int64, E = {Error}]) -> \
         Stream[T = Int64], s: Stream[T = Int64, E = {Error}]) -> Int64 = 1\n\
         \x20 operation ok(s: Stream[T = Int64, E = {Error}]) -> Int64 = \
         pass_through(widen, s)\n\
         end\n",
    );
}

/// THE PARAMETER POLARITY IS UNTOUCHED, asserted here rather than left to
/// `wi1059_unwritten_param_rigid_test` passing, because the two rules share ONE walk and a
/// policy read at the wrong position would flip both. A body that genuinely holds for every
/// instantiation still loads: at a CALL an unwritten PARAMETER is FLEXIBLE and binds from the
/// argument — that is §8.1's stated feature, and it is the opposite of what this ticket does
/// to a return.
///
/// CONTROL: passes on main, BY DESIGN. It fails if the call-site policy is applied to the
/// parameter expansion, which is the one-line mistake this file exists to catch.
#[test]
fn an_unwritten_parameter_still_binds_from_the_argument() {
    crate::common::load_kb_with(
        "namespace test.wi1063.paramside\n\
         \x20 import anthill.prelude.{Int64, Stream}\n\
         \x20 operation takes_any(s: Stream) -> Int64\n\
         \x20 operation mk_int() -> Stream[T = Int64, E = {}]\n\
         \x20 operation ok() -> Int64 = takes_any(mk_int())\n\
         end\n",
    );
}
