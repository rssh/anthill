//! WI-20261005-2KV4Y — a value in scope says nothing about what a call left open.
//!
//! A requirement nothing can build is still met when a value HOLDS it (§8.7's route (2);
//! `scope_contract_covers_dep`): its type carries the contract, and the call stated the
//! very instance the contract is at. The route asked less than that — it took a value as
//! saying what the call had NOT stated. MEASURED on the parent commit, each a clean load:
//!
//! * A CARRIER THE CALL DOES NOT FIX. `User requires Store[State = S]`, `ask() =
//!   Store.zero()`, and `run(b: Buf[…]) = User.ask()`: nothing at the call fixes `S`, and
//!   `b` — which the call never mentions — was taken to say it. The run died
//!   "`__req_store` not bound in caller frame"; without `b` the call was refused. The value
//!   spelling of `b`'s type was refused too, so the two spellings of one program disagreed.
//!   An ARGUMENT nothing relates to `S` did the same (`User.show(b)`); so did a value whose
//!   own SORT requires the spec (`w: Wrap[K = Buf[…]]`, `Wrap requires Store[State = K]`),
//!   and one typed at the CALLEE'S OWN spec (`h: Hold[C = Buf[…]]` beside `Hold.ask()`).
//! * AN OPEN SLOT OF A CARRIER THE CALL DID PIN. `User.go1(buf(v: 1))` leaves `Buf`'s `N`
//!   open, two providers tie, and a `c: Buf[T = Int64, N = Bool]` in scope was taken to say
//!   `N`: the same death. With the holder one of the call's own arguments the run raised
//!   `AmbiguousRequirement`.
//! * A REQUIREMENT DECLARED AFTER ONE A VALUE HOLDS. `User requires Tag[T = K]` and then
//!   `requires Store[State = S]`: the held `Tag` ended the judging of the chain, so `Store`,
//!   with nothing fixing `S`, was never asked.
//!
//! Each is refused at load now. A value covers a requirement the call states in full and
//! nothing of one it leaves an element of open (§5.2's refusal); the chain is judged to its
//! end; and a sort written with slots left out — the type of a result nothing has named,
//! `Bag.empty()` — is asked at its open slots when the requirement is CONSTRUCTED, where it
//! used to be met by swapping a value's type in and building nothing. What still discharges
//! is a requirement the call stated
//! ([`an_operations_own_requirement_is_supplied_through_the_callers`],
//! [`a_specs_own_operation_on_a_value_of_any_provider_runs`]) and a declared `require[…]`
//! bracket.
//!
//! THE STANDARD LIBRARY WAS THE ONE POPULATION THE FIRST DISCHARGE SERVED. `MappedStream`
//! and `FilteredStream` declared `requires Iterable[C = Source, …]` on the sort; `map` /
//! `filter` take `s: Sc` and return another instance, so no call of them fixes `Source`,
//! and the requirement was met by the list or the stream that happened to be there. No body
//! read it — the `source` field's type is what says the source is iterable — and the two
//! clauses are deleted. A user sort shaped that way is refused
//! ([`a_factory_that_leaves_its_sorts_requirement_unfixed_is_refused`]).
//!
//! A refusal row asserts a LOAD verdict naming the requirement; a row that runs asserts the
//! value.
//!
//! WI-20261005-KSSA4 — NO VALUE HOLDS A REQUIREMENT ANY MORE, AND THE ROWS THAT TYPED ONE
//! AT A SPEC ARE WRITTEN OVER ANY PROVIDER. `w: Tagger` was a value "typed at a spec", read
//! as a value of the spec's carrier that carries the spec's chain; a `B` provides `Tagger`
//! and is not one, so that parameter takes no `B` and nothing held there is a `Tagger.C`.
//! The rows that passed one write `w: Tagger.C` — a value of a sort of which `Tagger` is
//! required — and what they measure is unchanged where it was about the CALL: a
//! requirement the call states is supplied (now through the caller's own requirement,
//! whose chain has it), one it leaves an element of open is refused, and the chain is
//! judged to its end. Parts 2 and 7 of the ledger below back out the value half of the
//! route, which no longer exists: `held_spec_views` reads a declared `require[…]` bracket
//! and nothing else. The standard library's two clauses are back, on a field typed by the
//! sort's own parameter ([`a_factory_receiving_on_the_sorts_own_source_runs`]).
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ───────────────────────────────
//!
//! EACH PART backed out present-but-wrong, APPLIED AND RUN over this file's 29 rows.
//!
//! 1. THE PARENT COMMIT'S TYPER, the standard library as it now is. 17 FAIL. Twelve are
//!    "expected a refusal, got a clean load":
//!    [`a_value_in_scope_does_not_say_what_the_call_left_open`] (at `typed`),
//!    [`a_let_bound_value_does_not_say_it_either`],
//!    [`an_argument_the_signature_does_not_relate_to_the_carrier_does_not_fix_it`],
//!    [`a_value_whose_sort_requires_the_spec_does_not_say_it_either`],
//!    [`a_spec_typed_value_does_not_say_it_either`],
//!    [`a_value_of_the_callees_own_spec_does_not_say_it_either`],
//!    [`a_call_that_fixes_nothing_is_refused_alike_in_both_spellings`] (at `typed`),
//!    [`an_open_slot_is_not_filled_by_a_value_in_scope`],
//!    [`a_hole_in_the_receiver_bracket_is_not_filled_either`],
//!    [`a_tie_over_an_open_slot_is_refused_at_load_not_at_run_time`],
//!    [`a_requirement_declared_after_a_held_one_is_still_owed`] and
//!    [`a_factory_that_leaves_its_sorts_requirement_unfixed_is_refused`]. Three die at run
//!    time, "`__req_…` not bound in caller frame":
//!    [`a_carrier_written_as_its_bare_sort_gets_a_dictionary`],
//!    [`an_operation_level_requirement_at_a_bare_carrier_gets_a_dictionary`] and
//!    [`a_named_slot_at_a_bare_carrier_takes_the_default`]. Two are refused where they now
//!    answer or are named: [`a_bare_sort_is_opened_in_whichever_element_it_stands`] (with
//!    `From` declared first) and [`two_provisions_generic_in_the_slot_are_a_tie`] (refused,
//!    naming no rival).
//! 2. A VALUE ASKED AS A BRACKET IS — the open elements dropped for every holder, the
//!    parent's reading on today's route. 2 FAIL, each a clean load:
//!    [`a_spec_typed_value_does_not_say_it_either`] and
//!    [`a_value_of_the_callees_own_spec_does_not_say_it_either`].
//!    [`a_value_whose_sort_requires_the_spec_does_not_say_it_either`] loads only with this
//!    AND the rule that it is a spec which holds a chain backed out together: `Wrap` is a
//!    carrier, and is not asked at all.
//! 3. A HELD REQUIREMENT ENDING THE JUDGING OF THE CHAIN. 1 FAILS, a clean load:
//!    [`a_requirement_declared_after_a_held_one_is_still_owed`].
//! 4. THE SECOND ASKING NEVER MADE (`resolve_opening_unwritten_slots` answering the goal as
//!    written). 5 FAIL, each refused at load:
//!    [`a_carrier_written_as_its_bare_sort_gets_a_dictionary`],
//!    [`an_operation_level_requirement_at_a_bare_carrier_gets_a_dictionary`],
//!    [`a_named_slot_at_a_bare_carrier_takes_the_default`],
//!    [`a_bare_sort_is_opened_in_whichever_element_it_stands`] and
//!    [`two_provisions_generic_in_the_slot_are_a_tie`] (naming no rival).
//! 5. EACH PART OF THE SECOND ASKING, alone. 1 FAILS under each:
//!    * only the parameter an operation receives on opened —
//!      [`a_bare_sort_is_opened_in_whichever_element_it_stands`], refused with `From`
//!      declared first;
//!    * a cycle at the open slots taken as the answer —
//!      [`a_cycle_at_the_open_slots_is_refused_at_load`], a clean load;
//!    * only a construction taken, not a tie —
//!      [`two_provisions_generic_in_the_slot_are_a_tie`], refused naming no rival;
//!    * a sort with a parameter that has no variable opened like any other —
//!      [`a_sort_the_loader_has_refused_is_not_opened`], which panics on WI-954's
//!      assertion;
//!    * the named-slot inference asking the goal as written —
//!      [`a_named_slot_at_a_bare_carrier_takes_the_default`], refused as a tie.
//! 6. WI-20260929-020TH's CHAIN-END READ on its parent's read. 2 FAIL:
//!    [`a_hole_in_the_receiver_bracket_is_not_filled_either`] (refused, but as "no impl
//!    provides" rather than as the tie) and
//!    [`a_tie_over_an_open_slot_is_refused_at_load_not_at_run_time`] (loads).
//! 7. THE ROUTE ANSWERING "NOTHING IS HELD". 3 FAIL, each refused at load:
//!    [`an_operations_own_requirement_is_supplied_through_the_callers`] and
//!    [`a_specs_own_operation_on_a_value_of_any_provider_runs`] — what says the cover does
//!    not refuse too much — and [`a_requirement_declared_after_a_held_one_is_still_owed`],
//!    refused over the `Tag` its `w` no longer holds before `Store` is reached.
//! 8. THE TWO CLAUSES PUT BACK in the standard library. No row of this file moves — its
//!    own factory is a user sort; 7 fail elsewhere, the calls that owed them: `wi599
//!    …the_stdlib_combinators_are_general_over_any_iterable_source`, `wi_0rp29_nested_
//!    projection_value_in_type_test …the_fallback_over_a_carrier_written_with_its_
//!    parameters`, four rows of `x13yv_map_map_chain_test` and the capability matrix's
//!    consumer row.
//!
//! PASS UNDER EVERY ONE, by design: [`without_the_value_the_call_is_refused_the_same_way`],
//! [`a_bracket_fixes_the_carrier_and_the_call_runs`],
//! [`without_the_value_the_open_slot_is_the_same_tie`],
//! [`one_provider_answers_an_open_slot`],
//! [`declared_before_the_held_one_it_is_refused_the_same_way`],
//! [`a_factory_receiving_on_the_sorts_own_source_runs`], and the two that pin a case this change
//! leaves as it was: [`beside_a_generic_provision_the_bare_spelling_runs_the_generic_one`]
//! and [`a_provision_at_one_instance_does_not_answer_a_bare_carrier`].

use crate::common::{assert_refused_naming, load_errors_of, replace_in_fixture, run_int64};
use crate::wi_020th_two_hop_chain_test::{at_each_spelling, Spelling, CHAIN_CALL, USER_SORT};

/// `Buf[T, N]` and the spec `Store`, with an operation that takes a state and one that
/// takes nothing; `body` follows.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, Option}}
  import anthill.prelude.Option.{{some, none}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
    operation zero() -> Int64
  end
{body}
end
"#
    )
}

/// A provider of `Store` at `at`: `peek` answers the buffer's value plus `n`, `zero` `n`.
fn provider(name: &str, at: &str, n: i64) -> String {
    format!(
        "\n  sort {name}\n    provides Store[State = {at}]\n    \
         operation peek(s: {at}) -> Int64 = s.v + {n}\n    \
         operation zero() -> Int64 = {n}\n  end\n"
    )
}

const BOOL: &str = "Buf[T = Int64, N = Bool]";
const STRING: &str = "Buf[T = Int64, N = String]";

/// `User` with the requirement on the sort, an operation that takes nothing, one that
/// takes a `Buf` its signature does not relate to `S`, and one that takes an `S`.
fn user(unrelated: &str) -> String {
    format!(
        "\n  sort User\n    sort S = ?\n    requires Store[State = S]\n    \
         operation ask() -> Int64 = Store.zero()\n    \
         operation show(x: {unrelated}) -> Int64 = Store.zero()\n    \
         operation go1(s: S) -> Int64 = Store.peek(s)\n  end\n"
    )
}

/// The refusal of a call that leaves `User`'s `S` unfixed.
fn assert_unfixed(errs: &[String], ns: &str, op: &str, why: &str) {
    assert_refused_naming(
        errs,
        &[
            &format!("`{ns}.Store[State = {ns}.User.S]`"),
            &format!("cannot be supplied for call to `{ns}.User.{op}`"),
            &format!("element `State = {ns}.User.S` is unconstrained at this call site"),
        ],
        why,
    );
}

// ── a carrier the call does not fix ───────────────────────────────────────────────────

/// THE TICKET'S PROGRAM, both spellings of `b`'s type: `b` is in scope and the call does
/// not mention it. Loaded at `typed` before, and died at run time.
#[test]
fn a_value_in_scope_does_not_say_what_the_call_left_open() {
    at_each_spelling(|sp| {
        let ns = format!("wi2kv4y.scope_{}", sp.tag);
        let body = format!(
            "{}{}\n  operation run(b: {}) -> Int64 = User.ask()\n  \
             operation go() -> Int64 = run(buf(v: 1))\n",
            provider("P", sp.call, 100),
            user(sp.call),
            sp.call
        );
        assert_unfixed(
            &load_errors_of(&program(&ns, &body)),
            &ns,
            "ask",
            &format!("`User.ask()` beside an unrelated `b`, {}", sp.tag),
        );
    });
}

/// ITS CONTROL: no `Buf` in scope, the same refusal. Passes with or without the change.
#[test]
fn without_the_value_the_call_is_refused_the_same_way() {
    let ns = "wi2kv4y.noscope";
    let body = format!(
        "{}{}\n  operation run(n: Int64) -> Int64 = User.ask()\n  \
         operation go() -> Int64 = run(1)\n",
        provider("P", BOOL, 100),
        user(BOOL)
    );
    assert_unfixed(
        &load_errors_of(&program(ns, &body)),
        ns,
        "ask",
        "`User.ask()` with no `Buf` in scope",
    );
}

/// …AND THE CALL IS NOT WHAT IS WRONG: with the bracket saying `S`, the same operation
/// runs the provider at that type, in both spellings.
#[test]
fn a_bracket_fixes_the_carrier_and_the_call_runs() {
    at_each_spelling(|sp: &Spelling| {
        let ns = format!("wi2kv4y.bracket_{}", sp.tag);
        let body = format!(
            "{}{}{}\n  operation go() -> Int64 = User[S = {}].ask()\n",
            provider("P", sp.call, 100),
            provider("Q", sp.other, 200),
            user(sp.call),
            sp.call
        );
        assert_eq!(
            run_int64(&program(&ns, &body), &format!("{ns}.go")),
            Ok(100),
            "{}",
            sp.tag
        );
    });
}

/// A `let` is a value in scope as a parameter is.
#[test]
fn a_let_bound_value_does_not_say_it_either() {
    let ns = "wi2kv4y.letscope";
    let body = format!(
        "{}{}\n  operation mk() -> {BOOL} = buf(v: 1)\n  \
         operation go() -> Int64 =\n    let b = mk()\n    User.ask()\n",
        provider("P", BOOL, 100),
        user(BOOL)
    );
    assert_unfixed(
        &load_errors_of(&program(ns, &body)),
        ns,
        "ask",
        "`User.ask()` beside a let-bound `Buf`",
    );
}

/// AN ARGUMENT IS NOT ENOUGH EITHER, where nothing relates it to the requirement: `show`
/// takes a `Buf` and its signature says nothing of `S`. Loaded before, and died.
#[test]
fn an_argument_the_signature_does_not_relate_to_the_carrier_does_not_fix_it() {
    let ns = "wi2kv4y.unrelated";
    let body = format!(
        "{}{}\n  operation run(b: {BOOL}) -> Int64 = User.show(b)\n  \
         operation go() -> Int64 = run(buf(v: 1))\n",
        provider("P", BOOL, 100),
        user(BOOL)
    );
    assert_unfixed(
        &load_errors_of(&program(ns, &body)),
        ns,
        "show",
        "`User.show(b)`, `b` unrelated to `S`",
    );
}

/// A VALUE WHOSE OWN SORT REQUIRES THE SPEC DOES NOT SAY IT. `Wrap` is a carrier, not a
/// spec; its contract at `w`'s bindings is a goal a provider answers, which was once enough
/// to hold it, and the dep it was asked to cover named no element the call fixed. Loaded
/// before, and died.
#[test]
fn a_value_whose_sort_requires_the_spec_does_not_say_it_either() {
    // Not `wi2kv4y.wrap`: the bare `wrap` below would then name the namespace too.
    let ns = "wi2kv4y.wrapped";
    let body = format!(
        "{}\n  sort Wrap\n    sort K = ?\n    requires Store[State = K]\n    \
         entity wrap(x: K)\n  end\n{}\n  \
         operation run(w: Wrap[K = {BOOL}]) -> Int64 = User.ask()\n  \
         operation go() -> Int64 = run(wrap(buf(v: 1)))\n",
        provider("P", BOOL, 100),
        user(BOOL)
    );
    assert_unfixed(
        &load_errors_of(&program(ns, &body)),
        ns,
        "ask",
        "`User.ask()` beside a `Wrap` whose sort requires `Store`",
    );
}

/// …NOR A VALUE TYPED AT A SPEC, the route's own holder. `Hold requires Store[State = C]`,
/// so an `h: Hold` holds `Store` at ITS carrier — which is not the requirement a call that
/// pins nothing owes. The element the call left open used to be dropped from what `h` was
/// asked to cover, so `h` covered it. Loaded before, and died.
#[test]
fn a_spec_typed_value_does_not_say_it_either() {
    let ns = "wi2kv4y.hold";
    let body = format!(
        "{}\n  sort Hold\n    sort C = ?\n    requires Store[State = C]\n    \
         operation touch(c: C) -> Int64\n  end\n  \
         sort Car\n    entity car(n: Int64)\n    provides Store[State = Car]\n    \
         operation peek(s: Car) -> Int64 = s.n + 7\n    operation zero() -> Int64 = 7\n    \
         provides Hold[C = Car]\n    operation touch(c: Car) -> Int64 = c.n\n  end\n{}\n  \
         operation run(h: Hold) -> Int64 = User.ask()\n  \
         operation go() -> Int64 = run(car(n: 1))\n",
        provider("P", BOOL, 100),
        user(BOOL)
    );
    assert_unfixed(
        &load_errors_of(&program(ns, &body)),
        ns,
        "ask",
        "`User.ask()` beside an `h: Hold`, `Hold` requiring `Store`",
    );
}

/// …NOR ONE TYPED AT THE CALLEE'S OWN SPEC, in either spelling of its binding. `Hold.ask()`
/// fixes nothing of `Hold`'s `C`, and the `h: Hold[C = Buf[…]]` beside it is a `Hold` at a
/// carrier the call never names. This is the shape in which the holder's contract and the
/// requirement are written over ONE parameter: where the holder's binding is not read — a
/// type that holds a value rides as an occurrence — the two sides were that parameter and
/// the cover held. Loaded at both spellings on the parent commit; after the first cut of
/// this change at `value` only.
#[test]
fn a_value_of_the_callees_own_spec_does_not_say_it_either() {
    at_each_spelling(|sp| {
        let ns = format!("wi2kv4y.ownspec_{}", sp.tag);
        let at = sp.call;
        let body = format!(
            "\n  sort Hold\n    sort C = ?\n    requires Store[State = C]\n    \
             operation touch(c: C) -> Int64\n    operation ask() -> Int64 = Store.zero()\n  end\n  \
             sort P\n    provides Store[State = {at}]\n    \
             operation peek(s: {at}) -> Int64 = s.v + 100\n    operation zero() -> Int64 = 100\n    \
             provides Hold[C = {at}]\n    operation touch(c: {at}) -> Int64 = c.v\n  end\n  \
             operation run(h: Hold[C = {at}]) -> Int64 = Hold.ask()\n"
        );
        assert_refused_naming(
            &load_errors_of(&program(&ns, &body)),
            &[
                &format!("`{ns}.Store[State = {ns}.Hold.C]`"),
                &format!("cannot be supplied for call to `{ns}.Hold.ask`"),
                &format!("element `State = {ns}.Hold.C` is unconstrained at this call site"),
            ],
            &format!("`Hold.ask()` beside an `h: Hold[C = …]`, {}", sp.tag),
        );
    });
}

/// THE TWO SPELLINGS OF ONE PROGRAM AGREE. `User.mkS()` owes the sort's requirement with
/// nothing to fix `S`; at `typed` the `b` in scope discharged it and the program answered
/// 31, at `value` it was refused. Both are refused at `mkS()` now.
#[test]
fn a_call_that_fixes_nothing_is_refused_alike_in_both_spellings() {
    at_each_spelling(|sp| {
        let ns = format!("wi2kv4y.mks_{}", sp.tag);
        let body = format!(
            "{}{USER_SORT}\n  operation run(b: {}) -> Int64 = {CHAIN_CALL}\n  \
             operation go() -> Int64 = run(buf(v: 1))\n",
            provider("P", sp.call, 30),
            sp.call
        );
        assert_unfixed(
            &load_errors_of(&program(&ns, &body)),
            &ns,
            "mkS",
            &format!("`User.mkS()` fixing nothing, {}", sp.tag),
        );
    });
}

// ── an open slot of a carrier the call did pin ────────────────────────────────────────

/// `{caller}` over two providers that differ only in `N`; `go()` enters it.
fn open_slot_program(ns: &str, caller: &str, entry: &str) -> String {
    let body = format!(
        "{}{}{}\n  {caller}\n  operation go() -> Int64 = {entry}\n",
        provider("PStr", STRING, 30),
        provider("PBool", BOOL, 40),
        user(BOOL)
    );
    program(ns, &body)
}

/// The refusal of a requirement whose carrier has an open slot two providers fit.
fn assert_tie(errs: &[String], ns: &str, op: &str, why: &str) {
    assert_refused_naming(
        errs,
        &[
            &format!("`{ns}.Store[State = {ns}.Buf[T = anthill.prelude.Int64, N = "),
            &format!("cannot be supplied for call to `{ns}.User.{op}`"),
            &format!("is ambiguous among providers: {ns}.PStr, {ns}.PBool"),
        ],
        why,
    );
}

/// `buf(v: 1)` leaves `N` open; the `c` in scope is not what says it. Loaded before, and
/// died "`__req_store` not bound in caller frame".
#[test]
fn an_open_slot_is_not_filled_by_a_value_in_scope() {
    let ns = "wi2kv4y.slot";
    let src = open_slot_program(
        ns,
        &format!("operation run(c: {BOOL}) -> Int64 = User.go1(buf(v: 1))"),
        "run(buf(v: 9))",
    );
    assert_tie(&load_errors_of(&src), ns, "go1", "an open `N` beside a `c`");
}

/// ITS CONTROL: the same call with no `c`. Passes with or without the change.
#[test]
fn without_the_value_the_open_slot_is_the_same_tie() {
    let ns = "wi2kv4y.slotctl";
    let src = open_slot_program(
        ns,
        "operation run() -> Int64 = User.go1(buf(v: 1))",
        "run()",
    );
    assert_tie(
        &load_errors_of(&src),
        ns,
        "go1",
        "an open `N`, nothing in scope",
    );
}

/// THE SLOT WRITTEN AS A HOLE, `User[S = Buf[T = Int64, N = ?]]`: the same.
#[test]
fn a_hole_in_the_receiver_bracket_is_not_filled_either() {
    let ns = "wi2kv4y.hole";
    let src = open_slot_program(
        ns,
        &format!(
            "operation run(c: {BOOL}) -> Int64 = User[S = Buf[T = Int64, N = ?]].go1(buf(v: 1))"
        ),
        "run(buf(v: 9))",
    );
    assert_tie(
        &load_errors_of(&src),
        ns,
        "go1",
        "a hole for `N` beside a `c`",
    );
}

/// AN OPEN SLOT IS NOT A REFUSAL BY ITSELF: with ONE provider the slot is what that
/// provider says, a dictionary is built, and the call runs it. Passes with or without the
/// change — the control that the three rows above refuse the TIE.
#[test]
fn one_provider_answers_an_open_slot() {
    let ns = "wi2kv4y.one";
    let body = format!(
        "{}{}\n  operation go() -> Int64 = User.go1(buf(v: 1))\n",
        provider("PBool", BOOL, 40),
        user(BOOL)
    );
    assert_eq!(run_int64(&program(ns, &body), &format!("{ns}.go")), Ok(41));
}

/// THE HOLDER ONE OF THE CALL'S OWN ARGUMENTS, the requirement on the OPERATION: the open
/// `N` of `buf(v: 1)` reaches `S` through `mkS()`'s result, and `b` was taken to fill it.
/// Loaded before and raised `AmbiguousRequirement` at run time; the tie is a load refusal.
#[test]
fn a_tie_over_an_open_slot_is_refused_at_load_not_at_run_time() {
    let ns = "wi2kv4y.owntie";
    let body = format!(
        "{}{}\n  sort Tag\n    sort T = ?\n    sort N = ?\n    entity tag\n  end\n  \
         sort User\n    sort S = ?\n    sort U = ?\n    \
         operation mkS() -> Tag[T = S, N = 3] = tag()\n    \
         operation go13(o: Tag[T = U, N = 3], u: U, s: S) -> Int64 requires Store[State = S] \
         = Store.peek(s)\n  end\n  \
         operation run(b: {BOOL}) -> Int64 = User.go13(User.mkS(), buf(v: 1), b)\n  \
         operation go() -> Int64 = run(buf(v: 1))\n",
        provider("PStr", STRING, 30),
        provider("PBool", BOOL, 40),
    );
    assert_tie(
        &load_errors_of(&program(ns, &body)),
        ns,
        "go13",
        "an open `N` reaching an op-level requirement, `b` an argument",
    );
}

// ── a carrier written as its bare sort ────────────────────────────────────────────────

/// `Bag[T]`, whose `empty()` names no `T`, and `User` as above; `providers` follow.
fn bag_program(ns: &str, providers: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Bag
    sort T = ?
    entity bag(n: Int64)
    operation empty() -> Self = bag(n: 1)
  end

  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end

  sort User
    sort S = ?
    requires Store[State = S]
    operation go1(s: S) -> Int64 = Store.peek(s)
  end
{providers}
  operation go() -> Int64 = User.go1(Bag.empty())
end
"#
    )
}

/// A provider of `Store` at every `Bag`.
const AT_BAG: &str = "\n  sort PBag\n    sort E = ?\n    provides Store[State = Bag[T = E]]\n    \
                      operation peek(s: Bag[T = E]) -> Int64 = 7\n  end\n";

/// A DICTIONARY IS BUILT FOR IT. `Bag.empty()` is a result nothing names, so the carrier
/// is the bare `Bag`, which the provision at `Bag[T = E]` does not match as written; asked
/// at the sort's open slots it does, and `go1` reads the slot it is handed: 7. This used
/// to be a discharge — the argument's own type swapped in, nothing built — and `go1` died
/// "`__req_store` not bound in caller frame".
#[test]
fn a_carrier_written_as_its_bare_sort_gets_a_dictionary() {
    let ns = "wi2kv4y.bare";
    assert_eq!(
        run_int64(&bag_program(ns, AT_BAG), &format!("{ns}.go")),
        Ok(7)
    );
}

/// THE CASE THE BARE SPELLING STILL READS ITS OWN WAY, pinned so that it is seen when it
/// moves: beside a provision GENERIC in the carrier, the bare sort is answered by that one
/// as it is written — 55 — where the same carrier with its slot written open reaches the
/// provision at `Bag` (7). The same on the parent commit; `resolve_opening_unwritten_slots`
/// says why it is not closed here, and WI-20261005-SGXYH is the ticket that closes it.
#[test]
fn beside_a_generic_provision_the_bare_spelling_runs_the_generic_one() {
    let ns = "wi2kv4y.baregen";
    let providers = format!(
        "{AT_BAG}\n  sort Gen\n    sort X = ?\n    provides Store[State = X]\n    \
         operation peek(s: X) -> Int64 = 55\n  end\n"
    );
    let bare = bag_program(ns, &providers);
    assert_eq!(run_int64(&bare, &format!("{ns}.go")), Ok(55));
    let open = replace_in_fixture(&bare, BARE_CALL, "User[S = Bag[T = ?]].go1(Bag.empty())");
    assert_eq!(run_int64(&open, &format!("{ns}.go")), Ok(7));
}

/// The call every `bag_program` enters by.
const BARE_CALL: &str = "User.go1(Bag.empty())";

/// A second provider of `Store` at every `Bag`.
const AT_BAG_TOO: &str =
    "\n  sort PBag2\n    sort F = ?\n    provides Store[State = Bag[T = F]]\n    \
                          operation peek(s: Bag[T = F]) -> Int64 = 8\n  end\n";

/// A provider of `Store` at ONE `Bag`.
fn at_bag_of(name: &str, elem: &str, n: i64) -> String {
    format!(
        "\n  sort {name}\n    provides Store[State = Bag[T = {elem}]]\n    \
         operation peek(s: Bag[T = {elem}]) -> Int64 = {n}\n  end\n"
    )
}

/// `look`, with the requirement on the OPERATION, and the call that enters by it.
const LOOK: &str =
    "\n  operation look[K](x: K) -> Int64 requires Store[State = K] = Store.peek(x)\n";
const LOOK_CALL: &str = "look(Bag.empty())";

/// THE OPERATION-LEVEL HALF GETS ITS DICTIONARY TOO: `look[K](x: K) requires Store[State =
/// K]` at a `Bag.empty()`. Died "`__req_store` not bound in caller frame" on the parent
/// commit, the discharge having built nothing.
#[test]
fn an_operation_level_requirement_at_a_bare_carrier_gets_a_dictionary() {
    let ns = "wi2kv4y.bareop";
    let src = replace_in_fixture(
        &bag_program(ns, &format!("{AT_BAG}{LOOK}")),
        BARE_CALL,
        LOOK_CALL,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7));
}

/// TWO PROVISIONS GENERIC IN THE SLOT ARE A TIE, named as one, on both halves. On the parent
/// commit — and with only a construction taken from the second asking — the refusal is the
/// goal's as written, "no row of it answers at these bindings", which names no rival.
#[test]
fn two_provisions_generic_in_the_slot_are_a_tie() {
    for (half, call, extra) in [("sort", BARE_CALL, ""), ("op", LOOK_CALL, LOOK)] {
        let ns = format!("wi2kv4y.baretie_{half}");
        let src = replace_in_fixture(
            &bag_program(&ns, &format!("{AT_BAG}{AT_BAG_TOO}{extra}")),
            BARE_CALL,
            call,
        );
        assert_refused_naming(
            &load_errors_of(&src),
            &[
                &format!("`{ns}.Store[State = {ns}.Bag]`"),
                &format!(
                    "constructing `{ns}.Store[State = {ns}.Bag[T = ?]]` is ambiguous among \
                     providers: {ns}.PBag, {ns}.PBag2"
                ),
            ],
            &format!("two providers at every `Bag`, the {half}-level requirement"),
        );
    }
}

/// THE OPEN SLOT IS A VARIABLE, so a provision at ONE instance does not answer it: beside
/// `provides Store[State = Bag[T = Int64]]` alone the call is refused as the goal as written
/// is, and beside two such it is the same refusal and not a tie. The same on the parent
/// commit, and unlike a slot an argument's own type leaves undetermined, which one
/// provision at an instance does answer ([`one_provider_answers_an_open_slot`]) —
/// WI-20261005-SGXYH. Pinned so that it is seen when it moves.
#[test]
fn a_provision_at_one_instance_does_not_answer_a_bare_carrier() {
    for (which, providers) in [
        ("one", at_bag_of("PInt", "Int64", 9)),
        (
            "two",
            format!(
                "{}{}",
                at_bag_of("PInt", "Int64", 9),
                at_bag_of("PStr", "String", 5)
            ),
        ),
    ] {
        let ns = format!("wi2kv4y.bareinst_{which}");
        let errs = load_errors_of(&bag_program(&ns, &providers));
        assert_refused_naming(
            &errs,
            &[
                &format!("`{ns}.Store[State = {ns}.Bag]`"),
                &format!(
                    "`{ns}.Bag` does provide `{ns}.Store`, but no row of it answers at these bindings"
                ),
            ],
            &format!("{which} provision at an instance of `Bag`"),
        );
        assert!(
            !errs.join(" | ").contains("ambiguous among providers"),
            "{which}: a provision at an instance is not a rival for an open slot, got {errs:#?}"
        );
    }
}

/// A CYCLE AT THE OPEN SLOTS LEAVES THE REFUSAL OF THE GOAL AS WRITTEN. Two conditional
/// provisions that need each other: asked at the open slot the construction is cyclic, and
/// the operation half reads a cycle as a slot to leave absent. Taken as the answer it made
/// this program load and die "`__req_store` not bound in caller frame"; the parent commit
/// refuses it, as this does.
#[test]
fn a_cycle_at_the_open_slots_is_refused_at_load() {
    let ns = "wi2kv4y.barecycle";
    let providers = format!(
        "\n  sort Aux\n    sort T = ?\n    operation aux(x: T) -> Int64\n  end\n  \
         sort AuxOfBag\n    sort Y = ?\n    requires Store[State = Bag[T = Y]]\n    \
         provides Aux[T = Y]\n    operation aux(x: Y) -> Int64 = 2\n  end\n  \
         sort PBag\n    sort E = ?\n    requires Aux[T = E]\n    \
         provides Store[State = Bag[T = E]]\n    \
         operation peek(s: Bag[T = E]) -> Int64 = 7\n  end\n{LOOK}"
    );
    let src = replace_in_fixture(&bag_program(ns, &providers), BARE_CALL, LOOK_CALL);
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            &format!("`{ns}.Store[State = {ns}.Bag]` cannot be supplied for call to `{ns}.look`"),
            &format!(
                "`{ns}.Bag` does provide `{ns}.Store`, but no row of it answers at these bindings"
            ),
        ],
        "a cyclic pair of conditional provisions at a bare carrier",
    );
}

/// A SORT THE LOADER HAS ALREADY REFUSED IS NOT OPENED. The dotted `sort Inner.T = ?` of a
/// secondary entry leaves `Rec` a declared parameter with no variable; expanding `Rec` on
/// the way to its refusal asserted (WI-954), and the load panicked instead of reporting its
/// two errors. The parent commit reports them, as this does.
#[test]
fn a_sort_the_loader_has_refused_is_not_opened() {
    let ns = "wi2kv4y.dotted";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort Rec
    entity rec(n: Int64)
  end
  namespace Rec
    sort Inner.T = ?
  end
  sort Caller
    sort T = ?
    requires Show[T = T]
    operation useIt(x: T) -> Int64 = show(x)
  end
  operation go() -> Int64 = Caller.useIt(rec(n: 7))
end
"#
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            "`sort` 'Inner.T' is not allowed in a secondary entry",
            &format!("`{ns}.Show[T = {ns}.Rec]` of `{ns}.Caller` cannot be supplied"),
        ],
        "a requirement at a sort with a dotted parameter",
    );
}

/// EVERY ELEMENT IS READ SO, not the one an operation receives on. `User requires Conv[From
/// = S, To = U]` and `User.go2(1, Bag.empty())`: the bare `Bag` is `To`, and `conv` receives
/// on whichever of `From` and `To` the spec declares first. Opening only that one made the
/// verdict follow the declaration order — refused with `From` first, 7 with `To` first. On
/// the parent commit it was refused, and loaded and died.
#[test]
fn a_bare_sort_is_opened_in_whichever_element_it_stands() {
    for (order, declared) in [
        ("from_first", "sort From = ?\n    sort To = ?"),
        ("to_first", "sort To = ?\n    sort From = ?"),
    ] {
        let ns = format!("wi2kv4y.bareelem_{order}");
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Bag
    sort T = ?
    entity bag(n: Int64)
    operation empty() -> Self = bag(n: 1)
  end
  sort Conv
    {declared}
    operation conv(x: From, y: To) -> Int64
  end
  sort PConv
    sort E = ?
    provides Conv[From = Int64, To = Bag[T = E]]
    operation conv(x: Int64, y: Bag[T = E]) -> Int64 = 7
  end
  sort User
    sort S = ?
    sort U = ?
    requires Conv[From = S, To = U]
    operation go2(s: S, u: U) -> Int64 = Conv.conv(s, u)
  end
  operation go() -> Int64 = User.go2(1, Bag.empty())
end
"#
        );
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7), "{order}");
    }
}

/// A NAMED SLOT AT A BARE CARRIER TAKES THE DEFAULT, as its open-slot spelling does. `Keyed
/// requires O: Ord2[T]`; `Bag` provides `Ord2` for itself and `Rev` is a rival witness; `one`
/// READS the slot. The inference that writes the slot's provider into the type asks as the
/// dictionary build does, so the carrier's own provision is chosen: 1. Asking the goal as
/// written it bound nothing, and the build met the opened goal with the default withheld — a
/// tie. On the parent commit the bare spelling loaded and died "`__req_ord2` not bound".
#[test]
fn a_named_slot_at_a_bare_carrier_takes_the_default() {
    let ns = "wi2kv4y.barenamed";
    let bare = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Ord2
    sort T = ?
    operation cmp(a: T, b: T) -> Int64
  end
  sort Bag
    sort T = ?
    entity bag(n: Int64)
    operation empty() -> Self = bag(n: 1)
    provides Ord2[T = Self]
    operation cmp(a: Self, b: Self) -> Int64 = 1
  end
  sort Rev
    sort E = ?
    provides Ord2[T = Bag[T = E]]
    operation cmp(a: Bag[T = E], b: Bag[T = E]) -> Int64 = 2
  end
  sort Keyed
    sort T = ?
    requires O: Ord2[T]
    operation one(x: T) -> Int64 = Ord2.cmp(x, x)
  end
  operation go() -> Int64 = Keyed.one(Bag.empty())
end
"#
    );
    let entry = format!("{ns}.go");
    assert_eq!(run_int64(&bare, &entry), Ok(1), "the bare spelling");
    // The two controls, which pass with or without the change: the slot written open, and
    // the rival selected.
    let open = replace_in_fixture(&bare, "Keyed.one(", "Keyed[T = Bag[T = ?]].one(");
    assert_eq!(run_int64(&open, &entry), Ok(1), "the slot written open");
    let selected = replace_in_fixture(&bare, "Keyed.one(", "Keyed[T = Bag[T = ?], O = Rev].one(");
    assert_eq!(run_int64(&selected, &entry), Ok(2), "the rival selected");
}

// ── a requirement the call pinned is still held ───────────────────────────────────────

/// AN OPERATION'S OWN REQUIREMENT, PINNED BY ITS ARGUMENT, IS SUPPLIED THROUGH THE CALLER'S:
/// `w: Tagger.C` requires `Tagger` of `w`'s sort, and `Tagger requires Tag[T = C]`, so
/// `tag2(w)` owes `Tag` at that sort and the caller's own dictionary has it. 2, `B`'s tag —
/// the control for a cover that refuses too much.
#[test]
fn an_operations_own_requirement_is_supplied_through_the_callers() {
    let src = r#"
namespace wi2kv4y.opslot
  import anthill.prelude.{Int64}
  sort Tag
    sort T = ?
    operation tagOf(x: T) -> Int64
  end
  sort Tagger
    sort C = ?
    requires Tag[T = C]
    operation probe(x: C) -> Int64
  end
  sort B
    entity b(k: Int64)
    provides Tag[T = B]
    operation tagOf(x: B) -> Int64 = 2
    provides Tagger[C = B]
    operation probe(x: B) -> Int64 = 7
  end
  operation tag2[K](x: K) -> Int64 requires Tag[T = K] = Tag.tagOf(x)
  operation outside(w: Tagger.C) -> Int64 = tag2(w)
  operation go() -> Int64 = outside(b(k: 0))
end
"#;
    assert_eq!(run_int64(src, "wi2kv4y.opslot.go"), Ok(2));
}

/// THE HEADLINE SHAPE, DRIVEN: `size(c)` owes `FiniteCollection`'s `Iterable[…]` at the sort
/// `c` is a value of, and the dictionary `total` is handed for its own requirement has it —
/// over a list, and over a mapped stream.
#[test]
fn a_specs_own_operation_on_a_value_of_any_provider_runs() {
    let src = r#"
namespace wi2kv4y.own
  import anthill.prelude.{List, Int64, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}
  operation total(c: FiniteCollection.C) -> Int64 effects FiniteCollection.E = size(c)
  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation over_a_list() -> Int64 = total(rows())
  operation over_a_mapped_stream() -> Int64 = total(rows().map(lambda n -> n * 2))
end
"#;
    assert_eq!(run_int64(src, "wi2kv4y.own.over_a_list"), Ok(4));
    assert_eq!(run_int64(src, "wi2kv4y.own.over_a_mapped_stream"), Ok(4));
}

// ── a held requirement does not end the judging of the chain ──────────────────────────

/// `User` under two requirements, declared `first` then `second`: `both(x: K)` fixes `K`,
/// nothing fixes `S`, and `outside` passes a `w: Tagger.C`, whose `Tagger` supplies `Tag` at
/// its sort.
fn two_requirements_program(ns: &str, first: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Tag
    sort T = ?
    operation tagOf(x: T) -> Int64
  end
  sort Store
    sort State = ?
    operation zero() -> Int64
  end
  sort Tagger
    sort C = ?
    requires Tag[T = C]
    operation probe(x: C) -> Int64
  end
  sort B
    entity b(k: Int64)
    provides Tag[T = B]
    operation tagOf(x: B) -> Int64 = 2
    provides Tagger[C = B]
    operation probe(x: B) -> Int64 = 7
    provides Store[State = B]
    operation zero() -> Int64 = 100
  end
  sort User
    sort K = ?
    sort S = ?
    requires {first}
    requires {second}
    operation both(x: K) -> Int64 = Store.zero()
  end
  operation outside(w: Tagger.C) -> Int64 = User.both(w)
  operation go() -> Int64 = outside(b(k: 0))
end
"#
    )
}

const TAG_AT_K: &str = "Tag[T = K]";
const STORE_AT_S: &str = "Store[State = S]";

/// The refusal of `User.both(w)` over the `S` nothing fixes.
fn assert_store_is_owed(ns: &str, first: &str, second: &str, why: &str) {
    assert_refused_naming(
        &load_errors_of(&two_requirements_program(ns, first, second)),
        &[
            &format!("`{ns}.Store[State = {ns}.User.S]`"),
            &format!("cannot be supplied for call to `{ns}.User.both`"),
            &format!("element `State = {ns}.User.S` is unconstrained at this call site"),
        ],
        why,
    );
}

/// A REQUIREMENT DECLARED AFTER A HELD ONE IS STILL OWED. `w`'s `Tagger` supplies `Tag[T =
/// K]`, and the
/// first held requirement used to end the judging of the chain: `Store` was never asked, the
/// program loaded, and `both` died "`__req_store` not bound in caller frame". The same on
/// the parent commit.
#[test]
fn a_requirement_declared_after_a_held_one_is_still_owed() {
    assert_store_is_owed(
        "wi2kv4y.heldfirst",
        TAG_AT_K,
        STORE_AT_S,
        "`Store` declared after the `Tag` that `w` holds",
    );
}

/// ITS CONTROL: the two clauses in the other order, where `Store` is asked first. Passes
/// with or without the change.
#[test]
fn declared_before_the_held_one_it_is_refused_the_same_way() {
    assert_store_is_owed(
        "wi2kv4y.heldlast",
        STORE_AT_S,
        TAG_AT_K,
        "`Store` declared before the `Tag` that `w` holds",
    );
}

// ── the population the unfixed-carrier discharge served ───────────────────────────────

/// A mapped stream over any iterable source: the field holds a value of the sort's own
/// `Source`, and the sort requires `Iterable` of it. Where `unfixed`, `map` is a factory —
/// it takes `s: Sc` and returns another instance, so nothing at a call to it fixes the
/// sort's own `Source`; otherwise it receives on `Source`, and the call fixes it.
fn factory_program(ns: &str, unfixed: bool) -> String {
    let map = if unfixed {
        "    operation map[Sc, S, Dst, EffS, EffP](s: Sc, f: (x: S) -> Dst @ {EffP, -Modify[x]})\n      \
         -> MS[Source = Sc, Src = S, T = Dst, ES = EffS, EF = EffP]\n      \
         requires Iterable[C = Sc, Element = S, E = EffS] =\n      mapped(s, f)\n"
    } else {
        "    operation map[Dst, EffP](s: Source, f: (x: Src) -> Dst @ {EffP, -Modify[x]})\n      \
         -> MS[Source = Source, Src = Src, T = Dst, ES = ES, EF = EffP] =\n      mapped(s, f)\n"
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, Option, Pair, Stream, Iterable, Function, Modify}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort MS
    import anthill.prelude.{{Stream, Iterable, Function, Option, Pair, Modify}}
    import anthill.prelude.Option.{{some, none}}
    import anthill.prelude.Pair.{{pair}}
    sort Source = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    requires Iterable[C = Source, Element = Src, E = ES]
    entity mapped(source: Source, fn: (Src) -> T @ {{EF}})
    provides Stream[T = T, E = {{ES, EF}}]
    operation splitFirst(m: Self) -> Option[Pair[A = T, B = Stream[T = T, E = {{ES, EF}}]]] effects {{ES, EF}} =
      match m
        case mapped(src, fn) ->
          match Stream.splitFirst(Iterable.iterator(src))
            case none() -> none
            case some(pair(h, rest)) -> some(pair(fn(h), mapped(rest, fn)))
{map}  end

  operation sum(s: Stream[T = Int64]) -> Int64 effects s.E =
    match Stream.splitFirst(s)
      case none() -> 0
      case some(pair(h, rest)) -> h + sum(rest)

  operation go() -> Int64 = sum(MS.map([1, 2, 3], lambda n -> n * 2))
end
"#
    )
}

/// THE SHAPE THE STANDARD LIBRARY HAD. The sort declares a requirement over `Source`; the
/// factory never fixes `Source`; so the call owes it with every element open. It loaded on
/// the list argument's type, and is refused now naming the three elements.
#[test]
fn a_factory_that_leaves_its_sorts_requirement_unfixed_is_refused() {
    let ns = "wi2kv4y.factory";
    assert_refused_naming(
        &load_errors_of(&factory_program(ns, true)),
        &[
            &format!(
                "`anthill.prelude.Iterable[C = {ns}.MS.Source, Element = {ns}.MS.Src, E = {ns}.MS.ES]`"
            ),
            &format!("of `{ns}.MS` cannot be supplied for call to `{ns}.MS.map`"),
            "is unconstrained at this call site",
        ],
        "a factory under a sort-level requirement it does not fix",
    );
}

/// THE REPAIR THE STANDARD LIBRARY HAS NOW: `map` receives on the sort's own `Source`, so
/// its argument fixes it, the sort's requirement is asked at the list's own provision, and
/// the same program walks the stream. (The repair this ticket took was to delete the
/// clause: the field was typed `Iterable[C = Source, …]` and its type was what said the
/// source is iterable. A value of a sort that provides `Iterable` is not an `Iterable` —
/// WI-20261005-KSSA4 — so the field holds a `Source` and the clause is what says it.)
/// `MappedStream.map` over a bare list is driven on the library itself by `wi599
/// …the_stdlib_combinators_are_general_over_any_iterable_source`.
#[test]
fn a_factory_receiving_on_the_sorts_own_source_runs() {
    let ns = "wi2kv4y.factoryok";
    assert_eq!(
        run_int64(&factory_program(ns, false), &format!("{ns}.go")),
        Ok(12)
    );
}
