//! WI-20260929-JN09W — a value in scope does not stand in for the carrier a call pinned.
//!
//! A requirement nothing can build is still met when a value in scope HOLDS it (§8.7's
//! route (2); `scope_contract_covers_dep`). One leg of that route swapped a holder's TYPE
//! in for the requirement's carrier and asked the provider facts; where the call had PINNED
//! the carrier, it swapped in any holder of the pinned carrier's SORT. MEASURED on this
//! ticket's parent commit, in both spellings of `Buf`'s `N` unless one is named:
//!
//! * A HOLDER AT ANOTHER BINDING. `User requires Store[State = S]`, `go1(s: S) =
//!   Store.peek(s)`, and `run(b: Buf[T = Int64, N = Bool], c: Buf[T = String, N = Bool]) =
//!   User.go1(b)`, providers at another `N` and at `c`'s type: `c` is a `Buf`, its type was
//!   swapped in, its provider answered, and the requirement at `b`'s type was taken as held.
//!   The program LOADED — and, run at `typed`, died "`__req_store` not bound in caller
//!   frame"; without `c` it was refused.
//! * AN ARGUMENT THAT SAYS LESS. `sort U { requires Store[State = Buf[T = Int64, N = Bool]];
//!   operation use(s: Buf[T = Int64, N = Bool]) -> Int64 = Store.peek(s) }`, no provider at
//!   that `N`, called `U.use(buf(v: 1))`: the argument's own type leaves `N` open, so swapped
//!   in it matched a provider at another `N`. It loaded; the ticket's own program of this
//!   shape died the same way.
//! * THROUGH A TWO-LINK CHAIN — WI-20260929-PFAGY's program: the requirement on the sort,
//!   `go13(mkS(), b, b)`, the holder `c` beside it. Read one link, the requirement named no
//!   `Buf`: at `value` its carrier was then dropped as unpinned and `c` answered (loaded,
//!   died the same way), and at `typed` it was refused naming `Store[State = User.S]`. Read
//!   to the chain's end (WI-20260929-020TH) it pins `b`'s type.
//!
//! This ticket held the swap to a REFINEMENT — the holder's type had to say every argument
//! the pin states. WI-20261005-2KV4Y then deleted the leg: a slot the pin left open was
//! still filled by any holder, and a carrier the call did not pin at all by any value. The
//! one thing the swap was FOR — a carrier written as its bare sort, the type of a result
//! nothing has named — is construction's to answer, and it does: a sort written with slots
//! left out is asked at its open slots and a dictionary is built
//! (`resolve_opening_unwritten_slots`). No value's type stands in for a carrier any more.
//!
//! A refusal row asserts a LOAD verdict naming the requirement at the binding the call pinned
//! — nothing there can run, the requirement having no provider — and fails naming every
//! spelling it failed at. The two bare-carrier rows run.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ───────────────────────────────
//!
//! RE-MEASURED with WI-20261005-2KV4Y: each part of the code as it now stands backed out
//! present-but-wrong, APPLIED AND RUN over this file's 8 rows. A row named without a
//! spelling fails at both.
//!
//! 1. THE BARE CARRIER NOT OPENED (`resolve_opening_unwritten_slots` answering the goal as
//!    written). 2 FAIL, each refused at load:
//!    [`an_unnamed_result_pins_the_bare_sort_and_gets_a_dictionary`] and
//!    [`an_unnamed_stack_is_measured`].
//! 2. THE CHAIN-END READ of WI-20260929-020TH (`spec_param_binding`, then
//!    `spec_param_binding_term`, on its parent commit's read). 2 FAIL, the two chain rows: the op-level one loads clean, and the
//!    sort-level one is refused at `User.mkS()` and at `User.go13`, each naming
//!    `Store[State = User.S]` — a requirement that names no `Buf`.
//!
//! [`a_holder_at_another_binding_discharges_nothing`] and
//! [`an_argument_that_says_less_discharges_nothing`] FAIL UNDER NEITHER, and under no other
//! part of today's code: there is no swap left to back out. Their measurement is this
//! ticket's own — on its parent commit each was "expected a refusal, got a clean load" —
//! and what they guard is a value's type being put in a pinned carrier's place again.
//!
//! PASS UNDER EVERY ONE, by design: [`with_no_buf_at_the_call_it_is_refused_the_same_way`]
//! (no `Buf` to offer) and [`without_the_holder_the_call_is_refused_the_same_way`] (the only
//! `Buf` on offer is the pinned type itself).

use crate::common::{
    assert_refused_naming, interp_for, load_errors_of, register_modify_handler, run_int64,
};
use crate::wi_020th_two_hop_chain_test::{
    at_each_spelling, program as chain_program, shown_requirement, Spelling, CHAIN_CALL,
    USER_ONE_SORT, USER_OP, USER_SORT,
};
use crate::wi_wbhtm_value_in_type_call_test::provider;
use anthill_core::kb::term_view::TermView;

/// The holder's type: a `Buf`, at another binding than every call below.
const HOLDER: &str = "Buf[T = String, N = Bool]";

/// `wi_020th_two_hop_chain_test`'s `Buf` / `Store` program, with a provider `P2` at the
/// holder's type; `body` follows.
fn program(ns: &str, body: &str) -> String {
    chain_program(
        ns,
        &format!(
            "\n  sort P2\n    provides Store[State = {HOLDER}]\n    \
             operation peek(s: {HOLDER}) -> Int64 = 40\n  end\n{body}"
        ),
    )
}

/// `run({params}) = {call}`, entered by `go()` — with the holder `c` when `holder`.
fn run(sp: &Spelling, holder: bool, call: &str) -> String {
    let (params, args) = if holder {
        (
            format!("b: {}, c: {HOLDER}", sp.call),
            "buf(v: 1), buf(v: \"x\")",
        )
    } else {
        (format!("b: {}", sp.call), "buf(v: 1)")
    };
    format!(
        "\n  operation run({params}) -> Int64 = {call}\n  \
         operation go() -> Int64 = run({args})\n"
    )
}

// ── a holder at another binding ───────────────────────────────────────────────────────

/// `User requires Store[State = S]`, `go1(s: S) = Store.peek(s)`, called `User.go1(b)`; the
/// one provider beside `P2` is at another binding than `b`'s.
fn one_link(ns: &str, sp: &Spelling, holder: bool) -> Vec<String> {
    let body = format!(
        "{}{USER_ONE_SORT}{}",
        provider("P1", sp.other, 30),
        run(sp, holder, "User.go1(b)")
    );
    load_errors_of(&program(ns, &body))
}

/// THE TICKET'S SECOND PROGRAM: `c` is a `Buf` at another binding and discharges nothing.
#[test]
fn a_holder_at_another_binding_discharges_nothing() {
    at_each_spelling(|sp| {
        let ns = format!("wijn09w.held_{}", sp.tag);
        assert_refused_naming(
            &one_link(&ns, sp, true),
            &[
                &shown_requirement(&ns, sp),
                &format!("of `{ns}.User` cannot be supplied for call to `{ns}.User.go1`"),
            ],
            &format!("a holder at another binding, {}", sp.tag),
        );
    });
}

/// ITS TWIN WITHOUT `c`, refused with the same words. Passes either way by design: the only
/// `Buf` on offer is the argument `b`, whose type is the pin itself.
#[test]
fn without_the_holder_the_call_is_refused_the_same_way() {
    at_each_spelling(|sp| {
        let ns = format!("wijn09w.bare_{}", sp.tag);
        assert_refused_naming(
            &one_link(&ns, sp, false),
            &[
                &shown_requirement(&ns, sp),
                &format!("of `{ns}.User` cannot be supplied for call to `{ns}.User.go1`"),
            ],
            &format!("no holder, {}", sp.tag),
        );
    });
}

// ── an argument that says less ────────────────────────────────────────────────────────

/// `U requires Store` at the spelling's own binding, the one provider beside `P2` at another,
/// and `use({param})` calls `Store.peek` on `{arg}`.
fn fixed_requirement(ns: &str, sp: &Spelling, param: &str, arg: &str, call: &str) -> Vec<String> {
    let body = format!(
        "{}\n  sort U\n    requires Store[State = {req}]\n    \
         operation use({param}) -> Int64 = Store.peek({arg})\n  end\n  \
         operation go() -> Int64 = {call}\n",
        provider("P1", sp.other, 30),
        req = sp.call,
    );
    load_errors_of(&program(ns, &body))
}

/// THE TICKET'S FIRST PROGRAM: the argument `buf(v: 1)` leaves `N` open, so its type does
/// not say the requirement's `N` and discharges nothing.
#[test]
fn an_argument_that_says_less_discharges_nothing() {
    at_each_spelling(|sp| {
        let ns = format!("wijn09w.less_{}", sp.tag);
        assert_refused_naming(
            &fixed_requirement(&ns, sp, &format!("s: {}", sp.call), "s", "U.use(buf(v: 1))"),
            &[
                &shown_requirement(&ns, sp),
                &format!("of `{ns}.U` cannot be supplied for call to `{ns}.U.use`"),
            ],
            &format!("an argument whose type leaves `N` open, {}", sp.tag),
        );
    });
}

/// ITS TWIN WITH AN `Int64` PARAMETER — no `Buf` reaches the call — refused with the same
/// words. Passes either way by design.
#[test]
fn with_no_buf_at_the_call_it_is_refused_the_same_way() {
    at_each_spelling(|sp| {
        let ns = format!("wijn09w.int_{}", sp.tag);
        assert_refused_naming(
            &fixed_requirement(&ns, sp, "n: Int64", "buf(v: n)", "U.use(1)"),
            &[
                &shown_requirement(&ns, sp),
                &format!("of `{ns}.U` cannot be supplied for call to `{ns}.U.use`"),
            ],
            &format!("an `Int64` parameter, {}", sp.tag),
        );
    });
}

// ── through a two-link chain ──────────────────────────────────────────────────────────

/// WI-20260929-PFAGY's PROGRAM, both spellings: the requirement on the SORT, reached
/// through `go13(mkS(), b, b)`'s chain, with the holder `c` in scope.
#[test]
fn a_sort_level_requirement_through_the_chain_is_not_held_by_another_buf() {
    at_each_spelling(|sp| {
        let ns = format!("wijn09w.chain_sort_{}", sp.tag);
        let body = format!(
            "{}{USER_SORT}{}",
            provider("P1", sp.other, 30),
            run(sp, true, CHAIN_CALL)
        );
        assert_refused_naming(
            &load_errors_of(&program(&ns, &body)),
            &[
                &shown_requirement(&ns, sp),
                &format!("of `{ns}.User` cannot be supplied for call to `{ns}.User.go13`"),
            ],
            &format!("a sort-level requirement through the chain, {}", sp.tag),
        );
    });
}

/// THE SAME WITH THE REQUIREMENT ON THE OPERATION — WI-20260929-020TH's program with the
/// holder beside it.
#[test]
fn an_operation_level_requirement_through_the_chain_is_not_held_by_another_buf() {
    at_each_spelling(|sp| {
        let ns = format!("wijn09w.chain_op_{}", sp.tag);
        let body = format!(
            "{}{USER_OP}{}",
            provider("P1", sp.other, 30),
            run(sp, true, CHAIN_CALL)
        );
        assert_refused_naming(
            &load_errors_of(&program(&ns, &body)),
            &[
                &shown_requirement(&ns, sp),
                &format!("cannot be supplied for call to `{ns}.User.go13`"),
            ],
            &format!("an op-level requirement through the chain, {}", sp.tag),
        );
    });
}

// ── a carrier written as its bare sort ────────────────────────────────────────────────

/// A RESULT NOTHING NAMES keeps its slots open, so `size(PBag.empty())` pins the carrier as
/// the BARE sort — which no provision is written at. Asked at the sort's open slots, the
/// requirement is the one `PBag`'s own provision answers: a dictionary is built, and the
/// call answers 0.
#[test]
fn an_unnamed_result_pins_the_bare_sort_and_gets_a_dictionary() {
    let src = r#"
namespace wijn09w.bag
  import anthill.prelude.{List, Int64}
  import anthill.prelude.FiniteCollection.{size}

  sort PBag
    import anthill.prelude.{List, Stream, Iterable, FiniteCollection}
    import anthill.prelude.List.{nil}
    sort T = ?
    entity pbag(items: List[T = T])
    operation empty() -> Self = pbag(items: nil())
    operation iterator(b: Self) -> Stream[T, {}] = b.items
    provides Iterable[C = PBag[T], Element = T, E = {}]
    operation collect(b: Self) -> List[T = b.T] = b.items
    provides FiniteCollection[C = PBag[T], Element = T, E = {}]
  end

  operation go() -> Int64 = size(PBag.empty())
end
"#;
    assert_eq!(run_int64(src, "wijn09w.bag.go"), Ok(0));
}

/// THE SAME ON THE STANDARD LIBRARY'S OWN CARRIER: `size(MutableStack.new())` answers 0.
#[test]
fn an_unnamed_stack_is_measured() {
    let mut interp = interp_for(
        r#"
namespace wijn09w.stack
  import anthill.prelude.{Int64, MutableStack}
  import anthill.prelude.FiniteCollection.{size}

  operation go() -> Int64 effects Modify[result] = size(MutableStack.new())
end
"#,
    );
    register_modify_handler(&mut interp);
    let r = interp
        .call("wijn09w.stack.go", &[])
        .unwrap_or_else(|e| panic!("`size(MutableStack.new())` must run: {e:?}"));
    assert_eq!(r.literal_int64(interp.kb()), Some(0));
}
