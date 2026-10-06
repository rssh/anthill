//! WI-20260929-020TH — a spec parameter's binding is read through σ, and the same way on
//! every carrier.
//!
//! THE TICKET'S PROGRAM. `sort User { sort S = ?; sort U = ?; operation mkS() -> Option[T = S]
//! = none(); operation go13(o: Option[T = U], u: U, s: S) -> Int64 requires Store[State = S] =
//! Store.peek(s) }`, called `User.go13(User.mkS(), b, b)`. `mkS()`'s result names `S` unbound,
//! so the first argument binds `S` to `U`, and the second binds `U` to `b`'s type: σ holds
//! `S ↦ U ↦ Buf[…]`. The reader every dispatch question takes a spec parameter's binding from
//! (`spec_param_binding`, then `spec_param_binding_term`) read ONE link, met the variable `U`, and reported `S` as bound
//! to a variable — abstract. MEASURED on the parent commit, in both spellings of `Buf`'s `N`
//! (a type, and a value held in the type) unless one is named:
//!
//! * THE OPERATION'S OWN REQUIREMENT stayed `Store[State = User.S]`, nothing could build it,
//!   and an op-scoped slot nothing builds is left out in silence. The program LOADED, the
//!   callee was entered without the slot, and eval filled it from the argument's value, which
//!   cannot see `N`: the one provider, at another `N`, ran (31). With two providers the load
//!   was clean too and the run raised `AmbiguousRequirement`.
//! * THE SORT'S REQUIREMENT stayed abstract the same way and was refused naming
//!   `Store[State = User.S]`.
//! * THE SAME TWO LINKS WITHIN ONE CALL, a hole in a bracket. `User[S = ?].go1(b)` binds `S`
//!   to the hole's variable and the argument binds that: the op-level requirement was left
//!   out the same way, and the sort-level one refused a correct program. `Store.peek[State =
//!   ?](s)` puts the links on the spec's own parameter: the dispatch goal kept the hole, the
//!   provider at `Buf[T = Int64]` was refused on it, and the generic `Gen` ran (55); where
//!   nothing generic provides, the missing-`requires` walk read the hole abstract and refused
//!   the call — under a sort's `requires Store[State = …]`, at the call's own binding or at
//!   another sort, as much as with no provider at all.
//! * A VARIABLE INSIDE THE BINDING was resolved or not by the carrier the binding rode:
//!   `Store.peek[State = Buf[T = ?, N = Bool]](s)`, a term, ran `Gen` (55), where its
//!   value-in-type twin, an occurrence, reached the specific provider.
//!
//! The reader now resolves the binding through σ whichever carrier it rides: read at the END
//! of σ's chain of variable links (`sigma_chain_end`), the variables inside what the chain
//! ends at resolved too, and a chain that comes back on itself ended at one of its variables.
//!
//! Every row DRIVES what it claims: a call runs to a value naming the provider it reached
//! (each answers `v` plus its own offset), or a refusal names the requirement at the binding
//! the chain ends at. A row at both spellings fails naming every spelling it failed at.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ───────────────────────────────
//!
//! EACH PART backed out present-but-wrong, APPLIED AND RUN over this file's 14 rows,
//! `wi_jn09w_holder_gate_test`'s 8 and the reader's unit rows
//! (`kb::typing::tests::sigma_chain_end_tests`, whose own ledger is at their site). A row
//! named without a spelling fails at both.
//!
//! 1. THE WHOLE READ — the parent commit's: one link, a term as σ stored it, any other
//!    carrier resolved. 11 FAIL here, every row but the three named below, with
//!    [`a_hole_inside_the_bracket_reaches_the_specific_provider`] at `typed` alone; and the
//!    two chain rows of `wi_jn09w_holder_gate_test`.
//! 2. ONE READER on that read, the others on the new one:
//!    * a callee's requirement (`resolve_var_value_via_subst`, the supply's two halves) — 5:
//!      [`an_operation_level_requirement_over_the_chain_is_refused_at_load`],
//!      [`the_chain_reaches_the_provider_at_the_calls_own_binding`],
//!      [`a_sort_level_requirement_over_the_chain_names_what_it_ends_at`],
//!      [`a_hole_on_the_receiver_leaves_the_sort_level_requirement_suppliable`],
//!      [`a_hole_on_the_receiver_does_not_hide_the_binding_from_an_operation_level_requirement`];
//!      and the two chain rows of `wi_jn09w_holder_gate_test`;
//!    * the dispatch goal and the op-scoped licence (`spec_param_bindings`, their one walk) —
//!      4: [`a_bracket_that_is_a_hole_reaches_the_specific_provider`] (55),
//!      [`a_hole_inside_the_bracket_reaches_the_specific_provider`] at `typed` (55), and
//!      [`a_holed_call_is_not_licensed_by_a_requirement_over_another_element`] and
//!      [`a_holed_call_with_no_provider_names_the_carrier`], each then a CLEAN LOAD;
//!    * the defer-match (`entry_type_param_bindings`) — 1:
//!      [`a_holed_call_defers_to_a_requirement_at_its_own_binding`], which loads and fails
//!      at run time on the two providers;
//!    * the missing-`requires` walk — none. What it alone decides is under NOT COVERED.
//!
//!    [`a_holed_call_does_not_defer_to_a_requirement_at_another_sort`] fails under 1 and
//!    under no single reader.
//! 3. THE CHAIN FOLLOWED, AND A TERM AT ITS END HANDED OVER AS σ STORED IT. 2 FAIL, each
//!    answering `Gen`'s 55: [`a_hole_inside_the_bracket_reaches_the_specific_provider`] at
//!    `typed`, and [`a_term_reached_through_a_lambda_binder_is_resolved_inside`] — which the
//!    parent commit passes, a link on the value carrier having been resolved in full.
//!
//! PASS UNDER EVERY BACK-OUT, by design: [`the_provider_at_the_calls_binding_runs`] (eval
//! reached the same provider from the argument's value) and
//! [`the_one_link_twin_is_refused_with_the_same_words`] (no chain).
//!
//! NOT COVERED HERE, and why:
//! * A HOLED CALL AT A BINDING NO PROVIDER COVERS — `use(s: Buf[T = Int64, N = Bool]) =
//!   Store.peek[State = ?](s)`, the one provider at `N = String` — was refused "missing
//!   `requires`", the hole read abstract, and now loads and runs that provider (31), as its
//!   bracket-free twin and its `[State = Buf[T = ?, N = Bool]]` twin did before and do now:
//!   WI-20260929-05ZQE. The abstract reading refused the correct holed calls above with it.
//! * THE FIRST LINK OF THE TICKET'S CHAIN IS AN ALIAS BETWEEN TWO CALLS: `mkS()`'s open `S`
//!   is the very variable `go13`'s own `S` is. Where no argument is typed by `S` — `go(o:
//!   Option[T = U], u: U) requires Store[State = S]`, called `User.go(User.mkS(), b)` — the
//!   requirement is supplied at `b`'s type, where it loaded and died at run time; and
//!   `go13(mkS(), b, c)` over two types is refused, before and after. A call's unfixed
//!   parameter as a variable of its own is WI-20261004-KEGNC's. The receiver-hole rows hold
//!   the two links without that alias.
//! * A HOLDER IN SCOPE at another binding of the argument's sort used to discharge the
//!   requirement this reading now pins: `wi_jn09w_holder_gate_test`.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};
use crate::wi_wbhtm_value_in_type_call_test::{provider, OTHER_IMPL};

/// `Buf[T, N]`, the spec `Store`, and a second state sort `Other`; `body` follows.
pub(crate) fn program(ns: &str, body: &str) -> String {
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
  end

  sort Other
    entity other(w: Int64)
  end
{body}
end
"#
    )
}

/// A provider of `Store` at ANY state, answering 55 — what a call reaches when the provider
/// at its own type is refused on a variable.
const GEN: &str = "\n  sort Gen\n    sort X = ?\n    provides Store[State = X]\n    \
                   operation peek(s: X) -> Int64 = 55\n  end\n";

/// One spelling of the argument's type: the binding the CALL is at, another binding of the
/// same sort, and how a refusal shows the call's.
pub(crate) struct Spelling {
    pub(crate) tag: &'static str,
    pub(crate) call: &'static str,
    pub(crate) other: &'static str,
    shown: &'static str,
}

/// `N` a type, and `N` a value held in the type.
pub(crate) const SPELLINGS: [Spelling; 2] = [
    Spelling {
        tag: "typed",
        call: "Buf[T = Int64, N = Bool]",
        other: "Buf[T = Int64, N = String]",
        shown: "N = anthill.prelude.Bool",
    },
    Spelling {
        tag: "value",
        call: "Buf[T = Int64, N = 3]",
        other: "Buf[T = Int64, N = 4]",
        shown: "N = 3",
    },
];

/// Run `row` at each spelling and fail naming EVERY spelling it failed at. A loop that stops
/// at the first failure cannot say which spellings a back-out moves; each failing spelling's
/// own message is in the row's output above this one.
#[track_caller]
pub(crate) fn at_each_spelling(row: impl Fn(&Spelling)) {
    let failed: Vec<&str> = SPELLINGS
        .iter()
        .filter(|sp| std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| row(sp))).is_err())
        .map(|sp| sp.tag)
        .collect();
    assert!(failed.is_empty(), "failed at: {}", failed.join(", "));
}

/// The requirement at the call's binding, as a refusal renders it.
pub(crate) fn shown_requirement(ns: &str, sp: &Spelling) -> String {
    format!(
        "`{ns}.Store[State = {ns}.Buf[T = anthill.prelude.Int64, {}]]`",
        sp.shown
    )
}

/// `User` with the requirement on the OPERATION. `mkS()` names `S` in its result and binds
/// nothing, which is what puts the variable link into σ.
pub(crate) const USER_OP: &str = r#"
  sort User
    sort S = ?
    sort U = ?
    operation mkS() -> Option[T = S] = none()
    operation go13(o: Option[T = U], u: U, s: S) -> Int64 requires Store[State = S] = Store.peek(s)
  end
"#;

/// The same `User` with the requirement on the SORT.
pub(crate) const USER_SORT: &str = r#"
  sort User
    sort S = ?
    sort U = ?
    requires Store[State = S]
    operation mkS() -> Option[T = S] = none()
    operation go13(o: Option[T = U], u: U, s: S) -> Int64 = Store.peek(s)
  end
"#;

/// `User` with ONE parameter and `go1(s: S)`, the requirement on the operation.
const USER_ONE_OP: &str = "\n  sort User\n    sort S = ?\n    \
     operation go1(s: S) -> Int64 requires Store[State = S] = Store.peek(s)\n  end\n";

/// The same with the requirement on the sort.
pub(crate) const USER_ONE_SORT: &str = "\n  sort User\n    sort S = ?\n    \
     requires Store[State = S]\n    operation go1(s: S) -> Int64 = Store.peek(s)\n  end\n";

/// `run(b: {arg}) = {call}`, entered by `go()`.
fn run_with(arg: &str, call: &str) -> String {
    format!(
        "\n  operation run(b: {arg}) -> Int64 = {call}\n  \
         operation go() -> Int64 = run(buf(v: 1))\n"
    )
}

/// The ticket's call.
pub(crate) const CHAIN_CALL: &str = "User.go13(User.mkS(), b, b)";

fn answers(ns: &str, body: &str) -> i64 {
    run_int64(&program(ns, body), &format!("{ns}.go"))
        .unwrap_or_else(|why| panic!("`{ns}.go` must load and run: {why}"))
}

// ── the ticket's program: `go13(mkS(), b, b)` ─────────────────────────────────────────

/// THE TICKET'S PROGRAM, both spellings: the one provider is at ANOTHER binding, so nothing
/// supplies `Store` at the call's — refused where the call is written, naming the
/// requirement at the binding the chain ends at. It loaded and ran that provider (31).
#[test]
fn an_operation_level_requirement_over_the_chain_is_refused_at_load() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.op_{}", sp.tag);
        let body = format!(
            "{}{USER_OP}{}",
            provider("P1", sp.other, 30),
            run_with(sp.call, CHAIN_CALL)
        );
        assert_refused_naming(
            &load_errors_of(&program(&ns, &body)),
            &[
                &shown_requirement(&ns, sp),
                &format!("cannot be supplied for call to `{ns}.User.go13`"),
            ],
            &format!("an op-level requirement over a two-link chain, {}", sp.tag),
        );
    });
}

/// TWO PROVIDERS THAT DIFFER ONLY IN `N`: the call reaches the one at its own binding (41).
/// It loaded with the slot unfilled and the run raised `AmbiguousRequirement` over both.
#[test]
fn the_chain_reaches_the_provider_at_the_calls_own_binding() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.two_{}", sp.tag);
        let body = format!(
            "{}{}{USER_OP}{}",
            provider("P1", sp.other, 30),
            provider("P2", sp.call, 40),
            run_with(sp.call, CHAIN_CALL)
        );
        assert_eq!(answers(&ns, &body), 41, "{}", sp.tag);
    });
}

/// THE ONE PROVIDER AT THE CALL'S BINDING runs. Passes either way by design: with the slot
/// unfilled, eval reached the same provider from the argument's value.
#[test]
fn the_provider_at_the_calls_binding_runs() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.match_{}", sp.tag);
        let body = format!(
            "{}{USER_OP}{}",
            provider("P1", sp.call, 30),
            run_with(sp.call, CHAIN_CALL)
        );
        assert_eq!(answers(&ns, &body), 31, "{}", sp.tag);
    });
}

/// THE ONE-LINK TWIN — `go1(s: S)`, so the argument binds `S` itself — refused with the same
/// words. Passes either way by design: it is what the chain is held against.
#[test]
fn the_one_link_twin_is_refused_with_the_same_words() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.one_{}", sp.tag);
        let body = format!(
            "{}{USER_ONE_OP}{}",
            provider("P1", sp.other, 30),
            run_with(sp.call, "User.go1(b)")
        );
        assert_refused_naming(
            &load_errors_of(&program(&ns, &body)),
            &[
                &shown_requirement(&ns, sp),
                &format!("cannot be supplied for call to `{ns}.User.go1`"),
            ],
            &format!("an op-level requirement over one link, {}", sp.tag),
        );
    });
}

/// THE REQUIREMENT ON THE SORT, the provider at another binding: the refusal names the
/// requirement at the binding the chain ends at. It named `Store[State = User.S]`.
#[test]
fn a_sort_level_requirement_over_the_chain_names_what_it_ends_at() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.sort_{}", sp.tag);
        let body = format!(
            "{}{USER_SORT}{}",
            provider("P1", sp.other, 30),
            run_with(sp.call, CHAIN_CALL)
        );
        assert_refused_naming(
            &load_errors_of(&program(&ns, &body)),
            &[
                &shown_requirement(&ns, sp),
                &format!("of `{ns}.User` cannot be supplied for call to `{ns}.User.go13`"),
            ],
            &format!("a sort-level requirement over a two-link chain, {}", sp.tag),
        );
    });
}

// ── a hole on the receiver: the same two links within ONE call ────────────────────────
//
// `User[S = ?].go1(b)` binds `S` to the hole's variable and the argument then binds that
// variable: `S ↦ ?h ↦ Buf[…]`, with no second call to share a variable with.

/// THE REQUIREMENT ON THE SORT is supplied at the argument's type, and the call runs the
/// provider there (31). It was refused naming `Store[State = User.S]`.
#[test]
fn a_hole_on_the_receiver_leaves_the_sort_level_requirement_suppliable() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.recv_sort_{}", sp.tag);
        let body = format!(
            "{}{USER_ONE_SORT}{}",
            provider("P1", sp.call, 30),
            run_with(sp.call, "User[S = ?].go1(b)")
        );
        assert_eq!(answers(&ns, &body), 31, "{}", sp.tag);
    });
}

/// THE REQUIREMENT ON THE OPERATION, the one provider at another binding: refused naming the
/// requirement at the argument's type. It loaded, and ran that provider.
#[test]
fn a_hole_on_the_receiver_does_not_hide_the_binding_from_an_operation_level_requirement() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.recv_op_{}", sp.tag);
        let body = format!(
            "{}{USER_ONE_OP}{}",
            provider("P1", sp.other, 30),
            run_with(sp.call, "User[S = ?].go1(b)")
        );
        assert_refused_naming(
            &load_errors_of(&program(&ns, &body)),
            &[
                &shown_requirement(&ns, sp),
                &format!("cannot be supplied for call to `{ns}.User.go1`"),
            ],
            &format!("an op-level requirement under a receiver hole, {}", sp.tag),
        );
    });
}

// ── a hole in the spec operation's own bracket, through each other reader ─────────────
//
// `Store.peek[State = ?](s)` binds `State` to the hole's variable, and the argument then
// binds that variable: `State ↦ ?h ↦ Buf[…]`.

/// `use(s: {arg}) = {call}`, entered by `go() = use(buf(v: 7))`.
fn use_with(arg: &str, call: &str) -> String {
    format!(
        "\n  operation use(s: {arg}) -> Int64 = {call}\n  \
         operation go() -> Int64 = use(buf(v: 7))\n"
    )
}

/// THE DISPATCH GOAL. The call reaches the provider at `Buf[T = Int64]` (7), as the
/// bracket-free call does; it ran the generic `Gen` (55).
#[test]
fn a_bracket_that_is_a_hole_reaches_the_specific_provider() {
    at_each_spelling(|sp| {
        for (how, call) in [
            ("holed", "Store.peek[State = ?](s)"),
            ("plain", "Store.peek(s)"),
        ] {
            let ns = format!("wi020th.{how}_{}", sp.tag);
            let body = format!(
                "{}{GEN}{}",
                provider("Carrier", "Buf[T = Int64]", 0),
                use_with(sp.call, call)
            );
            assert_eq!(answers(&ns, &body), 7, "{how}, {}", sp.tag);
        }
    });
}

/// `User requires Store[State = {req}]`, and its `via` makes the holed call on `{arg}`.
fn requiring_user(req: &str, arg: &str) -> String {
    format!(
        "\n  sort User\n    requires Store[State = {req}]\n    \
         operation via(s: {arg}) -> Int64 = Store.peek[State = ?](s)\n  end\n"
    )
}

/// UNDER A REQUIREMENT AT ANOTHER SORT. `User requires Store[State = Other]` and the holed
/// call is on a `Buf`: the requirement is no cover, and the call reaches the `Buf` provider
/// (7). It was refused "missing `requires Store[State = …]`", the hole read abstract.
#[test]
fn a_holed_call_does_not_defer_to_a_requirement_at_another_sort() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.defer_{}", sp.tag);
        let body = format!(
            "{}{OTHER_IMPL}{}\n  operation go() -> Int64 = User.via(buf(v: 7))\n",
            provider("Carrier", "Buf[T = Int64]", 0),
            requiring_user("Other", sp.call)
        );
        assert_eq!(answers(&ns, &body), 7, "{}", sp.tag);
    });
}

/// UNDER A REQUIREMENT AT ITS OWN BINDING the holed call DEFERS, and runs through the
/// requirement: two providers at that binding (`C4a` +40, `C4b` +45), so the call could not
/// dispatch on its own, and the bracket on `User.via` picks the requirement's supplier (46).
#[test]
fn a_holed_call_defers_to_a_requirement_at_its_own_binding() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.same_{}", sp.tag);
        let body = format!(
            "{}{}{}\n  operation go() -> Int64 = User.via[Store = C4b](buf(v: 1))\n",
            provider("C4a", sp.call, 40),
            provider("C4b", sp.call, 45),
            requiring_user(sp.call, sp.call)
        );
        assert_eq!(answers(&ns, &body), 46, "{}", sp.tag);
    });
}

/// THE OP-SCOPED LICENCE. `use[S]` requires `Store[State = S]` and the holed call is on a
/// `Buf` — another element — so the requirement licenses nothing and the call is refused
/// naming the carrier. Only `OtherImpl` provides `Store`. It was refused "missing `requires
/// Store[State = …]`", under the very clause the message asks for.
#[test]
fn a_holed_call_is_not_licensed_by_a_requirement_over_another_element() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.licence_{}", sp.tag);
        let body = format!(
            "{OTHER_IMPL}\n  operation use[S](s: S, b: {}) -> Int64 requires Store[State = S] = \
             Store.peek[State = ?](b)\n  operation go() -> Int64 = use(other(1), buf(v: 7))\n",
            sp.call
        );
        assert_refused_naming(
            &load_errors_of(&program(&ns, &body)),
            &[&format!("`{ns}.Buf` provides no `{ns}.Store`")],
            &format!("a holed call under a requirement over `S`, {}", sp.tag),
        );
    });
}

/// NO PROVIDER AT ALL: the refusal names the carrier, as the bracket-free call's does —
/// `State` is bound, so nothing is abstract. It said "covering abstract type parameter".
#[test]
fn a_holed_call_with_no_provider_names_the_carrier() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.none_{}", sp.tag);
        let errs = load_errors_of(&program(
            &ns,
            &use_with(sp.call, "Store.peek[State = ?](s)"),
        ));
        assert_refused_naming(
            &errs,
            &[&format!("`{ns}.Buf` provides no `{ns}.Store`")],
            &format!("a holed call with no provider, {}", sp.tag),
        );
        assert!(
            !errs
                .iter()
                .any(|e| e.contains("covering abstract type parameter")),
            "{}: `State` is bound, so nothing is abstract; got {errs:#?}",
            sp.tag
        );
    });
}

// ── the variables INSIDE the binding ──────────────────────────────────────────────────

/// A HOLE INSIDE THE BRACKET binds `State` to `Buf[T = ?t, N = …]` and leaves `?t` to the
/// argument. The call reaches the provider at `Buf[T = Int64]` (7) on both spellings. The
/// typed one ran the generic `Gen` (55): a term binding was handed over as σ stored it, `?t`
/// still a variable, where the value-in-type one — an occurrence — was resolved first.
#[test]
fn a_hole_inside_the_bracket_reaches_the_specific_provider() {
    at_each_spelling(|sp| {
        let ns = format!("wi020th.inner_{}", sp.tag);
        let holed = sp.call.replace("T = Int64", "T = ?");
        let body = format!(
            "{}{GEN}{}",
            provider("Carrier", "Buf[T = Int64]", 0),
            use_with(sp.call, &format!("Store.peek[State = {holed}](s)"))
        );
        assert_eq!(answers(&ns, &body), 7, "{}", sp.tag);
    });
}

/// A LINK ON THE VALUE CARRIER, then a term with a variable inside. An un-annotated lambda
/// binder `o` gives `S ↦ ?o`, `Mk.mkO()` gives `?o ↦ Option[T = ?Q]`, and `some(1)` gives
/// `?Q ↦ Int64`: the requirement is at `Option[T = Int64]` and the call reaches `POpt` (41).
/// The parent commit answered 41 too — a link on another carrier than a term was resolved
/// in full — so this row guards the chain walk: following the link and then handing the term
/// over as σ stored it answers `Gen`'s 55.
#[test]
fn a_term_reached_through_a_lambda_binder_is_resolved_inside() {
    let body = format!(
        "{GEN}\n  sort POpt\n    provides Store[State = Option[T = Int64]]\n    \
         operation peek(s: Option[T = Int64]) -> Int64 = 41\n  end\n\n  \
         sort Mk\n    sort Q = ?\n    operation mkO() -> Option[T = Q] = none()\n  end\n\n  \
         sort User\n    sort S = ?\n    \
         operation go3(a: S, b: S, c: S) -> Int64 requires Store[State = S] = Store.peek(a)\n  \
         end\n\n  operation go() -> Int64 =\n    \
         let g = lambda (o) -> User.go3(o, Mk.mkO(), some(1))\n    g(some(7))\n"
    );
    assert_eq!(answers("wi020th.lambda", &body), 41);
}
