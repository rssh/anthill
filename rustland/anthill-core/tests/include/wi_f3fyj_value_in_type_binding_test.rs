//! WI-20260924-F3FYJ — a provision's VALUE-IN-TYPE binding is the type a signature writes.
//!
//! `provides Store[State = Buf[T = Int64, N = 3]]` binds `State` to a type holding the
//! value `3`. The loader lowered a NESTED binding value to the plain application only when
//! every argument was already a hash-consed term; the denoted `3` made it wrap the binding
//! in a `reflect.SortView(Buf, …)` instead, and the provision fact stored that wrapper. A
//! type position lowers the same text to the application `Buf[T = Int64, N = 3]`, so σ
//! (the provision's `State ↦ …`) never met a signature. MEASURED before the fix: a
//! CORRECT member `peek(s: Buf[T = Int64, N = 3])` was refused ("where the spec's is
//! `SortView(Buf)[T = Int64, N = 3]`"), a WRONG one (`N = 4`) got the same refusal, and
//! the ground `State = Buf[T = Int64]` loaded. The same wrapper reached the other σ
//! readers: an operation bound by name (`peek = bufPeek`) and a spec ALIAS fixing the
//! binding were refused the same way.
//!
//! The rest of the file is what that fix made reachable, each found by its review:
//!
//! * THE BARE-SPEC SUGAR (the ticket's own "Also"). `Store.State` in the carrier's block
//!   narrowed under `provides BufStore` but not under the bracketed spelling, because the
//!   carrier pre-scan decoded the UNLOWERED spec and dropped the binding; and the alias
//!   spelling narrowed a bare VALUE (`Sized.N` ↦ `3`), which kernel-language §5.4 excludes.
//! * DISPATCH. A provision at a value-in-type binding was invisible to load-time
//!   arbitration: the candidate matcher read `denoted(3)` as a STRUCTURED head.
//! * THE SLD READ. `resolve_sort_instantiation_param` in a rule answered only a `SortView`
//!   head, so it could no longer read INTO the nested binding this fix made plain.
//! * A `Nothing[…]` APPLICATION. The fix routed a refused `Nothing[X = 3]` binding into a
//!   builder that asked the typer's classifier for the base, which panics on `Nothing` —
//!   as the ground spelling, a signature and an alias target already did.
//!
//! Every correct row DRIVES what it claims: a call runs through the provision, a rule
//! answers, a refusal names the types — "it loads" is not what is measured.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! EIGHT PARTS, each backed out PRESENT-BUT-WRONG, APPLIED AND RUN over this file's 24 rows:
//!
//! 1. THE SOURCE FIX — `assemble_binding_value` wraps any non-term child in a `SortView`
//!    again. 12 FAIL: [`a_correct_member_loads_and_the_call_runs`],
//!    [`an_operation_bound_by_name_loads_and_the_call_runs`],
//!    [`a_spec_alias_fixing_the_binding_loads_and_the_call_runs`]; the four CONTROLS, AT THEIR
//!    MESSAGE only — each is still refused (which is what keeps a "fix" that stops comparing
//!    from passing), but the spec's side reads `SortView(Buf)[T = Int64, N = 3]`:
//!    [`a_wrong_member_parameter_is_refused`], [`a_wrong_member_return_is_refused`],
//!    [`an_operation_bound_by_name_at_a_wrong_type_is_refused`],
//!    [`a_spec_alias_fixing_the_binding_refuses_a_wrong_member`]; and the rows whose carrier
//!    has a member at the value, refused before what they drive can run —
//!    [`the_bracketed_spelling_narrows_the_spec_member`], [`the_alias_spelling_narrows_alike`],
//!    [`a_bracket_selects_the_provider_at_its_value`],
//!    [`beside_a_typed_provider_a_bracket_selects_the_valued_one`],
//!    [`a_sort_requirement_at_the_value_is_supplied`].
//! 2. THE PRE-SCAN DECODE — the carrier pre-scan reads the UNLOWERED spec again. 1 FAILS:
//!    [`the_bracketed_spelling_narrows_the_spec_member`].
//! 3. THE ROOT-VALUE REFUSAL — a bare value may narrow the sugar. 2 FAIL:
//!    [`a_bare_value_binding_narrows_nothing`] and
//!    [`a_bare_value_binding_narrows_nothing_through_an_alias`] (`got 3`).
//! 4. THE LEAF ARM — `match_candidate_against_goal` reads `denoted` as a structured head
//!    again. 4 FAIL: [`two_providers_at_different_values_are_ambiguous_at_load`],
//!    [`a_bracket_selects_the_provider_at_its_value`],
//!    [`beside_a_typed_provider_the_call_is_still_ambiguous`],
//!    [`beside_a_typed_provider_a_bracket_selects_the_valued_one`].
//! 5. THE VALUE GUARD — `dispatch_values_match` falls to its coarse head for a value. 1 FAILS:
//!    [`a_sort_requirement_at_another_value_is_refused`] (`N = 4` supplied by `N = 3`).
//! 6. THE SLD HEAD — `resolve_sort_instantiation_param` answers a `SortView` head only. 2 FAIL:
//!    [`a_rule_reads_into_a_nested_value_binding`], [`a_rule_reads_into_a_nested_ground_binding`].
//! 7. THE BASE READ — `make_parameterized_type` asks the typer's classifier alone again, with
//!    no bottom-sort arm. 4 FAIL, BY PANIC: the four `…_is_refused_not_a_crash` rows.
//! 8. THE GOAL RENDERING — `format_term_for_goal` prints a value raw. 1 FAILS, at its message:
//!    [`a_sort_requirement_at_another_value_is_refused`].
//!
//! PASSES UNDER EVERY BACK-OUT, by design: [`the_ground_binding_is_the_baseline`], the ticket's
//! "a ground nested binding loads", which never took the wrapper.
//!
//! NOT COVERED HERE, and why: a spec operation called with an argument whose STATIC type
//! carries a value-in-type (`s: Buf[T = Int64, N = 3]; Store.peek(s)`) is a different
//! question — how the CALL's binding reaches dispatch, not the provision's — and it tripped
//! the typer's WI-348 "Phase C" `debug_assert` independent of this fix (with it backed out,
//! with a GROUND provision, with no provision at all). The rows call with `buf(v: …)`, whose
//! inferred type carries no denoted; that call is `wi_wbhtm_value_in_type_call_test`'s
//! (WI-20260929-WBHTM). A value-in-type
//! written as a NAME (`N = size`, a zero-arg operation) still lowers to `Ref(size)` in a
//! binding where a signature reads `denoted(size)` — the same divergence one spelling over,
//! not closed here (WI-20260929-9WXK2).

use crate::common::{assert_refused_naming, definite_unary, interp_for, try_load_kb_with};
use anthill_core::eval::Value;

/// `Buf[T, N]` — `N` the value-in-type argument — and the spec `Store`, whose `State` the
/// provisions bind. `body` follows; `go()` is the row's driver.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
    operation fresh(n: Int64) -> State
  end
{body}
end
"#
    )
}

/// A carrier `name` whose own members implement `Store` — `peek` taking `peek_ty` and
/// returning `s.v + bump`, `fresh` returning `fresh_ty` — provided through `provision`.
fn carrier_named(name: &str, provision: &str, peek_ty: &str, fresh_ty: &str, bump: i64) -> String {
    format!(
        r#"
  sort {name}
    {provision}
    operation peek(s: {peek_ty}) -> Int64 = s.v + {bump}
    operation fresh(n: Int64) -> {fresh_ty} = buf(v: n)
  end
"#
    )
}

fn carrier(provision: &str, peek_ty: &str, fresh_ty: &str) -> String {
    carrier_named("Carrier", provision, peek_ty, fresh_ty, 0)
}

const VALUED: &str = "Buf[T = Int64, N = 3]";
const WRONG: &str = "Buf[T = Int64, N = 4]";
const PROVIDES_VALUED: &str = "provides Store[State = Buf[T = Int64, N = 3]]";

/// Load `program(ns, body)` with `go() = {go}` appended, call `ns.go()`, return its `Int64`.
fn answers(ns: &str, body: &str, go: &str) -> i64 {
    let src = program(ns, &format!("{body}\n  operation go() -> Int64 = {go}"));
    let mut interp = interp_for(&src);
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` must run to an Int64: {other:?}"),
    }
}

fn load_errors(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

// ── the carrier's own members ─────────────────────────────────────────────────────────

/// THE TICKET'S PROGRAM, driven: the members fit the provision at the value-in-type
/// binding — `peek` at the parameter, `fresh` at the return — and the spec operation,
/// called with a `Buf`, dispatches to the carrier's `peek` through the provision.
#[test]
fn a_correct_member_loads_and_the_call_runs() {
    let body = carrier(PROVIDES_VALUED, VALUED, VALUED);
    assert_eq!(answers("wif3fyj.member", &body, "Store.peek(buf(v: 7))"), 7);
}

/// THE CONTROL, at the parameter: `N = 4` is another type, refused naming both. The same
/// fixture as the row above but for the member's `N`.
#[test]
fn a_wrong_member_parameter_is_refused() {
    let body = carrier(PROVIDES_VALUED, WRONG, VALUED);
    let errs = load_errors(&program("wif3fyj.member_bad", &body));
    assert_refused_naming(
        &errs,
        &[
            "its own member 'peek' does not fit",
            "parameter 1 is `Buf[T = Int64, N = 4]` where the spec's is `Buf[T = Int64, N = 3]`",
        ],
        "a member at another value-in-type argument",
    );
}

/// THE CONTROL, at the return — the covariant leg, compared the same way.
#[test]
fn a_wrong_member_return_is_refused() {
    let body = carrier(PROVIDES_VALUED, VALUED, WRONG);
    let errs = load_errors(&program("wif3fyj.member_bad_ret", &body));
    assert_refused_naming(
        &errs,
        &[
            "its own member 'fresh' does not fit",
            "the member returns `Buf[T = Int64, N = 4]`, which is not a subtype of the \
             spec's `Buf[T = Int64, N = 3]`",
        ],
        "a member returning another value-in-type argument",
    );
}

/// THE BASELINE: the ground binding the ticket measured loading. It never took the wrapper,
/// so it passes either way; it is here so the rows above are read against it.
#[test]
fn the_ground_binding_is_the_baseline() {
    let ground = "Buf[T = Int64]";
    let body = carrier("provides Store[State = Buf[T = Int64]]", ground, ground);
    assert_eq!(answers("wif3fyj.ground", &body, "Store.peek(buf(v: 7))"), 7);
}

// ── the other σ readers ───────────────────────────────────────────────────────────────

/// Operations bound BY NAME in the provision (`peek = bufPeek`), not members: the
/// op-binding signature check reads the same σ.
fn bound_by_name(peek_ty: &str) -> String {
    format!(
        r#"
  operation bufPeek(s: {peek_ty}) -> Int64 = s.v
  operation bufFresh(n: Int64) -> {VALUED} = buf(v: n)
  sort Carrier
    provides Store[State = {VALUED}, peek = bufPeek, fresh = bufFresh]
  end
"#
    )
}

#[test]
fn an_operation_bound_by_name_loads_and_the_call_runs() {
    assert_eq!(
        answers(
            "wif3fyj.bound",
            &bound_by_name(VALUED),
            "Store.peek(buf(v: 9))"
        ),
        9
    );
}

#[test]
fn an_operation_bound_by_name_at_a_wrong_type_is_refused() {
    let errs = load_errors(&program("wif3fyj.bound_bad", &bound_by_name(WRONG)));
    assert_refused_naming(
        &errs,
        &[
            "binds 'wif3fyj.bound_bad.Store.peek' to a signature-incompatible operation",
            "has type `Buf[T = Int64, N = 4]`, incompatible with the spec parameter type \
             `Buf[T = Int64, N = 3]`",
        ],
        "an operation bound at another value-in-type argument",
    );
}

/// A spec ALIAS that fixes the binding (WI-20260924-F8PYZ): `provides BufStore` is
/// `provides Store[State = Buf[T = Int64, N = 3]]`. The alias's recorded reading is lowered
/// the way a binding value is, so it carried the wrapper too.
fn through_alias(peek_ty: &str) -> String {
    format!(
        "  sort BufStore = Store[State = {VALUED}]\n{}",
        carrier("provides BufStore", peek_ty, VALUED)
    )
}

#[test]
fn a_spec_alias_fixing_the_binding_loads_and_the_call_runs() {
    assert_eq!(
        answers(
            "wif3fyj.alias",
            &through_alias(VALUED),
            "Store.peek(buf(v: 11))"
        ),
        11
    );
}

#[test]
fn a_spec_alias_fixing_the_binding_refuses_a_wrong_member() {
    let errs = load_errors(&program("wif3fyj.alias_bad", &through_alias(WRONG)));
    assert_refused_naming(
        &errs,
        &[
            "its own member 'peek' does not fit",
            "parameter 1 is `Buf[T = Int64, N = 4]` where the spec's is `Buf[T = Int64, N = 3]`",
        ],
        "a member at another value-in-type argument, through the alias",
    );
}

// ── the bare-spec sugar narrows to the binding (the ticket's "Also") ─────────────────

/// The carrier's members written through the sugar: `Store.State` here must mean the
/// provision's `Buf[T = Int64, N = 3]` — `peek` reads the field `v`, which an abstract
/// `?State` does not have.
fn sugar_carrier(provision: &str) -> String {
    carrier(provision, "Store.State", "Store.State")
}

/// THE BRACKETED SPELLING NARROWS. The pre-scan decoded the unlowered spec, dropped the
/// occurrence-carried binding, and kept the generic reading: refused `?State.v … declare
/// no 'v'`, where writing the type out loads.
#[test]
fn the_bracketed_spelling_narrows_the_spec_member() {
    let body = sugar_carrier(PROVIDES_VALUED);
    assert_eq!(
        answers("wif3fyj.sugar", &body, "Store.peek(buf(v: 13))"),
        13
    );
}

/// THE ALIAS SPELLING, the same provision (WI-20260924-F8PYZ: the two read alike). Its fixed
/// bindings arrive lowered, so this narrows with the pre-scan part backed out — the parity
/// twin of the row above. (It narrowed before this ticket too, to the WRAPPER.)
#[test]
fn the_alias_spelling_narrows_alike() {
    let body = format!(
        "  sort BufStore = Store[State = {VALUED}]\n{}",
        sugar_carrier("provides BufStore")
    );
    assert_eq!(
        answers("wif3fyj.sugar_alias", &body, "Store.peek(buf(v: 15))"),
        15
    );
}

/// `Sized[WIS, 3]`, whose `N` is bound to the bare VALUE `3`, and an operation that returns
/// its `Sized.N` argument as a `Bool` — refused either way, and the refusal names the type
/// the sugar read: `Sized.N`, the member's own parameter printed as written
/// (WI-20261006-XQGEW; it read `?N`), for the generic reading, `3` if it narrowed.
fn value_binding_program(ns: &str, claim: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
  sort Sized
    sort T = ?
    sort N = ?
  end
  sort WIS
    entity wis(n: Int64)
  end
  sort SA = Sized[WIS, 3]
  sort Holder
    {claim}
    operation probeN(x: Sized.N) -> Bool = x
  end
end
"#
    )
}

fn assert_value_binding_stays_generic(ns: &str, claim: &str) {
    let errs = load_errors(&value_binding_program(ns, claim));
    assert_refused_naming(&errs, &["probeN", "got Sized.N"], claim);
    assert!(
        !errs.iter().any(|e| e.contains("got 3")),
        "{claim}: a bare value is no type a signature could spell (`x: 3` does not parse), so \
         `Sized.N` must keep the generic reading (kernel-language §5.4); got {errs:#?}"
    );
}

/// A BARE VALUE NARROWS NOTHING, bracketed. Passes before the pre-scan fix too (the value was
/// dropped then); the decode that now delivers it must not start narrowing to it.
#[test]
fn a_bare_value_binding_narrows_nothing() {
    assert_value_binding_stays_generic("wif3fyj.value_br", "provides Sized[WIS, 3]");
}

/// … AND THROUGH AN ALIAS, which narrowed `Sized.N` to `3` before (its bindings came lowered).
#[test]
fn a_bare_value_binding_narrows_nothing_through_an_alias() {
    assert_value_binding_stays_generic("wif3fyj.value_al", "provides SA");
}

// ── dispatch arbitrates between providers at value-in-type bindings ──────────────────

/// Two carriers of `Store`: `C1` at `c1_state` (answers `v`), `C2` at `N = 3` (answers
/// `v + 1`).
fn two_providers(c1_state: &str) -> String {
    format!(
        "{}{}",
        carrier_named(
            "C1",
            &format!("provides Store[State = {c1_state}]"),
            c1_state,
            c1_state,
            0
        ),
        carrier_named("C2", PROVIDES_VALUED, VALUED, VALUED, 1),
    )
}

fn assert_ambiguous_at_load(ns: &str, body: &str, why: &str) {
    let src = program(
        ns,
        &format!("{body}\n  operation go() -> Int64 = Store.peek(buf(v: 7))"),
    );
    assert_refused_naming(
        &load_errors(&src),
        &["ambiguous dispatch of", "2 instances provide", "C1", "C2"],
        why,
    );
}

/// TWO VALUES, NO BRACKET: a load error, as it is for two types. Was a clean load that died
/// "ambiguous dispatch" at run time — the candidate matcher refused `denoted(4)` / `denoted(3)`
/// as structured heads, so it saw NO candidate and deferred.
#[test]
fn two_providers_at_different_values_are_ambiguous_at_load() {
    assert_ambiguous_at_load(
        "wif3fyj.two_values",
        &two_providers(WRONG),
        "two providers at N = 4 / N = 3, unbracketed",
    );
}

/// THE BRACKET SELECTS the provider at its value. Was dropped: the load passed and the run
/// refused "nothing here selects one".
#[test]
fn a_bracket_selects_the_provider_at_its_value() {
    assert_eq!(
        answers(
            "wif3fyj.two_values_br",
            &two_providers(WRONG),
            "Store.peek[Store = C2](buf(v: 7))"
        ),
        8
    );
}

/// BESIDE A TYPED PROVIDER (`N = Int64`), still a tie. Was a silent pick of the typed one —
/// the valued provider never a candidate.
#[test]
fn beside_a_typed_provider_the_call_is_still_ambiguous() {
    assert_ambiguous_at_load(
        "wif3fyj.mixed",
        &two_providers("Buf[T = Int64, N = Int64]"),
        "a typed and a valued provider, unbracketed",
    );
}

/// … and the bracket reaches the valued one. Was refused at load: "C2 provides Store, but
/// not at the bindings this call … needs".
#[test]
fn beside_a_typed_provider_a_bracket_selects_the_valued_one() {
    assert_eq!(
        answers(
            "wif3fyj.mixed_br",
            &two_providers("Buf[T = Int64, N = Int64]"),
            "Store.peek[Store = C2](buf(v: 7))"
        ),
        8
    );
}

// ── a sort's requirement at a value-in-type binding ──────────────────────────────────

/// `User requires Store[State = {state}]`, and its operation calls `Store.peek` — deferred to
/// that requirement, which the one provider (`Carrier`, at `N = 3`) must supply at the call.
fn requiring_user(state: &str) -> String {
    format!(
        "{}\n  sort User\n    requires Store[State = {state}]\n    \
         operation use(n: Int64) -> Int64 = Store.peek(buf(v: n))\n  end",
        carrier(PROVIDES_VALUED, VALUED, VALUED)
    )
}

/// THE REQUIREMENT AT THE PROVIDER'S VALUE is supplied, and the deferred call runs.
#[test]
fn a_sort_requirement_at_the_value_is_supplied() {
    assert_eq!(
        answers("wif3fyj.req", &requiring_user(VALUED), "User.use(5)"),
        5
    );
}

/// THE CONTROL: at `N = 4` no provider answers. A value is related to a value BY VALUE — the
/// dispatch matcher's coarse head fallback would read every value-in-type as the one head
/// `Denoted` and call these a match.
#[test]
fn a_sort_requirement_at_another_value_is_refused() {
    let errs = load_errors(&program(
        "wif3fyj.req_bad",
        &format!(
            "{}\n  operation go() -> Int64 = User.use(5)",
            requiring_user(WRONG)
        ),
    ));
    assert_refused_naming(
        &errs,
        &["cannot be supplied", "N = 4"],
        "a requirement at N = 4",
    );
}

// ── a rule reads INTO the nested binding ──────────────────────────────────────────────

/// The binding keys as DATA (a fact slot keeps the spelling it was written with), and two
/// rules reading through the provision: the outer view's `State`, then `State`'s `key`.
fn sld_program(ns: &str, state: &str, key: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  import anthill.reflect.{{SortProvidesInfo, resolve_sort_instantiation_param, Term}}
  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end
  sort Store
    sort State = ?
  end
  sort Carrier
    provides Store[State = {state}]
  end
  entity Keys(outer: Term, inner: Term)
  fact Keys(outer: State(), inner: {key}())
  rule nested(?v)
    :- Keys(outer: ?ko, inner: ?ki),
       SortProvidesInfo(sort_ref: ?, spec: ?s),
       resolve_sort_instantiation_param(?s, ?ko, ?st),
       resolve_sort_instantiation_param(?st, ?ki, ?v)
end
"#
    )
}

fn nested_answers(ns: &str, state: &str, key: &str) -> Vec<String> {
    let mut kb = crate::common::load_kb_with(&sld_program(ns, state, key));
    // Each answer through the term it lowers to: a binding rides whichever carrier its
    // provision does, and an occurrence and its term print through two printers.
    definite_unary(&mut kb, &format!("{ns}.nested"))
        .iter()
        .map(|v| {
            let term = anthill_core::kb::node_occurrence::value_to_term(&mut kb, v)
                .expect("an answered binding has a term");
            crate::common::show_value(&kb, &anthill_core::eval::Value::term(term))
        })
        .collect()
}

/// THE VALUE-IN-TYPE BINDING, read in a rule: `N` of the provision's `State`. The SLD builtin
/// answered only a `SortView` head; the eval twin answered any.
#[test]
fn a_rule_reads_into_a_nested_value_binding() {
    let got = nested_answers("wif3fyj.sld_value", VALUED, "N");
    // The value-in-type binding, as its term prints: the value it holds.
    assert_eq!(
        got,
        vec!["3"],
        "one answer, the bound VALUE — not the outer `Buf[…]` binding"
    );
}

/// THE GROUND BINDING, the same read (`T` of `Buf[T = Int64]`) — which answered NOTHING since
/// WI-600 made a ground nested binding plain: the same builtin gap one carrier over.
#[test]
fn a_rule_reads_into_a_nested_ground_binding() {
    let got = nested_answers("wif3fyj.sld_ground", "Buf[T = Int64]", "T");
    assert_eq!(
        got,
        vec!["Int64"],
        "one answer, the bound TYPE — not the outer `Buf[…]` binding"
    );
}

// ── a refused `Nothing[…]` application is reported, not a crash ───────────────────────

fn nothing_program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Nothing}}
  sort Store
    sort State = ?
  end
{body}
end
"#
    )
}

fn assert_nothing_refused(ns: &str, body: &str) {
    let errs = load_errors(&nothing_program(ns, body));
    assert_refused_naming(
        &errs,
        &[
            "invalid type argument",
            "`anthill.prelude.Nothing` has no type parameter named 'X'",
        ],
        body,
    );
}

/// A VALUE-IN-TYPE BINDING under `Nothing` — the spelling the fix newly routed into the
/// builder, which asked the typer's classifier for the base and panicked on `Nothing`.
#[test]
fn a_valued_nothing_binding_is_refused_not_a_crash() {
    assert_nothing_refused(
        "wif3fyj.nothing_valued",
        "  sort Carrier\n    provides Store[State = Nothing[X = 3]]\n  end",
    );
}

/// THE GROUND SPELLING, a SIGNATURE and an ALIAS TARGET crashed the same way before the fix
/// (the builder's one `expect`); pinned beside it.
#[test]
fn a_ground_nothing_binding_is_refused_not_a_crash() {
    assert_nothing_refused(
        "wif3fyj.nothing_ground",
        "  sort Carrier\n    provides Store[State = Nothing[X = Int64]]\n  end",
    );
}

#[test]
fn a_nothing_application_in_a_signature_is_refused_not_a_crash() {
    assert_nothing_refused(
        "wif3fyj.nothing_sig",
        "  operation f(x: Nothing[X = Int64]) -> Int64 = 1",
    );
}

#[test]
fn a_nothing_application_in_an_alias_is_refused_not_a_crash() {
    assert_nothing_refused(
        "wif3fyj.nothing_alias",
        "  sort NStore = Store[State = Nothing[X = 3]]",
    );
}
