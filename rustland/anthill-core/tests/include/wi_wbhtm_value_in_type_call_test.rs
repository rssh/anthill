//! WI-20260929-WBHTM — a spec-operation call whose argument's STATIC TYPE holds a value
//! dispatches on that type, exactly as its typed twin does.
//!
//! `use(s: Buf[T = Int64, N = 3]) = Store.peek(s)`: σ binds the spec parameter `State` to the
//! argument's type, and a type holding a value rides as an OCCURRENCE (a `Value::Node`,
//! WI-477) — or as the entity spine `fn_value` rebuilds around one — not as a hash-consed
//! term. Every typer reader that turns σ into a dispatch question read only the term carrier
//! and DROPPED this one (WI-348 "Phase C"): a `debug_assert!` panicked a debug build, and a
//! release build went on without the binding. MEASURED on the release binary of the parent
//! commit, one shape per reader:
//!
//! * THE DISPATCH GOAL (`sort_goal_from_subst`) lost `State`: the correct call was refused
//!   "missing `requires Store[State = …]`", and so was a call with no provider at all, where
//!   the ground twin names the carrier.
//! * THE DEFER-MATCH (`entry_type_param_bindings`) had nothing to refute: a call on a `Buf`
//!   deferred to `requires Store[State = Other]` and RAN `Other`'s provider on it (99), and a
//!   call at `N = 4` deferred to a requirement at `N = 3` and ran THAT provider.
//! * THE OP-SCOPED LICENCE (`op_requires_covers_call`'s carriers) had no carrier to align,
//!   so a `requires Store[State = S]` licensed a call on a `Buf` "blind" — 99 again.
//! * A CALLEE'S REQUIREMENT (`resolve_param_value_via_subst`) kept `State = User.S`, and the
//!   supply refused the element as "unconstrained at this call site".
//! * A RECEIVER'S OWN ARGUMENTS (`receiver_type_args`) were EMPTY, so the carrier's
//!   `requires Tagger[T = Src]` was asked about the declaration's `Src` and refused.
//! * THE WI-325 WALK read the binding ABSTRACT for not being a term: a call over `s: Src[E =
//!   {Modify[c]}]` was refused "missing `requires`" where the term-carried row loaded (under
//!   a `requires` the vacuous defer above hid it — and refused it again, under the very
//!   `requires` it asks for, once the defer-match compared the row).
//! * THE UNIFIER (`unify_parameterized_with_sort_ref`) never bound such a type through a
//!   parameter declared as the bare sort: `User.via(u)` with `u: User[S = Buf[…, N = 3]]`
//!   was refused "unconstrained" — and stayed refused once the readers above served the
//!   `via(u: User[S = S])` spelling — and `first(h: Holder) -> S` let a wrong annotation
//!   through.
//!
//! The binding is now resolved through σ and LOWERED to its term twin where a `TermId` is
//! needed — the carrier its provision is filed on — by one reader, `spec_param_binding_term`,
//! and the unifier binds it as it binds a term.
//!
//! Every row that can DRIVES what it claims: a call runs to a value that names the provider
//! it reached (each answers `v` plus its own offset), or a refusal names what failed. The two
//! effect-row rows assert a LOAD verdict and say at their site why nothing can run.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! NINE PARTS, each backed out PRESENT-BUT-WRONG — the reader goes back to taking a `Term`
//! binding only and skipping any other, the release behaviour the ticket measured (the
//! original `debug_assert`s would panic these rows instead) — APPLIED AND RUN over this
//! file's 21 rows:
//!
//! 1. THE GOAL (`sort_goal_from_subst`). 6 FAIL: [`two_providers_are_told_apart_by_the_value`],
//!    [`with_no_provider_the_refusal_names_the_carrier`], [`a_bracket_selects_the_provider_at_the_value`],
//!    [`a_bracket_at_another_value_is_refused`], and — the dispatch that follows a refused
//!    cover being this goal's — [`a_requirement_at_another_value_is_no_cover`],
//!    [`an_op_scoped_requirement_over_another_element_licenses_nothing`].
//! 2. THE σ WALK before the lowering (`spec_param_binding_term`). 1 FAILS:
//!    [`a_bracket_with_a_hole_reaches_the_specific_provider`] (55, the generic provider).
//! 3. THE DEFER-MATCH (`entry_type_param_bindings`). 3 FAIL:
//!    [`the_ticket_defer_case_reaches_the_buf_provider`] (99),
//!    [`a_requirement_at_another_value_is_no_cover`] (31), and
//!    [`an_op_scoped_requirement_over_another_element_licenses_nothing`] — an operation's own
//!    `requires` is in the chain the defer trigger walks (WI-822 LEG 1).
//! 4. THE OP-SCOPED LICENCE (`op_requires_covers_call`'s carriers). 1 FAILS:
//!    [`an_op_scoped_requirement_over_another_element_licenses_nothing`].
//! 5. THE CALLEE'S REQUIREMENT (`resolve_param_value_via_subst`). 2 FAIL:
//!    [`a_callees_requirement_is_supplied_at_the_value`], [`a_bare_sort_parameter_binds_the_value_in_type`].
//! 6. THE ENTITY RECEIVER (`receiver_type_args` dropping an entity spine). 1 FAILS:
//!    [`an_entity_carried_receiver_type_keeps_its_arguments`].
//! 7. EVERY NON-TERM RECEIVER (the same, for any carrier but a term). 3 FAIL: the entity row,
//!    [`a_receivers_arguments_reach_the_carriers_requirement`], and the control
//!    [`a_receivers_argument_is_not_a_wildcard`] (its refusal names `Pairer.Src`, not `Light`).
//! 8. THE WI-325 WALK reading a non-term binding abstract again. 1 FAILS:
//!    [`an_effect_row_carrying_a_value_is_not_read_abstract`].
//! 9. THE UNIFIER skipping a non-row occurrence again. 2 FAIL:
//!    [`a_bare_sort_parameter_binds_the_value_in_type`], [`a_wrong_annotation_through_a_bare_sort_parameter_is_refused`].
//!
//! [`the_ticket_call_dispatches_to_its_provider`] passes under each ONE of these — with a
//! single reader backed out its one provider is still reached — and fails on the parent
//! commit, where every reader dropped the binding (release: "missing `requires`"; debug: the
//! WI-348 panic).
//!
//! PASS UNDER EVERY BACK-OUT, by design: [`a_requirement_at_the_same_value_still_covers`] (a
//! dropped binding covers vacuously, so it defers either way — the row says the fix did not
//! stop a correct deferral), and the four twins that never take another carrier:
//! [`an_op_scoped_requirement_over_another_element_licenses_nothing_typed`],
//! [`an_effect_row_carrying_a_value_is_not_read_abstract_ground`],
//! [`a_matching_annotation_through_a_bare_sort_parameter_runs`] and
//! [`a_receivers_arguments_reach_the_carriers_requirement_ground`].
//!
//! NOT COVERED HERE, and why:
//! * A value-in-type written as a NAME (`N = size`, a zero-arg operation): a `requires` files
//!   it as `Ref(size)` while the call's type lowers it to `denoted(Ref(size))`, so a
//!   requirement at `N = size` no longer covers its own call — it did only vacuously, while
//!   the binding was dropped. The divergence is WI-20260929-9WXK2's, whose fix closes this.
//! * A call at a value NO provision covers (the one provider at `N = 3`, the call at
//!   `N = 4`) runs that provider, on every spelling — occurrence, `let`-annotated term, and
//!   the typed twin alike: WI-20260929-05ZQE. Reading the binding abstract had refused the
//!   occurrence spelling alone, by accident, and refused correct effect-row calls with it.
//! * THE TYPED TWINS OF THE HOLE ROW, which this ticket left as it found them: a hole inside a
//!   TERM binding (`[State = Buf[T = ?, N = Bool]]`) ran the generic provider (55), and a
//!   bracket whose WHOLE binding is a hole (`[State = ?]`) met a variable one link into σ on
//!   both spellings. Both are read through σ on every carrier since WI-20260929-020TH, and
//!   driven in `wi_020th_two_hop_chain_test`.

use crate::common::{assert_refused_naming, interp_for, try_load_kb_with};
use anthill_core::eval::Value;

/// `Buf[T, N]` — `N` the value-in-type argument — the spec `Store`, and a second state sort
/// `Other`. `body` follows.
pub(crate) fn program(ns: &str, body: &str) -> String {
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
  end

  sort Other
    entity other(w: Int64)
  end
{body}
end
"#
    )
}

/// A carrier `name` providing `Store` at `state`; its `peek` answers `s.v + offset`, so the
/// answer names the provider that ran.
pub(crate) fn provider(name: &str, state: &str, offset: i64) -> String {
    format!(
        r#"
  sort {name}
    provides Store[State = {state}]
    operation peek(s: {state}) -> Int64 = s.v + {offset}
  end
"#
    )
}

/// `Store` at `Other`, answering 99 — the provider no `Buf` may reach.
pub(crate) const OTHER_IMPL: &str = r#"
  sort OtherImpl
    provides Store[State = Other]
    operation peek(s: Other) -> Int64 = 99
  end
"#;

const N3: &str = "Buf[T = Int64, N = 3]";
const N4: &str = "Buf[T = Int64, N = 4]";

/// The providers at `N = 3` (answers `v + 30`) and at `N = 4` (answers `v + 40`).
pub(crate) fn by_value() -> String {
    format!("{}{}", provider("C3", N3, 30), provider("C4", N4, 40))
}

/// Load `src` and call `ns.go()`, which must run to an `Int64`.
fn run_go(ns: &str, src: &str) -> i64 {
    let mut interp = interp_for(src);
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` must run to an Int64: {other:?}"),
    }
}

/// `program(ns, body)` with `go() = {go}` appended, run.
fn answers(ns: &str, body: &str, go: &str) -> i64 {
    run_go(
        ns,
        &program(ns, &format!("{body}\n  operation go() -> Int64 = {go}")),
    )
}

fn load_errors(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

// ── the dispatch goal ─────────────────────────────────────────────────────────────────

/// THE TICKET'S FIRST CALL: the argument's type holds `N = 3` and the one provider is at
/// `N = 3`.
#[test]
fn the_ticket_call_dispatches_to_its_provider() {
    let body = format!(
        "{}\n  operation use(s: {N3}) -> Int64 = Store.peek(s)",
        provider("C3", N3, 30)
    );
    assert_eq!(answers("wiwbhtm.call", &body, "use(buf(v: 7))"), 37);
}

/// THE VALUE DECIDES: two providers that differ ONLY in `N`, and each call reaches the one
/// at its own value. A goal that dropped `State` could not tell them apart.
#[test]
fn two_providers_are_told_apart_by_the_value() {
    let body = format!(
        "{}\n  operation use3(s: {N3}) -> Int64 = Store.peek(s)\n  \
         operation use4(s: {N4}) -> Int64 = Store.peek(s)",
        by_value()
    );
    assert_eq!(answers("wiwbhtm.by_value3", &body, "use3(buf(v: 1))"), 31);
    assert_eq!(answers("wiwbhtm.by_value4", &body, "use4(buf(v: 1))"), 41);
}

/// NO PROVIDER: refused naming the carrier and the binding, as the ground twin is — not the
/// "missing `requires`" the abstract reading produced.
#[test]
fn with_no_provider_the_refusal_names_the_carrier() {
    let src = program(
        "wiwbhtm.none",
        &format!("  operation use(s: {N3}) -> Int64 = Store.peek(s)"),
    );
    let errs = load_errors(&src);
    assert_refused_naming(
        &errs,
        &["`wiwbhtm.none.Buf` provides no `wiwbhtm.none.Store`", "N = 3"],
        "a value-in-type call with no provider",
    );
    assert!(
        !errs.iter().any(|e| e.contains("covering abstract type parameter")),
        "`State` is bound — to a type holding a value — so nothing is abstract; got {errs:#?}"
    );
}

/// THE VARIABLES INSIDE THE BINDING ARE RESOLVED before it is lowered. A bracket with a hole
/// binds `State` to `Buf[T = ?t, N = 4]` and leaves `?t` to the argument; read as σ stored
/// it, the goal kept `?t`, the provider at `Buf[T = Int64]` was refused on it, and the
/// generic `Gen` ran (55). The bracket-free call is the control: it reaches `Carrier` either
/// way.
#[test]
fn a_bracket_with_a_hole_reaches_the_specific_provider() {
    let body = format!(
        "{}\n  sort Gen\n    sort X = ?\n    provides Store[State = X]\n    \
         operation peek(s: X) -> Int64 = 55\n  end\n  \
         operation holed(s: {N4}) -> Int64 = Store.peek[State = Buf[T = ?, N = 4]](s)\n  \
         operation plain(s: {N4}) -> Int64 = Store.peek(s)",
        provider("Carrier", "Buf[T = Int64]", 0)
    );
    assert_eq!(answers("wiwbhtm.hole", &body, "holed(buf(v: 7))"), 7);
    assert_eq!(answers("wiwbhtm.hole_plain", &body, "plain(buf(v: 7))"), 7);
}

// ── a call-site selection ─────────────────────────────────────────────────────────────

/// Two providers at the SAME value, `C3a` (+30) and `C3b` (+35), so only a bracket decides.
fn two_at_three() -> String {
    format!("{}{}", provider("C3a", N3, 30), provider("C3b", N3, 35))
}

/// A BRACKET SELECTS at the value — `selection_goals` forms the same goal — and without it
/// the same call is refused as ambiguous, which is what makes the 36 the bracket's.
#[test]
fn a_bracket_selects_the_provider_at_the_value() {
    let body = format!(
        "{}\n  operation use(s: {N3}) -> Int64 = Store.peek[Store = C3b](s)",
        two_at_three()
    );
    assert_eq!(answers("wiwbhtm.bracket", &body, "use(buf(v: 1))"), 36);
    let unselected = program(
        "wiwbhtm.bracket_none",
        &format!(
            "{}\n  operation use(s: {N3}) -> Int64 = Store.peek(s)",
            two_at_three()
        ),
    );
    assert_refused_naming(
        &load_errors(&unselected),
        &["ambiguous dispatch", "C3a", "C3b"],
        "two providers at N = 3 and no bracket",
    );
}

/// … and a bracket naming the provider at ANOTHER value is refused.
#[test]
fn a_bracket_at_another_value_is_refused() {
    let src = program(
        "wiwbhtm.bracket_bad",
        &format!(
            "{}\n  operation use(s: {N3}) -> Int64 = Store.peek[Store = C4](s)",
            by_value()
        ),
    );
    assert_refused_naming(
        &load_errors(&src),
        &["C4 provides", "not at the bindings this call"],
        "a bracket selecting the provider at N = 4 for a call at N = 3",
    );
}

// ── the defer-match ───────────────────────────────────────────────────────────────────

/// `User requires Store[State = {req}]`; its `via` calls `Store.peek` on an argument of
/// type `arg`.
fn requiring_user(req: &str, arg: &str) -> String {
    format!(
        "\n  sort User\n    requires Store[State = {req}]\n    \
         operation via(s: {arg}) -> Int64 = Store.peek(s)\n  end\n"
    )
}

/// THE TICKET'S SECOND CALL: the requirement is at `Other`, the argument a `Buf` at `N = 4`,
/// so the call must NOT defer to that requirement — it reaches the `Buf` provider (`N`
/// left open there). Ran `OtherImpl.peek` on the `Buf` (99).
#[test]
fn the_ticket_defer_case_reaches_the_buf_provider() {
    let body = format!(
        "{}{OTHER_IMPL}{}",
        provider("Carrier", "Buf[T = Int64]", 0),
        requiring_user("Other", N4)
    );
    assert_eq!(answers("wiwbhtm.defer", &body, "User.via(buf(v: 7))"), 7);
}

/// A REQUIREMENT AT ANOTHER VALUE is no cover either: `N = 3` required, the call at `N = 4`
/// reaches the provider at `N = 4`. Ran the `N = 3` provider on it (31).
#[test]
fn a_requirement_at_another_value_is_no_cover() {
    let body = format!("{}{}", by_value(), requiring_user(N3, N4));
    assert_eq!(answers("wiwbhtm.req_other", &body, "User.via(buf(v: 1))"), 41);
}

/// A REQUIREMENT AT THE CALL'S OWN VALUE still covers it, and the call runs THROUGH it:
/// two providers at `N = 4` (`C4a` +40, `C4b` +45), so the inner `Store.peek` could not
/// dispatch on its own — the bracket on `User.via` picks the requirement's supplier, and only
/// a deferral to that requirement can answer 46.
#[test]
fn a_requirement_at_the_same_value_still_covers() {
    let body = format!(
        "{}{}{}{}",
        provider("C3", N3, 30),
        provider("C4a", N4, 40),
        provider("C4b", N4, 45),
        requiring_user(N4, N4)
    );
    assert_eq!(
        answers("wiwbhtm.req_same", &body, "User.via[Store = C4b](buf(v: 1))"),
        46
    );
}

// ── the op-scoped licence ─────────────────────────────────────────────────────────────

/// `use[S]` declares `requires Store[State = S]` and calls `Store.peek` on a `Buf` of type
/// `arg` — another element. Only `OtherImpl` provides `Store`.
fn op_scoped(ns: &str, arg: &str) -> Vec<String> {
    load_errors(&program(
        ns,
        &format!(
            "{OTHER_IMPL}\n  operation use[S](s: S, b: {arg}) -> Int64 requires Store[State = S] = \
             Store.peek(b)\n  operation go() -> Int64 = use(other(1), buf(v: 7))"
        ),
    ))
}

/// THE REQUIREMENT IS OVER `S`, NOT OVER THE `Buf`, so it licenses nothing and the call is
/// refused as its typed twin is. With the carrier dropped the licence went "blind" and the
/// program ran `OtherImpl.peek` on the `Buf` (99).
#[test]
fn an_op_scoped_requirement_over_another_element_licenses_nothing() {
    assert_refused_naming(
        &op_scoped("wiwbhtm.op_value", N3),
        &["`wiwbhtm.op_value.Buf` provides no `wiwbhtm.op_value.Store`", "N = 3"],
        "an op-scoped requirement over S, the call on a Buf at N = 3",
    );
}

/// THE TYPED TWIN, refused the same way. Passes either way by design.
#[test]
fn an_op_scoped_requirement_over_another_element_licenses_nothing_typed() {
    assert_refused_naming(
        &op_scoped("wiwbhtm.op_typed", "Buf[T = Int64, N = Bool]"),
        &["`wiwbhtm.op_typed.Buf` provides no `wiwbhtm.op_typed.Store`"],
        "an op-scoped requirement over S, the call on a Buf at N = Bool",
    );
}

// ── an effect row carrying a value (the WI-325 walk) ──────────────────────────────────

/// `Src` has no provider, and `go` calls `Src.val` on `s: Src[E = {row}]` under `{clause}` —
/// a sort-level `requires`, an op-scoped one, or none.
///
/// A LOAD VERDICT, not a run, because nothing here CAN run: with no provider there is no
/// `Src` value to pass, and with one the call takes the abstract-receiver route before the
/// dispatch these rows are about. What is measured is the typer's verdict on the call — the
/// thing the abstract reading got wrong — held against the term-carried twin's.
fn effect_row_program(ns: &str, row: &str, clause: &str) -> String {
    let (sort_clause, op_clause, op_params) = match clause {
        "sort" => ("\n    requires Src[E = R]", "", ""),
        "op" => ("", " requires Src[E = R2]", "[R2]"),
        _ => ("", "", ""),
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Modify, Cell, Error, EmptyStream}}

  sort Src
    effects E = ?
    operation val(s: Self) -> Int64 effects s.E
  end

  sort User
    effects R = ?{sort_clause}
    operation go{op_params}(c: Cell[V = Int64], s: Src[E = {{{row}}}]) -> Int64 effects {{{row}}}{op_clause} = Src.val(s)
  end
end
"#
    )
}

fn assert_loads(src: &str, why: &str) {
    let errs = load_errors(src);
    assert!(errs.is_empty(), "{why}: must load, got {errs:#?}");
}

/// A ROW CARRYING A VALUE (`{Modify[c]}` — the `c` rides as an occurrence) is as concrete as a
/// ground row. Read abstract, the call was refused "missing `requires Src[E = …]`" — here
/// with no `requires` at all (on both builds before this ticket), and with the sort's or the
/// operation's own `requires Src[E = R]` once the defer-match stopped covering it vacuously.
#[test]
fn an_effect_row_carrying_a_value_is_not_read_abstract() {
    for clause in ["none", "sort", "op"] {
        let ns = format!("wiwbhtm.row_value_{clause}");
        assert_loads(
            &effect_row_program(&ns, "Modify[c]", clause),
            &format!("a row carrying `c`, clause {clause}"),
        );
    }
}

/// THE TERM-CARRIED TWIN, a ground row. Passes either way by design.
#[test]
fn an_effect_row_carrying_a_value_is_not_read_abstract_ground() {
    for clause in ["none", "sort", "op"] {
        let ns = format!("wiwbhtm.row_ground_{clause}");
        assert_loads(
            &effect_row_program(&ns, "Error[EmptyStream]", clause),
            &format!("a ground row, clause {clause}"),
        );
    }
}

// ── a callee's requirement ────────────────────────────────────────────────────────────

/// `User requires Store[State = S]` and `via(s: S)`: the call `User.via(b)` must supply
/// `Store` at the argument's type.
#[test]
fn a_callees_requirement_is_supplied_at_the_value() {
    let body = format!(
        "{}\n  sort User\n    sort S = ?\n    requires Store[State = S]\n    \
         operation via(s: S) -> Int64 = Store.peek(s)\n  end\n  \
         operation run3(b: {N3}) -> Int64 = User.via(b)\n  \
         operation run4(b: {N4}) -> Int64 = User.via(b)",
        by_value()
    );
    assert_eq!(answers("wiwbhtm.supply3", &body, "run3(buf(v: 1))"), 31);
    assert_eq!(answers("wiwbhtm.supply4", &body, "run4(buf(v: 1))"), 41);
}

/// THE SAME REQUIREMENT, the argument typed `User[S = …]` and the parameter the sort at its
/// own parameters: the unifier binds `User.S` from the argument's binding, so the supply sees
/// the value. Was refused "element `State = User.S` is unconstrained" on both builds.
///
/// The parameter was written `u: User` — the bare sort, which inside its own definition meant
/// this instance — until proposal 070 (WI-20261001-80ZV8) made the bare name the sort at `?`,
/// any instance; `Self` is this instance, written.
#[test]
fn a_self_parameter_binds_the_value_in_type() {
    let body = format!(
        "{}\n  sort User\n    sort S = ?\n    requires Store[State = S]\n    \
         entity user(s: S)\n    \
         operation via(u: Self) -> Int64 =\n      match u\n        case user(s) -> Store.peek(s)\n  \
         end\n  \
         operation run3(u: User[S = {N3}]) -> Int64 = User.via(u)\n  \
         operation run4(u: User[S = {N4}]) -> Int64 = User.via(u)",
        by_value()
    );
    assert_eq!(
        answers("wiwbhtm.bare3", &body, "run3(user(buf(v: 1)))"),
        31
    );
    assert_eq!(
        answers("wiwbhtm.bare4", &body, "run4(user(buf(v: 1)))"),
        41
    );
}

/// `Holder[S]` and `first(h: Holder) -> S`, read back under an annotation at `N = {ann}`.
fn holder_body(ann: &str) -> String {
    format!(
        "\n  sort Holder\n    sort S = ?\n    entity holder(s: S)\n    \
         operation first(h: Self) -> S =\n      match h\n        case holder(s) -> s\n  \
         end\n  \
         operation read(h: Holder[S = {N3}]) -> Int64 =\n    \
         let b: Buf[T = Int64, N = {ann}] = Holder.first(h)\n    b.v"
    )
}

/// THROUGH THE BARE SORT the result type is the argument's `S` — so an annotation at another
/// value is refused naming both types, as its typed twin always was. It LOADED and ran (7):
/// `S` was never bound, and the annotation checked against a free variable.
#[test]
fn a_wrong_annotation_through_a_bare_sort_parameter_is_refused() {
    let errs = load_errors(&program("wiwbhtm.holder_bad", &holder_body("4")));
    assert_refused_naming(
        &errs,
        &["expected Buf[T = Int64, N = 4], got Buf[T = Int64, N = 3]"],
        "an N = 4 annotation over an N = 3 value",
    );
}

/// THE MATCHING ANNOTATION runs. Passes either way by design — a free `S` accepted it too.
#[test]
fn a_matching_annotation_through_a_bare_sort_parameter_runs() {
    assert_eq!(
        answers(
            "wiwbhtm.holder_ok",
            &holder_body("3"),
            "read(holder(buf(v: 7)))"
        ),
        7
    );
}

// ── a receiver's own arguments ────────────────────────────────────────────────────────

/// WI-20260828-EKWDC's `Pairer`, with a value-in-type parameter `N` beside the two it
/// already had: its `requires Tagger[T = Src]` names a parameter its `provides Stream`
/// head does not, so only the RECEIVER'S arguments can instantiate it. `Heavy` provides
/// `Tagger`, `Light` does not, and `BufTagger` provides it at a value-in-type. `ops` follows.
fn receiver_program(ns: &str, ops: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, Option, Pair, Stream}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Tagger
    sort T = ?
    operation tagOf(x: T) -> Int64
  end

  sort Heavy
    entity heavy(k: Int64)
    provides Tagger[T = Heavy]
    operation tagOf(h: Heavy) -> Int64 =
      match h
        case heavy(k) -> k
  end

  sort Light
    entity light(k: Int64)
  end

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort BufTagger
    provides Tagger[T = Buf[T = Int64, N = 3]]
    operation tagOf(h: Buf[T = Int64, N = 3]) -> Int64 = 5
  end

  sort Pairer
    sort Src = ?
    sort Out = ?
    sort N = ?
    requires Tagger[T = Src]
    entity pairer(item: Src, out: Out)
    provides Stream[T = Out, E = {{}}]
    operation splitFirst(p: Self) -> Option[Pair[A = Out, B = Stream[T = Out, E = {{}}]]] =
      match p
        case pairer(_, o) -> some(pair(o, rest()))
    operation rest() -> List[T = Out] = []
  end
{ops}
end
"#
    )
}

/// `w(p: {receiver})` splits a `Pairer` and returns its `out`; `go` passes `pairer({item},
/// 42)`.
fn split_receiver(receiver: &str, item: &str) -> String {
    format!(
        r#"
  operation w(p: {receiver}) -> Int64 =
    match Stream.splitFirst(p)
      case some(pair(v, _)) -> v
      case none() -> 0

  operation go() -> Int64 = w(pairer({item}, 42))
"#
    )
}

/// THE RECEIVER'S TYPE HOLDS A VALUE, and its `Src = Heavy` still reaches the carrier's
/// requirement: the dispatched `Pairer.splitFirst` runs. Was refused `unresolved:
/// Tagger[T = …Pairer.Src]`, the requirement asked about the declaration's parameter.
#[test]
fn a_receivers_arguments_reach_the_carriers_requirement() {
    let ops = split_receiver("Pairer[Src = Heavy, Out = Int64, N = 3]", "heavy(7)");
    assert_eq!(
        run_go("wiwbhtm.recv", &receiver_program("wiwbhtm.recv", &ops)),
        42
    );
}

/// THE GROUND TWIN. Passes either way by design — it never took the occurrence carrier.
#[test]
fn a_receivers_arguments_reach_the_carriers_requirement_ground() {
    let ops = split_receiver("Pairer[Src = Heavy, Out = Int64]", "heavy(7)");
    assert_eq!(
        run_go(
            "wiwbhtm.recv_ground",
            &receiver_program("wiwbhtm.recv_ground", &ops)
        ),
        42
    );
}

/// THE CONTROL: the lowered argument PINS `Src`. At `Light`, which provides no `Tagger`, the
/// call is refused naming the receiver's own `Light` — a lowering that handed back a wildcard
/// would let `Heavy`'s provision answer, and a dropped one names `Pairer.Src`.
#[test]
fn a_receivers_argument_is_not_a_wildcard() {
    let ns = "wiwbhtm.recv_light";
    let ops = split_receiver("Pairer[Src = Light, Out = Int64, N = 3]", "light(7)");
    assert_refused_naming(
        &load_errors(&receiver_program(ns, &ops)),
        &["unresolved: wiwbhtm.recv_light.Tagger[T = wiwbhtm.recv_light.Light]"],
        "a receiver at Src = Light",
    );
}

/// AN ENTITY-CARRIED RECEIVER TYPE keeps its arguments: `mkp(b)`'s type is `Pairer[Src = S,
/// Out = Int64]` instantiated at an `S` holding a value, which `fn_value` rebuilds as an
/// entity spine. Its arguments were ALL dropped — `Src` too — and the call refused naming
/// `Pairer.Src`.
#[test]
fn an_entity_carried_receiver_type_keeps_its_arguments() {
    let ns = "wiwbhtm.recv_entity";
    let ops = r#"
  operation mkp[S](s: S) -> Pairer[Src = S, Out = Int64] requires Tagger[T = S] = pairer(s, 42)

  operation w(b: Buf[T = Int64, N = 3]) -> Int64 =
    match Stream.splitFirst(mkp(b))
      case some(pair(v, _)) -> v
      case none() -> 0

  operation go() -> Int64 = w(buf(v: 7))
"#;
    assert_eq!(run_go(ns, &receiver_program(ns, ops)), 42);
}
