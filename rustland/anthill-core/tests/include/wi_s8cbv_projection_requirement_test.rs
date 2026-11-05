//! WI-20260909-S8CBV — A REQUIREMENT MAY BE WRITTEN AT A PATH-DEPENDENT PROJECTION.
//!
//! `operation pick(x: Box) requires Desc[T = x.E]` names the `Desc` instance of the
//! ELEMENT of whatever `Box` this call was handed — not a fixed sort. Measured
//! 2026-09-09, before this ticket: it reported `unresolved name 'x.E'`, while
//! `operation h(x: Box, e: x.E)` and `operation k(x: Box) -> x.E` — the same projection,
//! the same signature, one position over — both LOADED. The requirement channel was the
//! only type position that could not resolve one.
//!
//! ## Why a BODY-LESS spec op, and why the fixture would otherwise measure nothing
//!
//! A spec op with a DEFAULT BODY answers that default whenever no dictionary arrives, so
//! every row below would pass with the `requires` deleted and the file would measure the
//! default rather than the channel. MEASURED on this very fixture: with `Desc.tag()`
//! declared `= 1`, all of `requires Desc[T = Red]`, `requires Desc[T = Blue]` and NO
//! `requires` answered `1`. Body-less, the same three answer `7`, `9` and `[]` — the
//! `[]` is what says the dictionary is the ONLY channel here.
//!
//! ## The control that separates a PROJECTION from a CONSTANT
//!
//! [`a_projection_requirement_tracks_its_own_argument`] runs ONE operation at TWO call
//! sites and gets 7 and 9. On its own that could be value dispatch, so
//! [`a_constant_requirement_does_not_track_the_argument`] runs the identical pair
//! against `requires Desc[T = Red]` and gets 7 and 7. Same body, same calls, same spec
//! op; only the bracket differs, and only the projection tracks the argument.
//!
//! ## The seven halves, and what fails when each is backed out
//!
//! MEASURED with the tree restored between runs and every back-out patched by a script
//! that ASSERTS its pattern matched exactly once — a back-out that silently no-ops
//! reports "no failures", which is indistinguishable from a control that measures
//! nothing.
//!
//! | backed out | rows |
//! |---|---|
//! | the `Term::Ref` projection rung (`Loader::try_contract_projection`) | **7** |
//! | the `ExprCarried` stop in `wrap_places_as_var_ref` | **6** |
//! | δ-grounding in `resolve_bridge_requirements` | **3** |
//! | δ-grounding in `build_op_scoped_dicts` | **3** |
//! | the `caller_covers` refusal | **2** |
//! | the EXACT comparison (reverted to spec-base + "has a projection") | **1** |
//! | the bridge's `Unresolvable` guard | **2**, both PANICS |
//!
//!   * **The rung** resolves `x.E` in a `requires` clause through the type ladder's own
//!     classifier — asked with the WI-428 rigid-type-projection route DISABLED, so every
//!     non-value head still falls to `remap_symbol_strict` exactly as before. Backed out,
//!     no fixture here LOADS (`unresolved name 'x.E'`).
//!   * **The `ExprCarried` stop**: WI-552 canonicalizes a contract goal's parameter refs
//!     to `var_ref` and was descending INTO the projection, so the requires copy stored
//!     `ExprCarried(var_ref(pick.x), E)` where the parameter-type copy one line up stored
//!     `ExprCarried(Ref(pick.x), E)`. The eliminator keys on the `Ref`.
//!   * **The two δs** are the same rule at two readers — the bridge (a rule body calling
//!     an operation, `requirement-channel.md` §10 item 4) and the typed call site. δ runs
//!     BEFORE σ at both: `x` is a parameter, not a type variable, so a substitution walks
//!     straight past the projection.
//!   * **`caller_covers` + the EXACT comparison** are one guard measured twice, because
//!     the coarse version of it is not merely weaker — it is WRONG. See
//!     [`a_caller_requirement_at_a_different_receiver_does_not_cover_this_call`].
//!
//! [`a_constant_requirement_does_not_track_the_argument`],
//! [`without_the_requirement_nothing_can_run_the_call`] and
//! [`a_dotted_name_whose_head_is_no_value_place_is_still_unresolved`] pass under ALL SEVEN
//! by design — the first two describe the fixture (they are what the acceptance's numbers
//! are read against) and the third is the arm the rung declines.
//!
//! ## Two narrowings whose control is the CORPUS, not a row here
//!
//! Both restore prior behaviour rather than add any, so the thing that measures them is
//! the 6754-test suite, and a row here could only restate it:
//!
//!   * `in_op_contract_clause` covers `requires` and NOT `ensures` — an `ensures` goal is
//!     a predicate over values, whose dotted uppercase-tailed arguments are entity names,
//!     not projections;
//!   * the two REFUSALS ask `value_contains_expr_carried`, not `value_contains_projection`
//!     — the latter is also true of a `RigidTypeProjection` (`P.Key`), writable in a
//!     `requires` chain since WI-428, and each refusal justifies itself as "a shape no
//!     program could write before this ticket".
//!
//! ## What this ticket does NOT deliver
//!
//! INFERRING the caller's requirement. A caller that forwards must declare the same
//! requirement at the same receiver; one that declares nothing, or declares it at a
//! DIFFERENT receiver, is refused at load. Both are rows below.
//!
//! THE ATTRIBUTION BY PROJECTION ROOT — keying WHICH dictionary a `require` means on the
//! projection's root rather than on the bound SORT. That is the ticket's own acceptance
//! and it is untouched; gate (1), the rule-body `require[Desc[T = p.E]]` bracket, IS
//! delivered and has its own section at the foot of this file.

use anthill_core::eval::Value;

/// `Red` answers 7 and `Blue` answers 9 through `Desc`; `Box` is the parameterized
/// carrier whose element type a projection names.
///
/// `Desc.tag()` is NULLARY and BODY-LESS on purpose — see the file header. Nullary so no
/// argument can value-direct it, body-less so an absent dictionary is observable — as a
/// refused call in an operation body, as an UNDECIDED row in a rule body — rather than as
/// a default.
fn fixture(ns: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation tag() -> Int64
  end

  sort Red
    import anthill.prelude.Int64
    entity red
    provides Desc[T = Red]
    operation tag() -> Int64 = 7
  end

  sort Blue
    import anthill.prelude.Int64
    entity blue
    provides Desc[T = Blue]
    operation tag() -> Int64 = 9
  end

  sort Box
    sort E = ?
    entity box(v: E)
  end

{tail}end
"#
    )
}

/// The single DEFINITE Int of a solution list, or `None` for anything else — an empty
/// list (no dictionary reached the body), an indefinite residual, or more than one.
fn one_definite(got: &[(Value, bool)]) -> Option<i64> {
    match got {
        [(Value::Int(i), true)] => Some(*i),
        _ => None,
    }
}

fn answer(ns: &str, decl: &str, query: &str) -> Option<i64> {
    let src = fixture(ns, &format!("{decl}  rule answer(?r) :- {query}\n"));
    let mut kb = crate::common::load_kb_with(&src);
    one_definite(&crate::common::query_unary(
        &mut kb,
        &format!("{ns}.answer"),
    ))
}

/// `pick`'s requirement is written at the PROJECTION `x.E`, so it names a different
/// `Desc` instance per call. One declaration, two call sites, two answers.
const PROJ: &str = "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag[T = x.E]()\n";

#[test]
fn a_projection_requirement_tracks_its_own_argument() {
    // THE ACCEPTANCE for the operation half. Before this ticket the declaration did not
    // LOAD (`unresolved name 'x.E'`), so neither row existed.
    //
    // BACK-OUTS that turn these red — each measured with a patch that asserts it applied:
    //   * the `Term::Ref` projection rung (`Loader::try_contract_projection`): the source
    //     no longer LOADS at all, `unresolved name 'x.E'`. Both rows.
    //   * the `ExprCarried` stop in `wrap_places_as_var_ref`: it loads, and both rows go
    //     to `None` — the receiver is stored as `var_ref(pick.x)`, which the eliminator
    //     (keyed on a `Ref`) cannot match, so no dictionary is ever built and eval dies
    //     `__req_desc not bound in caller frame`.
    //   * the δ-grounding in `resolve_bridge_requirements`: both rows go to `None` for
    //     the same reason one layer down — σ alone cannot reach a projection.
    assert_eq!(
        answer("test.s8cbv.proj.r", PROJ, "pick(box(v: red()), ?r)"),
        Some(7),
        "`x.E` is `Red` at this call, so `Desc`'s `Red` instance answers",
    );
    assert_eq!(
        answer("test.s8cbv.proj.b", PROJ, "pick(box(v: blue()), ?r)"),
        Some(9),
        "`x.E` is `Blue` at THIS call — same operation, different instance",
    );
}

#[test]
fn a_constant_requirement_does_not_track_the_argument() {
    // THE CONTROL THAT MAKES THE ROW ABOVE MEAN SOMETHING. Identical fixture, identical
    // calls, identical body — only the bracket is a SORT instead of a projection, and
    // both calls now answer the same number. Without this row, 7-and-9 above is equally
    // consistent with ordinary value dispatch on `red()` / `blue()`.
    //
    // PASSES EITHER WAY BY DESIGN: nothing in this ticket touches a concrete bracket.
    // It is here to bound what the acceptance is allowed to claim, not to detect a
    // regression in the projection path.
    const CONST_REQ: &str =
        "  operation pick(x: Box) -> Int64 requires Desc[T = Red] = Desc.tag[T = Red]()\n";
    assert_eq!(
        answer("test.s8cbv.const.r", CONST_REQ, "pick(box(v: red()), ?r)"),
        Some(7),
    );
    assert_eq!(
        answer("test.s8cbv.const.b", CONST_REQ, "pick(box(v: blue()), ?r)"),
        Some(7),
        "a CONSTANT bracket ignores the argument — this is the row the projection's \
         `9` is read against",
    );
}

#[test]
fn without_the_requirement_nothing_can_run_the_call() {
    // THE OTHER HALF OF THE CONTROL, and the reason the spec op is BODY-LESS: with no
    // `requires`, `Desc.tag()` has no instance and no default, so nothing can run the
    // call. That is what says every number above arrived through the requirement channel
    // rather than through the spec's own body. The program used to load and answer
    // NOTHING (`[]`); WI-20260909-M8QWJ moved that from eval to LOAD, refusing the call.
    //
    // PASSES EITHER WAY BY DESIGN — it describes the fixture, not this ticket's change.
    const NO_REQ: &str = "  operation pick(x: Box) -> Int64 = Desc.tag()\n";
    for (ns, query) in [
        ("test.s8cbv.none.r", "pick(box(v: red()), ?r)"),
        ("test.s8cbv.none.b", "pick(box(v: blue()), ?r)"),
    ] {
        let errs = refusal(&fixture(ns, &format!("{NO_REQ}  rule answer(?r) :- {query}\n")));
        assert!(
            errs.contains(&format!("a call of `{ns}.Desc.tag` that nothing can run")),
            "got:\n{errs}"
        );
    }
}

fn refusal(src: &str) -> String {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a refusal; it loaded clean:\n{src}"))
        .join("\n")
}

#[test]
fn a_dotted_name_whose_head_is_no_value_place_is_still_unresolved() {
    // THE RUNG IS NOT A BLANKET ADMISSION. `try_expr_carried_projection_segments` answers
    // `None` for any head that is not a VALUE PLACE, so a typo keeps the diagnostic it
    // always had rather than becoming a silently-formed projection off a name that
    // denotes nothing.
    //
    // BACK-OUT: passes either way — this is the arm the rung declines, and declining is
    // what routes it to the resolver. It is here so a future widening of the rung
    // (dropping the value-head gate) is caught.
    let errs = refusal(&fixture(
        "test.s8cbv.neg",
        "  operation z(x: Box) -> Int64 requires Desc[T = Zork.E] = Desc.tag[T = Zork.E]()\n",
    ));
    assert!(errs.contains("unresolved name 'Zork.E'"), "got:\n{errs}");
}

#[test]
fn a_compound_receiver_is_refused_by_name_rather_than_mis_lowered() {
    // A COMPOUND receiver (`x.v.E`) classifies as a projection and needs the
    // `TypeNode::ExprCarried` Node carrier, which a TERM slot cannot hold. Refused with
    // its own message — loud over silent — rather than dropped back to the resolver,
    // which would blame the NAME for a shape this position recognized perfectly well.
    //
    // BACK-OUT of the `TypeChild::Node` arm: the row reports `unresolved name 'x.v.E'`
    // instead — still a refusal, but one that says the author misspelled something.
    let errs = refusal(&fixture(
        "test.s8cbv.compound",
        "  operation z2(x: Box) -> Int64 requires Desc[T = x.v.E] = Desc.tag[T = x.v.E]()\n",
    ));
    assert!(errs.contains("COMPOUND receiver"), "got:\n{errs}");
}

#[test]
fn a_projection_requirement_forwards_when_the_caller_declares_it() {
    // AN INTERMEDIATE OPERATION that carries the SAME projection-carried requirement can
    // pass it on: inside `outer`, `b.E` is abstract and `pick`'s slot cannot be ground at
    // that call, so it is `outer`'s own slot that supplies it.
    //
    // BACK-OUT of the `caller_covers` gate in `build_op_scoped_dicts`: this row is
    // REFUSED at load — the gate is what separates it from the row below, and without it
    // the refusal swallows the working program too.
    const FWD: &str = "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag[T = x.E]()\n  \
                       operation outer(b: Box) -> Int64 requires Desc[T = b.E] = pick(b)\n";
    assert_eq!(
        answer("test.s8cbv.fwd", FWD, "outer(box(v: red()), ?r)"),
        Some(7),
    );
}

#[test]
fn a_projection_the_caller_cannot_ground_is_refused_at_load_not_at_eval() {
    // THE ROW THIS TICKET OWES ITS OWN CHANGE. Making `requires Desc[T = x.E]` LOADABLE
    // also made this program loadable, and it is one no call can supply: `outer` hands
    // `pick` its own abstract parameter and declares nothing to forward.
    //
    // MEASURED before the refusal: it loaded CLEAN and died `DeferToRequirement:
    // __req_desc not bound in caller frame`, raised as `EvalError::Internal`, tripping
    // `bridge_op_to_eval`'s `debug_assert` — a debug-build ABORT from a program that
    // type-checked. Loud and located beats clean-then-abort.
    //
    // BACK-OUT of the refusal: this row does not merely fail, it ABORTS the test binary.
    const BARE: &str = "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag[T = x.E]()\n  \
                        operation outer(b: Box) -> Int64 = pick(b)\n";
    let errs = refusal(&fixture("test.s8cbv.bare", BARE));
    assert!(
        errs.contains("a projection this call does not ground")
            && errs.contains("no `requires` of the caller names that same receiver"),
        "got:\n{errs}"
    );
}

#[test]
fn a_call_that_grounds_the_projection_itself_needs_no_caller_requirement() {
    // THE ROW THAT SAYS THE REFUSAL IS ABOUT GROUNDING AND NOT ABOUT THE CALLER. `outer`
    // declares NO `requires` — the same as the refused program above — but it names a
    // CONCRETE receiver, so δ answers `Red` right here and there is nothing left to
    // forward. Caller-coverage is never consulted.
    //
    // THIS IS THE ROW THE δ IN `build_op_scoped_dicts` EXISTS FOR, and it is what makes
    // that δ measurable: backed out, the projection survives, the `caller_covers` gate
    // sees an unground-able carrier at a caller with an empty chain, and this WORKING
    // program is REFUSED. Without this row the δ backs out with zero failures and reads
    // like dead code.
    const GROUNDED: &str =
        "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag[T = x.E]()\n  \
         operation outer() -> Int64 = pick(box(v: red()))\n";
    assert_eq!(
        answer("test.s8cbv.grounded", GROUNDED, "outer(?r)"),
        Some(7),
    );
}

#[test]
fn a_caller_requirement_at_a_different_receiver_does_not_cover_this_call() {
    // THE SILENT-WRONG-ANSWER ROW, and the reason the coverage test compares the WHOLE
    // re-keyed spec rather than the spec base.
    //
    // `outer` declares the requirement at `c` and calls `pick(b)`. The caller holds ONE
    // `__req_desc` slot and the callee reads whatever is in it, so a gate that cannot
    // tell `b.E` from `c.E` hands `b`'s call `c`'s dictionary. MEASURED with a
    // base-only gate: this program LOADED and answered **9** — `c` is a `Box` of `Blue`
    // — where `b` is a `Box` of `Red` and `7` is the only correct answer. A clean load
    // and a definite wrong answer.
    //
    // BACK-OUT of the re-key (`arg_syms` → `None` in `build_op_scoped_dicts`' δ): the
    // two sides are neutrals keyed to different scopes, nothing compares equal, and
    // [`a_projection_requirement_forwards_when_the_caller_declares_it`] — the program
    // that SHOULD forward — is refused instead. The re-key is what makes the comparison
    // mean anything in either direction.
    const CROSS: &str = "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag[T = x.E]()\n  \
                         operation outer(b: Box, c: Box) -> Int64 requires Desc[T = c.E] = pick(b)\n";
    let errs = refusal(&fixture("test.s8cbv.cross", CROSS));
    assert!(
        errs.contains("no `requires` of the caller names that same receiver"),
        "got:\n{errs}"
    );
}

#[test]
fn the_same_call_with_the_requirement_at_the_matching_receiver_answers() {
    // THE CONTROL FOR THE ROW ABOVE, one character apart: `c.E` becomes `b.E` and the
    // identical two-parameter clause loads and answers `7` — `b`'s instance, not `c`'s.
    // Same shape, same arity, same call; only the receiver in the caller's bracket
    // differs, and that is exactly what the exact comparison reads.
    const MATCHED: &str = "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag[T = x.E]()\n  \
                           operation outer(b: Box, c: Box) -> Int64 requires Desc[T = b.E] = pick(b)\n";
    assert_eq!(
        answer(
            "test.s8cbv.matched",
            MATCHED,
            "outer(box(v: red()), box(v: blue()), ?r)"
        ),
        Some(7),
        "`b` is a `Box` of `Red`; `c`'s `Blue` must not be what answers",
    );
}

// ════════════════════════════════════════════════════════════════════════════════════
// GATE (1) — A RULE'S REQUIREMENT AT A HEAD COLUMN'S ELEMENT
//
// Everything above is the OPERATION channel (`operation f(x: Box) requires Desc[T = x.E]`).
// This half is the RULE one. It was `?d = require[Desc[T = p.E]]` in a clause body,
// projecting off the clause's own sigil-free typed head parameter — the loader's projection
// rung (`try_require_spec_projection`), the anchor route (`written_projection_anchor`), the
// runtime δ (`requirement_projection_member`), a static member check, a suspend arm, an early
// routing past the witness scans and a tri-state report, each backed out on its own, no two
// failing the same rows (measured 2026-09-13).
//
// Proposal 060.1 §5 removed `require[X]`. A rule declares the requirement at its head's
// introducer, the element named by the column's type rather than projected off its
// variable — `anchored[E](p: Box[E = E], ?r) :- require d: Desc[T = E], d.tag(?r)` — and the
// element is the citation's to fix, as any type parameter of a clause is: `Red` at
// `box(v: red())`, `Blue` at `box(v: blue())`. `tag()` takes no argument, so the call names
// the requirement it reads. The rows below are that spelling, each asserting what its
// `require[…]` row asserted where the language still says it; the projection's own
// machinery was measured on the removed form and is not reached now. What the language says
// otherwise is at each row: a member `Box` cannot declare is refused by the column's type, a
// projection off a spec-bound parameter (`p: A` beside `Desc[A]`) has no spelling, and two
// requirements are told apart by their names.
// ════════════════════════════════════════════════════════════════════════════════════

/// The rule-body twin of [`PROJ`]: the requirement at the element of `p`'s type.
/// `d.tag(?r)` is nullary, so nothing in it can value-dispatch, and body-less, so no
/// default can stand in for the dictionary (file header).
const PROJ_RULE: &str =
    "  rule anchored[E](p: Box[E = E], ?r) :- require d: Desc[T = E], d.tag(?r)\n";

/// THE ACCEPTANCE FOR GATE (1): one clause, two call sites, two instances — `7` and `9` reach
/// `?r` only by dispatching `tag()` through the dictionary at the element the citation fixes.
#[test]
fn a_rule_body_require_may_project_off_a_typed_head_parameter() {
    assert_eq!(
        answer("test.s8cbv.rule.r", PROJ_RULE, "anchored(box(v: red()), ?r)"),
        Some(7),
        "the element is `Red` at this call, so `Desc`'s `Red` instance answers",
    );
    assert_eq!(
        answer("test.s8cbv.rule.b", PROJ_RULE, "anchored(box(v: blue()), ?r)"),
        Some(9),
        "the element is `Blue` at THIS call — same clause, different instance",
    );
}

#[test]
fn a_rule_with_no_require_has_no_dictionary_at_all() {
    // THE CONTROL THE NUMBERS ABOVE ARE READ AGAINST. `Desc.tag()` is body-less, so with no
    // requirement in the clause there is no instance and no default: the call is UNREDUCED
    // (proposal 068 §2) and the clause's one row is UNDECIDED, naming that cause. Every `7` /
    // `9` above therefore arrived through the dictionary rather than through the spec.
    // PASSES EITHER WAY BY DESIGN — it describes the fixture, not gate (1).
    const NO_REQ: &str = "  rule anchored(p: Box, ?r) :- Desc.tag(?r)\n";
    for (ns, query) in [
        ("test.s8cbv.rule.none.r", "anchored(box(v: red()), ?r)"),
        ("test.s8cbv.rule.none.b", "anchored(box(v: blue()), ?r)"),
    ] {
        assert_eq!(
            undecided_causes(ns, NO_REQ, query),
            vec![vec![anthill_core::kb::resolve::UnknownCause::Unreduced]],
            "{query}: one UNDECIDED row",
        );
    }
}

/// The undecided causes of each row of `<ns>.answer` ([`crate::common::undecided_causes`]).
fn undecided_causes(
    ns: &str,
    decl: &str,
    query: &str,
) -> Vec<Vec<anthill_core::kb::resolve::UnknownCause>> {
    let src = fixture(ns, &format!("{decl}  rule answer(?r) :- {query}\n"));
    let mut kb = crate::common::load_kb_with(&src);
    crate::common::undecided_causes(&mut kb, &format!("{ns}.answer"))
}

/// The raw solution rows of `{ns}.answer`, for the three-valued distinctions
/// [`one_definite`] flattens: `[]` is a goal that FAILED, one INDEFINITE row is a goal
/// that SUSPENDED and residualized.
fn rows(ns: &str, decl: &str, query: &str) -> Vec<(Value, bool)> {
    let src = fixture(ns, &format!("{decl}  rule answer(?r) :- {query}\n"));
    let mut kb = crate::common::load_kb_with(&src);
    crate::common::query_unary(&mut kb, &format!("{ns}.answer"))
}

/// A MEMBER THE COLUMN'S SORT CANNOT DECLARE IS A LOAD ERROR, named with what it does declare;
/// so is a member of a sort that declares none. (They were `require[Desc[T = p.Zork]]` under
/// `p: Box` and `require[Desc[T = p.E]]` under `p: Red`, refused by the projection's static
/// member check, which had been residualizing silently; the column's type says it now.)
#[test]
fn a_member_the_roots_bound_cannot_declare_is_a_LOAD_ERROR() {
    let errs = refusal(&fixture(
        "test.s8cbv.rule.nomember",
        "  rule anchored[E](p: Box[Zork = E], ?r) :- require d: Desc[T = E], d.tag(?r)\n",
    ));
    assert!(
        errs.contains("no type parameter named 'Zork'") && errs.contains("declares type parameter(s) E"),
        "expected a refusal naming the member and what `Box` does declare; got:\n{errs}",
    );
    let errs = refusal(&fixture(
        "test.s8cbv.rule.noparams",
        "  rule anchored[E](p: Red[E = E], ?r) :- require d: Desc[T = E], d.tag(?r)\n",
    ));
    assert!(
        errs.contains("declares no type parameters"),
        "expected a refusal saying `Red` declares no type parameters; got:\n{errs}",
    );
}

/// AN ELEMENT NOT YET BOUND DELAYS: at the moment the body is entered `p` may not be bound,
/// and nothing here binds it, so the guard's read suspends and the clause residualizes —
/// loud at the drain rather than quietly deciding the clause false (WI-067).
#[test]
fn an_unbound_carrier_suspends_too() {
    let got = rows("test.s8cbv.rule.unbound", PROJ_RULE, "anchored(?any, ?r)");
    assert!(matches!(got.as_slice(), [(_, false)]), "expected one INDEFINITE row, got {got:?}");
}

/// [`fixture`] with a carrier-bearing operation added to the spec: `describe(x: T)` has a
/// spec-carrier parameter, so a call to it is answered at its own argument.
fn fixture_with_witness(ns: &str, tail: &str) -> String {
    fixture(ns, tail).replace(
        "operation tag() -> Int64\n  end",
        "operation tag() -> Int64\n    operation describe(x: T) -> Int64 = 90\n  end",
    )
}

/// The raw solution rows of `<ns>.answer` for a source built WHOLE.
fn rows_src(src: &str) -> Vec<(Value, bool)> {
    let ns = src
        .lines()
        .next()
        .and_then(|l| l.strip_prefix("namespace "))
        .expect("source must open with a namespace line")
        .trim()
        .to_owned();
    let mut kb = crate::common::load_kb_with(src);
    crate::common::query_unary(&mut kb, &format!("{ns}.answer"))
}

/// A REQUIREMENT AT THE ELEMENT BESIDE A CALL AT ANOTHER ARGUMENT: the call at `?q`, a `Blue`,
/// is answered at its own carrier (`90`, `describe`'s default, which `Blue` keeps), definitely.
/// The row was a projected `require[Desc[T = p.E]]` beside the call, which took the witness
/// path and suspended for ever until the projection was routed first; the guard is at its
/// introducer and covers no call at another carrier.
#[test]
fn a_projected_bracket_beside_a_witness_call_still_anchors() {
    let got = rows_src(&fixture_with_witness(
        "test.s8cbv.witness.proj",
        "  rule r[E, Q](p: Box[E = E], ?q: Q, ?res) :- Desc[T = E], Desc[T = Q], Desc.describe(?q, ?res)\n  \
         rule answer(?r) :- r(box(v: red()), blue(), ?r)\n",
    ));
    assert!(matches!(got.as_slice(), [(Value::Int(90), true)]), "expected a DEFINITE 90, got {got:?}");
}

/// THE CONTROL: the same call with no requirement answers the same definite `90`. PASSES
/// EITHER WAY BY DESIGN. (It wrote `require[Desc[T = Red]]`, a concrete instance, which a call
/// at another argument never read.)
#[test]
fn the_control_a_concrete_bracket_beside_a_witness_call_is_unchanged() {
    let got = rows_src(&fixture_with_witness(
        "test.s8cbv.witness.concrete",
        "  rule r[Q](p: Box, ?q: Q, ?res) :- Desc[T = Q], Desc.describe(?q, ?res)\n  \
         rule answer(?r) :- r(box(v: red()), blue(), ?r)\n",
    ));
    assert!(matches!(got.as_slice(), [(Value::Int(90), true)]), "expected a DEFINITE 90, got {got:?}");
}

/// A MEMBER THE COLUMN'S SORT CANNOT DECLARE IS REFUSED BESIDE A CARRIER-BEARING CALL too — the
/// projection's static check was unreachable whenever a covered call existed, and loaded
/// clean; the column's type is read whatever the body holds.
#[test]
fn a_bogus_member_beside_a_witness_call_is_still_refused() {
    let errs = refusal(&fixture_with_witness(
        "test.s8cbv.witness.bogus",
        "  rule r[E](p: Box[Zork = E], ?q, ?res) :- Desc[T = E], Desc.describe(?q, ?res)\n  \
         rule answer(?r) :- r(box(v: red()), blue(), ?r)\n",
    ));
    assert!(errs.contains("no type parameter named 'Zork'"), "got:\n{errs}");
}

// ════════════════════════════════════════════════════════════════════════════════════
// THE ATTRIBUTION — WHICH dictionary a requirement means.
//
// The ticket's own acceptance: `rule two(x: Box, y: Box, ?d1, ?d2) :- ?d1 = require[Desc[T =
// x.E]], ?d2 = require[Desc[T = y.E]]` bound TWO dictionaries, each holding its own root's
// element, read by the `impl` each named. Proposal 060.1 §5 removed the form and every column
// a dictionary rides; the two requirements are at two introducers now, the elements of `x`'s
// and `y`'s types, and the NAME is what a nullary call reads one of them by. So the rows read
// the numbers each dictionary gives, and the requirements' order and the argument order are
// varied as the `impl` rows varied them.
// ════════════════════════════════════════════════════════════════════════════════════

/// `two`'s first and second answers, at `args`, with the requirements written `requires`.
fn two_answers(ns: &str, requires: &str, args: &str) -> (Option<i64>, Option<i64>) {
    let src = fixture(
        ns,
        &format!(
            "  rule two[E, F](x: Box[E = E], y: Box[E = F], ?r1, ?r2) :- {requires}, \
             d1.tag(?r1), d2.tag(?r2)\n  \
             rule first(?r) :- two({args}, ?r, ?)\n  \
             rule second(?r) :- two({args}, ?, ?r)\n"
        ),
    );
    let mut kb = crate::common::load_kb_with(&src);
    let mut one = |rel: &str| one_definite(&crate::common::query_unary(&mut kb, &format!("{ns}.{rel}")));
    (one("first"), one("second"))
}

const BOTH: &str = "require d1: Desc[T = E], require d2: Desc[T = F]";

/// THE ACCEPTANCE — two elements of ONE sort, two requirements, two dictionaries, each its own
/// element's, asserted BY VALUE: `(7, 9)` over a red and a blue box, and with the colours
/// exchanged at the call, `(9, 7)`.
#[test]
fn two_projected_requires_bind_two_dictionaries_at_their_own_roots() {
    assert_eq!(
        two_answers("test.s8cbv.two", BOTH, "box(v: red()), box(v: blue())"),
        (Some(7), Some(9)),
        "`x`'s element is `Red` and `y`'s is `Blue`, so the two requirements name two instances"
    );
    assert_eq!(
        two_answers("test.s8cbv.swap", BOTH, "box(v: blue()), box(v: red())"),
        (Some(9), Some(7)),
        "the attribution follows the element's value, not the clause's text"
    );
}

/// THE DISCRIMINATOR — the requirements' ORDER swapped, the arguments held fixed: keyed by the
/// parameter each is at, `d1` is still `x`'s element's.
#[test]
fn which_dictionary_a_require_means_is_keyed_on_its_root_not_its_position() {
    assert_eq!(
        two_answers(
            "test.s8cbv.reorder",
            "require d2: Desc[T = F], require d1: Desc[T = E]",
            "box(v: red()), box(v: blue())",
        ),
        (Some(7), Some(9)),
        "`d1` names `E`, `x`'s element, because its guard says so, wherever it is written"
    );
}

/// THE BACK-OUT THE ROWS ABOVE ARE READ AGAINST — with the requirements deleted, the two
/// nullary calls name no instance and are UNREDUCED: the clause's row is undecided, naming that
/// cause, where the rows above answer numbers. PASSES EITHER WAY BY DESIGN; it is what makes the
/// others evidence.
#[test]
fn with_the_requires_gone_neither_slot_is_a_dictionary() {
    assert_eq!(
        undecided_causes(
            "test.s8cbv.noreq",
            "  rule two(x: Box, y: Box, ?r1, ?r2) :- Desc.tag(?r1), Desc.tag(?r2)\n",
            "two(box(v: red()), box(v: blue()), ?r, ?)",
        ),
        vec![vec![
            anthill_core::kb::resolve::UnknownCause::Unreduced,
            anthill_core::kb::resolve::UnknownCause::Unreduced
        ]],
    );
}

/// TWO ELEMENTS THAT AGREE NAME ONE INSTANCE: `x` and `y` are different parameters bound to
/// boxes of the SAME colour, and both requirements land on that colour's provider, `(7, 7)`.
#[test]
fn two_roots_that_agree_name_one_instance() {
    assert_eq!(
        two_answers("test.s8cbv.agree", BOTH, "box(v: red()), box(v: red())"),
        (Some(7), Some(7)),
        "both elements are `Red`, so both requirements name `Red`'s provision"
    );
}
