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
//! ## The five halves, and what fails when each is backed out
//!
//! MEASURED with the tree restored between runs and every back-out patched by a script
//! that ASSERTS its pattern matched exactly once — a back-out that silently no-ops
//! reports "no failures", which is indistinguishable from a control that measures
//! nothing.
//!
//!   * **The `Term::Ref` projection rung** (`Loader::try_contract_projection`, gated on
//!     `Loader::in_op_contract_clause`) — resolves `x.E` in a contract clause through the
//!     type ladder's own classifier. Backed out, no fixture here LOADS at all
//!     (`unresolved name 'x.E'`): **4 rows**.
//!   * **The `ExprCarried` stop in `wrap_places_as_var_ref`** — WI-552 canonicalizes a
//!     contract goal's parameter refs to `var_ref`, and it was descending INTO the
//!     projection, so the requires copy stored `ExprCarried(var_ref(pick.x), E)` where
//!     the parameter-type copy one line up stored `ExprCarried(Ref(pick.x), E)`. The
//!     eliminator keys on the `Ref`, so the requires copy eliminated to itself. **2
//!     rows**, both to `None` — eval never sees a dictionary.
//!   * **The δ-grounding in `resolve_bridge_requirements`** (`requirement-channel.md`
//!     §10 item 4's site) — **2 rows**.
//!   * **The δ-grounding in `build_op_scoped_dicts`** — **1 row**:
//!     [`a_call_that_grounds_the_projection_itself_needs_no_caller_requirement`], which
//!     is REFUSED without it. Note what that row is for: this δ is not a second SUPPLIER
//!     (the bridge answers first on every path reachable from a query, so backing it out
//!     alone moved nothing until that row existed) — it is what lets the refusal below
//!     tell a projection that GROUNDS HERE from one that cannot.
//!   * **The `caller_covers` refusal in `build_op_scoped_dicts`** — **1 row**:
//!     [`a_projection_the_caller_cannot_ground_is_refused_at_load_not_at_eval`].
//!   * **The `Unresolvable` guard in `resolve_bridge_requirements`** — **1 row**:
//!     [`a_projection_requirement_forwards_when_the_caller_declares_it`], which does not
//!     merely fail, it PANICS.
//!
//! [`a_constant_requirement_does_not_track_the_argument`],
//! [`without_the_requirement_the_body_has_no_dictionary_at_all`] and
//! [`a_dotted_name_whose_head_is_no_value_place_is_still_unresolved`] pass under ALL SIX
//! by design — the first two describe the fixture (they are what the acceptance's numbers
//! are read against) and the third is the arm the rung declines.
//!
//! ## What this ticket does NOT deliver
//!
//! FORWARDING A PROJECTION-CARRIED DICTIONARY THROUGH A CALLER THAT DOES NOT DECLARE IT.
//! The caller must repeat the requirement (`operation outer(b: Box) requires Desc[T =
//! b.E]`); without it the call is refused, loudly and at load. Making it inferable means
//! matching the callee's `pick.x` neutral against the caller's `outer.b` one, which needs
//! WI-459's receiver RE-KEYING before the ζ identity check can answer — see the
//! `caller_covers` comment for why the gate is deliberately coarse until then.
//!
//! THE RULE-BODY `require[Desc[T = p.E]]` BRACKET. Still refused, by WI-20260909-51W18's
//! drop rule ("`p.E` … names neither a sort nor one of `Desc`'s own type parameters") —
//! that is S8CBV's gate (1), and the attribution-by-projection-root work it feeds.

use anthill_core::eval::Value;

/// `Red` answers 7 and `Blue` answers 9 through `Desc`; `Box` is the parameterized
/// carrier whose element type a projection names.
///
/// `Desc.tag()` is NULLARY and BODY-LESS on purpose — see the file header. Nullary so no
/// argument can value-direct it, body-less so an absent dictionary is observable as `[]`
/// rather than as a default.
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
const PROJ: &str = "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()\n";

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
        "  operation pick(x: Box) -> Int64 requires Desc[T = Red] = Desc.tag()\n";
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
fn without_the_requirement_the_body_has_no_dictionary_at_all() {
    // THE OTHER HALF OF THE CONTROL, and the reason the spec op is BODY-LESS: with no
    // `requires`, `Desc.tag()` has no instance and no default, so the call answers
    // NOTHING. That `[]` is what says every number above arrived through the
    // requirement channel rather than through the spec's own body.
    //
    // PASSES EITHER WAY BY DESIGN — it describes the fixture, not this ticket's change.
    const NO_REQ: &str = "  operation pick(x: Box) -> Int64 = Desc.tag()\n";
    assert_eq!(
        answer("test.s8cbv.none.r", NO_REQ, "pick(box(v: red()), ?r)"),
        None,
    );
    assert_eq!(
        answer("test.s8cbv.none.b", NO_REQ, "pick(box(v: blue()), ?r)"),
        None,
    );
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
        "  operation z(x: Box) -> Int64 requires Desc[T = Zork.E] = Desc.tag()\n",
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
        "  operation z2(x: Box) -> Int64 requires Desc[T = x.v.E] = Desc.tag()\n",
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
    const FWD: &str = "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()\n  \
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
    const BARE: &str = "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()\n  \
                        operation outer(b: Box) -> Int64 = pick(b)\n";
    let errs = refusal(&fixture("test.s8cbv.bare", BARE));
    assert!(
        errs.contains("a projection this call does not ground")
            && errs.contains("declares no matching `requires` to forward"),
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
        "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()\n  \
         operation outer() -> Int64 = pick(box(v: red()))\n";
    assert_eq!(
        answer("test.s8cbv.grounded", GROUNDED, "outer(?r)"),
        Some(7),
    );
}
