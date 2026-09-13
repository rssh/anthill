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
//! [`without_the_requirement_the_body_has_no_dictionary_at_all`] and
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
        "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()\n  \
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
    const CROSS: &str = "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()\n  \
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
    const MATCHED: &str = "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()\n  \
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
// GATE (1) — THE RULE-BODY BRACKET
//
// Everything above is the OPERATION channel (`operation f(x: Box) requires Desc[T = x.E]`).
// This half is the RULE one: `?d = require[Desc[T = p.E]]` in a clause body, projecting
// off the clause's own §2.1 sigil-free typed head parameter.
//
// It was refused until now by WI-20260909-51W18's drop rule, whose two rungs are both
// about NAMES — "does this spell a sort?", "is it the spec's own type parameter?" — so a
// projection read as neither and was reported as a typo. `Loader::try_require_spec_
// projection` is the third rung, asked FIRST for that reason.
//
// THE TWO HALVES ARE NOT ONE MECHANISM, and the difference is the receiver. An
// operation's `x.E` carries `Ref(x)` — a parameter symbol — and is δ-eliminated against
// the argument at the CALL. A clause's `p.E` carries a logic VARIABLE, closed to a De
// Bruijn slot with the rest of the rule and opened fresh per firing, so the member is
// projected off the carrier's CARRIED TYPE at the RESOLVER
// (`requirement_projection_member` + `projected_arg_types`). `path-dependent-types.md` §4
// names the split: a flexible projection "arises only where a receiver is a logic
// variable, i.e. in rule bodies, never in operation signatures".
//
// ## THE SEVEN AXES AND WHAT EACH BACK-OUT COSTS
//
// The last two are REPAIRS TO WHAT THIS TICKET SHIPPED, found by `/code-review` after
// the first commit and measured before they were believed. Both were the same defect
// seen twice: `anchor_grounding` is consulted LAST, after four witness scans, so every
// clause carrying a projected bracket AND a covered spec-op call took the witness path
// — the bracket silently ignored, the member check unreachable, the resolver's δ
// rewriting the witness call's own argument as though it were the projection root.
//
// MEASURED 2026-09-13, each back-out applied by a script that ASSERTS its pattern matched
// exactly once (`scratchpad/gate1-backout/backout.py`), the tree restored by checksum
// between runs. No two axes fail the same set:
//
// | backed out | rows | which |
// |---|---|---|
// | the LOADER RUNG (`try_require_spec_projection`) | **4** | all of them — nothing LOADS, with WI-20260909-51W18's drop-rule message verbatim, the pre-ticket verdict |
// | the ANCHOR ROUTE (`written_projection_anchor`) | **3** | the `Box`-rooted clauses do not LOAD: "head bound(s) — Box — provide no `Desc`", the `provides` scan asking about the ROOT where the question is about its ELEMENT |
// | the RUNTIME δ (`requirement_projection_member`) | **2** | both LOAD CLEAN and answer WRONGLY — the acceptance drops to no answer, and the spec-bound row stops delaying |
// | the STATIC MEMBER CHECK | **1** | [`a_member_the_roots_bound_cannot_declare_is_a_LOAD_ERROR`] — a member `Box` cannot declare goes back to loading clean and residualizing, with no diagnostic anywhere |
// | the SUSPEND ARM (`Suspend` → `DontFire`) | **2** | the two delay rows answer ZERO rows instead of one indefinite one — WI-067's silent drop |
// | the EARLY ROUTING (`spec_arg_has_projection`) | **2** | a projected bracket falls back to the WITNESS scans: [`a_projected_bracket_beside_a_witness_call_still_anchors`] returns to an INDEFINITE residual and [`a_bogus_member_beside_a_witness_call_is_still_refused`] to a CLEAN LOAD |
// | the TRI-STATE (`Reported` → `Dropped`) | **1** | [`a_refused_projection_is_reported_once_and_not_twice`] sees the rung's accurate error AND the misdiagnosis it replaces |
//
// THE δ AXIS IS WHY THE ACCEPTANCE IS TWO NUMBERS RATHER THAN A CLEAN LOAD: with δ gone
// the carrier type read at the fetch is the RECEIVER's own type rather than its member,
// `Box[E = Red]` matches no `Desc` provider, and the clause silently has no answers.
//
// THE STATIC-MEMBER AND SUSPEND AXES DRAW ONE LINE BETWEEN THEM, and it is the line
// `/code-review` found this file on the wrong side of. A member the bound sort STATICALLY
// cannot declare is a typo and refuses at LOAD; a member it declares that the carrier has
// not yet BOUND is a run-time condition and DELAYS. The first was residualizing silently
// (indistinguishable from the second), and the row that used to measure "suspends" was
// really measuring a typo — see [`a_member_the_roots_bound_cannot_declare_is_a_LOAD_ERROR`].
// ════════════════════════════════════════════════════════════════════════════════════

/// The rule-body twin of [`PROJ`]. `Desc.tag(?r)` is the covered call the weave threads
/// the fetched dictionary into; it is NULLARY, so nothing in it can value-dispatch, and
/// BODY-LESS, so no default can stand in for the dictionary (file header).
const PROJ_RULE: &str =
    "  rule anchored(p: Box, ?r) :- ?d = require[Desc[T = p.E]], Desc.tag(?r)\n";

#[test]
fn a_rule_body_require_may_project_off_a_typed_head_parameter() {
    // THE ACCEPTANCE FOR GATE (1), and the link the parked attempt could never observe:
    // that `?d` actually RECEIVES the fetched dictionary. The previous attempt verified
    // only that `fetch_dictionary` produced one — the `out` slot was a casualty of
    // WI-20260909-C7ANM (it walked to the carrier's value, `Ref(red)`, instead of the
    // clause variable), so nothing downstream of the fetch was measurable until C7ANM
    // landed. These two numbers are that link: `7` and `9` reach `?r` only by dispatching
    // `Desc.tag()` through the dictionary bound to `?d`.
    //
    // ONE CLAUSE, TWO CALL SITES, TWO INSTANCES — the same thing
    // [`a_projection_requirement_tracks_its_own_argument`] says one level up.
    //
    // FAILS UNDER THREE OF GATE (1)'s FIVE BACK-OUTS — the rung, the anchor route and the
    // runtime δ — each in a different way; the file header's table says which.
    assert_eq!(
        answer(
            "test.s8cbv.rule.r",
            PROJ_RULE,
            "anchored(box(v: red()), ?r)"
        ),
        Some(7),
        "`p.E` is `Red` at this call, so `Desc`'s `Red` instance answers",
    );
    assert_eq!(
        answer(
            "test.s8cbv.rule.b",
            PROJ_RULE,
            "anchored(box(v: blue()), ?r)"
        ),
        Some(9),
        "`p.E` is `Blue` at THIS call — same clause, different instance",
    );
}

#[test]
fn a_rule_with_no_require_has_no_dictionary_at_all() {
    // THE CONTROL THE NUMBERS ABOVE ARE READ AGAINST, and the rule-body twin of
    // [`without_the_requirement_the_body_has_no_dictionary_at_all`]. `Desc.tag()` is
    // body-less, so with no `require` in the clause there is no instance and no default:
    // the call answers NOTHING. Every `7` / `9` above therefore arrived through the
    // dictionary rather than through the spec.
    //
    // ZERO ROWS, not "no definite row", and the distinction is load-bearing twice over:
    // it is what says the clause FAILED rather than residualized, and it is the control
    // the two DELAY rows — [`an_unbound_carrier_suspends_too`] and
    // [`a_spec_bound_keeps_the_runtime_delay`] — read their single INDEFINITE row against.
    // Asserted on the raw rows for that reason: [`one_definite`] maps both shapes to
    // `None`, so it cannot tell a failed clause from a delayed one.
    //
    // PASSES EITHER WAY BY DESIGN — it describes the fixture, not gate (1).
    const NO_REQ: &str = "  rule anchored(p: Box, ?r) :- Desc.tag(?r)\n";
    assert!(
        rows("test.s8cbv.rule.none.r", NO_REQ, "anchored(box(v: red()), ?r)").is_empty(),
    );
    assert!(
        rows("test.s8cbv.rule.none.b", NO_REQ, "anchored(box(v: blue()), ?r)").is_empty(),
    );
}

#[test]
fn a_constant_bracket_under_the_same_head_is_refused_where_the_projection_is_admitted() {
    // THE ROOT IS THE ANCHOR AND ITS BOUND IS NOT TESTED FOR `provides` — the one rule
    // that separates a projected carrier from a direct one, driven by the pair.
    //
    // `require[Desc[T = Box]]` SAYS the carrier is `Box`, so `Box` must provide `Desc`,
    // and it does not: refused, naming `Box`. `require[Desc[T = p.E]]` says the carrier
    // is `Box`'s ELEMENT, about which `Box` says nothing at all — so the same head, the
    // same bound and the same spec are ADMITTED one row up.
    //
    // This is the control that makes the acceptance's admission mean something: without
    // the projection route, `anchor_grounding`'s `provides` scan is what the clause meets,
    // and it answers `Box` to a question about `Box`'s element.
    //
    // PASSES UNDER ALL FIVE BACK-OUTS BY DESIGN — it is a refusal that stands either way
    // (measured).
    // MEASURED: backing out the anchor route makes the acceptance row join this one,
    // refused with this very message, which is what says the two rows differ by the
    // PROJECTION and by nothing else.
    let errs = refusal(&fixture(
        "test.s8cbv.rule.constbound",
        "  rule anchored(p: Box, ?r) :- ?d = require[Desc[T = Box]], Desc.tag(?r)\n",
    ));
    assert!(
        errs.contains("provide no `Desc`"),
        "a bracket naming the BOUND must still be refused; got:\n{errs}",
    );
}

#[test]
fn a_projection_off_a_name_this_clause_does_not_bind_keeps_the_drop_rule_message() {
    // THE RUNG IS NOT A BLANKET ADMISSION — the rule-body twin of
    // [`a_dotted_name_whose_head_is_no_value_place_is_still_unresolved`].
    // `try_require_spec_projection` resolves its root in `rule_param_vars`, the §2.1
    // parameter map, and answers `None` for anything else — so a dotted name whose head
    // this clause does not bind falls to the two NAME rungs below it and keeps
    // WI-20260909-51W18's diagnostic, which is the one that names the author's typo.
    //
    // PASSES EITHER WAY BY DESIGN: this is the arm the rung declines. It is here so that
    // widening the rung (admitting any dotted name) is caught.
    let errs = refusal(&fixture(
        "test.s8cbv.rule.unbound",
        "  rule anchored(p: Box, ?r) :- ?d = require[Desc[T = q.E]], Desc.tag(?r)\n",
    ));
    assert!(
        errs.contains("names neither a sort nor"),
        "got:\n{errs}",
    );
}

/// The raw solution rows of `{ns}.answer`, for the three-valued distinctions
/// [`one_definite`] flattens: `[]` is a goal that FAILED, one INDEFINITE row is a goal
/// that SUSPENDED and residualized.
fn rows(ns: &str, decl: &str, query: &str) -> Vec<(Value, bool)> {
    let src = fixture(ns, &format!("{decl}  rule answer(?r) :- {query}\n"));
    let mut kb = crate::common::load_kb_with(&src);
    crate::common::query_unary(&mut kb, &format!("{ns}.answer"))
}

/// The raw solution rows of `<ns>.answer` for a source built WHOLE, where [`rows`]
/// composes the clause and the query itself.
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

fn is_one_residual(got: &[(Value, bool)]) -> bool {
    matches!(got, [(_, false)])
}

#[test]
fn a_member_the_roots_bound_cannot_declare_is_a_LOAD_ERROR() {
    // LOUD OVER SILENT, and this row exists because the first cut was silent. MEASURED by
    // `/code-review`: `require[Desc[T = p.Zork]]` under `p: Box` LOADED CLEAN and
    // residualized with no diagnostic — while the typo one character over,
    // `require[Desc[T = Zork]]` (a bogus SORT), is a load error. The rung that admits a
    // projection checks only that the last segment is Capitalized; the bound sort's
    // declared parameters were never asked.
    //
    // NOT COVERED BY THE SUSPEND RULE, and that is the distinction the pair below draws.
    // Suspending is justified by "the head variable may not be bound yet", which is a
    // RUN-TIME condition; a member `Box` statically cannot declare is not waiting for
    // anything, and delaying on it converts an author's typo into a residual nobody reads.
    let errs = refusal(&fixture(
        "test.s8cbv.rule.nomember",
        "  rule anchored(p: Box, ?r) :- ?d = require[Desc[T = p.Zork]], Desc.tag(?r)\n",
    ));
    assert!(
        errs.contains("Zork") && errs.contains("declares E"),
        "expected a refusal naming the member and what `Box` does declare; got:\n{errs}",
    );

    // THE OTHER HALF OF THE SAME RULE: a bound that declares NO parameters at all. `Red`
    // is a data sort with a bare `entity red`, so `p.E` can never resolve. Before this
    // check the row answered ONE INDEFINITE row (suspended) and was written up as WI-067
    // discipline — which it is not: [`an_unbound_carrier_suspends_too`] is the runtime
    // case, and this one is a static impossibility wearing its clothes.
    let errs = refusal(&fixture(
        "test.s8cbv.rule.noparams",
        "  rule anchored(p: Red, ?r) :- ?d = require[Desc[T = p.E]], Desc.tag(?r)\n",
    ));
    assert!(
        errs.contains("declares none"),
        "expected a refusal saying `Red` declares no type parameters; got:\n{errs}",
    );
}

#[test]
fn an_unbound_carrier_suspends_too() {
    // THE OTHER HALF OF THE SAME RULE, and the one the discipline exists for: at the
    // moment the body is entered `p` may simply not be bound yet. The goal delays and
    // rotates; nothing here ever binds it, so it residualizes and is loud at the drain
    // (WI-737's route) rather than quietly deciding the clause false.
    //
    // FAILS under the LOADER RUNG, the ANCHOR route and the SUSPEND arm. Under the first
    // two the clause does not load at all, so it is `load_kb_with` that panics rather than
    // this assertion; under the third it answers ZERO rows, the silent drop. It PASSES
    // under the δ back-out by design — with `p` unbound there is no carried type to
    // project from, so the goal suspends whether or not the member ever reaches it.
    let got = rows(
        "test.s8cbv.rule.unbound",
        "  rule anchored(p: Box, ?r) :- ?d = require[Desc[T = p.E]], Desc.tag(?r)\n",
        "anchored(?any, ?r)",
    );
    assert!(
        is_one_residual(&got),
        "expected one INDEFINITE row (suspended), got {got:?}",
    );
}

#[test]
fn a_spec_bound_keeps_the_runtime_delay() {
    // THE ONE SHAPE THAT STILL REACHES `projected_arg_types`' OWN `Suspend` ARM, and it
    // is here because adding the static check above took the other one away.
    //
    // [`a_member_the_roots_bound_cannot_declare_is_a_LOAD_ERROR`] is gated on the bound
    // being a DATA sort, because only there are the declared parameters the whole truth
    // (§8.4: nothing can be narrower than a data-sort bound). An INTRODUCER bound records
    // THE SPEC, which admits every provider — and a provider may declare members the spec
    // does not — so the check is skipped and the member is read at run time, off the
    // carrier's carried type. `Leaf` binds no `E`, so the goal SUSPENDS and the clause
    // residualizes; it does not decide false and drop the clause.
    //
    // BACK-OUT of that arm (`Suspend` → `DontFire`): this row goes from one INDEFINITE
    // row to ZERO rows — the silent drop WI-067 forbids. It is the only row that moves,
    // and without it the arm has no driver at all.
    let got = rows(
        "test.s8cbv.rule.specbound",
        "  rule anchored[A](p: A, ?r) :- Desc[A], ?d = require[Desc[T = p.E]], Desc.tag(?r)\n",
        "anchored(red(), ?r)",
    );
    assert!(
        is_one_residual(&got),
        "expected one INDEFINITE row (suspended), got {got:?}",
    );
}

/// [`fixture`] with a WITNESS-capable operation added to the spec: `describe(x: T)` has a
/// spec-carrier parameter, so a call to it grounds the requirement by the WITNESS path —
/// the path that runs before the anchor one.
fn fixture_with_witness(ns: &str, tail: &str) -> String {
    fixture(ns, tail).replace(
        "operation tag() -> Int64\n  end",
        "operation tag() -> Int64\n    operation describe(x: T) -> Int64 = 90\n  end",
    )
}

#[test]
fn a_projected_bracket_beside_a_witness_call_still_anchors() {
    // A PROJECTED BRACKET TAKES THE ANCHOR PATH, AND TAKES IT FIRST — the repair for a
    // defect this ticket SHIPPED and `/code-review` measured.
    //
    // `anchor_grounding` is consulted LAST, after four witness scans, so a clause with
    // both a projected bracket and a covered spec-op call took the witness path: the
    // requirement was grounded at the CALL's argument, the author's `p.E` was silently
    // ignored, and the resolver's δ then rewrote that argument as though it were the
    // projection root. MEASURED before the repair — the clause below answered
    // `[(Int(90), false)]`, INDEFINITE, suspending forever, where the concrete-bracket
    // twin answered a definite `90`. It loaded clean either way.
    //
    // BACK-OUT of the early routing (`spec_arg_has_projection` never true): this row goes
    // back to that indefinite residual, and
    // [`a_bogus_member_beside_a_witness_call_is_still_refused`] goes back to loading clean.
    let got = rows_src(&fixture_with_witness(
        "test.s8cbv.witness.proj",
        "  rule r(p: Box, ?q, ?res) :- ?d = require[Desc[T = p.E]], Desc.describe(?q, ?res)\n  \
         rule answer(?r) :- r(box(v: red()), blue(), ?r)\n",
    ));
    assert!(
        matches!(got.as_slice(), [(Value::Int(90), true)]),
        "expected a DEFINITE answer, got {got:?}",
    );
}

#[test]
fn the_control_a_concrete_bracket_beside_a_witness_call_is_unchanged() {
    // WHAT SAYS THE ROW ABOVE IS ABOUT THE PROJECTION and not about the witness path in
    // general: the same clause with a CONCRETE bracket answered a definite `90` both
    // before and after the repair. PASSES EITHER WAY BY DESIGN.
    let got = rows_src(&fixture_with_witness(
        "test.s8cbv.witness.concrete",
        "  rule r(p: Box, ?q, ?res) :- ?d = require[Desc[T = Red]], Desc.describe(?q, ?res)\n  \
         rule answer(?r) :- r(box(v: red()), blue(), ?r)\n",
    ));
    assert!(
        matches!(got.as_slice(), [(Value::Int(90), true)]),
        "expected a DEFINITE answer, got {got:?}",
    );
}

#[test]
fn a_bogus_member_beside_a_witness_call_is_still_refused() {
    // THE STATIC MEMBER CHECK REACHES A CLAUSE THAT HAS A WITNESS. It lives inside
    // `anchor_grounding`, so before the early routing above it was unreachable whenever
    // any covered call existed — MEASURED: `require[Desc[T = p.Zork]]` beside
    // `Desc.describe(...)` LOADED CLEAN and residualized, exactly the silent failure
    // [`a_member_the_roots_bound_cannot_declare_is_a_LOAD_ERROR`] was added to remove,
    // while its witness-free twin was refused. One check, two clauses, two verdicts.
    let errs = refusal(&fixture_with_witness(
        "test.s8cbv.witness.bogus",
        "  rule r(p: Box, ?q, ?res) :- ?d = require[Desc[T = p.Zork]], Desc.describe(?q, ?res)\n  \
         rule answer(?r) :- r(box(v: red()), blue(), ?r)\n",
    ));
    assert!(
        errs.contains("Zork") && errs.contains("declares E"),
        "got:\n{errs}",
    );
}

#[test]
fn a_refused_projection_is_reported_once_and_not_twice() {
    // ONE BINDING, ONE DIAGNOSTIC. The projection rung reports its own located error and
    // then has to tell its caller so — `SpecBindingLowering::Reported`, distinct from
    // `Dropped`. With a bare `Option` both callers ALSO ran `report_dropped_spec_binding`
    // and the author got the accurate message followed by the very misdiagnosis the rung
    // exists to prevent (`/code-review`).
    //
    // Driven through the AMBIGUITY refusal, which is the reachable `Reported` arm: a head
    // parameter named like a namespace makes `mylib.Thing` read two ways.
    let errs = refusal(
        "namespace mylib\n  import anthill.prelude.Int64\n  sort Thing\n    entity thing\n  end\n\
         \n  sort Desc\n    sort T = ?\n    operation tag() -> Int64\n  end\n\
         \n  sort Foo\n    entity foo\n  end\n\
         \n  rule r(mylib: Foo, ?res) :- ?d = require[Desc[T = mylib.Thing]], Desc.tag(?res)\nend\n",
    );
    assert!(
        errs.contains("reads two ways here"),
        "expected the ambiguity refusal; got:\n{errs}",
    );
    assert!(
        !errs.contains("names neither a sort nor"),
        "the drop rule must NOT speak over the rung's own error; got:\n{errs}",
    );
}
