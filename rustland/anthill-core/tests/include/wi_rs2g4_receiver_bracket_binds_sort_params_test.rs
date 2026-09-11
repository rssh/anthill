//! WI-20260911-RS2G4 — A CALL-SITE BRACKET **BINDS** THE ENCLOSING SORT'S TYPE
//! PARAMETERS, at the typer and at eval.
//!
//! 058 rule 1 (`docs/design/058-implementation.md` §2, and `call_bracket_scopes`' doc)
//! says a call-site bracket spans TWO scopes — the operation's own type parameters and
//! its enclosing sort's. The loader enforced only the COLLISION half, and said so in its
//! own message: `operation dom[T]()` inside `sort Box[T]` is refused because "a call-site
//! bracket binds BOTH scopes … so `Box.dom[T = …](…)` would have two targets"
//! (`wi840_named_requires_slot_test::a_type_param_colliding_with_its_enclosing_sorts_is_refused`,
//! unchanged by this ticket and the pin for that half). The BINDING half existed for the
//! CALLEE spelling only (WI-841) and for the typer only.
//!
//! FOUR THINGS WERE MISSING, each measured on the parent commit before it was built:
//!
//!  1. **The RECEIVER bracket was validated and then dropped** — a silent wrong answer,
//!     not a missing feature. `operation p8() -> Option[T = Letter] = Box[T = Int64].empty()`
//!     LOADED CLEAN: nothing else carried `T`, so the return's `T` was pinned by the
//!     EXPECTED type and the written `Int64` meant nothing. The name check fired
//!     (`Box[W = Int64]` was loud), which is what made the drop invisible.
//!  2. **A bracket VALUE naming a parametric sort BARE erased the element**, in BOTH
//!     spellings. `[T = List]` seeded `?T := Ref(List)`, and an argument's `List[T =
//!     Int64]` reached nothing.
//!  3. **The eval channel carried operation parameters only** (WI-272/WI-708), so a body
//!     read of the SORT's parameter dangled: `Box[T = Letter].selfType()` with `operation
//!     selfType() -> Type = Box[T = T]` evaluated to `Box[T = Box.T]`.
//!  4. **A bare SIBLING call inside a member lost the instance**: `viaSibling()`, whose
//!     body is the single call `selfType()`, dangled even once (3) was fixed — the call
//!     site says nothing about `T` because it MEANS "the instance I am running at".
//!
//! FIVE MECHANISMS, FIVE BACK-OUTS, MEASURED SEPARATELY — a single "all off" run credits
//! one site for another's rows. Each is a MUTATION (the site still runs, its answer is
//! discarded), never a deletion, so what is measured is the capability and not whether
//! the tree still builds. Counts are of this file's 16 rows.
//!
//! **(A) the receiver seeding off** — `seed_receiver_type_args` returns at entry:
//! **10 red, 6 green.** Red: [`a_receiver_bracket_pins_a_nullary_members_return`],
//! [`a_let_annotation_reads_the_receivers_binding`],
//! [`the_receiver_spelling_reads_as_the_callee_spelling`],
//! [`two_disagreeing_brackets_are_one_contradiction`],
//! [`both_parameters_of_a_two_parameter_sort_are_read`],
//! [`a_receiver_bracket_reaches_a_body_read_of_the_sorts_parameter`],
//! [`both_parameters_reach_a_two_parameter_members_body`],
//! [`a_nested_body_read_substitutes_at_depth`], [`the_two_channels_have_distinct_keys`],
//! [`a_bare_sibling_call_keeps_the_enclosing_instance`] — the last five because a receiver
//! bracket is what puts a value on the channel at all, so the eval rows have nothing to
//! read. Green: the two controls, the WI-708 control, the CALLEE-spelling body read, the
//! expanded-carrier pin, and — stated because it is a SURPRISE —
//! [`a_bare_parametric_bracket_value_no_longer_erases_the_inner_element`], whose RECEIVER
//! arm passes under (A) for the OPPOSITE reason: with the bracket ignored entirely the
//! ARGUMENT decides and the call is refused anyway. That row therefore isolates (B) and
//! (C), never (A).
//!
//! **(B) the bracket-value expansion off** — `expand_written_bracket_value` returns
//! `None`: **2 red**, [`a_bare_parametric_bracket_value_no_longer_erases_the_inner_element`]
//! and [`a_bracket_value_with_an_unwritten_slot_arrives_expanded`].
//!
//! **(C) the refining re-bind off** — `bind_or_refine_member_param` always takes the raw
//! `subst.bind`: **1 red**, [`a_bare_parametric_bracket_value_no_longer_erases_the_inner_element`].
//! (B) and (C) are each NECESSARY for that row and neither alone is sufficient: the
//! expansion mints the variable, the refining bind is what lets an argument reach it.
//! Both are named at the row.
//!
//! **(D) the eval channel's sort half off** — the `sort_params` loop in
//! `set_resolved_type_args` skipped: **6 red** —
//! [`a_receiver_bracket_reaches_a_body_read_of_the_sorts_parameter`],
//! [`the_callee_spelling_reaches_the_same_body_read`],
//! [`both_parameters_reach_a_two_parameter_members_body`],
//! [`a_nested_body_read_substitutes_at_depth`], [`the_two_channels_have_distinct_keys`],
//! and [`a_bare_sibling_call_keeps_the_enclosing_instance`] (which needs (D) to have
//! anything to inherit). Every TYPING row stays green, which is what says the two levels
//! are two mechanisms.
//!
//! **(E) the same-sort inheritance off** — `inherit_enclosing_sort_type_args` returns its
//! argument: **1 red**, [`a_bare_sibling_call_keeps_the_enclosing_instance`]. The five
//! direct eval rows stay green; that isolation is the point, since a bare sibling call is
//! the only shape whose value cannot come from the call site.
//!
//! CONTROLS, green under all five and stated at their sites:
//! [`an_argument_carried_pin_needs_no_bracket`],
//! [`a_bracket_contradicting_an_argument_stays_loud`],
//! [`the_wi708_operation_parameter_channel_is_unchanged`].
//!
//! WHAT THIS DELIVERY MAKES REACHABLE AND DOES NOT FIX — measured, not assumed, and NOT
//! a row here because the failure is an ABORT that would take the whole test binary with
//! it. A call-site bracket whose VALUE mentions the enclosing sort's own type parameter —
//! `Box.empty[T = Option[T = T]]()`, `[T = List[T = T]]`, `[T = Box[T = T]]` written
//! inside `sort Box[T]` — does not terminate: σ gets a binding whose `Ref(Box.T)` the
//! SortAlias chain resolves back to the very variable, `walk_type_deep` chases it, and the
//! loader overflows its stack. MEASURED AT THE PARENT COMMIT: the CALLEE spelling already
//! aborted there (since WI-841 gave it the sort scope), while the receiver spelling loaded
//! clean *because the bracket was dropped*. So this ticket adds no defect and removes no
//! defect; it gives the second spelling the first one's behaviour, crash included. The
//! occurs check at `bind_resolved` does not catch it because it is structural over
//! `Term::Var` and the cycle runs through a `Term::Ref` alias — making it alias-aware is a
//! change to the core unifier with its own census, not this ticket's.
//!
//! THE MOVED W6JH0 ROWS are in `wi_w6jh0_companion_receiver_bracket_test`, each rewritten
//! there with what moved and why; the largest is that a receiver bracket on a
//! NON-CONSTRUCTOR callee, which W6JH0 deliberately left alone, is now read.

use anthill_core::eval::Value;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{interp_for, try_load_kb_with};

/// The shared declarations. `Box[T]` is the one-parameter fixture; `Duo[A, B]` is the
/// two-parameter one, and it is not decoration — a one-parameter fixture cannot tell a
/// correct implementation from one that binds only the FIRST parameter.
const DECLS: &str = r#"
  import anthill.prelude.{Option, Int64, String, Bool, Type, List, Map}
  import anthill.prelude.Option.{none}
  import anthill.prelude.Map.{put, size}

  sort Letter
    entity la
    entity lb
  end

  sort Box[T]
    import anthill.prelude.{Option, Type, List}
    import anthill.prelude.Option.{none}
    entity box(v: T)
    operation empty() -> Option[T = T] = none()
    operation mine(b: Box) -> Box[T = T] = b
    operation mine2(b: Box) -> Option[T = T] = none()
  end

  sort Duo[A, B]
    import anthill.prelude.{Option, Type}
    import anthill.prelude.Option.{none}
    entity duo(x: A, y: B)
    operation pairOf() -> Option[T = Duo[A = A, B = B]] = none()
  end
"#;

fn load_errors(body: &str) -> Vec<String> {
    let src = format!("\nnamespace test.rs2g4\n{DECLS}\n{body}\nend\n");
    match try_load_kb_with(&src) {
        Ok(_) => Vec::new(),
        Err(es) => es.to_vec(),
    }
}

/// Strip the leading `<line>:<col>: ` so two spellings written at different columns can
/// be compared for the MESSAGE, which is what "one rule, two spellings" claims.
fn message_only(errs: Vec<String>) -> Vec<String> {
    errs.into_iter()
        .map(|e| e.split_once(": ").map(|(_, m)| m.to_string()).unwrap_or(e))
        .collect()
}

// ── TYPING ───────────────────────────────────────────────────────────────────────

/// THE TICKET'S HEADLINE ROW. `Box[T = Int64].empty()` in an `Option[T = Letter]`
/// position is a LOUD refusal naming both types, and the matching
/// `Box[T = Letter].empty()` loads. Before: the first loaded clean, because the bracket's
/// value was dropped and the EXPECTED type pinned `T` instead.
#[test]
fn a_receiver_bracket_pins_a_nullary_members_return() {
    let errs = load_errors("  operation p8() -> Option[T = Letter] = Box[T = Int64].empty()");
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(
        errs[0].contains("expected Option[T = Letter], got Option[T = Int64]"),
        "{errs:#?}"
    );

    assert_eq!(
        load_errors("  operation p8ok() -> Option[T = Letter] = Box[T = Letter].empty()"),
        Vec::<String>::new(),
        "the agreeing spelling must still load"
    );
}

/// …and the same pin reached through a `let` ANNOTATION rather than the return, which is
/// proposal 035's form (1) beside form (3). The value TYPES as the receiver says: the
/// agreeing annotation loads and the disagreeing one is refused AT THE LET.
#[test]
fn a_let_annotation_reads_the_receivers_binding() {
    let errs = load_errors(
        "  operation p9() -> Int64 =\n    \
         let v: Option[T = Int64] = Box[T = Letter].empty()\n    0",
    );
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains("v.annotation (let-binding)"), "{errs:#?}");
    assert!(
        errs[0].contains("expected Option[T = Int64], got Option[T = Letter]"),
        "{errs:#?}"
    );

    assert_eq!(
        load_errors(
            "  operation p9ok() -> Int64 =\n    \
             let v: Option[T = Letter] = Box[T = Letter].empty()\n    0",
        ),
        Vec::<String>::new(),
    );
}

/// ONE RULE, TWO SPELLINGS — the strongest row in the file. Proposal 035 lists the
/// receiver and the callee bracket as two ways of writing one thing, so it is not enough
/// that the receiver spelling now errors: it has to error IDENTICALLY, at the same site,
/// with the same bytes. Three callees whose diagnostics land in three DIFFERENT places
/// (`op-return`, `op-type-params`, `op-arg`), because agreement at one site could be a
/// coincidence.
#[test]
fn the_receiver_spelling_reads_as_the_callee_spelling() {
    // The two programs are written with the SAME operation name, so the messages are
    // comparable verbatim rather than through a rewrite that could paper over a
    // difference.
    for (recv, callee) in [
        (
            "  operation w() -> Option[T = Letter] = Box[T = Int64].empty()",
            "  operation w() -> Option[T = Letter] = Box.empty[T = Int64]()",
        ),
        (
            r#"  operation w() -> Int64 = Map[K = Bool, V = Bool].size(put(Map.empty(), "a", 1))"#,
            r#"  operation w() -> Int64 = Map.size[K = Bool, V = Bool](put(Map.empty(), "a", 1))"#,
        ),
        (
            r#"  operation w() -> Int64 = size(Map[V = Bool].put(Map.empty(), "a", 1))"#,
            r#"  operation w() -> Int64 = size(Map.put[V = Bool](Map.empty(), "a", 1))"#,
        ),
    ] {
        let r = message_only(load_errors(recv));
        let c = message_only(load_errors(callee));
        assert_eq!(r.len(), 1, "receiver spelling: {r:#?}\n{recv}");
        assert_eq!(r, c, "form (3) must read as the callee bracket:\n{recv}\n{callee}");
    }
}

/// TWO WRITTEN BRACKETS BINDING ONE PARAMETER DIFFERENTLY IS A CONTRADICTION, not a
/// precedence question — they bind the SAME variable now. One error, naming the parameter
/// and BOTH sources. Before: the receiver silently won and the arguments were checked
/// against its claim, so one of the two written bindings meant nothing.
#[test]
fn two_disagreeing_brackets_are_one_contradiction() {
    let errs = load_errors(
        "  operation t1() -> Option[T = Letter] = Box[T = Letter].empty[T = Int64]()",
    );
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(
        errs[0].contains("expected the receiver bracket's T = Letter")
            && errs[0].contains("got the callee bracket's T = Int64"),
        "the message must name the parameter and both sources: {errs:#?}"
    );

    // The AGREEING pair still loads — the control that keeps this from being "refuse the
    // two-bracket spelling".
    assert_eq!(
        load_errors(
            "  operation t2() -> Option[T = Letter] = Box[T = Letter].empty[T = Letter]()",
        ),
        Vec::<String>::new(),
    );

    // AS WRITTEN, not as expanded (`/code-review` finding). A bare `[T = List]` is
    // reported back as `List`, not as the `List[T = ?T]` the value expansion makes of it
    // — telling the author their `List` disagrees with `List[T = ?T]` would name a
    // variable this pass minted and they cannot see.
    let bare = load_errors(
        "  operation t3() -> Option[T = Letter] = Box[T = List].empty[T = Int64]()",
    );
    assert_eq!(bare.len(), 1, "{bare:#?}");
    assert!(
        bare[0].contains("the receiver bracket's T = List,"),
        "the written value, not the expansion: {bare:#?}"
    );
}

/// TWO-PARAMETER ARITY IS DRIVEN. `Duo[A = Letter, B = Int64].pairOf()` must read BOTH
/// bindings: a wrong `A` and a wrong `B` are each refused, and a correct pair loads. An
/// implementation that bound only the first parameter passes the `A` row and fails the
/// `B` row; one that bound only the last does the reverse. A one-parameter fixture cannot
/// separate either from a correct one.
#[test]
fn both_parameters_of_a_two_parameter_sort_are_read() {
    assert_eq!(
        load_errors(
            "  operation d0() -> Option[T = Duo[A = Letter, B = Int64]] = \
             Duo[A = Letter, B = Int64].pairOf()",
        ),
        Vec::<String>::new(),
        "the agreeing pair loads"
    );

    let wrong_a = load_errors(
        "  operation d1() -> Option[T = Duo[A = Int64, B = Int64]] = \
         Duo[A = Letter, B = Int64].pairOf()",
    );
    assert_eq!(wrong_a.len(), 1, "{wrong_a:#?}");
    assert!(
        wrong_a[0].contains("got Option[T = Duo[A = Letter, B = Int64]]"),
        "A is read: {wrong_a:#?}"
    );

    let wrong_b = load_errors(
        "  operation d2() -> Option[T = Duo[A = Letter, B = Letter]] = \
         Duo[A = Letter, B = Int64].pairOf()",
    );
    assert_eq!(wrong_b.len(), 1, "{wrong_b:#?}");
    assert!(
        wrong_b[0].contains("got Option[T = Duo[A = Letter, B = Int64]]"),
        "B is read: {wrong_b:#?}"
    );
}

/// A BRACKET VALUE NAMING A PARAMETRIC SORT BARE NO LONGER ERASES ITS ELEMENT, in either
/// spelling. `[T = List]` says "a list of something", and the something is a FRESH
/// variable an argument can pin — not an absent slot that width-ignoring unification
/// silently lets the context fill.
///
/// TWO BACK-OUTS, both named because each alone reddens this row and neither alone would
/// have delivered it: (B) the expansion, which mints the variable, and (C) the refining
/// re-bind, which is what lets the argument's `List[T = Int64]` reach it. The ticket's own
/// predicted mechanism was (B) alone — "the argument binds `?f := Int64`" — and MEASURING
/// it is what found (C): `unify_parameterized_with_sort_ref` RAW-binds the canonical
/// parameter, so the bracket's claim wins and the refinement is proved only in
/// `enforce_member_tie`'s scratch substitution and thrown away.
///
/// NOT A CONTROL FOR (A). Its RECEIVER arm passes with the receiver seeding backed out
/// too — for the opposite reason, since the bracket is then ignored entirely and the
/// argument decides. The (A) axis is measured by the ten rows the header names.
#[test]
fn a_bare_parametric_bracket_value_no_longer_erases_the_inner_element() {
    // The CONTROL: with no bracket at all, the argument's inner `Int64` always reached
    // the result. Green either way, and it is what says the rows below are about the
    // bracket rather than about `mine`.
    let control = load_errors(
        "  operation n1() -> Option[T = List[T = String]] = Box.mine2(box(v: [1]))",
    );
    assert_eq!(control.len(), 1, "{control:#?}");
    assert!(
        control[0].contains("got Option[T = List[T = Int64]]"),
        "{control:#?}"
    );

    for body in [
        // CALLEE spelling.
        "  operation n2() -> Option[T = List[T = String]] = Box.mine2[T = List](box(v: [1]))",
        // RECEIVER spelling.
        "  operation n5() -> Option[T = List[T = String]] = Box[T = List].mine2(box(v: [1]))",
        // …and through a `let`, the site that made this reachable without a declared return.
        "  operation n6() -> Int64 =\n    \
         let v: Option[T = List[T = String]] = Box.mine2[T = List](box(v: [1]))\n    0",
    ] {
        let errs = load_errors(body);
        assert_eq!(errs.len(), 1, "{body}\n{errs:#?}");
        assert!(
            errs[0].contains("List[T = String]") && errs[0].contains("List[T = Int64]"),
            "both inner types must be named: {body}\n{errs:#?}"
        );
    }

    // CONTROL, AND THE LIMIT — passes either way BY DESIGN. With nothing else determining
    // the inner slot, the minted variable is filled by the CONTEXT and the partial
    // annotation is admitted. `[T = List]` is a true, partial claim there.
    assert_eq!(
        load_errors("  operation n4() -> Option[T = List[T = String]] = Box.empty[T = List]()"),
        Vec::<String>::new(),
    );
}

/// CONTROL — an ARGUMENT pins the sort's parameter with no bracket anywhere, and did
/// before this ticket. Green either way BY DESIGN; it is what says the rows above measure
/// the BRACKET and not the pin.
#[test]
fn an_argument_carried_pin_needs_no_bracket() {
    let errs = load_errors(
        "  operation a1(b: Box[T = Letter]) -> Box[T = Int64] = Box.mine(b)",
    );
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(
        errs[0].contains("expected Box[T = Int64], got Box[T = Letter]"),
        "{errs:#?}"
    );
}

/// CONTROL — a bracket that CONTRADICTS an argument was already loud and stays loud.
/// Green either way BY DESIGN, though the SITE moves: the receiver's claim is now seeded
/// before argument unification, so the conflict is the §3 member tie
/// (`op-type-params`) rather than the return. The row asserts loudness and names the
/// parameter, which is what must not regress.
#[test]
fn a_bracket_contradicting_an_argument_stays_loud() {
    let errs = load_errors(
        "  operation a2(b: Box[T = Letter]) -> Box[T = Int64] = Box[T = Int64].mine(b)",
    );
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(
        errs[0].contains("Int64") && errs[0].contains("Letter"),
        "both claims must be named: {errs:#?}"
    );
}

// ── EVAL ─────────────────────────────────────────────────────────────────────────

const EVAL_SRC: &str = r#"
namespace test.rs2g4e
  import anthill.prelude.{Option, Int64, String, Bool, Type, List}

  sort Letter
    entity la
    entity lb
  end

  sort Duo2[A, B]
    entity duo2(x: A, y: B)
  end

  sort Box[T]
    import anthill.prelude.{Type, List}
    entity box(v: T)
    operation selfType() -> Type = Box[T = T]
    operation viaSibling() -> Type = selfType()
    operation nestedSelf() -> Type = List[T = List[T = T]]
    operation both2[U]() -> Type = Duo2[A = T, B = U]
  end

  sort Pair2[A, B]
    import anthill.prelude.Type
    entity pr(x: A, y: B)
    operation both() -> Type = Pair2[A = A, B = B]
  end

  operation ty[U]() -> Type = Box[T = U]

  operation w_recv_self() -> Type = Box[T = Letter].selfType()
  operation w_callee_self() -> Type = Box.selfType[T = Letter]()
  operation w_pair() -> Type = Pair2[A = Letter, B = Int64].both()
  operation w_sibling() -> Type = Box[T = Letter].viaSibling()
  operation w_nested() -> Type = Box[T = List[T = Letter]].nestedSelf()
  operation w_dual() -> Type = Box[T = Letter].both2[U = Int64]()
  operation w_ty() -> Type = ty[U = Letter]()
end
"#;

/// Evaluate a nullary operation and render the type value it delivers.
fn eval_type(interp: &mut anthill_core::eval::Interpreter, op: &str) -> String {
    match interp.call(&format!("test.rs2g4e.{op}"), &[]) {
        Ok(Value::Term { id, .. }) => TermPrinter::new(interp.kb()).print_term(id),
        Ok(other) => panic!("{op}: expected a term-carried type, got {other:?}"),
        Err(e) => panic!("{op}: {e:?}"),
    }
}

/// THE TICKET'S EVAL ROW. A body read of the SORT's parameter carries the RECEIVER
/// bracket's binding. Before: `Box(T: T)` — a dangling reference to the parameter's own
/// symbol, which is what a channel miss looks like (WI-708's defect, one scope up).
#[test]
fn a_receiver_bracket_reaches_a_body_read_of_the_sorts_parameter() {
    let mut interp = interp_for(EVAL_SRC);
    assert_eq!(eval_type(&mut interp, "w_recv_self"), "Box(T: Letter)");
}

/// …AND THE CALLEE SPELLING, which dangled too even though the TYPER bound `T` for it.
/// The two spellings write one channel, so they must read one way.
#[test]
fn the_callee_spelling_reaches_the_same_body_read() {
    let mut interp = interp_for(EVAL_SRC);
    assert_eq!(eval_type(&mut interp, "w_callee_self"), "Box(T: Letter)");
}

/// BOTH PARAMETERS, at eval. The arity driver for the channel: a writer that filled only
/// the first entry answers `Pair2(A: Letter, B: Pair2.B)` here.
#[test]
fn both_parameters_reach_a_two_parameter_members_body() {
    let mut interp = interp_for(EVAL_SRC);
    assert_eq!(
        eval_type(&mut interp, "w_pair"),
        "Pair2(A: Letter, B: Int64)"
    );
}

/// A BARE SIBLING CALL KEEPS THE ENCLOSING INSTANCE. `viaSibling`'s whole body is
/// `selfType()`, written with no receiver and no bracket, because inside the sort that
/// MEANS "the instance I am running at" — so the typer has nothing to write and the value
/// must come from the caller's frame. This is the row back-out (E) isolates.
#[test]
fn a_bare_sibling_call_keeps_the_enclosing_instance() {
    let mut interp = interp_for(EVAL_SRC);
    assert_eq!(eval_type(&mut interp, "w_sibling"), "Box(T: Letter)");
}

/// NESTED POSITION IS NOT A SECOND MECHANISM. `nestedSelf() -> List[T = List[T = T]]`
/// substitutes at depth because each `SortTypeArgs` frame consults the channel — WI-708's
/// mechanism recursing — so the only thing this ticket owed at depth was the channel
/// entry itself. Measured before: `List(T: List(T: T))`.
#[test]
fn a_nested_body_read_substitutes_at_depth() {
    let mut interp = interp_for(EVAL_SRC);
    assert_eq!(
        eval_type(&mut interp, "w_nested"),
        "List(T: List(T: List(T: Letter)))"
    );
}

/// THE TWO CHANNELS HAVE DISTINCT KEYS, which is the claim the sort half rests on:
/// `<ns>.<op>.U` and `<ns>.<Sort>.T` are different symbols, and WI-840 refuses an
/// operation whose own bracket repeats its sort's SHORT name — so `find_type_arg`'s
/// last-wins reverse scan can never have two candidates. Driven rather than argued: ONE
/// body reads both, from one call that writes both.
///
/// Red under (A) and (D) — its `A` slot is the sort half, which needs both the binding
/// and the channel. Its `B` slot is the WI-708 control and is green either way, which is
/// what makes the pair a distinctness test rather than two separate reads.
#[test]
fn the_two_channels_have_distinct_keys() {
    let mut interp = interp_for(EVAL_SRC);
    assert_eq!(
        eval_type(&mut interp, "w_dual"),
        "Duo2(A: Letter, B: Int64)"
    );
}

/// CONTROL — WI-708's own row, an OPERATION-scoped parameter read in a body. Green either
/// way BY DESIGN: it is the channel this ticket widened, and a widening that broke it
/// would be a regression rather than a delivery.
#[test]
fn the_wi708_operation_parameter_channel_is_unchanged() {
    let mut interp = interp_for(EVAL_SRC);
    assert_eq!(eval_type(&mut interp, "w_ty"), "Box(T: Letter)");
}

/// WHAT THE CHANNEL CARRIES FOR A BRACKET VALUE WITH AN UNWRITTEN SLOT — DECIDED AND
/// PINNED, because both readings are honest ("a list of something") and a consumer has to
/// know which one arrives.
///
/// It carries what σ HOLDS: the expanded `List[T = ?T]`, variable and all, rather than
/// the bare `Ref(List)` the author wrote. Translating it back at the channel would be a
/// SECOND representation of one decision, kept in step by hand. The consumer owns the
/// verdict either way — `bound_names_a_determinate_type` refuses a bare `Ref` and a bare
/// `Var` alike — so nothing downstream has to tell them apart to be correct, only to
/// report well.
#[test]
fn a_bracket_value_with_an_unwritten_slot_arrives_expanded() {
    let src = r#"
namespace test.rs2g4x
  import anthill.prelude.{Int64, Type, List}
  sort Box[T]
    import anthill.prelude.Type
    entity box(v: T)
  end
  operation tyb[U]() -> Type = Box[T = U]
  operation w_bare() -> Type = tyb[U = List]()
  operation w_written() -> Type = tyb[U = List[T = Int64]]()
end
"#;
    let mut interp = interp_for(src);
    let bare = match interp.call("test.rs2g4x.w_bare", &[]) {
        Ok(Value::Term { id, .. }) => TermPrinter::new(interp.kb()).print_term(id),
        other => panic!("{other:?}"),
    };
    assert!(
        bare.starts_with("Box(T: List(T: ") && bare.ends_with("))"),
        "a bare inner value arrives as `List` APPLIED to the minted variable, not bare: {bare}"
    );

    // CONTROL — a WRITTEN inner value is untouched by the expansion and by the channel.
    let written = match interp.call("test.rs2g4x.w_written", &[]) {
        Ok(Value::Term { id, .. }) => TermPrinter::new(interp.kb()).print_term(id),
        other => panic!("{other:?}"),
    };
    assert_eq!(written, "Box(T: List(T: Int64))");
}
