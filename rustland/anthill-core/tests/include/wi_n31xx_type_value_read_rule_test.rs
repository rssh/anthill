//! WI-20260919-N31XX (proposal 065, "The rule") — A RIGID TYPE IS A VALUE ONLY WHERE A
//! REQUIREMENT SAYS SO.
//!
//! TWO HALVES, and the second is not decoration. The READ half refuses
//! `operation bad[B](x: B) -> Type = Cell[V = B]`, which inspects `B` without saying so.
//! The FORWARD half refuses `mid[U](y: U) = tyOf(y)`, which inspects nothing but hands
//! its own rigid to an operation that does, holding no evidence and having declared none.
//! With only the first, a signature could still quietly depend on a type it promises
//! nothing about — see [`a_middle_level_that_drops_the_clause_is_refused_at_the_call`].
//!
//! `operation bad[B](x: B) -> Type = Cell[V = B]` reads `B` in VALUE position. Under 065
//! that is a LOAD error unless `TypeValue[T = B]` stands among the requirements in scope,
//! and the refusal names the parameter, the read's line and column, and the clause to
//! add. The point is not tidiness: without it a signature `f[B](x: B) -> R` promises
//! nothing about whether `f` inspects `B`, so parametricity is false, a provider's own
//! parameter entered through a slot has no call site that could supply it, and an
//! erasing backend has nothing to read (065's opening paragraph).
//!
//! BACK-OUTS — each a MUTATION run on its own (the site still runs, its answer is
//! discarded), never a deletion, and each count is of a run over this file plus the five
//! census files the migration touched:
//!
//! * **the rule off** — the `TypeValueReadUnbacked` push in `check_operation_bodies`
//!   neutralized: **1 red**, [`a_value_read_with_no_clause_is_refused`]. Nothing else in
//!   any of the six files moves, and that isolation is the point — it says the migration
//!   added clauses that were NEEDED and not clauses that merely silenced something.
//!   [`the_operation_level_subset_rule_is_065_3`] stays green: `check_override_refinement`
//!   is a separate leg, so that row measures §3 and this rule independently.
//! * **the clause reader's op-level half off** — `type_value_backed_params` reads only
//!   `direct_requires`: **31 red across the six files, 4 of them here** —
//!   [`the_clause_admits_the_read_and_the_answer_is_the_ground_type`],
//!   [`the_clause_reaches_through_two_generic_levels`],
//!   [`a_middle_level_that_drops_the_clause_still_loads_today`] and
//!   [`a_simp_expanded_type_position_is_not_a_value_read`], because every clause in this
//!   file that admits a read is written on an OPERATION. MEASURED, and it was the first
//!   cut's actual defect: an op-level clause arrives as the bare application the author
//!   wrote, not as a `SortView`, and `unwrap_spec_view_value` answers "no bindings" for
//!   it — so `operation ty[T]() -> Type requires TypeValue[T = T]` was refused with its
//!   own clause written two columns away.
//! * **the FORWARD leg off** — the `TypeValue` arm in `build_op_scoped_dicts` removed:
//!   **1 red**, [`a_middle_level_that_drops_the_clause_is_refused_at_the_call`], which
//!   is now red on its MESSAGE rather than on the load. Since WI-20260920-XSVCS the
//!   program is still refused with the arm gone — the caller-rigid park catches the same
//!   shape — but with the other arm's wording, and the row asserts 065's. Its plain-spec
//!   half is that other arm, and was this leg's narrowness control until XSVCS closed
//!   the wider gap; see the row's own doc.
//! * **the post-simp placement off** — the rule reading `op.body_node` (the tree the
//!   typer was handed) instead of `result.node` (the tree it wrote back): **2 red** —
//!   [`a_simp_expanded_type_position_is_not_a_value_read`] and, in the census file
//!   itself, `wi_h054k_type_position_subst_test::a_binding_that_denotes_no_type_is_bottom_and_says_so`.
//!   That second one is why the placement is the rule and not a detail: 065 §6's
//!   nineteenth site is a real program in the corpus, and judging it before `@[simp]`
//!   inlining refuses it for a `K` that only ever reaches a TYPE position.
//!
//! PASS EITHER WAY BY DESIGN — controls, stated at their sites:
//! [`a_type_position_read_needs_no_clause`],
//! [`a_concrete_sort_in_value_position_needs_no_clause`].

use anthill_core::eval::Value;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{interp_for, try_load_kb_with};

fn load_errors(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

fn eval_type(src: &str, op: &str) -> String {
    let mut interp = interp_for(src);
    match interp.call(op, &[]) {
        Ok(Value::Term { id, .. }) => TermPrinter::new(interp.kb()).print_term(id),
        Ok(other) => panic!("{op}: expected a term-carried type, got {other:?}"),
        Err(e) => panic!("{op}: {e:?}"),
    }
}

// ── THE RULE ─────────────────────────────────────────────────────────────────────────

/// 065's own example, refused with 065's own message. The `-> Type` return is what makes
/// this a VALUE read and not a type one: `B` is the thing being produced.
#[test]
fn a_value_read_with_no_clause_is_refused() {
    let errs = load_errors(
        r#"
namespace test.n31xx.bad
  import anthill.prelude.{Cell, Type}

  operation bad[B](x: B) -> Type = Cell[V = B]
end
"#,
    );
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    let e = &errs[0];
    // THE PARAMETER, THE CLAUSE TO ADD, AND THE OPERATION THAT MUST CARRY IT — a
    // refusal that named only "a type parameter is read as a value" would leave the
    // author to work out which one and where the clause goes.
    for want in [
        "`B` is read as a VALUE",
        "anthill.reflect.TypeValue[T = B]",
        "test.n31xx.bad.bad",
    ] {
        assert!(e.contains(want), "expected {want:?} in the refusal; got {e:?}");
    }
    // AND THE READ'S LINE AND COLUMN, which 065 asks for by name. The read is on the
    // fixture's fifth line; the column is the `B` inside `Cell[V = B]`, not the
    // operation's own line, because the repair is read at the signature but the FAULT is
    // at the read.
    assert!(
        e.starts_with("5:"),
        "the refusal must be located at the read's line; got {e:?}"
    );
}

/// THE CONTROL, and it asserts the ANSWER and not merely that the program loads: the
/// clause must admit the read AND leave the value the read delivers intact. One generic
/// level — the caller pins `B` at the call site.
#[test]
fn the_clause_admits_the_read_and_the_answer_is_the_ground_type() {
    let src = r#"
namespace test.n31xx.one
  import anthill.prelude.{Cell, Int64, String, Type}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]

  operation ask_int() -> Type = tyOf(5)
  operation ask_str() -> Type = tyOf("s")
end
"#;
    assert_eq!(eval_type(src, "test.n31xx.one.ask_int"), "Cell(V: Int64)");
    // The SECOND instantiation is not decoration: a single row cannot tell a correct
    // answer from a first binding that leaked.
    assert_eq!(eval_type(src, "test.n31xx.one.ask_str"), "Cell(V: String)");
}

/// …and THROUGH TWO GENERIC LEVELS, which is where the rule earns its keep: the middle
/// operation has to declare the clause too, because it passes its own rigid down. That
/// propagation IS 065's parametricity claim — an operation that cannot name the evidence
/// cannot hand it on.
#[test]
fn the_clause_reaches_through_two_generic_levels() {
    let src = r#"
namespace test.n31xx.two
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]
  operation mid[U](y: U) -> Type requires TypeValue[T = U] = tyOf(y)

  operation ask() -> Type = mid(5)
end
"#;
    assert_eq!(eval_type(src, "test.n31xx.two.ask"), "Cell(V: Int64)");
}

/// …AND A MIDDLE LEVEL THAT DROPS THE CLAUSE IS REFUSED AT THE CALL — the FORWARD half
/// of the rule, which the read half above does not cover.
///
/// `mid[U](y: U) = tyOf(y)` reads nothing; it hands its own rigid to an operation that
/// `requires TypeValue[T = U]`, holding no evidence and having declared none. Without
/// this the rule would cover the READ and not the FORWARD, and a signature could still
/// quietly depend on a type it promises nothing about — parametricity half enforced.
///
/// WHY IT IS REFUSED RATHER THAN LEFT AS AN UNFILLED SLOT. `build_op_scoped_dicts` makes
/// an unsuppliable op slot a SILENT ABSENCE on purpose, and its own comment gives the
/// measured reason: 29 stdlib bodies declare a chain and never read it, so a slot nothing
/// fills costs them nothing. `TypeValue` can never be one of those — `type_value()` is
/// NULLARY, so no argument and no receiver names the type and the dispatching dictionary
/// is the ONLY carrier of the answer (WI-20260919-HXGXF's fact 1). A body holding this
/// evidence necessarily reads it through the slot, so an unfilled one is either an
/// eval-time `Internal` death no handler can catch or a clause that was pure noise.
///
/// AT THE CALL, NOT AT THE DECLARATION: `mid`'s signature is legal on its own, and it is
/// only this call that needs what `mid` has not got. The refusal is located there.
///
/// THE SECOND HALF WAS THIS LEG'S NARROWNESS CONTROL AND IS NOW ITS SUBSUMPTION ROW.
/// The same forward shape over a plain user spec — `requires TT[T = B]`, nothing to do
/// with 065 — used to LOAD, because this leg said only that `TypeValue` evidence is
/// never benignly absent and not that operation-level requirement propagation was
/// checked in general. WI-20260920-XSVCS closed that wider gap: a carrier that is the
/// CALLER's own type parameter is unfillable whatever the spec, so the plain-spec shape
/// is now refused too — parked, and reported because `tyOf`'s body reads the slot.
///
/// THE TWO ARMS ARE NOW ONE (WI-20260921-3G1YT). 065's arm was keyed on
/// `dep.required_sort == anthill.reflect.TypeValue` and ran first, so this half used to
/// carry its own message; that hardcode is deleted and both halves take XSVCS's, which
/// says the same thing for ANY spec and additionally names where to declare the evidence.
/// See `wi_xsvcs_op_requires_forward_test` for the plain-spec shape driven to an answer,
/// and [`a_rule_body_forward_is_refused_too`] for the site that hardcode really covered.
/// WI-20260921-3G1YT — THE SAME FORWARD FROM A **RULE BODY**, where there is no
/// enclosing operation. Added because its ABSENCE is what made deleting 065's arm look
/// safe: with `type_value_forward_unsuppliable` disabled the suite is 6385 passed / 2
/// FAILED and both failures are about MESSAGE TEXT, so the corpus said "this arm decides
/// no verdict". It does decide one — here — and **a refusal that becomes silent fails no
/// test**, which is why nothing caught it.
///
/// WHY THIS SITE IS THE ONE THE OTHER ARM CANNOT REACH: `caller_rigid_carrier` is
/// `enclosing_op`-scoped, and a rule body has no enclosing operation. WI-945's note says
/// a rule-body goal is deliberately NOT refused in general — it reaches eval through the
/// SLD bridge, which resolves dictionaries from concrete argument values and suspends
/// when it cannot. `TypeValue` is the exception, because 065 §1's lowering synthesizes
/// the read and the slot is therefore not optional.
///
/// DRIVEN BY BACKING OUT: with the arm removed this program LOADS CLEAN (measured: 4203
/// facts, 431 rules) and dies at eval on an unbound `__req_typevalue`. This row is the
/// only one in the workspace that fails on that removal.
#[test]
fn a_rule_body_forward_is_refused_too() {
    let errs = load_errors(
        r#"
namespace test.n31xx.rulebody
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]

  rule names(?x, ?t) :- ?t = tyOf(?x)
end
"#,
    );
    assert!(
        !errs.is_empty(),
        "a rule body forwarding an unevidenced rigid into a TypeValue reader must be \
         refused at load, not left to die on an unbound slot at eval"
    );
    assert!(
        errs.iter().any(|e| e.contains("anthill.reflect.TypeValue")
            && e.contains("test.n31xx.rulebody.tyOf")),
        "the refusal must name the evidence and the callee; got {errs:#?}"
    );
}

/// WI-20260921-3G1YT — **THE SAME DEFECT AT A USER TYPECLASS, WHICH IS WHY THE RULE IS
/// NOT `TypeValue`'s.** `Stamp` is `TypeValue` in miniature and shares nothing with it but
/// its SHAPE: it DECLARES an operation, so it is not a marker spec and its callers really
/// would miss the slot, and nothing in the KB provides it, so the provider facts determine
/// no dictionary. Both halves are readable at LOAD, which is the point.
///
/// MEASURED BEFORE THE FIX: this program LOADED CLEAN while the byte-identical shape
/// spelled `TypeValue` was refused — because N31XX's arm asked
/// `dep.required_sort == anthill.reflect.TypeValue` and nothing asked the general
/// question. That hardcode is deleted; the rule keys on the spec's SHAPE and on the
/// provider facts — `spec_is_a_marker` and `dep_completes_to_a_unique_provider` — and
/// `TypeValue` is an instance of it like any other spec. (It keyed on
/// `spec_has_value_directed_route` between WI-20260921-3G1YT and WI-20260922-0DK3H, which
/// deleted that predicate for appealing to what a value might name at fire time.)
///
/// WHICH TESTS FAIL IF THE RULE IS BACKED OUT: this one and
/// [`a_rule_body_forward_is_refused_too`], the `TypeValue` spelling of the same site.
/// Both, together, are what says the rule is general rather than one spec's.
#[test]
fn a_user_typeclass_of_the_same_shape_is_refused_too() {
    let errs = load_errors(
        r#"
namespace test.n31xx.userclass
  import anthill.prelude.{Int64}

  sort Stamp
    sort T = ?
    operation stamp() -> Int64
  end

  operation stampOf[B](x: B) -> Int64 requires Stamp[T = B] = Stamp.stamp()

  rule names(?x, ?n) :- ?n = stampOf(?x)
end
"#,
    );
    assert!(
        !errs.is_empty(),
        "a rule body forwarding an unevidenced rigid into a NULLARY user typeclass must \
         be refused, exactly as the `TypeValue` spelling is"
    );
    assert!(
        errs.iter().any(|e| e.contains("test.n31xx.userclass.Stamp")
            && e.contains("nothing in the clause determines")),
        "the refusal must name the user spec and say why the clause determines no \
         instance; got {errs:#?}"
    );
}

/// WI-20260921-3G1YT — THE SORT HALF OF THE SAME SITE, pinned because deleting its arm
/// is a REGRESSION and the suite could not see it. A `requires` on the SORT, at a
/// no-route spec, reached from a rule body: refused, and it must stay so.
///
/// MEASURED: with `type_value_forward_unsuppliable`'s remaining call site removed, this
/// program LOADS CLEAN while every other row in the file stays green — the same
/// silent-refusal shape as [`a_rule_body_forward_is_refused_too`], one channel over.
/// /code-review caught it with this exact probe.
///
/// IT IS NO LONGER SPELLED `TypeValue`. An earlier cut of this ticket left the sort half
/// hardcoded because the general rule needs the CALLEE'S OP to ask whether its body reads
/// the slot, and `build_dispatching_dict_from_chain` was handed the callee's SORT.
/// `rule_body_callee` now plumbs that op through, both hardcodes are deleted, and
/// [`a_sort_level_user_typeclass_is_refused_too`] drives the general form — the gap this
/// row's note previously recorded as PRE-EXISTING is closed with it.
#[test]
fn a_sort_level_rule_body_forward_is_refused_too() {
    let errs = load_errors(
        r#"
namespace test.n31xx.sortlevel
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  sort Holder
    sort U = ?
    requires TypeValue[T = U]
    operation get(x: U) -> Type = Cell[V = U]
  end

  rule names(?x, ?t) :- ?t = Holder.get(?x)
end
"#,
    );
    assert!(
        !errs.is_empty(),
        "a SORT-level TypeValue clause forwarded from a rule body must be refused; \
         leaving it silent is the regression this row exists to catch"
    );
    assert!(
        errs.iter().any(|e| e.contains("anthill.reflect.TypeValue")),
        "the refusal must name the evidence; got {errs:#?}"
    );
}

/// WI-20260921-3G1YT — **THE SORT HALF, GENERAL.** The same shape as
/// [`a_sort_level_rule_body_forward_is_refused_too`] with a USER typeclass in place of
/// `TypeValue`, which is what says the sort-half rule is keyed on a spec's PROPERTY and
/// not on one spec's name.
///
/// MEASURED AS A GAP THIS CLOSES, and it is older than this ticket: while the sort half
/// asked `dep.required_sort == anthill.reflect.TypeValue`, this program LOADED CLEAN
/// while the `TypeValue` spelling of it was refused. Both are refused now.
///
/// WHICH TESTS FAIL IF THE SORT-HALF RULE IS BACKED OUT: this one and
/// [`a_sort_level_rule_body_forward_is_refused_too`], and no others.
#[test]
fn a_sort_level_user_typeclass_is_refused_too() {
    let errs = load_errors(
        r#"
namespace test.n31xx.sluser
  import anthill.prelude.{Int64}

  sort Stamp
    sort T = ?
    operation stamp() -> Int64
  end

  sort Holder
    sort U = ?
    requires Stamp[T = U]
    operation get(x: U) -> Int64 = Stamp.stamp()
  end

  rule names(?x, ?n) :- ?n = Holder.get(?x)
end
"#,
    );
    assert!(
        !errs.is_empty(),
        "a SORT-level clause at a nullary USER typeclass, forwarded from a rule body, \
         must be refused exactly as the `TypeValue` spelling is"
    );
    assert!(
        errs.iter().any(|e| e.contains("test.n31xx.sluser.Stamp")
            && e.contains("nothing in the clause determines")),
        "the refusal must name the user spec and say why the clause determines no \
         instance; got {errs:#?}"
    );
}

/// WI-20260921-3G1YT — **CONTROL: A NULLARY SPEC WITH A PINNED ELEMENT STILL LOADS.**
/// The third rescue route, and the counterexample that sharpened the rule. `Tag` declares
/// only a NULLARY operation, so no value can name its carrier — but the call pins
/// `M = Alpha` concretely, and the SLD bridge answers the goal from that element off
/// `Alpha provides Tag[M = Alpha, N = Beta]`. "No value-directed route" is therefore not
/// enough to refuse; the dep must also carry NOTHING searchable.
///
/// MEASURED: with `dep_has_searchable_pin` dropped, this row fails and so does
/// `wi_nx4fd …a_completion_selects_the_provider_the_pinned_element_names` — which is the
/// row that caught it, on the full workspace, after the narrower rule passed every
/// targeted test.
///
/// THE CONTRAST WITH [`a_sort_level_user_typeclass_is_refused_too`] IS THE WHOLE RULE:
/// there the element is the CALLER'S OWN RIGID, which is determined but abstract, so no
/// provider fact can match it and nothing can ever supply the slot.
#[test]
fn a_nullary_spec_with_a_pinned_element_still_loads() {
    let errs = load_errors(
        r#"
namespace test.n31xx.pinned
  import anthill.prelude.{Int64}

  sort Tag
    sort M = ?
    sort N = ?
    operation code() -> Int64
  end

  sort Alpha
    entity alpha
    provides Tag[M = Alpha, N = Beta]
    operation code() -> Int64 = 11
  end

  sort Beta
    entity beta
    provides Tag[M = Beta, N = Alpha]
    operation code() -> Int64 = 22
  end

  sort Ghost
    sort GM = ?
    sort GN = ?
    requires Tag[M = GM, N = GN]
    operation probe(x: GM) -> Int64 = Tag.code()
  end

  rule ra(?n) :- Ghost.probe(alpha(), ?n)
end
"#,
    );
    assert!(
        errs.is_empty(),
        "the call pins `M = Alpha`, so the resolver can complete the goal from a provider \
         fact at fire time even though `Tag` has no receiver; got {errs:#?}"
    );
}

/// WI-20260922-0DK3H — **INVERTED, AND THE INVERSION IS THE TICKET.** This row used to
/// assert that the program LOADS, on the reason `spec_has_value_directed_route` gave:
/// `shown(x: T)` receives on its carrier, so eval could classify a value and recover the
/// provider at fire time. That predicate is deleted — "we can't have runtime dispatch
/// because it is a runtime error instead of a loading error" (user, 2026-09-22) — and
/// with it the reason this row stood.
///
/// NOTHING PINS `U` AND THE CLAUSE DECLARES NOTHING, so no route reaches the slot: the
/// caller's own `requires` (Strategies 1/2) is a rule body's `require[…]` and there is
/// none, the clause holds no spec-typed value (route 4), and the provider facts decide
/// nothing ([`dep_completes_to_a_unique_provider`] — `Shown` has no provider at all
/// here). The dep is owed and unfillable, so it is refused where it is written.
///
/// ITS CONTROL IS [`a_sort_level_call_that_pins_the_carrier_still_loads`], one fixture
/// down: the SAME spec and the SAME forwarding operation, differing only in that the call
/// names a concrete argument. That pair is what says this refusal is about the missing
/// evidence and not about the shape.
#[test]
fn a_sort_level_user_typeclass_with_a_receiver_is_refused() {
    let errs = load_errors(
        r#"
namespace test.n31xx.sluserrecv
  import anthill.prelude.{Int64}

  sort Shown
    sort T = ?
    operation shown(x: T) -> Int64
  end

  sort Holder
    sort U = ?
    requires Shown[T = U]
    operation get(x: U) -> Int64 = Shown.shown(x)
  end

  rule names(?x, ?n) :- ?n = Holder.get(?x)
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains("test.n31xx.sluserrecv.Shown")),
        "a rule-body goal that pins nothing and declares nothing must be refused AT LOAD, \
         and the refusal must name the spec whose evidence is missing; got {errs:#?}"
    );
}

/// CONTROL for the row above, and the half that says the refusal is about EVIDENCE rather
/// than about a spec with a receiver. Same `Shown`, same `Holder.get`, but the call names
/// `leaf()`, so the dep is `Shown[T = Leaf]` and `Leaf provides Shown` answers it
/// statically. It passes on both trees.
#[test]
fn a_sort_level_call_that_pins_the_carrier_still_loads() {
    let errs = load_errors(
        r#"
namespace test.n31xx.sluserpin
  import anthill.prelude.{Int64}

  sort Shown
    sort T = ?
    operation shown(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    provides Shown[T = Leaf]
    operation shown(x: Leaf) -> Int64 = 7
  end

  sort Holder
    sort U = ?
    requires Shown[T = U]
    operation get(x: U) -> Int64 = Shown.shown(x)
  end

  rule names(?n) :- ?n = Holder.get(leaf())
end
"#,
    );
    assert!(
        errs.is_empty(),
        "the call pins `U = Leaf` and `Leaf provides Shown`, so the dictionary is \
         determined at load; got {errs:#?}"
    );
}

/// WI-20260922-0DK3H — **INVERTED, the OP-half twin of
/// [`a_sort_level_user_typeclass_with_a_receiver_is_refused`].** Same deletion, same
/// reason: `shown(x: T)` receiving on its carrier used to rescue this through
/// `spec_has_value_directed_route`, and a rescue that says "eval will recover it" is the
/// runtime dispatch this ticket removes.
///
/// THE TWO HALVES ARE BOTH HERE ON PURPOSE. WI-855 legislates that the sort-level and
/// op-level spellings of one requirement give ONE verdict; an inversion that moved only
/// one of them would split that, and this pair is what catches it.
#[test]
fn a_user_typeclass_with_a_receiver_is_refused() {
    let errs = load_errors(
        r#"
namespace test.n31xx.userclassrecv
  import anthill.prelude.{Int64}

  sort Shown
    sort T = ?
    operation shown(x: T) -> Int64
  end

  operation shownOf[B](x: B) -> Int64 requires Shown[T = B] = Shown.shown(x)

  rule names(?x, ?n) :- ?n = shownOf(?x)
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains("test.n31xx.userclassrecv.Shown")),
        "the op-half spelling must be refused exactly as the sort-half one is, and name \
         the same spec; got {errs:#?}"
    );
}

/// CONTROL for the row above — the SAME rule body with the clause DECLARED on the
/// forwarding operation, so the evidence is in scope and nothing is refused. Without it
/// the row above would pass for a program that is refused for some unrelated reason.
#[test]
fn a_rule_body_forward_with_the_clause_loads() {
    let errs = load_errors(
        r#"
namespace test.n31xx.rulebodyok
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]

  rule names(?t) :- ?t = tyOf(5)
end
"#,
    );
    assert!(errs.is_empty(), "a CONCRETE argument needs no forwarded clause; got {errs:#?}");
}

#[test]
fn a_middle_level_that_drops_the_clause_is_refused_at_the_call() {
    let type_value = load_errors(
        r#"
namespace test.n31xx.twobad
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]
  operation mid[U](y: U) -> Type = tyOf(y)

  operation ask() -> Type = mid(5)
end
"#,
    );
    assert_eq!(type_value.len(), 1, "exactly one refusal, got {type_value:#?}");
    let e = &type_value[0];
    for want in [
        "anthill.reflect.TypeValue",
        "cannot be supplied for call to",
        "test.n31xx.twobad.tyOf",
        // WI-20260921-3G1YT — XSVCS's wording, shared with the plain-spec half below.
        // 065's arm was a hardcoded `dep.required_sort == anthill.reflect.TypeValue` and
        // is deleted; this clause IS "answered only by the dispatching dictionary", said
        // for any spec, and it additionally names WHERE to declare the evidence.
        "the caller's frame is the only thing that could ever fill this slot",
        "test.n31xx.twobad.mid",
    ] {
        assert!(e.contains(want), "expected {want:?} in the refusal; got {e:?}");
    }
    // LOCATED AT THE CALL inside `mid` (the fixture's seventh line), not at `tyOf`'s
    // declaration on the sixth: `tyOf` is well-formed, and the caller is what is wrong.
    assert!(
        e.starts_with("7:"),
        "the refusal belongs at the forwarding call; got {e:?}"
    );

    // THE SAME SHAPE OVER A PLAIN SPEC — refused since WI-20260920-XSVCS, by the OTHER
    // arm. See the doc above.
    let plain_spec = load_errors(
        r#"
namespace test.n31xx.othersp
  import anthill.prelude.{Type, Int64}

  sort TT
    import anthill.prelude.Type
    sort T = ?
    operation valueOf() -> Type
  end

  operation tyOf[B](x: B) -> Type requires TT[T = B] = TT.valueOf()
  operation mid[U](y: U) -> Type = tyOf(y)
  operation ask() -> Type = mid(5)
end
"#,
    );
    assert_eq!(plain_spec.len(), 1, "exactly one refusal, got {plain_spec:#?}");
    let p = &plain_spec[0];
    // THE OTHER ARM'S MESSAGE, asserted rather than just the count: a row that checked
    // only "one error" would keep passing if 065's arm started answering for this shape
    // too, which is the thing the doc above says does NOT happen.
    for want in [
        "cannot be supplied for call to `test.n31xx.othersp.tyOf`",
        "type parameter of the CALLING operation `test.n31xx.othersp.mid`",
        "Declare `requires test.n31xx.othersp.TT[T = U]` on `test.n31xx.othersp.mid`",
    ] {
        assert!(p.contains(want), "expected {want:?} in the refusal; got {p:?}");
    }
    assert!(
        !p.contains("proposal 065"),
        "the plain-spec shape must NOT get the TypeValue arm's message; got {p:?}"
    );
}

// ── 065 §1, THE LOWERING ─────────────────────────────────────────────────────────────

/// THE LOWERING IS REAL AND THE ANSWER COMES FROM THE DICTIONARY, NOT THE CHANNEL.
///
/// 065 §1: a value-position read of a rigid IS a slot dispatch —
/// `TypeValue[T = B].type_value()`, through the requirement slot. Every row above would
/// pass equally against the pre-065 frame type-argument channel, so none of them measures
/// this; that is what this row is for.
///
/// THE CONTROL IS THE BACKED-OUT CHANNEL, and it was RUN. Neutralize the `find_type_arg`
/// lookup in eval's `Expr::TypeValue` bare-head arm — the thing that served every one of
/// these reads before 065 — and the measurement is exact:
///
///  * this row, [`a_bare_read_and_a_nested_read_lower_alike`],
///    [`the_clause_admits_the_read_and_the_answer_is_the_ground_type`] and
///    [`the_clause_reaches_through_two_generic_levels`] stay GREEN, so their answers come
///    from the DICTIONARY and not from the channel;
///  * **`wi708_body_type_arg_read_test` passes in full with the channel OFF** — the file
///    whose entire subject is that channel, because its reads are op-level and therefore
///    lowered. That is the sharpest statement of what changed;
///  * 16 rows go red, every one of them a SORT-half read —
///    `wi_r541x_body_read_of_type_param_test`'s (A)/(B) rows,
///    `wi_rs2g4_receiver_bracket_binds_sort_params_test`'s eval half, and this file's own
///    [`the_operation_level_subset_rule_is_065_3`], whose `Box.valueOf` reads `V` under a
///    SORT-level clause.
///
/// So the channel is still load-bearing for exactly the half `lower_rigid_read_to_slot`
/// declines to lower, and for nothing else. 065 §1's "the channel stops being consulted"
/// is now true of op-level reads; WI-20260919-H20YY is what makes it true of the rest.
///
/// WHAT IT DRIVES: a read one level deep (`tyOf`) and a read TWO levels deep (`mid`
/// forwards its own rigid, so the evidence must travel caller → callee as a DICTIONARY,
/// which is precisely what the channel could not do for a provider entered through a
/// slot). Both answer the ground type.
///
/// AND A NESTED READ — `Pair[A = B, B = C]` reads two distinct rigids in one type
/// expression, so the argument pump has to resolve two different slots. A single-rigid
/// row cannot tell a correct slot lookup from one that always picks slot 0.
#[test]
fn a_lowered_read_answers_through_its_slot() {
    let src = r#"
namespace test.n31xx.lower
  import anthill.prelude.{Int64, String, Bool, Type}
  import anthill.reflect.{TypeValue}

  sort Pair2[A, B]
    entity pr(x: A, y: B)
  end

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = B
  operation mid[U](y: U) -> Type requires TypeValue[T = U] = tyOf(y)

  operation both[A, B](a: A, b: B) -> Type
    requires TypeValue[T = A], TypeValue[T = B] = Pair2[A = A, B = B]

  operation one_level() -> Type = tyOf(5)
  operation two_levels() -> Type = mid("s")
  operation two_slots() -> Type = both(5, true)
end
"#;
    assert_eq!(eval_type(src, "test.n31xx.lower.one_level"), "Int64");
    assert_eq!(eval_type(src, "test.n31xx.lower.two_levels"), "String");
    // TWO DISTINCT SLOTS IN ONE EXPRESSION — `A` is slot 0 and `B` is slot 1, and a
    // lookup that ignored the parameter would answer `Pair2(A: Int64, B: Int64)`.
    assert_eq!(
        eval_type(src, "test.n31xx.lower.two_slots"),
        "Pair2(A: Int64, B: Bool)"
    );
}

/// THE BARE READ AND THE NESTED READ ARE THE SAME NODE, which is why 065 §1 says only the
/// LEAF changes: `= B` and `= Cell[V = B]` differ by who consumes the `Type` the read
/// produces, and the argument pump was always the builder for the second.
#[test]
fn a_bare_read_and_a_nested_read_lower_alike() {
    let src = r#"
namespace test.n31xx.leaf
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  operation bare[B](x: B) -> Type requires TypeValue[T = B] = B
  operation nested[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]

  operation ask_bare() -> Type = bare(5)
  operation ask_nested() -> Type = nested(5)
end
"#;
    assert_eq!(eval_type(src, "test.n31xx.leaf.ask_bare"), "Int64");
    assert_eq!(eval_type(src, "test.n31xx.leaf.ask_nested"), "Cell(V: Int64)");
}

// ── 065 §3, THE OPERATION-LEVEL SUBSET RULE ──────────────────────────────────────────

/// AN IMPLEMENTATION MAY NOT ADD AN OPERATION-LEVEL CLAUSE, AND MAY ADD AN INSTANCE ONE.
///
/// 065 §3's table in one program. An operation-level `requires` is an extra INPUT the
/// caller supplies per call, and a caller dispatching through the spec knows only the
/// spec's signature — so `Box.valueOf requires TypeValue[T = V]` is refused. The SAME
/// evidence written on the SORT rides the instance, which the spec's caller never sees,
/// and loads.
///
/// MEASURED, not reasoned: this is the refusal the r541x migration actually hit, and
/// moving the clause from the operation to the sort is what cleared it.
///
/// TWO INDEPENDENT LEGS, so this row is not a duplicate of part 1's: part 1 made a
/// RESTATED clause load (`check_override_refinement`'s type-parameter alignment); this
/// asserts that an ADDED one still does not.
#[test]
fn the_operation_level_subset_rule_is_065_3() {
    const SPEC: &str = r#"
namespace test.n31xx.sub
  import anthill.prelude.{Type, String}
  import anthill.reflect.{TypeValue}

  sort TT
    import anthill.prelude.Type
    sort T = ?
    operation valueOf() -> Type
  end

  sort Boom
    entity boom(why: String)
  end

  sort Box
    import anthill.prelude.Type
    import anthill.reflect.{TypeValue}
    sort V = ?
    entity box(v: V)
@CLAUSE@
    provides TT[T = Box[V = V]]
    operation valueOf() -> Type @OPCLAUSE@= Box[V = V]
  end

  operation ask() -> Type = Box[V = Boom].valueOf()
end
"#;
    // (a) the OPERATION-level addition — refused.
    let added = SPEC.replace("@CLAUSE@\n", "").replace(
        "@OPCLAUSE@",
        "requires TypeValue[T = V] ",
    );
    let errs = load_errors(&added);
    assert!(
        errs.iter()
            .any(|e| e.contains("strengthens the precondition")),
        "an implementation may not ADD an operation-level clause the spec lacks; got {errs:#?}"
    );

    // (b) the INSTANCE-level spelling — loads, and answers.
    let instance = SPEC
        .replace("@CLAUSE@", "    requires TypeValue[T = V]")
        .replace("@OPCLAUSE@", "");
    assert_eq!(
        eval_type(&instance, "test.n31xx.sub.ask"),
        "Box(V: Boom)",
        "a clause over the provider's OWN parameter rides the instance and is permitted"
    );
}

// ── CONTROLS — green with or without the rule ────────────────────────────────────────

/// A TYPE POSITION IS NOT A READ. `x: B` and `-> List[T = B]` are static and erasable,
/// and nothing reads them at run time — 065's first exclusion. This operation mentions
/// `B` three times and carries no clause.
#[test]
fn a_type_position_read_needs_no_clause() {
    let src = r#"
namespace test.n31xx.typepos
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{cons, nil}

  operation single[B](x: B) -> List[T = B] = cons(x, nil())
  operation ask() -> Int64 = 1
end
"#;
    assert_eq!(load_errors(src), Vec::<String>::new(), "no clause is needed");
    let mut interp = interp_for(src);
    // DRIVEN, not merely loaded: a signature-only assertion would stay green if the
    // operation resolved to nothing.
    assert!(matches!(
        interp.call("test.n31xx.typepos.ask", &[]),
        Ok(Value::Int(1))
    ));
}

/// A CONCRETE SORT IN VALUE POSITION READS NO RIGID — 065's second exclusion. Its
/// `TypeValue` is the derived instance, discharged statically at no cost to the author,
/// so `Cell[V = Int64]` as a value needs nothing declared.
#[test]
fn a_concrete_sort_in_value_position_needs_no_clause() {
    let src = r#"
namespace test.n31xx.concrete
  import anthill.prelude.{Cell, Int64, Type}

  operation ty() -> Type = Cell[V = Int64]
end
"#;
    assert_eq!(eval_type(src, "test.n31xx.concrete.ty"), "Cell(V: Int64)");
}

/// 065 §6's NINETEENTH CENSUS SITE, and the reason the rule is judged on the tree the
/// typer WROTE BACK rather than the one it was handed.
///
/// `dq[K]()` passes `K` as an ARGUMENT to a `@[simp]` equation whose RHS puts it in a
/// TYPE position. Before expansion `K` looks like a value read and the rule would refuse
/// a program whose only use of `K` is as a type; after expansion there is no value read
/// at all. `dq` therefore carries NO clause — that absence is the assertion.
///
/// THE CONTROL IS THE SECOND OPERATION, which reads `K` as a genuine value and does
/// carry the clause: without it this row would pass equally against a rule that never
/// fired in this file at all.
#[test]
fn a_simp_expanded_type_position_is_not_a_value_read() {
    let src = r#"
namespace test.n31xx.simp
  import anthill.prelude.{Map, Int64, String, Cell, Type}
  import anthill.prelude.Map.{put, size}
  import anthill.reflect.{TypeValue}

  rule mkq(?k) <=> Map[K = ?k, V = Int64].empty() @[simp]

  operation dq[K]() -> Int64 = size(put(mkq(K), "a", 1))
  operation genuine[K]() -> Type requires TypeValue[T = K] = Cell[V = K]

  operation ask() -> Int64 = dq[K = String]()
  operation ask_ty() -> Type = genuine[K = String]()
end
"#;
    assert_eq!(
        load_errors(src),
        Vec::<String>::new(),
        "a `K` that @[simp] inlining places in a TYPE position is not a value read"
    );
    let mut interp = interp_for(src);
    assert!(
        matches!(interp.call("test.n31xx.simp.ask", &[]), Ok(Value::Int(1))),
        "and the program still answers"
    );
    assert_eq!(
        eval_type(src, "test.n31xx.simp.ask_ty"),
        "Cell(V: String)",
        "the control: a genuine value read in the same file, under its clause"
    );
}

// ── PROPOSAL 065 OPEN QUESTION 3 — A FORMER CARRIER ──────────────────────────────────

/// A REQUIREMENT AT A STRUCTURAL FORMER IS REFUSED AT LOAD, where it used to load and
/// PANIC — proposal 065 open question 3, fixed inline 2026-09-22.
///
/// §2's derivation is SORTS ONLY: a tuple or an arrow has no sort to carry a `provides`
/// row, so no `TypeValue` instance names one. 065 predicted this shape needed "either an
/// effect-row analogue or a refusal" and proposed refusing. What actually happened was
/// neither. MEASURED before the fix, and it is why this is a defect and not a deferral:
///
/// ```text
/// bridge_op_to_eval: internal evaluator error bridging `tyOf`:
/// DeferToRequirement: requirement param `__req_typevalue` not bound in caller frame
/// ```
///
/// — a PANIC, from a program that LOADED CLEAN. Both arms beside the new one answer
/// `None` here and neither is wrong to: `unprovided_provision` bails at
/// `sort_functor_of_view` (a former has no sort to name in a repair line) and
/// `caller_rigid_carrier` bails because the carrier is ground, not a caller parameter.
/// With both silent the slot fell through to the silent-absence rule, which exists for
/// the 29 stdlib bodies that declare a chain and never read it — and this body reads it.
///
/// BACK-OUT: delete the `former_carrier` arm in `build_op_scoped_dicts` and this row is
/// red BY PANIC, not by a wrong message — the abort is the pre-fix behaviour.
#[test]
fn a_requirement_at_a_former_is_refused_rather_than_aborting() {
    let errs = load_errors(
        r#"
namespace test.n31xx.former
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]

  operation ask() -> Type = tyOf((1, 2))
end
"#,
    );
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    let e = &errs[0];
    for want in [
        "anthill.reflect.TypeValue",
        "test.n31xx.former.tyOf",
        "a STRUCTURAL FORMER",
        // THE REASON, not just the verdict: what the refusal says is that NOTHING
        // PROVIDES the spec at this former — not that a former is unprovidable, which
        // /code-review measured to be false (see
        // [`control_a_former_carrier_with_a_provision_loads`]). A row asserting only
        // "refused" would keep passing against a refusal that blamed the wrong thing,
        // and these two strings are exactly what the first cut got wrong.
        "nothing provides `anthill.reflect.TypeValue` at it",
        // AND THE REPAIR THAT WORKS: the row an author could write. The superseded
        // wording advised wrapping the former in a sort, which is a different program.
        "Give some sort the row that names this former",
    ] {
        assert!(e.contains(want), "expected {want:?} in the refusal; got {e:?}");
    }
    // AT THE CALL (the fixture's eighth line), not at `tyOf`'s declaration on the sixth:
    // `tyOf` is well-formed and it is this argument that cannot supply its clause.
    assert!(
        e.starts_with("8:"),
        "the refusal belongs at the call that passes the former; got {e:?}"
    );
}

/// CONTROL — THE SORT-LEVEL SPELLING WAS NEVER BROKEN, and that is why the fix is one
/// arm in the OP half rather than a rule in both.
///
/// `build_dispatching_dict_from_chain` is all-or-nothing: `require_complete` drops an
/// incomplete dictionary whole, so a former carrier there was already a load refusal.
/// The op half is best-effort and PER-SLOT — a discharged dep leaves its own slot empty
/// and its siblings supplied — which is exactly how one unfillable slot could stay
/// silent. This row is GREEN EITHER WAY BY DESIGN; it fails only if the fix widened into
/// the sort half and changed a verdict that was already right.
#[test]
fn control_a_former_under_a_sort_level_clause_was_already_refused() {
    let errs = load_errors(
        r#"
namespace test.n31xx.formersort
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  sort Holder[U]
    import anthill.prelude.Type
    import anthill.reflect.{TypeValue}
    requires TypeValue[T = U]
    entity hold(u: U)
    operation tyb() -> Type = Cell[V = U]
  end

  operation ask() -> Type = Holder[U = (Int64, Int64)].tyb()
end
"#,
    );
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    assert!(
        errs[0].contains("anthill.reflect.TypeValue"),
        "the sort half's own refusal, unchanged; got {:?}",
        errs[0]
    );
}

/// CONTROL — A SORT CARRIER KEEPS ITS OWN DIAGNOSTIC, which is the thing a new arm is
/// most likely to steal.
///
/// `Plain` is a sort with no `TypeValue` provision. That is `unprovided_provision`'s
/// case, and its message can name the declaration to repair — `provides` on the carrier
/// — where the former arm's cannot, because a former has no declaration. The new arm is
/// ordered LAST and guards on `sort_functor_of_view(...).is_none()` for exactly this;
/// this row is what says the ordering holds.
///
/// BACK-OUT: ask `former_carrier` BEFORE the other two arms, or drop its sort-functor
/// guard, and this row goes red with the former arm's wording on a carrier that has a
/// perfectly good sort.
#[test]
fn control_a_sort_carrier_with_no_instance_keeps_its_own_message() {
    let errs = load_errors(
        r#"
namespace test.n31xx.plainsort
  import anthill.prelude.{Cell, Int64, Type}

  sort TT
    import anthill.prelude.Type
    sort T = ?
    operation valueOf() -> Type
  end

  sort Plain
    entity plain(n: Int64)
  end

  operation tyOf[B](x: B) -> Type requires TT[T = B] = TT.valueOf()

  operation ask() -> Type = tyOf(plain(1))
end
"#,
    );
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    let e = &errs[0];
    assert!(
        !e.contains("STRUCTURAL FORMER"),
        "a SORT carrier must not be reported as a former; got {e:?}"
    );
    assert!(
        e.contains("test.n31xx.plainsort.Plain") && e.contains("provides"),
        "it keeps the repair that names the carrier's own declaration; got {e:?}"
    );
}

/// CONTROL — THE POSITIVE SIDE, so the arm above is not passing against a rule that
/// refuses every concrete carrier. A SORT with a derived `TypeValue` still answers
/// through the same slot the former could not fill.
#[test]
fn control_a_sort_carrier_with_an_instance_still_answers() {
    let src = r#"
namespace test.n31xx.formerok
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]

  operation ask() -> Type = tyOf(1)
end
"#;
    assert_eq!(load_errors(src), Vec::<String>::new(), "the control must load");
    assert_eq!(eval_type(src, "test.n31xx.formerok.ask"), "Cell(V: Int64)");
}

/// CONTROL — A BODY-LESS CALLEE IS EXEMPT, and this row is why the arm above carries a
/// guard instead of refusing every former carrier.
///
/// `Error.reify` declares `requires ErrorTag[T = T1]` and has NO anthill body on purpose:
/// the boundary is a frame the interpreter installs by symbol. A TUPLE payload is a live,
/// correct program — the host NARROWS the caught payload when the evidence is there and
/// catches WIDE when it is not, which is what every boundary did before narrowing
/// existed. So the missing dictionary is the wide case, not a death.
///
/// MEASURED, AND IT IS THE COST OF LEARNING IT: without `former_carrier`'s
/// `op_body_node` guard this program is refused, and with it 20 rows of
/// `wi_9wvt7_error_reify_test` go red — the whole file, since its fixture loads as one
/// program. That is the back-out, and it is a real corpus program rather than a fixture
/// written to defend the guard.
///
/// THE DISTINCTION THE GUARD DRAWS is who interprets an absent slot, not whether the
/// clause is owed. An anthill body has no fallback: 065 §1 lowers a value read to a
/// dispatch through the slot, so an absent one aborts.
#[test]
fn control_a_body_less_callee_may_take_a_former_carrier() {
    let errs = load_errors(
        r#"
namespace test.n31xx.formerhost
  import anthill.prelude.{Error, Int64, Result, String}

  operation raisesTuple(n: Int64) -> Int64 effects {Error[(a: Int64, b: String)]} =
    Error.raise((a: n, b: "neg"))

  operation caughtTuple() -> Result[E = (a: Int64, b: String), T = Int64] =
    Error.reify(lambda () -> raisesTuple(0 - 1))
end
"#,
    );
    assert_eq!(
        errs,
        Vec::<String>::new(),
        "a body-less host-backed callee catches wide at a former payload; got {errs:#?}"
    );
}

/// CONTROL — A FORMER CARRIER **WITH** A PROVISION STILL LOADS, which is what says the
/// arm above refuses "nothing provides it" and not "a former".
///
/// FOUND BY /code-review, as a FALSE CLAIM in the first cut's own message: it said "no
/// instance of `{spec}` can ever name it" and advised wrapping the former in a sort. A
/// former cannot CARRY a provision — a `provides` row is written on a sort — but a SORT
/// may carry one whose spec BINDING is a former, and that satisfies the requirement.
/// The two are different things and the message had conflated them, so its repair sent
/// the author to a different program from the one that works.
///
/// This row is the program that works. It never reaches `former_carrier` at all, because
/// `build_dep_projection` finds `Wrapper`'s row — which is exactly the point: the arm
/// fires on a failed SEARCH, and a widening of it to "a former is unprovidable" would
/// take this row red.
///
/// BACK-OUT: drop the `build_dep_projection` result check and refuse on the carrier's
/// shape alone, and this goes red while the refusal row above stays green — the pair is
/// what distinguishes the two readings.
#[test]
fn control_a_former_carrier_with_a_provision_loads() {
    let errs = load_errors(
        r#"
namespace test.n31xx.formerprov
  import anthill.prelude.{Int64, String, Type}

  sort TT
    import anthill.prelude.Type
    sort T = ?
    operation valueOf() -> Type
  end

  sort Wrapper
    import anthill.prelude.{Int64, String, Type}
    entity wrap(n: Int64)
    provides TT[T = (a: Int64, b: String)]
    operation valueOf() -> Type = Int64
  end

  operation tyOf[B](x: B) -> Type requires TT[T = B] = TT.valueOf()

  operation ask() -> Type = tyOf((a: 1, b: "x"))
end
"#,
    );
    assert_eq!(
        errs,
        Vec::<String>::new(),
        "a sort may provide a spec AT a former binding; got {errs:#?}"
    );
}
