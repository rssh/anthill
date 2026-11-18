//! WI-20260919-H20YY — A PROVIDER'S OVERRIDE OF A DEFAULTED, RECEIVER-LESS SPEC MEMBER
//! MUST BE REACHED THROUGH THE REQUIREMENT SLOT.
//!
//! `TypeTerm` declares `valueOf() -> Type = T` — a DEFAULT body. `Box` provides
//! `TypeTerm[T = Box[V = V]]` and OVERRIDES `valueOf` as `Option[T = V]`. A caller that
//! holds the slot (`tagOfP[P] requires TypeTerm[T = P]`) and writes `TypeTerm.valueOf()`
//! ran the SPEC'S DEFAULT and never saw the override — silently, no diagnostic. Since
//! 2026-10-17 the call names the instance in its bracket, `TypeTerm.valueOf[T = P]()`, and
//! the bare call beside the clause is refused at load.
//!
//! MEASURED before the fix, on the `Box` row: `Box(V: Boom)` (the default's `T`) where
//! the override says `Option(T: Boom)`. The body-less twin — `TypeTermB.valueOfB` with
//! no default — dispatched to the provider correctly, which is what made the defaulted
//! half a dispatch defect rather than a design gap (WI-20260918-R541X recorded it while
//! writing its (C) fixtures; WI-20260919-891QP closed the body-less half).
//!
//! WHY IT MATTERS: WI-20260911-3MV2C's `raise(error: T) ... requires ErrorTag[T]` has a
//! DEFAULT that is the type term. Overriding that default is the ONE reason to write a
//! provision beyond it, and the override would have been ignored exactly like this.
//!
//! ## The fix, in one line
//!
//! A defaulted spec member whose call names NO carrier is classified
//! `CallClass::DeferToRequirement` — the same classification a body-less one gets — so
//! eval walks the slot's dictionary. It is a DEFERRAL and not a static reroute, which is
//! what keeps the control rows below on the default: `resolve_op_target` answers the
//! provider's override when it has one and the SPEC OP ITSELF when it does not. The
//! rejected alternative (reroute every such call into the WI-210 dispatch block) broke
//! three shipped rows where the default is right; see
//! `wi_nr6fj_defect_b_slot_over_default_test::a_type_variable_slot_now_reaches_the_
//! provider_too`, whose residue this closes.
//!
//! ## Back-outs, each MEASURED over these five rows
//!
//! * **(deferral)** — `defer_defaulted_call_to_slot` returns `false` at entry: the THREE
//!   positives go red, both controls stay green. It also reddens NR6FJ's flipped row and
//!   nothing else in the suite.
//! * **(type-param filter)** — drop the `genuine_concrete_sort` filter in
//!   `carrier_from_declared_slot`: the same three go red, both controls stay green. That
//!   filter is what makes the deferral REACHABLE — without it a slot over `T = P` pins the
//!   type PARAMETER `P` as a carrier sort, and the block takes its no-supplier arm instead.
//! * **(sole-clause gate)** — drop `sole_chain_entry_over_spec` from the deferral: these
//!   five stay green, and two OTHER rows go red —
//!   `wi_nr6fj_defect_b_slot_over_default_test::two_slots_that_disagree_pin_nothing` and
//!   `wi_r541x_body_read_of_type_param_test::two_clauses_over_one_spec_are_refused_at_load`.
//!   Recorded here because it is the gate this file's rows do NOT drive.
//!
//! PASS EITHER WAY BY DESIGN: both control rows below, stated at their sites.
//!
//! ## Since WI-20261105-CBRD2
//!
//! A static operation with a body is the spec's own, and no provider overrides it (decided with
//! the user 2026-11-14): `Box`'s `valueOf` is refused at load. What the slot still carries is the
//! instance the spec's body runs at, its `T` read through the sort's own `requires
//! TypeValue[T = T]`: at `Box[V = Boom]` the body answers `Box[V = Boom]`, through either
//! spelling of the slot and two generic levels. The three rows that reached the override assert
//! that, and the ledger above was measured before.

use anthill_core::persistence::print::TermPrinter;

use crate::common::interp_for;

const SRC: &str = r#"
namespace test.h20yy
  import anthill.prelude.{Option, Int64, String, Type}
  import anthill.reflect.{TypeValue}

  -- The spec, with a DEFAULT body. 065 §3: the clause reading `T` as a VALUE is the
  -- SORT's, not the member's.
  sort TypeTerm
    import anthill.prelude.Type
    import anthill.reflect.{TypeValue}
    sort T = ?
    requires TypeValue[T = T]
    operation valueOf() -> Type = T
  end

  -- A provider with NO override: the default is what should run. The control row.
  sort Boom
    entity boom(why: String)
    provides TypeTerm[T = Boom]
  end

  -- A provider at an application of its own. It may not override `valueOf`, a static
  -- operation with a body ([`a_providers_override_of_a_static_operation_is_refused`]).
  sort Box
    import anthill.prelude.{Option, Type}
    import anthill.reflect.{TypeValue}
    sort V = ?
    entity box(v: V)
    requires TypeValue[T = V]
    provides TypeTerm[T = Box[V = V]]
  end

  -- The OPERATION-level slot spelling.
  operation tagOfP[P](x: P) -> Type requires TypeValue[T = P], TypeTerm[T = P] =
    TypeTerm.valueOf[T = P]()
  operation outerP[Q](y: Q) -> Type requires TypeValue[T = Q], TypeTerm[T = Q] = tagOfP(y)

  -- The SORT-level slot spelling, read at the receiver's instance.
  sort SHold
    import anthill.prelude.Type
    import anthill.reflect.{TypeValue}
    sort E = ?
    entity shold(e: E)
    requires TypeValue[T = E]
    requires TypeTerm[T = E]
    operation f() -> Type = TypeTerm.valueOf[T = E]()
  end

  operation h_override() -> Type = tagOfP(box(boom("x")))
  operation h_override_2lvl() -> Type = outerP(box(boom("x")))
  operation h_default() -> Type = tagOfP(boom("x"))
  operation h_sort_override() -> Type = SHold[E = Box[V = Boom]].f()
  operation h_sort_default() -> Type = SHold[E = Boom].f()
end
"#;

fn eval_type(op: &str) -> String {
    let mut interp = interp_for(SRC);
    let ty = interp
        .call(&format!("test.h20yy.{op}"), &anthill_core::eval::HostValue::all(&[])).map(|h| h.value)
        .unwrap_or_else(|e| panic!("{op}: {e:?}"));
    TermPrinter::new(interp.kb()).print_value(&ty)
}

/// A provider's override of `valueOf` is refused at load: a static operation with a body is the
/// spec's own (WI-20261105-CBRD2). It was the override this file existed to reach.
#[test]
fn a_providers_override_of_a_static_operation_is_refused() {
    let src = SRC.replace(
        "    provides TypeTerm[T = Box[V = V]]\n  end",
        "    provides TypeTerm[T = Box[V = V]]\n    operation valueOf() -> Type = Option[T = V]\n  end",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&src),
        &["`test.h20yy.Box.valueOf` overrides `test.h20yy.TypeTerm.valueOf`", "a static operation with a body"],
        "a provider's own `valueOf`",
    );
}

/// THE HEADLINE ROW, after WI-20261105-CBRD2: the spec's body, reached through an
/// OPERATION-scoped slot, runs at the slot's instance — `Box[V = Boom]`. It was the
/// provider's override, `Option[T = Boom]`.
#[test]
fn the_specs_body_runs_at_an_op_scoped_slots_instance() {
    assert_eq!(eval_type("h_override"), "Box[V = Boom]");
}

/// …through TWO generic levels.
#[test]
fn the_slots_instance_reaches_through_two_generic_levels() {
    assert_eq!(eval_type("h_override_2lvl"), "Box[V = Boom]");
}

/// …and through the SORT-level spelling of the same slot.
#[test]
fn the_specs_body_runs_at_a_sort_level_slots_instance() {
    assert_eq!(eval_type("h_sort_override"), "Box[V = Boom]");
}

/// THE CONTROL THAT MUST STAY GREEN — R541X's headline row
/// (`a_spec_default_reads_the_requirement_it_runs_under`, the same program). A provider
/// WITHOUT an override still runs the spec's DEFAULT body, which reads the spec's own
/// `T`. Defaults fill GAPS; this row is the gap.
///
/// PASSES EITHER WAY BY DESIGN, and MEASURED so under both back-outs above. That is the
/// whole evidence that the fix is a DEFERRAL and not a reroute: `Boom` provides
/// `TypeTerm` and writes no `valueOf`, so the dictionary this call now walks resolves the
/// target back to the spec op itself and the default runs — the same answer by a
/// different route. A reroute would have had to invent one, which is how the rejected
/// alternative broke three shipped rows.
#[test]
fn a_provider_without_an_override_still_gets_the_default() {
    assert_eq!(eval_type("h_default"), "Boom");
}

/// …the same, through the sort-level spelling. Also passes either way by design.
#[test]
fn a_sort_level_slot_without_an_override_still_gets_the_default() {
    assert_eq!(eval_type("h_sort_default"), "Boom");
}
