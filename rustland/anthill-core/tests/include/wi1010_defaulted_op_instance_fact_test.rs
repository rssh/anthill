//! WI-1010 — a spec op's DEFAULT BODY must not SHADOW an implementation a
//! PROVISION supplies for the carrier.
//!
//! WI-444 stated the rule ("defaults fill GAPS, they do not SHADOW") and
//! implemented it for ONE supply route: the carrier's own member
//! (`carrier_override_op`, filtered `impl_parent_of_op(o) == carrier`). A WI-431
//! retroactive instance fact's op-valued binding never reached that gate, so a
//! carrier whose only implementation is written as `fact Desc[T = Leaf, describe =
//! leafDescribe]` ran the DEFAULT — with the loader having already validated that
//! binding's signature (`check_instance_fact_op_signatures`) and counted it as
//! backing. A silent wrong answer, not a missing feature.
//!
//! The fix gives every supply route the same standing by reading the SAME owner the
//! body-less path reads (`spec_op_suppliers_for_carrier`, WI-842 / 058 §4.9),
//! narrowed to what the interpreter can run — see `carrier_override_suppliers`.
//!
//! WHAT FAILS IF THIS IS BACKED OUT — MEASURED by reverting each half on its own and
//! then both, not predicted. The prediction was wrong, and the way it was wrong is
//! the useful part: for a call the typer can PIN, the two halves are REDUNDANT, so
//! the three headline answers need BOTH backed out before they move.
//!
//! | test | typer | eval | both |
//! |---|---|---|---|
//! | `a_fact_bound_impl_beats_the_spec_default` | ok | ok | **FAILS** |
//! | `a_fact_completing_a_type_only_provision_beats_the_default` | ok | ok | **FAILS** |
//! | `a_witness_supplied_impl_beats_the_spec_default` | ok | ok | **FAILS** |
//! | `an_unrunnable_own_member_is_not_a_supplier` | ok | ok | **FAILS** |
//! | `an_abstract_receiver_reaches_the_fact_bound_impl` | ok | **FAILS** | **FAILS** |
//! | `a_fact_bound_impls_effects_reach_the_call_site` | **FAILS** | ok | **FAILS** |
//! | `an_own_member_rivalled_by_a_fact_binding_is_refused_at_the_call` | **FAILS** | **FAILS** | **FAILS** |
//! | `the_carriers_own_member_still_beats_the_default` | ok | ok | ok |
//! | `a_carrier_with_no_supplier_still_runs_the_default` | ok | ok | ok |
//!
//! So each half is separately load-bearing, and the two tests that prove it are the
//! ones the redundancy does NOT cover: only the typer's static pin can surface a
//! bound impl's EFFECTS at the call, and only the eval read sees a carrier the typer
//! could not pin. The tie needs both, since either half left un-widened selects
//! silently on its own.
//!
//! `an_unrunnable_own_member_is_not_a_supplier` has a SECOND control, orthogonal to
//! this table and stated at the test: deleting the interpretability filter (with both
//! halves in place) turns its 7 into `AmbiguousSpecOpDispatch`.
//!
//! The last two pass EITHER WAY **by design**: they are route 1 and the gap case,
//! the two answers this ticket must NOT change. Route 1's reader is preserved
//! bit-for-bit (`carrier_own_op` + `op_is_interpretable` is what
//! `carrier_override_op` already was), and the gap case is what makes a default a
//! default. They are here to fail if a later change moves either.
//!
//! GUARDRAIL: the precedence change was measured corpus-inert before any arm was
//! written (the ticket's precondition, since WI-876 gave `PartialOrd.gt/gte/lt/lte`
//! and `Ordered.max/min` default bodies). The numbers live in
//! `docs/design/058-implementation.md` §12 and are NOT restated here — they are a
//! point-in-time fact about the stdlib, and the first library provision that supplies
//! a defaulted spec op falsifies them; one copy is findable, two rot apart.
//!
//! REFERENCE: WI-444; WI-431; WI-842; `docs/design/058-implementation.md` §11, §12.

use anthill_core::eval::{EvalError, Value};

/// Load `src` and answer `{ns}.probe` as an Int.
///
/// No separate load-clean assertion: `interp_for` goes through `expect_loaded`, which
/// is WI-966's one owner of "a load error fails the test" and already panics naming
/// every error. Asserting it here again would re-implement that policy AND pay a
/// second full stdlib `load_all` per call.
fn probe(ns: &str, src: &str) -> i64 {
    let op = format!("{ns}.probe");
    match crate::common::interp_for(src).call(&op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// The ticket's program shape: a spec whose `describe` has a DEFAULT BODY (1), and a
/// `Leaf` carrier whose implementation (7) arrives however `supply` writes it. The
/// two answers disagree on purpose — 1 is the default firing, 7 is the supplied impl.
fn program(ns: &str, leaf_body: &str, supply: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
{leaf_body}  end
{supply}
  operation probe() -> Int64 = Desc.describe(leaf())
end
"#
    )
}

/// THE TICKET'S PROGRAM (B) — the retroactive fact ALONE. `Leaf` writes no provision
/// of its own, so the fact is the only thing that says `Leaf` implements `Desc`, and
/// the binding is the only implementation. Before the fix this answered 1.
#[test]
fn a_fact_bound_impl_beats_the_spec_default() {
    let ns = "test.wi1010.factonly";
    let src = program(
        ns,
        "",
        "\n  operation leafDescribe(x: Leaf) -> Int64 = 7\n\n  \
         fact Desc[T = Leaf, describe = leafDescribe]\n",
    );
    assert_eq!(
        probe(ns, &src),
        7,
        "the fact's `describe = leafDescribe` binding is the carrier's ONLY \
         implementation — the spec default must not shadow it",
    );
}

/// THE TICKET'S PROGRAM (A) — the same fact BESIDE the carrier's own type-only
/// provision. The provision is what WI-859 calls a self-provider; it supplies no op,
/// so it neither adds a candidate nor hides the fact's. Pinned separately from (B)
/// because it is what proved the carrier's provision was not the cause.
#[test]
fn a_fact_completing_a_type_only_provision_beats_the_default() {
    let ns = "test.wi1010.provplusfact";
    let src = program(
        ns,
        "    provides Desc[T = Leaf]\n",
        "\n  operation leafDescribe(x: Leaf) -> Int64 = 7\n\n  \
         fact Desc[T = Leaf, describe = leafDescribe]\n",
    );
    assert_eq!(probe(ns, &src), 7, "a type-only provision beside the fact changes nothing");
}

/// ROUTE 3 — a WITNESS sort supplying the defaulted op. The same defect one route
/// over, and it closes with the fix because the fix shares one reader across all
/// three routes rather than adding a leg for the fact alone.
#[test]
fn a_witness_supplied_impl_beats_the_spec_default() {
    let ns = "test.wi1010.witness";
    let src = program(
        ns,
        "",
        "\n  sort LeafDesc\n    import anthill.prelude.Int64\n    \
         provides Desc[T = Leaf]\n    \
         operation describe(x: Leaf) -> Int64 = 7\n  end\n",
    );
    assert_eq!(probe(ns, &src), 7, "a witness sort's member is an implementation, not a gap");
}

/// ROUTE 1, THE CONTROL — passes either way by design. The carrier's own member is
/// what WI-444 already resolved, and this ticket must not move it: the new reader's
/// own leg is the old reader spelled out.
#[test]
fn the_carriers_own_member_still_beats_the_default() {
    let ns = "test.wi1010.ownmember";
    let src = program(
        ns,
        "    provides Desc[T = Leaf]\n    operation describe(x: Leaf) -> Int64 = 7\n",
        "",
    );
    assert_eq!(probe(ns, &src), 7, "WI-444's own answer, unchanged");
}

/// THE GAP, THE OTHER CONTROL — passes either way by design. No route supplies an
/// implementation, so the default fires. This is what makes a default a default, and
/// widening which routes are consulted must not consume it.
#[test]
fn a_carrier_with_no_supplier_still_runs_the_default() {
    let ns = "test.wi1010.gap";
    let src = program(ns, "    provides Desc[T = Leaf]\n", "");
    assert_eq!(probe(ns, &src), 1, "nothing supplies `describe` — the default fills the gap");
}

/// THE EVAL HALF. The typer pins the fixtures above statically (the receiver's static
/// carrier IS `Leaf`), so a program is needed where it cannot: `via_spec` takes an
/// abstract-spec `Shape`, which `carrier_is_abstract_spec` makes the typer defer on,
/// and only the runtime value names `Leaf`. This is the only test whose answer the
/// eval read ALONE decides — the tie below reaches that read too, but needs the
/// typer half as well (see the matrix at the top).
#[test]
fn an_abstract_receiver_reaches_the_fact_bound_impl() {
    let ns = "test.wi1010.evalhalf";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Shape
    sort E = ?
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Shape[E = Int64]
  end

  operation leafDescribe(x: Leaf) -> Int64 = 7

  fact Desc[T = Leaf, describe = leafDescribe]

  operation via_spec(s: Shape) -> Int64 = Desc.describe(s)
  operation probe() -> Int64 = via_spec(leaf())
end
"#
    );
    assert_eq!(
        probe(ns, &src),
        7,
        "the typer cannot pin an abstract-spec carrier — the runtime value's own \
         sort must still reach the fact's binding",
    );
}

/// THE SECOND CANDIDATE. The carrier's own member and a fact binding a DIFFERENT
/// operation are two implementations, and this read SELECTS one — so 058 §4.9 makes
/// it loud rather than letting route order decide. Before the fix the fact was
/// invisible here and the own member answered 7 silently.
///
/// Raised at the CALL, in eval, not at load: this is a bracket-less site (nothing
/// later can name a selection), and `TypeError::DispatchAmbiguous` cannot describe
/// this tie at all — its `InstanceTie` carries PROVIDER SYMBOLS, and an instance
/// fact has no name (058 §4.3). `EvalError::AmbiguousSpecOpDispatch` renders the
/// ROUTE of each candidate, so the fact leg can echo the binding the author wrote.
#[test]
fn an_own_member_rivalled_by_a_fact_binding_is_refused_at_the_call() {
    let ns = "test.wi1010.tie";
    let src = program(
        ns,
        "    provides Desc[T = Leaf]\n    operation describe(x: Leaf) -> Int64 = 7\n",
        "\n  operation otherDescribe(x: Leaf) -> Int64 = 9\n\n  \
         fact Desc[T = Leaf, describe = otherDescribe]\n",
    );
    // The pair is legal to DECLARE — `interp_for` panics on a load error, so reaching
    // the call at all is that assertion; the refusal belongs to the call, not the load.
    let err = crate::common::interp_for(&src)
        .call(&format!("{ns}.probe"), &[])
        .expect_err("two implementations, no selection — the call must be refused");
    let EvalError::AmbiguousSpecOpDispatch { carrier, candidates, .. } = &err else {
        panic!("expected AmbiguousSpecOpDispatch, got {err:?}");
    };
    assert!(carrier.ends_with(".Leaf"), "the tie is per CARRIER: {carrier}");
    assert!(
        candidates.iter().any(|c| c.contains("own member") && c.ends_with("Leaf.describe'")),
        "route 1 must be named: {candidates:?}",
    );
    assert!(
        candidates.iter().any(|c| c.contains("instance fact binding")
            && c.contains("describe = ")
            && c.ends_with("otherDescribe`")),
        "the nameless fact must be quoted by its BINDING: {candidates:?}",
    );
}

/// WHAT THE TYPER HALF UNIQUELY BUYS — effect soundness (the WI-453 pattern the
/// carrier-own path already had). The fact binds an impl that raises `Boom`; the spec
/// op's DEFAULT is pure. Only a static pin surfaces the impl's real effects at the
/// call, so without the typer half `probe` types against the pure default, loads
/// CLEAN, and then runs an effectful operation — an undeclared effect escaping,
/// which is a soundness hole and not merely a wrong number.
///
/// The signature validator cannot cover this: `check_instance_fact_op_signatures`
/// checks arity, params and return, NOT effects (WI-431 increment 5), and
/// `check_override_refinement`'s effect check is fail-open by design.
///
/// Both directions are driven, because "it is refused" alone would also be satisfied
/// by refusing the shape outright: declaring the effect makes the same program load
/// AND answer through the binding.
#[test]
fn a_fact_bound_impls_effects_reach_the_call_site() {
    let effectful_program = |ns: &str, decl: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Effect, Int64}}
  sort Boom end
  fact Effect[T = Boom]

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
  end

  operation leafDescribe(x: Leaf) -> Int64 effects Boom = 7

  fact Desc[T = Leaf, describe = leafDescribe]

  operation probe() -> Int64{decl} = Desc.describe(leaf())
end
"#
        )
    };
    let errs = crate::common::try_load_kb_with(&effectful_program("test.wi1010.effundeclared", ""))
        .err()
        .unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect: Boom")),
        "the bound impl's `Boom` must reach the call site, not the default's empty row: {errs:?}",
    );

    let ns = "test.wi1010.effdeclared";
    assert_eq!(
        probe(ns, &effectful_program(ns, " effects Boom")),
        7,
        "declaring the effect must make the SAME program load and answer through the binding",
    );
}

/// THE INTERPRETABILITY FILTER's own control — the one thing
/// `carrier_override_suppliers` adds on top of the shared owner it delegates to.
/// `Leaf.describe` is DECLARED with no body, so the interpreter cannot run it; a fact
/// binds a runnable `otherDescribe`. Dropping the unrunnable member BEFORE the count
/// leaves ONE supplier and the call answers 7.
///
/// MEASURED both ways: with the filter removed this is not "7 from the other
/// candidate" but `AmbiguousSpecOpDispatch` — a refusal caused entirely by a member
/// nothing can call. What this does NOT pin is the filter's PLACEMENT: pushing it down
/// into `spec_op_suppliers_for_carrier` keeps the whole suite green, because the tree
/// holds no cpp-mapped rival that would make the body-less path's coherence count
/// diverge. That argument is stated at `carrier_override_suppliers` and guarded by
/// nothing else — said plainly here so the gap is known rather than assumed covered.
#[test]
fn an_unrunnable_own_member_is_not_a_supplier() {
    let ns = "test.wi1010.unrunnable";
    let src = program(
        ns,
        "    provides Desc[T = Leaf]\n    operation describe(x: Leaf) -> Int64\n",
        "\n  operation otherDescribe(x: Leaf) -> Int64 = 7\n\n  \
         fact Desc[T = Leaf, describe = otherDescribe]\n",
    );
    assert_eq!(
        probe(ns, &src),
        7,
        "a member the interpreter cannot run is not a supplier — it must neither be \
         selected nor counted as the second candidate",
    );
}
