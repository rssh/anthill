//! WI-1095 — the frame-read predicate counted THREE channels and there are FIVE. The
//! two it missed each LOADED CLEAN and died at evaluation, which is the one outcome
//! §5.2 exists to forbid ("deferring the failure to evaluation would be a clean load
//! that crashes at run time").
//!
//! THE SAME DEFECT, A SECOND TIME. WI-945 shipped its predicate with TWO channels and
//! gained the third from /code-review, pinned by
//! `a_forwarded_slot_inside_a_built_dictionary_is_refused_too`. This file is the third
//! and fourth, found the same way. The repair is therefore not "two more arms": the
//! `match` on `CallClass` is now EXHAUSTIVE with no `_`, so a sixth variant that can
//! carry a dictionary is a compile error rather than a silent `Nothing`. MEASURED, not
//! asserted — a sixth variant added to `CallClass` and the workspace built: `error[E0004]
//! non-exhaustive patterns` at BOTH predicates (`typing.rs` sort half and op half), then
//! removed. A compile-time guard nobody has tripped on purpose is a claim, not a guard,
//! and this one cannot be driven from a test file.
//!
//! THE TWO CHANNELS, and what each one is:
//!
//!  (4) AN OP-SCOPED FORWARD. `ConcreteApplyWithin` carries `op_dicts` beside
//!      `dispatch_dict`, and `build_op_scoped_dicts` projects those against the
//!      enclosing frame chain — so one of them can be a `var_ref` into THIS frame,
//!      exactly the shape the `dispatch_dict` arm was added for. Worse, the miss was
//!      systematic in the shape where `dispatch_dict` is `None` (a callee whose SORT
//!      requires nothing while its OPERATION does): the old code read that `None` as
//!      "inherits", and the inherit arm drops every cross-sort target.
//!
//!  (5) AN ETA. `CallClass::EtaOpRef` was not matched at all — it fell through the `_`
//!      arm. `attach_eta_dispatch_dict` mints `var_ref(__req_self)` for a same-sort eta
//!      and a `build_concrete_dispatch_dict` result (forwards included) for a cross-sort
//!      one, with `op_dicts` riding beside both. An eta never INHERITS however same-sort
//!      it is — the `OpRef` escapes to a foreign apply frame, which is precisely why the
//!      typer hands it a `var_ref` instead.
//!
//! TWO EDITS, ONE CHANNEL, and the reason `an_eta_of_a_same_sort_sibling_is_refused` is
//! its own row: `sort_names` is `chain.names()`, the `__req_<spec>` list, and
//! `__req_self` is not in it. MEASURED — with the `EtaOpRef` arm wired and the
//! `__req_self` push backed out, this file's cross-sort eta row is refused and the
//! same-sort one still loads clean and dies `var_ref(__req_self) unbound in requirement
//! position`. A fix that makes only the first edit looks right and changes no verdict on
//! that row.
//!
//! WHAT EACH TEST MEASURES, AND WHAT BACKING THE CHANGE OUT COSTS. Every subject below
//! was run against the pre-fix predicate (`git stash` on `typing.rs`, full workspace):
//! each LOADED CLEAN and raised at eval, verbatim —
//!  - `an_op_scoped_forward_is_refused`: `DeferToRequirement: requirement param
//!    `__req_doubler` not bound in caller frame (running `…Inner.innerOp`…; frame binds
//!    [])`;
//!  - `an_eta_of_a_same_sort_sibling_is_refused`: `var_ref(__req_self) unbound in
//!    requirement position (running `…HolderVS.twice`; frame binds [])`;
//!  - `an_eta_of_a_cross_sort_op_forwards_this_frame_too`: `var_ref(__req_doubler)
//!    unbound in requirement position (running `…HolderVS.twice`; frame binds [])`;
//!  - `an_eta_reaches_the_op_half_slot_too`: `DeferToRequirement: requirement param
//!    `__req_desc` not bound in caller frame (running `…Silent.helper`…; frame binds
//!    [])`.
//! Each control PASSES with the change backed out, BY DESIGN — that is what makes it a
//! control: it says the refusal is attributable to the unsuppliable element and not to
//! anything else in its fixture.
//!
//! THE CORPUS, measured rather than assumed (WI-945's own lesson: its predicted blanket
//! fix would have flipped four call-site classes, three of them working programs). Both
//! predicates were run side by side with their pre-WI-1095 twins over the full
//! workspace: 98 parked refusals reach the verdict (84 sort-half, 14 op-half), 16
//! answered `true` under both, 78 answered `false` under both, and exactly 4 flip — the
//! four subjects in this file. Nothing that ran before is refused now.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;

// ── fixtures ────────────────────────────────────────────────────────────────

/// (4) AN OP-SCOPED FORWARD. `HolderVS.twice` calls `Inner.innerOp`, whose OWN
/// `requires Doubler[W]` is filled by forwarding `HolderVS`'s `__req_doubler` — so the
/// forward rides in `op_dicts` and `dispatch_dict` is `None` (`Inner` declares no
/// `requires` of its own). The parent-bundle dictionary is all-or-nothing, so the
/// unconstrained `F` costs the frame `__req_doubler` as well.
fn op_forward_src(ns: &str, requires_vs: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.geometry.{{Vec3}}
  import anthill.prelude.{{Float}}
  import anthill.prelude.algebra.{{VectorSpace}}

  sort Doubler
    sort V = ?
    operation dbl(a: V) -> V
  end

  sort Vec3Doubler
    provides Doubler[V = Vec3]
    operation dbl(a: Vec3) -> Vec3 = a
  end

  sort Inner
    operation innerOp[W](a: W) -> W requires Doubler[W] = Doubler.dbl(a)
  end

  sort HolderVS
    sort V = ?
    sort F = ?
    {requires_vs}
    requires Doubler[V]
    operation twice(a: V) -> V = Inner.innerOp(a)
  end

  sort Driver
    operation drive(a: Vec3) -> Vec3 = HolderVS.twice(a)
  end
end
"#
    )
}

/// (5) A SAME-SORT ETA — the row that drives `__req_self`. `helper` is eta-lifted into
/// `Ap.ap`'s callback slot, and a same-sort eta's dict is `var_ref(__req_self)`: the
/// parent-bundle dictionary itself, read out of a frame that has none.
fn same_sort_eta_src(ns: &str, requires_vs: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.geometry.{{Vec3}}
  import anthill.prelude.{{Float, Function}}
  import anthill.prelude.algebra.{{VectorSpace}}

  sort Ap
    sort T = ?
    operation ap(f: Function[T, T], a: T) -> T = f(a)
  end

  sort HolderVS
    sort V = ?
    sort F = ?
    {requires_vs}
    operation helper(a: V) -> V = VectorSpace.vec_add(a, a)
    operation twice(a: V) -> V = Ap.ap(helper, a)
  end

  sort Driver
    operation drive(a: Vec3) -> Vec3 = HolderVS.twice(a)
  end
end
"#
    )
}

/// (5b) A CROSS-SORT ETA — the row that drives the ARM alone. `Inner`'s sort-level
/// `requires Doubler[V]` at an abstract `V` is FORWARDED into the eta's dict as
/// `var_ref(__req_doubler)`, a name `sort_names` already held: this row is refused as
/// soon as `EtaOpRef` is matched, with or without the `__req_self` half.
fn cross_sort_eta_src(ns: &str, requires_vs: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.geometry.{{Vec3}}
  import anthill.prelude.{{Float, Function}}
  import anthill.prelude.algebra.{{VectorSpace}}

  sort Doubler
    sort V = ?
    operation dbl(a: V) -> V
  end

  sort Vec3Doubler
    provides Doubler[V = Vec3]
    operation dbl(a: Vec3) -> Vec3 = a
  end

  sort Inner
    sort V = ?
    requires Doubler[V]
    operation innerOp(a: V) -> V = Doubler.dbl(a)
  end

  sort Ap
    sort T = ?
    operation ap(f: Function[T, T], a: T) -> T = f(a)
  end

  import {ns}.Inner.{{innerOp}}

  sort HolderVS
    sort V = ?
    sort F = ?
    {requires_vs}
    requires Doubler[V]
    operation twice(a: V) -> V = Ap.ap(innerOp, a)
  end

  sort Driver
    operation drive(a: Vec3) -> Vec3 = HolderVS.twice(a)
  end
end
"#
    )
}

/// (5c) THE OP HALF's eta, at the other predicate and the other park (WI-1102's
/// use-site discharge, `SlotToRead::Op`). `probe`'s own `requires Desc[T = HT]` is read
/// ONLY through the eta of a sibling whose op-scoped slot forwards it — the op-half
/// twin of (5b), and the reason that predicate gained the same arm.
fn op_half_eta_src(ns: &str, carrier: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Function}}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Mystery
    entity mystery
  end
  sort Known
    entity known
  end
  sort KnownDesc
    provides Desc[T = Known]
    operation describe(x: Known) -> Int64 = 7
  end
  sort Ap
    sort T = ?
    operation ap(f: Function[T, Int64], a: T) -> Int64 = f(a)
  end
  sort Silent
    sort HT = ?
    operation helper(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Ap.ap(helper, x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Silent.probe({carrier}())
  end
end
"#
    )
}

// ── helpers ─────────────────────────────────────────────────────────────────

/// A `Vec3(x:, y:, z:)` value. Field symbols are interned, not resolved: `Entity.named`
/// keys on the label and the declared order is (x, y, z).
fn vec3(kb: &mut KnowledgeBase, x: f64, y: f64, z: f64) -> Value {
    let functor = kb
        .try_resolve_symbol("anthill.geometry.Vec3")
        .expect("Vec3 sort");
    let named: Vec<(Symbol, Value)> = vec![
        (kb.intern("x"), Value::Float(x)),
        (kb.intern("y"), Value::Float(y)),
        (kb.intern("z"), Value::Float(z)),
    ];
    Value::Entity {
        functor,
        pos: vec![].into(),
        named: named.into(),
    }
}

fn components(kb: &KnowledgeBase, v: &Value) -> (f64, f64, f64) {
    let Value::Entity { named, .. } = v else {
        panic!("expected a Vec3 entity, got {v:?}");
    };
    let read = |label: &str| -> f64 {
        named
            .iter()
            .find(|(sym, _)| kb.local_name_of(*sym) == label)
            .map(|(_, val)| match val {
                Value::Float(f) => *f,
                other => panic!("field `{label}` is not a Float: {other:?}"),
            })
            .unwrap_or_else(|| panic!("no field `{label}` on {v:?}"))
    };
    (read("x"), read("y"), read("z"))
}

/// The refusal among a fixture's load errors. When the source loads CLEAN — which is
/// what every subject here did before the fix — this RUNS it and puts the evaluator's
/// own raise in the failure message, so backing the change out fails with the crash it
/// re-opened rather than with a claim about one.
fn refusal(src: &str, what: &str, run: impl FnOnce(&str) -> String) -> String {
    let errs = match crate::common::try_load_kb_with(src) {
        Err(errs) => errs,
        Ok(_) => panic!(
            "{what}: expected a load refusal, but the source LOADED CLEAN — and running \
             it then gave: {}",
            run(src)
        ),
    };
    errs.iter()
        .find(|e| e.contains("cannot be supplied"))
        .unwrap_or_else(|| panic!("{what}: no refusal among load errors:\n{}", errs.join("\n")))
        .clone()
}

/// What `<ns>.Driver.drive(Vec3(1,2,3))` does — the evaluator's raise verbatim when
/// there is one. Reached only from [`refusal`]'s clean-load failure path.
fn drive_outcome_vec3(src: &str, ns: &str) -> String {
    let mut interp = crate::common::interp_for(src);
    let a = vec3(interp.kb_mut(), 1.0, 2.0, 3.0);
    match interp.call(&format!("{ns}.Driver.drive"), &[a]) {
        Ok(v) => format!("an ANSWER, {v:?}"),
        Err(e) => format!("{e}"),
    }
}

/// The same for the `Int64`-valued op-half fixture.
fn drive_outcome_int(src: &str, ns: &str) -> String {
    let mut interp = crate::common::interp_for(src);
    match interp.call(&format!("{ns}.Driver.drive"), &[Value::Int(0)]) {
        Ok(v) => format!("an ANSWER, {v:?}"),
        Err(e) => format!("{e}"),
    }
}

/// `<ns>.Driver.drive(Vec3(1,2,3))` must answer `want`. A FRESH interpreter per call —
/// a trapped call poisons a shared one.
fn drive_123(src: &str, ns: &str, want: (f64, f64, f64), why: &str) {
    let mut interp = crate::common::interp_for(src);
    let a = vec3(interp.kb_mut(), 1.0, 2.0, 3.0);
    let entry = format!("{ns}.Driver.drive");
    let out = interp
        .call(&entry, &[a])
        .unwrap_or_else(|e| panic!("{entry}: {why}; got {e}"));
    assert_eq!(components(interp.kb(), &out), want, "{entry}: {why}");
}

/// Every piece §5.2 requires of the sort-half diagnostic, plus its location.
fn assert_names_the_unconstrained_element(text: &str, ns: &str, callee: &str) {
    for piece in [
        // the requirement, rendered at the call's own bindings
        "anthill.prelude.algebra.VectorSpace[V = anthill.geometry.Vec3",
        // the unconstrained element — the whole point of the refusal
        &format!("F = {ns}.HolderVS.F"),
        "unconstrained",
        // and which call it is about
        callee,
    ] {
        assert!(
            text.contains(piece),
            "the refusal must name `{piece}`; got:\n{text}"
        );
    }
    assert!(
        text.chars().next().is_some_and(|c| c.is_ascii_digit()),
        "the refusal must be located (line:col prefix); got:\n{text}"
    );
}

// ── (4) the op-scoped forward ───────────────────────────────────────────────

#[test]
fn an_op_scoped_forward_is_refused() {
    let ns = "test.wi1095.opfwd";
    let text = refusal(
        &op_forward_src(ns, "requires VectorSpace[V, F]"),
        "an op-scoped `requires` filled by a caller-frame forward",
        |src| drive_outcome_vec3(src, ns),
    );
    assert_names_the_unconstrained_element(&text, ns, &format!("{ns}.HolderVS.twice"));
}

/// CONTROL — the identical program with `F` pinned. It loads AND answers, so the
/// refusal above is attributable to the unconstrained `F` and to nothing else in the
/// fixture (the eta, the op-scoped clause and the forward are all still there).
/// Vec3(1,2,3) because `Vec3Doubler.dbl` is the identity. Passes with the change
/// backed out, by design.
#[test]
fn control_the_op_scoped_forward_with_f_pinned_still_runs() {
    let ns = "test.wi1095.opfwd.pinned";
    drive_123(
        &op_forward_src(ns, "requires VectorSpace[V = V, F = Float]"),
        ns,
        (1.0, 2.0, 3.0),
        "a pinned element must still build the dictionary the op-scoped slot forwards",
    );
}

// ── (5) the eta, same-sort: the `__req_self` row ────────────────────────────

/// THE `__req_self` ROW. Backing out ONLY the `sort_names.push(__req_self)` — leaving
/// the `EtaOpRef` arm wired — makes this test fail (loads clean, then
/// `var_ref(__req_self) unbound in requirement position`) while every other test in
/// this file still passes. That is what it is here to say.
#[test]
fn an_eta_of_a_same_sort_sibling_is_refused() {
    let ns = "test.wi1095.selfeta";
    let text = refusal(
        &same_sort_eta_src(ns, "requires VectorSpace[V, F]"),
        "a same-sort eta, whose dict is `var_ref(__req_self)`",
        |src| drive_outcome_vec3(src, ns),
    );
    assert_names_the_unconstrained_element(&text, ns, &format!("{ns}.HolderVS.twice"));
}

/// CONTROL — `F` pinned, same eta, and the HOF still applies the `OpRef` to answer
/// Vec3(2,4,6). Passes with the change backed out, by design.
#[test]
fn control_the_same_sort_eta_with_f_pinned_still_runs() {
    let ns = "test.wi1095.selfeta.pinned";
    drive_123(
        &same_sort_eta_src(ns, "requires VectorSpace[V = V, F = Float]"),
        ns,
        (2.0, 4.0, 6.0),
        "a pinned element must still mint an `OpRef` carrying its sort's dictionary",
    );
}

// ── (5b) the eta, cross-sort: the arm alone ─────────────────────────────────

#[test]
fn an_eta_of_a_cross_sort_op_forwards_this_frame_too() {
    let ns = "test.wi1095.crosseta";
    let text = refusal(
        &cross_sort_eta_src(ns, "requires VectorSpace[V, F]"),
        "a cross-sort eta whose built dict forwards `__req_doubler`",
        |src| drive_outcome_vec3(src, ns),
    );
    assert_names_the_unconstrained_element(&text, ns, &format!("{ns}.HolderVS.twice"));
}

/// CONTROL — `F` pinned, and the eta'd cross-sort `innerOp` runs through the HOF.
/// Passes with the change backed out, by design.
#[test]
fn control_the_cross_sort_eta_with_f_pinned_still_runs() {
    let ns = "test.wi1095.crosseta.pinned";
    drive_123(
        &cross_sort_eta_src(ns, "requires VectorSpace[V = V, F = Float]"),
        ns,
        (1.0, 2.0, 3.0),
        "a pinned element must still build the dictionary the eta forwards into",
    );
}

// ── (5c) the eta at the OP half ─────────────────────────────────────────────

/// The op-half predicate's own eta arm, driven through WI-1102's use-site discharge:
/// `Mystery` provides no `Desc`, `probe` reads its op-scoped slot only through the eta
/// of `helper`, and pre-fix that read was invisible.
#[test]
fn an_eta_reaches_the_op_half_slot_too() {
    let ns = "test.wi1095.opeta";
    let text = refusal(
        &op_half_eta_src(ns, "mystery"),
        "an op-scoped slot read only through an eta",
        |src| drive_outcome_int(src, ns),
    );
    for piece in [
        &format!("{ns}.Desc[T = {ns}.Mystery]"),
        &format!("{ns}.Silent.probe"),
        &format!("`{ns}.Mystery` provides no `{ns}.Desc`"),
    ] {
        assert!(
            text.contains(piece.as_str()),
            "the refusal must name `{piece}`; got:\n{text}"
        );
    }
}

/// CONTROL — the same program at a carrier that DOES provide `Desc`. It loads and the
/// eta'd `helper` answers 7 through the HOF, so the refusal above is attributable to the
/// missing provision and not to the eta. Passes with the change backed out, by design.
#[test]
fn control_the_op_half_eta_at_a_provided_carrier_still_runs() {
    let ns = "test.wi1095.opeta.provided";
    let src = op_half_eta_src(ns, "known");
    let mut interp = crate::common::interp_for(&src);
    let entry = format!("{ns}.Driver.drive");
    let out = interp
        .call(&entry, &[Value::Int(0)])
        .unwrap_or_else(|e| panic!("{entry}: a provided carrier must still run; got {e}"));
    assert!(
        matches!(out, Value::Int(7)),
        "{entry}: the eta'd `helper` must reach `KnownDesc.describe` through the \
         op-scoped slot the refusal above is about; got {out:?}",
    );
}
