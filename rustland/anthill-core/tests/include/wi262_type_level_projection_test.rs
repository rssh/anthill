//! WI-262 — type-level dot-access (field projection in TYPE positions).
//!
//! A dotted name in a type slot (here: an `effects Modify[...]` row) whose HEAD
//! resolves to a VALUE place (op param / `result` / local) and whose tail names
//! field(s) is lowered as a value-in-type `denoted` PLACE — the field-access
//! chain over the value — instead of a qualified-name lookup. This is the
//! load-time, scope-aware disambiguation the WI proposed: a value head ⇒
//! projection (`try_denoted_value_path` / `try_expr_carried_projection`); a
//! sort/namespace head ⇒ qualified name (`remap_name`). The capability was built
//! by the WI-302 (denoted value-in-type) / WI-376 (type-member projection) /
//! WI-475 (effect-row projection) cluster; WI-262 confirms it covers the
//! per-component effect-attribution cases and removes the WI-261 stopgap.
//!
//! WI-261 had pre-registered a synthetic `result.<field>` Param symbol per
//! named-tuple return component so qualified-name lookup would find it. That
//! stopgap is now removed (`scan_operation_params`): the projection path
//! intercepts `result.a` BEFORE `remap_name`, so the synthetic symbols were
//! already dead (their kind was `Param`, which `is_result_binder`/region-masking
//! and the WI-352 flow `arg_places` never consult; the projected effect is
//! threaded via the value path, not a symbol-table lookup of `result.a`). The
//! `projected_effect_propagates_and_rejects_pure_caller` test pins that the
//! projected effect is genuinely enforced, not silently dropped.
//!
//! WI-489 (CLOSED the v1 limitation): the denoted place still interns field names
//! raw and resolves them at the elimination/eval site, but when the projection
//! HEAD's type is statically known — a param / `result` of entity or named-tuple
//! type — the loader now validates each tail segment names a real field and emits
//! a loud `InvalidFieldProjection` load error otherwise. (The HEAD was always
//! validated — an unresolved head is a loud error, see
//! `unresolved_projection_head_is_rejected`.) `bogus_field_projection_is_rejected`
//! pins the rejection; `abstract_head_field_projection_defers` pins that the
//! legitimately-deferred case (an abstract receiver whose fields are unknowable
//! until the carrier is concrete — `s.T` / `s.E`, WI-376/WI-475) still loads.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// `Modify[result.a]` / `Modify[result.b]` per named-tuple-return component —
/// the WI-261 driver — typechecks via the projection path with the synthetic
/// `result.<field>` symbols removed.
#[test]
fn result_tuple_component_projection() {
    let src = r#"
namespace wi262.resulttuple
  import anthill.prelude.{Cell, Int64}
  operation make_pair() -> (a: Cell[V = Int64], b: Cell[V = Int64])
    effects {Modify[result.a], Modify[result.b]}
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "Modify[result.a/b] must typecheck via projection; got: {errs:?}");
}

/// `Modify[c.backend]` for a param `c` of ENTITY type — the generalization WI-262
/// adds over WI-261's result-only stopgap.
#[test]
fn entity_param_field_projection() {
    let src = r#"
namespace wi262.entityparam
  import anthill.prelude.{Int64, Modify, EffectsRuntime}
  sort Backend
    entity backend(slot: Int64)
  end
  sort Cellish
    import wi262.entityparam.Backend
    entity cellish(backend: Backend)
  end
  operation touch(c: Cellish) -> Int64
    effects Modify[c.backend]
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "Modify[c.backend] (entity param) must typecheck; got: {errs:?}");
}

/// `Modify[c.x]` for a param `c` of TUPLE type.
#[test]
fn tuple_param_field_projection() {
    let src = r#"
namespace wi262.tupleparam
  import anthill.prelude.{Cell, Int64, Modify, EffectsRuntime}
  operation touch(c: (x: Cell[V = Int64], y: Cell[V = Int64])) -> Int64
    effects Modify[c.x]
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "Modify[c.x] (tuple param) must typecheck; got: {errs:?}");
}

/// Multi-level projection `c.inner.slot` (open-design Q2): the projection path
/// builds the field-access chain over every tail segment.
#[test]
fn multilevel_field_projection() {
    let src = r#"
namespace wi262.multi
  import anthill.prelude.{Int64, Modify, EffectsRuntime}
  sort Leaf
    entity leaf(slot: Int64)
  end
  sort Mid
    import wi262.multi.Leaf
    entity mid(inner: Leaf)
  end
  operation touch(c: Mid) -> Int64
    effects Modify[c.inner.slot]
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "multi-level Modify[c.inner.slot] must typecheck; got: {errs:?}");
}

/// Positional tuple projection `result._1` (open-design Q4).
#[test]
fn positional_tuple_projection() {
    let src = r#"
namespace wi262.positional
  import anthill.prelude.{Cell, Int64, Modify, EffectsRuntime}
  operation make_pair() -> (a: Cell[V = Int64], b: Cell[V = Int64])
    effects Modify[result._1]
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "positional Modify[result._1] must typecheck; got: {errs:?}");
}

/// A sort/namespace HEAD keeps qualified-name resolution (the projection path
/// declines a non-value head) — `Cell[V = Int64]` is a normal parameterized
/// sort, not a projection, and loads as such.
#[test]
fn sort_head_stays_qualified_name() {
    let src = r#"
namespace wi262.sorthead
  import anthill.prelude.{Cell, Int64}
  operation make() -> Cell[V = Int64]
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "a sort-headed parameterized type must still load; got: {errs:?}");
}

/// WI-489: a projection onto a NON-EXISTENT field of a concrete-typed head —
/// `result.nonexistent` where the return is the named tuple `(a:.., b:..)` — is a
/// loud `InvalidFieldProjection` load error (the head's type is statically known,
/// so the field is checkable at load), not the old silent accept.
#[test]
fn bogus_field_projection_is_rejected() {
    let src = r#"
namespace wi262.bogus
  import anthill.prelude.{Cell, Int64}
  operation make_pair() -> (a: Cell[V = Int64], b: Cell[V = Int64])
    effects Modify[result.nonexistent]
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("field projection") && e.contains("nonexistent")),
        "a bogus field in a value-in-type projection off a concrete-typed head must \
         be a loud load error; got: {errs:?}",
    );
}

/// WI-489: the entity-param twin — `Modify[c.bogus]` for a param `c` of a known
/// ENTITY type whose constructor has no `bogus` field is rejected at load.
#[test]
fn bogus_entity_param_field_projection_is_rejected() {
    let src = r#"
namespace wi262.bogusentity
  import anthill.prelude.{Int64, Modify, EffectsRuntime}
  sort Cellish
    entity cellish(backend: Int64)
  end
  operation touch(c: Cellish) -> Int64
    effects Modify[c.bogus]
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("field projection") && e.contains("bogus")),
        "a bogus field off a concrete entity param must be rejected; got: {errs:?}",
    );
}

/// WI-489: a bogus field at a DEEPER level of a multi-level path
/// (`c.inner.bogus`) is rejected too — the walk threads the intermediate field's
/// type (`Mid.inner : Leaf`) and validates `bogus` against `Leaf`.
#[test]
fn bogus_deep_field_projection_is_rejected() {
    let src = r#"
namespace wi262.bogusdeep
  import anthill.prelude.{Int64, Modify, EffectsRuntime}
  sort Leaf
    entity leaf(slot: Int64)
  end
  sort Mid
    import wi262.bogusdeep.Leaf
    entity mid(inner: Leaf)
  end
  operation touch(c: Mid) -> Int64
    effects Modify[c.inner.bogus]
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("field projection") && e.contains("bogus")),
        "a bogus field at a deeper path level must be rejected; got: {errs:?}",
    );
}

/// WI-489 (the must-NOT-regress half): when the projection head's type is ABSTRACT
/// — here a param of an operation type-parameter type `c: T` — the field is only
/// knowable once the carrier is concrete, so validation DEFERS and the projection
/// still loads. This is the legitimately-deferred case the `s.T` / `s.E` abstract
/// projections (WI-376/WI-475) rely on; a field check must not false-reject it.
#[test]
fn abstract_head_field_projection_defers() {
    let src = r#"
namespace wi262.abstracthead
  import anthill.prelude.{Int64, Modify, EffectsRuntime}
  operation touch[T](c: T) -> Int64
    effects Modify[c.whatever]
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "a field projection off an ABSTRACT-typed head must DEFER (load clean), not \
         false-reject — its fields are unknowable until the carrier is concrete; \
         got: {errs:?}",
    );
}

// ── Semantic-strength tests: the projected effect actually PROPAGATES ─────────

/// THE soundness payoff (the WI-475 reject-the-pure-caller pattern): an op
/// declares `effects Modify[c.backend]`; a PURE caller invoking it is REJECTED
/// with an undeclared-effect diagnostic naming the projected `Modify[c.backend]`.
/// This proves the projection attributes a REAL effect that the typer threads
/// and checks — not a silently-dropped no-op the `errs.is_empty()` positives
/// above couldn't distinguish.
#[test]
fn projected_effect_propagates_and_rejects_pure_caller() {
    let src = r#"
namespace wi262.propagate
  import anthill.prelude.{Int64, Bool, Modify, EffectsRuntime}
  sort Backend
    entity backend(slot: Int64)
  end
  sort Cellish
    import wi262.propagate.Backend
    entity cellish(backend: Backend)
  end
  operation touch(c: Cellish) -> Int64
    effects Modify[c.backend]
  operation pure_caller(c: Cellish) -> Int64 = touch(c)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect") && e.contains("Modify")),
        "a pure caller of an op with `effects Modify[c.backend]` must be rejected \
         with an undeclared-effect diagnostic naming Modify — proving the \
         projected effect propagates; got: {errs:?}",
    );
}

/// A dotted HEAD that resolves to nothing (not a value, not a sort) stays a loud
/// error: the projection gate declines a non-value head, and `remap_name`
/// reports the unresolved name. (Field resolution is deferred — see
/// `bogus_field_projection_is_not_yet_rejected` — but HEAD resolution is not.)
#[test]
fn unresolved_projection_head_is_rejected() {
    let src = r#"
namespace wi262.badhead
  import anthill.prelude.{Int64, Modify, EffectsRuntime}
  operation touch() -> Int64
    effects Modify[nonexistent.field]
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("unresolved") && e.contains("nonexistent")),
        "a projection whose HEAD resolves to nothing must be a loud unresolved-name \
         error; got: {errs:?}",
    );
}
