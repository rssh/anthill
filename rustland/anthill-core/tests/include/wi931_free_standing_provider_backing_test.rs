//! WI-931 — §6.3's free-standing carriers are checked for operation backing like
//! any other, with no staging left.
//!
//! WI-928 made a free-standing `entity E(…)` emit the same `SortInfo` its long
//! form emits, which put four such carriers inside `check_provider_operations`'
//! CONCRETE scope for the first time and produced 12 `UnbackedProviderOperation`
//! reports. All twelve were TRUE. They are closed here at their source, and the
//! staging that hid them (`load::free_standing_entity_sorts` and the skip that
//! read it) is DELETED — so this suite's job is to pin, per family, that the
//! backing is real rather than merely no longer looked for.
//!
//! THE THREE FAMILIES, and what each one's fix actually was:
//!
//!   * `Vec3` / `VectorSpace` — the four members were "implemented" by RELATIONAL
//!     RULES at namespace level (`rule vec_add(?a, ?b, ?c) :- …`), which WI-818
//!     settled do not back an operation, and which are not even the same arity as
//!     the spec's functional `vec_add(a, b) -> V`. Giving `Vec3` real bodies works
//!     but MOVES THE SHORT NAME off the relational rules (measured, silently), so
//!     the provision is withdrawn instead and WI-935 owns restoring it.
//!
//!   * the persistence stores — the backing WAS real (six registered eval
//!     builtins) but lived in a registry no load-time reader can see, since
//!     `op_is_executable`'s builtin leg reads the RESOLVER's `kb.builtins` and
//!     these sat in the interpreter's. They moved to `operation_map` clauses
//!     (`rustland/anthill-stl/anthill/persistence.anthill`), which every reader
//!     can see and which the arity check covers. The operations are declared and
//!     mapped ONCE, on the specs — they are common operations over a store's
//!     state, one host function each — while WHICH BACKENDS the host realizes is
//!     declared per carrier. `a_spec_level_host_mapping_backs_no_carrier` is the
//!     test that keeps those two questions apart.
//!
//!   * `BulkStore` — no anthill-callable `pull` exists at all, so neither file
//!     backend provides it (WI-932). The absence is the honest answer, and
//!     `no_backend_provides_bulk_store` is what keeps it from being restored
//!     without an implementation.
//!
//! The CONTROL is `control_the_stdlib_loads_clean` in
//! `wi928_entity_load_record_test`, which is the measurement this whole ticket is
//! scored against; the tests here say WHY it is clean, which a load-clean
//! assertion alone cannot distinguish from a check that stopped looking.
//!
//! CONTROL DISCIPLINE, MEASURED rather than asserted. Re-introducing pre-WI-928
//! blindness (dropping every `SortInfo.kind = entity` carrier back out of
//! `check_provider_operations`' concrete scope) fails
//! `control_an_unbacked_free_standing_carrier_is_still_refused` and NOTHING ELSE
//! here — which is the point of that test and the reason it is not redundant with
//! the load-clean control. The three subject families were driven the same way,
//! by staging the fixes in one at a time against the 12 reports: closing `Vec3`
//! took it to 8, the persistence binding file to 1, and withdrawing the
//! `BulkStore` provision to 0.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

use crate::common::{interp_for, try_load_kb_with};

/// Every provision as `(carrier, spec)` SHORT names — the shared
/// `common::sort_provisions` walk, shortened because every claim here is about a
/// name this file spells literally.
fn provisions(kb: &KnowledgeBase) -> Vec<(String, String)> {
    let short = |s: String| s.rsplit('.').next().unwrap_or("").to_string();
    crate::common::sort_provisions(kb)
        .into_iter()
        .map(|(c, s)| (short(c), short(s)))
        .collect()
}

// ── Vec3 / VectorSpace: the provision is WITHDRAWN ──────────────────

/// SUBJECT — nothing provides `VectorSpace`, and the RELATIONAL vector rules are
/// intact and still reachable BY THEIR SHORT NAME.
///
/// Those two halves are one claim. `Vec3` genuinely is a vector space, so the
/// obvious close was to give it the four functional members `VectorSpace`
/// declares — and that was written and it worked. What it also did was move the
/// short name: with a second `vec_add` in `anthill.geometry`, a rule body doing
/// `import anthill.geometry.{vec_add}` and calling the relational form went from
/// ONE solution to ZERO, silently (the fully qualified name kept resolving, so the
/// rules were intact and only the import moved). Trading a working relational
/// surface — the one the algebraic laws in that file and every SMT consumer are
/// written against — for a provision nothing calls is the wrong way round, so the
/// provision was withdrawn instead and WI-935 owns restoring it.
///
/// The import is driven, not just declared, because "it loads" is exactly what
/// stayed true through the regression: `vec3_ops_test::vec_ops_callable_from_user_rule`
/// imports this same name and asserts only that the rule LOADS, so it passed
/// while the goal it documents matched nothing.
#[test]
fn the_relational_vec_rules_keep_their_short_name() {
    use anthill_core::kb::term::{Term, Var};
    use anthill_core::kb::resolve::ResolveConfig;
    use smallvec::SmallVec;

    let mut kb = try_load_kb_with(
        "
namespace wi931.rel
  import anthill.geometry.{Vec3, vec_add}

  rule add_x(?x) :- vec_add(Vec3(x: 1.0, y: 2.0, z: 3.0),
                            Vec3(x: 10.0, y: 20.0, z: 30.0), ?c),
                    ?c = Vec3(x: ?x, y: ?, z: ?)
end
",
    )
    .expect("stdlib + probe loads");

    // Nothing provides VectorSpace — the withdrawn claim.
    let vs = kb
        .try_resolve_symbol("anthill.prelude.algebra.VectorSpace")
        .expect("the VectorSpace spec still exists");
    assert!(
        kb.rules_by_functor(vs).is_empty(),
        "VectorSpace must have no satisfaction fact while its members are unbacked",
    );

    // And the relational surface still answers through the SHORT name.
    let sym = kb.try_resolve_symbol("wi931.rel.add_x").expect("probe rule");
    let r_sym = kb.intern("r");
    let r_vid = kb.fresh_var(r_sym);
    let r_var = kb.alloc(Term::Var(Var::Global(r_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_elem(r_var, 1),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    // ONE SOLUTION is the whole assertion, and it is the exact signal the
    // regression gave: this goal answered 1 before the operations were added and 0
    // after, with no diagnostic in between.
    //
    // The BOUND VALUE is deliberately not asserted to be 11.0. These clauses build
    // `Vec3(x: ?ax + ?bx, …)` and SLD leaves that sum SYMBOLIC — the per-component
    // arithmetic is for Z3 to discharge, which is the whole reason the relational
    // spelling exists (`?x` reifies to the unevaluated term, on this build and on
    // the pre-change one alike). Asserting a number here would be asserting that
    // this surface is something it is not.
    assert_eq!(
        sols.len(),
        1,
        "the imported short name `vec_add` must still reach the relational rule",
    );
}

// ── the persistence stores: declared host backing ───────────────────

/// SUBJECT — each of the six storage operations is now visible to a LOAD-TIME
/// reader as host-implemented. `is_host_mapped_op` is the predicate
/// `op_is_executable` consults, and before WI-931 it answered `false` for every
/// one of these while the interpreter could nevertheless run them: the backing
/// was real and undeclared, which is exactly what made the provisions read as
/// unbacked.
#[test]
fn the_six_storage_operations_are_declared_host_mapped() {
    let kb = try_load_kb_with("namespace wi931.stores\nend\n").expect("stdlib loads");
    for op in [
        "anthill.persistence.Store.persist",
        "anthill.persistence.Store.flush",
        "anthill.persistence.Store.monotonicity",
        "anthill.persistence.NonMonotonicStore.retract",
        "anthill.persistence.NonMonotonicStore.update",
        "anthill.persistence.QueryableStore.retrieve",
    ] {
        let sym = kb.try_resolve_symbol(op).unwrap_or_else(|| panic!("{op} must resolve"));
        assert!(
            kb.is_host_mapped_op(sym),
            "{op} must carry an `operation_map` host implementation",
        );
    }
}

/// SUBJECT — the store provisions stand in the HOST closure, not in the stdlib.
/// That placement is the rule `geometry.anthill` already followed and WI-931
/// applied here: a `fact Spec[Carrier]` may only be declared where the spec's
/// operations are backed, and `anthill.persistence`'s are host primitives. The
/// pairs must therefore be present in a stdlib+bindings load (this one) and — see
/// `stdlib_alone_declares_no_store_provision` — absent without the bindings.
#[test]
fn the_file_backends_provide_their_store_traits() {
    let kb = try_load_kb_with("namespace wi931.prov\nend\n").expect("stdlib loads");
    let provs = provisions(&kb);
    for pair in [
        ("FileStore", "NonMonotonicStore"),
        ("IndexedFileStore", "NonMonotonicStore"),
        ("IndexedFileStore", "QueryableStore"),
    ] {
        assert!(
            provs.iter().any(|(c, s)| (c.as_str(), s.as_str()) == pair),
            "{pair:?} must be provided; provisions were {provs:?}",
        );
    }
}

/// SUBJECT — a stdlib-only load declares NO store provision, which is the other
/// half of the placement rule and the half that a stdlib+bindings test cannot
/// see. Nothing backs `retract` without a host, so a provision standing in
/// `stdlib/anthill/persistence/` would be unsound exactly there.
#[test]
fn stdlib_alone_declares_no_store_provision() {
    // `load_stdlib_kb` is the shared binding-free load and it `expect`s a clean
    // one, so "the stdlib alone still loads" is asserted by calling it at all.
    let provs = provisions(&crate::common::load_stdlib_kb());
    for spec in ["NonMonotonicStore", "QueryableStore"] {
        assert!(
            !provs.iter().any(|(_, s)| s == spec),
            "a stdlib-only load must declare no carrier for `{spec}`; provisions were {provs:?}",
        );
    }
}

/// SUBJECT — `BulkStore` is provided by NOBODY, in either closure. Its sole
/// member `pull` has no anthill-callable implementation (WI-932), so any
/// provision would certify an operation that dies at the call. This is the one
/// finding of the twelve that was closed by REMOVING a claim rather than by
/// making it true, and it is the one most likely to be undone by someone reading
/// the Rust `BulkStore::pull` trait method and assuming it is reachable.
#[test]
fn no_backend_provides_bulk_store() {
    let kb = try_load_kb_with("namespace wi931.bulk\nend\n").expect("stdlib loads");
    let provs = provisions(&kb);
    assert!(
        !provs.iter().any(|(_, s)| s == "BulkStore"),
        "nothing may provide BulkStore while `pull` is unimplemented; provisions were {provs:?}",
    );
    // The spec itself is untouched — this is a missing IMPLEMENTATION, not a
    // deleted capability, so `pull` must still be declared for WI-932 to fill in.
    assert!(
        kb.try_resolve_symbol("anthill.persistence.BulkStore.pull").is_some(),
        "`BulkStore.pull` must still be DECLARED — only its provision was withdrawn",
    );
}

/// SUBJECT — `SqlStore` provides nothing either, and for a different reason: no
/// realization implements a SQL backend at all (rustland's `persistence/` has the
/// two file stores and nothing else), so there is no closure the provisions could
/// honestly move to. Separate from the `BulkStore` case on purpose — that one is a
/// missing operation, this one is a missing BACKEND.
#[test]
fn sql_store_provides_nothing() {
    let kb = try_load_kb_with("namespace wi931.sql\nend\n").expect("stdlib loads");
    let provs = provisions(&kb);
    assert!(
        !provs.iter().any(|(c, _)| c == "SqlStore"),
        "SqlStore has no realization, so it may provide nothing; provisions were {provs:?}",
    );
    assert!(
        kb.try_resolve_symbol("anthill.persistence.sql.SqlStore").is_some(),
        "the SqlStore SHAPE stays — a backend would be written against it",
    );
}

/// SUBJECT — a host mapping on a SPEC op backs the OPERATION, never a CARRIER.
///
/// The six storage operations are mapped once, on `Store` / `NonMonotonicStore` /
/// `QueryableStore`, because one rust function serves every backend. That spelling
/// is only safe because `op_backed` refuses to let it discharge a carrier's
/// obligation: `is_host_mapped_op` is a flat set with no carrier dimension, so
/// counting it would certify EVERY carrier of the spec — WI-876's defect A, the
/// half that being genuinely polymorphic does not answer.
///
/// MEASURED on the first cut of this ticket, before the refusal existed: this very
/// program LOADED CLEAN. An arbitrary entity could claim to be a store.
#[test]
fn a_spec_level_host_mapping_backs_no_carrier() {
    let src = "
namespace wi931.notastore
  import anthill.persistence.{NonMonotonicStore}
  entity ZzNotAStore(v: Int64)
  fact NonMonotonicStore[ZzNotAStore]
end
";
    let errs = match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    assert!(
        errs.iter().any(|e| e.contains("ZzNotAStore") && e.contains("retract")),
        "an arbitrary carrier must NOT inherit the spec-level host mapping: {errs:?}",
    );
}

/// SUBJECT — and the same refusal is what makes `sql_store_provides_nothing` a
/// consequence rather than a promise. Re-adding the provision this ticket withdrew
/// is REFUSED, so the withdrawal is enforced by the check and not only by prose.
#[test]
fn reinstating_the_sql_store_provision_is_refused() {
    let src = "
namespace wi931.sqlback
  import anthill.persistence.{NonMonotonicStore}
  import anthill.persistence.sql.{SqlStore}
  fact NonMonotonicStore[SqlStore]
end
";
    let errs = match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    assert!(
        errs.iter().any(|e| e.contains("SqlStore") && e.contains("retract")),
        "no host implements a SQL backend, so the provision must be refused: {errs:?}",
    );
}

// ── Controls: what must NOT have changed ────────────────────────────

/// CONTROL — the check still FIRES. Every subject above removes a report, so a
/// check that had simply stopped looking would pass all of them; this one
/// constructs a fresh free-standing carrier whose provision is unbacked and
/// requires the refusal. It is the shape WI-928 made visible, so it also pins
/// that the widening survived the staging's deletion.
#[test]
fn control_an_unbacked_free_standing_carrier_is_still_refused() {
    let src = "
namespace wi931.control
  sort W931Spec
    sort T = ?
    operation w931op(x: T) -> T
  end
  entity W931Carrier(v: Int64)
  fact W931Spec[T = W931Carrier]
end
";
    let errs = match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    assert!(
        errs.iter().any(|e| e.contains("W931Carrier") && e.contains("w931op")),
        "a free-standing entity providing a spec whose op nothing backs must be \
         refused: {errs:?}",
    );
}

/// CONTROL — and it passes either way BY DESIGN. The same declaration WITH a
/// runnable body loads clean, so the refusal above is about backing and not about
/// the free-standing spelling. Without this pair, a check that refused every
/// `entity`-declared carrier would satisfy the test above.
#[test]
fn control_a_backed_free_standing_carrier_loads() {
    let src = "
namespace wi931.controlok
  sort W931OkSpec
    sort T = ?
    operation w931ok(x: T) -> T
  end
  sort W931OkCarrier {
    entity W931OkCarrier(v: Int64)
    operation w931ok(x: W931OkCarrier) -> W931OkCarrier = x
  }
  fact W931OkSpec[T = W931OkCarrier]
end
";
    let errs = match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    assert!(errs.is_empty(), "a backed carrier must load clean: {errs:?}");
}
