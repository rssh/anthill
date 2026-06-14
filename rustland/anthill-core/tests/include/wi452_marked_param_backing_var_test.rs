//! WI-452 (§5.4 "The carrier is a non-rigid type variable") — the LOADER half.
//!
//! A MARKED structured sort param (`sort [F] { … }`, the higher-kinded carrier of
//! `sort Spec[F[T]]`, carried by `SortWithBody.is_type_param` from WI-451) is
//! registered as a NON-RIGID type parameter of the enclosing sort, exactly as
//! `sort T = ?` is: `add_type_param` puts it in `type_params_of_sort`, and a
//! `SortAlias(F, Var)` fact gives it a backing logic var (`CpsMonad.F ↦ ?F`). So
//! F now resolves to a Var via `sort_type_params_as_pairs` and can unify/fill
//! (WI-453). An UNMARKED `sort F { … }` stays a concrete nested sort — no param
//! registration, no backing var.

use anthill_core::kb::term::{Term, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::intern::Symbol;
use anthill_core::parse;

fn load_kb(extra: &str) -> (KnowledgeBase, Vec<String>) {
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
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let errs = match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    };
    (kb, errs)
}

/// True iff there is a `SortAlias(<sort_sym>, Var)` fact — i.e. `sort_sym` has a
/// non-rigid backing var (the `sort T = ?` / marked-param shape). Mirrors the
/// loader's `find_sort_alias_var` scan, read-only.
fn has_backing_var(kb: &KnowledgeBase, sort_sym: Symbol) -> bool {
    let Some(alias_sym) = kb.try_resolve_symbol("SortAlias") else {
        return false;
    };
    for rid in kb.rules_by_functor(alias_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(head) = kb.fact_head_term(rid) else {
            continue;
        };
        // Copy out the sort-ref and target TermIds without holding the borrow.
        let args = match kb.get_term(head) {
            Term::Fn { pos_args, .. } if pos_args.len() >= 2 => Some((pos_args[0], pos_args[1])),
            _ => None,
        };
        let Some((sref, target)) = args else {
            continue;
        };
        let is_target_sort =
            matches!(kb.get_term(sref), Term::Fn { functor, .. } if *functor == sort_sym);
        if is_target_sort && matches!(kb.get_term(target), Term::Var(Var::Global(_))) {
            return true;
        }
    }
    false
}

/// A MARKED HK carrier `F` is a var-backed type param of the enclosing spec, with
/// its member `T` as F's own param; and the spec's body typechecks (def-site
/// skolemization keeps `F[T = A]` decomposing rigidly).
#[test]
fn marked_hk_param_is_var_backed_type_param() {
    let src = r#"namespace test.wi452.marked
  sort CpsMonad[F[T]]
    operation unit[A](a: A) -> F[T = A]
    operation reUnit[A](fa: F[T = A]) -> F[T = A] = fa
  end
end
"#;
    let (kb, errs) = load_kb(src);
    assert!(errs.is_empty(), "marked enclosing-list spec should load clean: {errs:?}");

    let cps = kb
        .try_resolve_symbol("test.wi452.marked.CpsMonad")
        .expect("CpsMonad symbol");
    assert!(
        kb.type_params_of_sort(cps).iter().any(|p| p == "F"),
        "marked carrier F must be a type param of CpsMonad; got {:?}",
        kb.type_params_of_sort(cps)
    );

    let f = kb
        .try_resolve_symbol("test.wi452.marked.CpsMonad.F")
        .expect("CpsMonad.F symbol");
    assert!(
        kb.type_params_of_sort(f).iter().any(|p| p == "T"),
        "F's member T must be F's own type param; got {:?}",
        kb.type_params_of_sort(f)
    );
    assert!(
        has_backing_var(&kb, f),
        "marked CpsMonad.F must have a SortAlias → Var backing var (resolve like `sort T = ?`)"
    );
}

/// Def-site SKOLEMIZATION: because the marked carrier F is now a sort type param
/// (var-backed), the WI-392 rigidify pass skolemizes it inside CpsMonad's own
/// bodies, so a wrong binding is rejected — `bad(fa: F[T = A]) -> F[T = B] = fa`
/// fails `F[T = A] ≟ F[T = B]` (distinct rigids `?A` / `?B`). This proves F goes
/// RIGID at the definition site (the wi383_hk decomposition property, now for the
/// marked form), not that it accepts everything trivially.
#[test]
fn marked_param_skolemizes_at_def_site_rejects_wrong_binding() {
    let src = r#"namespace test.wi452.skolem
  sort CpsMonad[F[T]]
    operation unit[A](a: A) -> F[T = A]
    operation bad[A, B](fa: F[T = A]) -> F[T = B] = fa
  end
end
"#;
    let (_kb, errs) = load_kb(src);
    assert!(
        errs.iter().any(|e| e.contains("bad") && e.contains("?A") && e.contains("?B")),
        "marked F must skolemize at def-site so `bad` (F[T=A] vs F[T=B]) is rejected \
         with a binding-distinct diagnostic (?A vs ?B); got: {errs:?}"
    );
}

/// The HK carrier's MEMBER `T` (`sort T = ?` inside the marked `F`) is itself a
/// var-backed type param of `F` — so `F[T = A]`'s binding label resolves. (Emitted
/// by `load_abstract_sort`, not the WI-452 helper, but part of the same `F ↦ ?F`
/// promise that the marked carrier "carries its member sub-decls".)
#[test]
fn marked_param_member_is_also_var_backed() {
    let src = r#"namespace test.wi452.member
  sort CpsMonad[F[T]]
    operation unit[A](a: A) -> F[T = A]
  end
end
"#;
    let (kb, errs) = load_kb(src);
    assert!(errs.is_empty(), "should load clean: {errs:?}");
    let f_t = kb
        .try_resolve_symbol("test.wi452.member.CpsMonad.F.T")
        .expect("CpsMonad.F.T symbol");
    assert!(
        has_backing_var(&kb, f_t),
        "F's member T must itself have a SortAlias → Var (it is `sort T = ?` inside F)"
    );
}

/// NESTED marked params `sort Outer[F[G[H]]]`: each marked level (`F`, `G`) is a
/// var-backed type param of its enclosing level, recursively — the pre-pass emits
/// the carrier var at every nesting depth. Locks in the recursion.
#[test]
fn nested_marked_params_each_var_backed() {
    let src = r#"namespace test.wi452.nest
  sort Outer[F[G[H]]]
  end
end
"#;
    let (kb, errs) = load_kb(src);
    assert!(errs.is_empty(), "nested marked params should load clean: {errs:?}");
    for (sort, param) in [
        ("test.wi452.nest.Outer", "F"),
        ("test.wi452.nest.Outer.F", "G"),
        ("test.wi452.nest.Outer.F.G", "H"),
    ] {
        let sym = kb.try_resolve_symbol(sort).unwrap_or_else(|| panic!("{sort} symbol"));
        assert!(
            kb.type_params_of_sort(sym).iter().any(|p| p == param),
            "{param} must be a type param of {sort}; got {:?}",
            kb.type_params_of_sort(sym)
        );
    }
    // The two MARKED carriers (F, G) carry backing vars (H is `sort H = ?`, also).
    for sort in ["test.wi452.nest.Outer.F", "test.wi452.nest.Outer.F.G"] {
        let sym = kb.try_resolve_symbol(sort).unwrap_or_else(|| panic!("{sort} symbol"));
        assert!(has_backing_var(&kb, sym), "marked carrier {sort} must have a backing var");
    }
}

/// The ordering the pre-pass fix targets: a marked carrier `F` referenced by an
/// ENTITY FIELD (`content: F[T = Int64]`) is resolved during the entity FieldInfo
/// build — which runs BEFORE `F`'s own body loads. Emitting F's backing var in the
/// pre-pass (not inline in F's later load) means the field resolves to F's
/// canonical var, and the spec loads clean with F still a var-backed param.
#[test]
fn marked_carrier_in_entity_field_loads_clean() {
    let src = r#"namespace test.wi452.field
  import anthill.prelude.Int64
  sort Boxed[F[T]]
    entity boxed(content: F[T = Int64])
  end
end
"#;
    let (kb, errs) = load_kb(src);
    assert!(
        errs.is_empty(),
        "a marked carrier referenced in an entity field should load clean: {errs:?}"
    );
    let boxed = kb
        .try_resolve_symbol("test.wi452.field.Boxed")
        .expect("Boxed symbol");
    assert!(
        kb.type_params_of_sort(boxed).iter().any(|p| p == "F"),
        "F must still be a var-backed type param of Boxed even when referenced by a field"
    );
    let f = kb
        .try_resolve_symbol("test.wi452.field.Boxed.F")
        .expect("Boxed.F symbol");
    assert!(has_backing_var(&kb, f), "Boxed.F must have a backing var");
}

/// An UNMARKED nested `sort F { … }` (the body form, no enclosing list) stays a
/// CONCRETE nested sort: NOT a type param of the enclosing sort, NO backing var.
#[test]
fn unmarked_nested_sort_is_not_a_type_param() {
    let src = r#"namespace test.wi452.body
  sort Box
    sort F
      sort T = ?
    end
  end
end
"#;
    let (kb, errs) = load_kb(src);
    assert!(errs.is_empty(), "body-form spec should load clean: {errs:?}");

    let box_sym = kb
        .try_resolve_symbol("test.wi452.body.Box")
        .expect("Box symbol");
    assert!(
        !kb.type_params_of_sort(box_sym).iter().any(|p| p == "F"),
        "unmarked nested F must NOT be a type param of Box; got {:?}",
        kb.type_params_of_sort(box_sym)
    );

    let f = kb
        .try_resolve_symbol("test.wi452.body.Box.F")
        .expect("Box.F symbol");
    assert!(
        !has_backing_var(&kb, f),
        "unmarked Box.F must NOT get a backing var (it is a concrete nested sort)"
    );
}
