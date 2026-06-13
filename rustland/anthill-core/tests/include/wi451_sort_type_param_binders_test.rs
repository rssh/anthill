//! WI-451 (§5.4 "The carrier is a non-rigid type variable") — grammar + parse for
//! the operation-style enclosing sort type-param list `sort CpsMonad[F[T], A, B]`.
//!
//! The list goes AFTER the name (mirroring `operation name[…]`) and desugars at
//! convert time into MARKED body items: a SIMPLE param `A` becomes `sort A = ?`
//! (byte-identical to the existing type-param form); a HIGHER-KINDED `F[T]` becomes
//! a `sort F { sort T = ? }` marked `is_type_param: true` (its bracketed member `T`
//! is the one shape the flat `operation_type_param_list` lacks). The loader (WI-452)
//! reads the marker to mint the carrier's backing var; until then it is inert, so
//! the enclosing form LOADS identically to the body form. The marker is exactly what
//! distinguishes a parameter-variable from a concrete nested sort — an UNMARKED
//! `sort F { … }` stays `is_type_param: false`.

use anthill_core::intern::SymbolTable;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse::{
    self,
    ir::{AbstractSort, Item, SortWithBody, TypeExpr},
};

/// Recursively find a `SortWithBody` by short name.
fn find_sort<'a>(items: &'a [Item], syms: &SymbolTable, name: &str) -> Option<&'a SortWithBody> {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                if s.name.segments.last().is_some_and(|sym| syms.name(*sym) == name) {
                    return Some(s);
                }
                if let Some(f) = find_sort(&s.items, syms, name) {
                    return Some(f);
                }
            }
            Item::Namespace(ns) => {
                if let Some(f) = find_sort(&ns.items, syms, name) {
                    return Some(f);
                }
            }
            _ => {}
        }
    }
    None
}

/// An `AbstractSort` (the `sort X = ?` form) with short name `name`, directly among `items`.
fn abstract_named<'a>(
    items: &'a [Item],
    syms: &SymbolTable,
    name: &str,
) -> Option<&'a AbstractSort> {
    items.iter().find_map(|i| match i {
        Item::AbstractSort(a) if a.name.segments.last().is_some_and(|s| syms.name(*s) == name) => {
            Some(a)
        }
        _ => None,
    })
}

/// HK carrier `F[T]` desugars to a structured sort MARKED `is_type_param`, carrying
/// its member `T` as `sort T = ?`.
#[test]
fn enclosing_hk_param_desugars_to_marked_structured_sort() {
    let src = r#"namespace test.wi451.hk
  sort CpsMonad[F[T]]
    operation unit[A](a: A) -> F[T = A]
  end
end
"#;
    let parsed = parse::parse(src).expect("parse");
    let cps = find_sort(&parsed.items, &parsed.symbols, "CpsMonad").expect("CpsMonad sort");
    let f = find_sort(&cps.items, &parsed.symbols, "F").expect("F param sort");
    assert!(f.is_type_param, "the HK param F must be marked is_type_param");
    let t = abstract_named(&f.items, &parsed.symbols, "T").expect("F's member T");
    assert!(
        matches!(t.definition, TypeExpr::Variable { .. }),
        "F's member T must be the `?` (unspecified) form, got {:?}",
        t.definition
    );
}

/// Simple params `A, B` desugar to `sort A = ?` / `sort B = ?` AbstractSorts — the
/// SAME IR as the existing type-param form, never a marked structured sort.
#[test]
fn enclosing_simple_params_desugar_to_abstract_sorts() {
    let src = r#"namespace test.wi451.simple
  sort Duo[A, B]
    entity duo(x: A, y: B)
  end
end
"#;
    let parsed = parse::parse(src).expect("parse");
    let duo = find_sort(&parsed.items, &parsed.symbols, "Duo").expect("Duo sort");
    for p in ["A", "B"] {
        let a = abstract_named(&duo.items, &parsed.symbols, p)
            .unwrap_or_else(|| panic!("simple param {p} must desugar to an AbstractSort"));
        assert!(
            matches!(a.definition, TypeExpr::Variable { .. }),
            "simple param {p} must be `= ?`"
        );
    }
    assert!(
        find_sort(&duo.items, &parsed.symbols, "A").is_none(),
        "a simple param must NOT become a structured SortWithBody"
    );
}

/// The marker is the distinction: an UNMARKED nested `sort F { … }` (no enclosing
/// list) stays a concrete nested sort, `is_type_param: false`.
#[test]
fn unmarked_nested_sort_stays_concrete() {
    let src = r#"namespace test.wi451.body
  sort Box
    sort F
      sort T = ?
    end
  end
end
"#;
    let parsed = parse::parse(src).expect("parse");
    let f = find_sort(&parsed.items, &parsed.symbols, "F").expect("nested F");
    assert!(
        !f.is_type_param,
        "an unmarked nested `sort F {{ … }}` must stay is_type_param: false (concrete)"
    );
}

// ── Load equivalence: the marker is inert until WI-452, so the enclosing form
//    loads identically to the body form. ──────────────────────────────────────

fn load_errors(extra: &str) -> Vec<String> {
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
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// `sort CpsMonad[F[T]]` whose ops reference `F[T = A]` loads clean — the desugar
/// yields the body-form equivalent (F a concrete nested sort pre-WI-452).
#[test]
fn enclosing_hk_form_loads_clean() {
    let src = r#"namespace test.wi451.load
  sort CpsMonad[F[T]]
    operation unit[A](a: A) -> F[T = A]
    operation flatMap[A, B](fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
  end
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "enclosing-list CpsMonad should load clean: {errs:?}");
}

/// Simple-param enclosing form `sort Duo[A, B]` with a real use loads clean.
#[test]
fn enclosing_simple_form_loads_clean() {
    let src = r#"namespace test.wi451.loadsimple
  import anthill.prelude.Int64
  sort Duo[A, B]
    entity duo(x: A, y: B)
  end
  operation mk(n: Int64) -> Duo[A = Int64, B = Int64] = duo(x: n, y: n)
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "enclosing-list Duo should load clean: {errs:?}");
}
