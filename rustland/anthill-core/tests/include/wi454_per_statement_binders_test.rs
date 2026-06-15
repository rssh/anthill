//! WI-454 (§5.4 surface sugar, deferred from WI-451) — the PER-STATEMENT non-rigid
//! type-variable binder synonyms:
//!   - `sort ?X`            (the `?x` logical-var marker as the binder name)
//!   - `sort [X]`           (standalone bracket binder)
//!   - `sort ?F { sort ?T }` / `sort [F] { sort [T] }`  (structured / higher-kinded)
//!
//! All four desugar at convert time to EXACTLY the IR the WI-451 enclosing-list form
//! `sort CpsMonad[F[T], A, B]` produces: a bare binder → `sort X = ?` (an
//! `AbstractSort` with a fresh `?`); a structured binder → a `SortWithBody` marked
//! `is_type_param: true` carrying its (recursively desugared) members. The headline
//! test is the PARSE-IR EQUIVALENCE of the per-statement form and the enclosing-list
//! form; the load tests confirm the desugar rides the WI-452/453 backing-var
//! machinery end-to-end.

use anthill_core::intern::SymbolTable;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse::{
    self,
    ir::{Item, Name, SortWithBody, TypeExpr},
};

fn short(name: &Name, syms: &SymbolTable) -> String {
    name.segments
        .last()
        .map(|s| syms.name(*s).to_string())
        .unwrap_or_default()
}

/// Recursively find a `SortWithBody` by short name.
fn find_sort<'a>(items: &'a [Item], syms: &SymbolTable, name: &str) -> Option<&'a SortWithBody> {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                if short(&s.name, syms) == name {
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

/// Var-id-independent summary of a sort's type-parameter binders: a SIMPLE param
/// (`sort X = ?`, an `AbstractSort` whose definition is the `?` var) and a
/// HIGHER-KINDED param (a `SortWithBody` marked `is_type_param`, recursively
/// summarized). Non-param items (ops, entities) are ignored. Two forms are
/// parse-IR-equivalent iff their summaries are equal.
#[derive(Debug, PartialEq, Eq)]
enum ParamShape {
    Simple(String),
    Hk(String, Vec<ParamShape>),
}

fn summarize(items: &[Item], syms: &SymbolTable) -> Vec<ParamShape> {
    items
        .iter()
        .filter_map(|i| match i {
            Item::AbstractSort(a) if matches!(a.definition, TypeExpr::Variable { .. }) => {
                Some(ParamShape::Simple(short(&a.name, syms)))
            }
            Item::SortWithBody(s) if s.is_type_param => {
                Some(ParamShape::Hk(short(&s.name, syms), summarize(&s.items, syms)))
            }
            _ => None,
        })
        .collect()
}

fn cps_params(src: &str) -> Vec<ParamShape> {
    let parsed = parse::parse(src).expect("parse");
    let cps = find_sort(&parsed.items, &parsed.symbols, "CpsMonad").expect("CpsMonad sort");
    summarize(&cps.items, &parsed.symbols)
}

/// HEADLINE: the per-statement binder form is PARSE-IR-EQUIVALENT to the
/// enclosing-list form `sort CpsMonad[F[T], A, B]` — same params, same kinds,
/// same nesting.
#[test]
fn per_statement_equivalent_to_enclosing_list() {
    let enclosing = r#"namespace test.wi454.enc
  sort CpsMonad[F[T], A, B]
  end
end
"#;
    let bracket = r#"namespace test.wi454.brk
  sort CpsMonad
    sort [F] {
      sort [T]
    }
    sort [A]
    sort [B]
  end
end
"#;
    let var = r#"namespace test.wi454.var
  sort CpsMonad
    sort ?F {
      sort ?T
    }
    sort ?A
    sort ?B
  end
end
"#;
    let enc = cps_params(enclosing);
    let brk = cps_params(bracket);
    let v = cps_params(var);

    let expected = vec![
        ParamShape::Hk("F".into(), vec![ParamShape::Simple("T".into())]),
        ParamShape::Simple("A".into()),
        ParamShape::Simple("B".into()),
    ];
    assert_eq!(enc, expected, "sanity: the enclosing-list form's summary");
    assert_eq!(brk, enc, "bracket per-statement form must match the enclosing list");
    assert_eq!(v, enc, "?-marker per-statement form must match the enclosing list");
}

/// A bare bracket binder `sort [A]` desugars to a simple `sort A = ?` AbstractSort,
/// never a structured SortWithBody.
#[test]
fn bare_binders_are_simple_abstract_sorts() {
    let src = r#"namespace test.wi454.bare
  sort Holder
    sort [A]
    sort ?B
  end
end
"#;
    let parsed = parse::parse(src).expect("parse");
    let syms = &parsed.symbols;
    let holder = find_sort(&parsed.items, syms, "Holder").expect("Holder");
    assert_eq!(
        summarize(&holder.items, syms),
        vec![ParamShape::Simple("A".into()), ParamShape::Simple("B".into())],
    );
    assert!(
        find_sort(&holder.items, syms, "A").is_none() && find_sort(&holder.items, syms, "B").is_none(),
        "a bare binder must NOT become a structured SortWithBody"
    );
}

// ── Guards: the structured binder body mirrors the enclosing HK member list ───

/// A structured binder body admits ONLY binder members (mirroring the enclosing
/// `F[T, …]`); a non-binder declaration inside is a loud PARSE error, not a type
/// parameter silently carrying a real declaration.
#[test]
fn non_binder_in_structured_body_is_a_parse_error() {
    let src = r#"namespace test.wi454.opinbody
  sort C
    sort [F] {
      operation bogus() -> F
    }
  end
end
"#;
    assert!(
        parse::parse(src).is_err(),
        "an operation inside a `sort [F] {{ … }}` binder body must be a loud parse error",
    );
}

/// An empty structured body `sort [F] {}` has no enclosing-form equivalent
/// (`commaSep1` requires ≥1 member) — it is a loud parse error, never a degenerate
/// zero-member HK carrier.
#[test]
fn empty_structured_binder_body_is_a_parse_error() {
    let src = r#"namespace test.wi454.empty
  sort C
    sort [F] {}
  end
end
"#;
    assert!(
        parse::parse(src).is_err(),
        "an empty `sort [F] {{}}` binder body must be a loud parse error",
    );
}

/// An anonymous `sort ?` (the `?` marker with no name) binds nothing referenceable
/// — a loud convert error, not a silent `_`-named sort.
#[test]
fn anonymous_var_binder_is_a_loud_error() {
    let src = r#"namespace test.wi454.anon
  sort C
    sort ?
  end
end
"#;
    assert!(
        parse::parse(src).is_err(),
        "a nameless `sort ?` binder must be a loud error",
    );
}

// ── Load equivalence: the per-statement form rides WI-452/453 end-to-end ──────

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

/// The §5.4 HK carrier written with per-statement bracket binders loads clean —
/// the desugar is identical to the enclosing `sort CpsMonad[F[T]]` form WI-451/453
/// already load.
#[test]
fn per_statement_hk_form_loads_clean() {
    let src = r#"namespace test.wi454.loadbrk
  sort CpsMonad
    sort [F] {
      sort [T]
    }
    operation unit[A](a: A) -> F[T = A]
    operation flatMap[A, B](fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
  end
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "per-statement HK CpsMonad should load clean: {errs:?}");
}

/// Simple-param per-statement form (`sort ?A` / `sort [B]`) with a real use loads
/// clean, mirroring WI-451's `sort Duo[A, B]` load test.
#[test]
fn per_statement_simple_form_loads_clean() {
    let src = r#"namespace test.wi454.loadsimple
  import anthill.prelude.Int64
  sort Duo
    sort [A]
    sort ?B
    entity duo(x: A, y: B)
  end
  operation mk(n: Int64) -> Duo[A = Int64, B = Int64] = duo(x: n, y: n)
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "per-statement Duo should load clean: {errs:?}");
}
