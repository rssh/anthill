//! WI-658: the load-time `Eq` ⊥ `NonEq` mutual-exclusion check
//! (`check_eq_noneq_exclusive`). A carrier must not provide BOTH the lawful
//! (reflexive) `Eq` and the witnessed non-reflexive `NonEq`. These tests guard
//! against the check silently degrading to a no-op — the enforcement is
//! otherwise unexercised, since the stdlib itself carries no conflict (only the
//! non-parametric leaf `Float` provides `NonEq`, and it does not provide `Eq`).

use anthill_core::kb::load::{self, LoadError, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Stdlib + rust bindings + `extra` source → load errors. Mirrors the helper in
/// `wi325_missing_requires_test.rs`.
fn try_load(extra: &str) -> Vec<LoadError> {
    let files = crate::common::collect_stdlib_and_rust_bindings();
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
    load::load_all(&mut kb, &refs, &NullResolver)
        .err()
        .unwrap_or_default()
}

fn fmt(errs: &[LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

/// A user `fact Eq[T = Float]` conflicts with Float's stdlib `NonEq` provision:
/// IEEE Float's `eq` is non-reflexive (Float already provides `NonEq`), so it
/// cannot also be a lawful `Eq`. The check must reject the load.
#[test]
fn eq_on_float_conflicts_with_its_noneq() {
    let src = r#"
namespace test.wi658.eq_float
  import anthill.prelude.{Eq, Float}
  fact Eq[T = Float]
end
"#;
    let errs = try_load(src);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            LoadError::IncompatibleEqNonEq { carrier } if carrier.contains("Float")
        )),
        "expected IncompatibleEqNonEq for Float; got:\n{}",
        fmt(&errs),
    );
}

/// Opt-in: a carrier that declares only ONE side is untouched. The stdlib's many
/// lawful `Eq`-only carriers (Int64, String, Bool, TotalFloat, …) plus `Float`
/// (NonEq-only) do NOT conflict — a clean load emits no `IncompatibleEqNonEq`.
#[test]
fn eq_only_and_noneq_only_carriers_do_not_conflict() {
    let src = r#"
namespace test.wi658.clean
  import anthill.prelude.{Int64}
end
"#;
    let errs = try_load(src);
    assert!(
        !errs
            .iter()
            .any(|e| matches!(e, LoadError::IncompatibleEqNonEq { .. })),
        "unexpected IncompatibleEqNonEq on a clean load:\n{}",
        fmt(&errs),
    );
}
