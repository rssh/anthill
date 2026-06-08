//! WI-398: CROSS-PARAMETER projection — a parameter whose declared type projects
//! ANOTHER parameter of the same operation (`check(s: State, k: s.provider.K)`).
//!
//! WI-376/397 deliver projection in the RETURN / EFFECTS positions, where every
//! parameter is already synthesized before the elimination runs. A projection in a
//! PARAMETER type adds a synthesis-order obligation: the receiver param (`s`) must be
//! synthesized before the projecting param's (`k`) type is read. Because the call site
//! synthesizes every argument first (`param_to_arg_type` fully populated) and a
//! projection reads the receiver's ARGUMENT type (ground, concrete), the elimination is
//! order-independent at the call — but a CYCLIC projection signature (`f(a: b.T, b:
//! a.T)`, or the self-projection `f(a: a.T)`) has no synthesis order and is an
//! ill-formed signature, rejected loudly at LOAD (signature well-formedness).
//!
//! Design: `docs/design/path-dependent-types.md` §1 (the `s.provider.K` trace) + §6
//! seam map (WI-398 = "`k : s.provider.K` depends on param `s`; cross-param + synthesis
//! order"). As in WI-397 the member projected is a DIRECT type-param of the field's
//! sort (`Inner[T = String].T`); a provided-spec member is the separate follow-on.

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

/// A cross-parameter projection conforms: `check(s: Wrapper, k: s.cell.T)` called on a
/// `Wrapper[P = Inner[T = String]]` resolves `s.cell : Inner[T = String]` then `.T =
/// String`, so passing a `String` for `k` is well-typed.
#[test]
fn cross_param_projection_conforms() {
    let ok = r#"
namespace test.wi398.ok
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation check(s: Wrapper, k: s.cell.T) -> String
  operation caller(w: Wrapper[P = Inner[T = String]]) -> String = check(w, "abc")
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "k's type s.cell.T resolves to String for w: Wrapper[P=Inner[T=String]]; \
         passing \"abc\" (String) for k must conform",
    );
}

/// The cross-parameter projection is REAL: `k : s.cell.T` is `String`, so passing an
/// `Int64` for `k` must be REJECTED — the projecting param type is not a fresh var that
/// absorbs any argument.
#[test]
fn cross_param_projection_wrong_arg_is_rejected() {
    let wrong = r#"
namespace test.wi398.wrong
  import anthill.prelude.{String, Int64}
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation check(s: Wrapper, k: s.cell.T) -> String
  operation caller(w: Wrapper[P = Inner[T = String]]) -> String = check(w, 42)
end
"#;
    assert!(
        !load_errors(&[wrong]).is_empty(),
        "k : s.cell.T is String, so passing 42 (Int64) for k must be rejected",
    );
}

/// SYNTHESIS ORDER: the projecting param may be declared BEFORE its receiver param
/// (`check2(k: s.cell.T, s: Wrapper)`). Elimination must read `s`'s synthesized
/// argument type regardless of source order, so the call still type-checks.
#[test]
fn cross_param_projection_receiver_declared_after_is_ordered() {
    let ok = r#"
namespace test.wi398.reorder
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation check2(k: s.cell.T, s: Wrapper) -> String
  operation caller(w: Wrapper[P = Inner[T = String]]) -> String = check2("abc", w)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "k is declared before its receiver s, but s.cell.T must still resolve to String \
         (synthesis order, not source order)",
    );
}

/// A CYCLIC cross-parameter projection signature (`a : b.T`, `b : a.T`) has no
/// synthesis order — an ill-formed signature, rejected loudly at LOAD, never a silent
/// accept.
#[test]
fn cyclic_cross_param_projection_is_loud_load_error() {
    let bad = r#"
namespace test.wi398.cycle
  import anthill.prelude.String
  sort Box
    sort T = ?
    entity box(v: T)
  end
  operation cyc(a: b.T, b: a.T) -> String = "cycle"
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("cyclic") || e.contains("cycle")),
        "a cyclic cross-parameter projection must be a loud load error; got: {errs:?}",
    );
}

/// A SELF-projection (`a : a.T`) is the length-1 cycle — also rejected at LOAD.
#[test]
fn self_param_projection_is_loud_load_error() {
    let bad = r#"
namespace test.wi398.selfcycle
  import anthill.prelude.String
  operation self_cyc(a: a.T) -> String = "self"
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("cyclic") || e.contains("cycle")),
        "a self-projecting parameter must be a loud load error; got: {errs:?}",
    );
}

/// A CHAIN of cross-parameter projections — `c` projects `b`, `b` projects `a`, each
/// carrier nesting one level — threads correctly: every projection reads its receiver's
/// synthesized ARGUMENT type, so `a.P = Mid[…]`, `b.Q = Inner[T = String]`, and passing
/// the matching concrete value for each conforms. (Proves the elimination is read-only
/// over the fully-synthesized argument environment, not a single-level special case.)
#[test]
fn cross_param_chain_projection_threads() {
    let ok = r#"
namespace test.wi398.chain
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Mid
    sort Q = ?
    entity mid(q: Q)
  end
  sort Outer
    sort P = ?
    entity outer(p: P)
  end
  operation chain(a: Outer, b: a.P, c: b.Q) -> String
  operation caller(
      a: Outer[P = Mid[Q = Inner[T = String]]],
      b: Mid[Q = Inner[T = String]],
      c: Inner[T = String]
  ) -> String = chain(a, b, c)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "chained cross-param projection with matching args must conform",
    );
}

/// The chain is REAL: when `b`'s argument disagrees with `a.P` (the projecting param's
/// resolved type), the call is REJECTED — `b` is validated against the ELIMINATED `a.P`
/// (`Mid[Q = Inner[T = String]]`), not the raw projection.
#[test]
fn cross_param_chain_arg_disagreement_is_rejected() {
    let bad = r#"
namespace test.wi398.chain2
  import anthill.prelude.{String, Int64}
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Mid
    sort Q = ?
    entity mid(q: Q)
  end
  sort Outer
    sort P = ?
    entity outer(p: P)
  end
  operation chain(a: Outer, b: a.P, c: b.Q) -> String
  operation caller(
      a: Outer[P = Mid[Q = Inner[T = String]]],
      b: Mid[Q = Inner[T = Int64]],
      c: Inner[T = Int64]
  ) -> String = chain(a, b, c)
end
"#;
    assert!(
        !load_errors(&[bad]).is_empty(),
        "b's arg Mid[Q=Inner[T=Int64]] disagrees with a.P = Mid[Q=Inner[T=String]] — must be rejected",
    );
}

/// Signature well-formedness must cover a body-less FREE operation (a namespace-level
/// spec): the body-type-check pass skips it, so the dedicated `check_operation_signatures`
/// pass over ALL operations is what catches its cyclic signature. (Regression guard for
/// the all-operations signature pass.)
#[test]
fn cyclic_signature_in_bodyless_free_op_is_rejected() {
    let bad = r#"
namespace test.wi398.bodyless_free
  import anthill.prelude.String
  sort Box
    sort T = ?
    entity box(v: T)
  end
  operation cyc_free(a: b.T, b: a.T) -> String
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("cyclic") || e.contains("cycle")),
        "a body-less FREE op with a cyclic signature must still be rejected; got: {errs:?}",
    );
}

/// And a body-less SORT spec (`operation … ` inside a sort, no body) is caught too.
#[test]
fn cyclic_signature_in_bodyless_sort_spec_is_rejected() {
    let bad = r#"
namespace test.wi398.bodyless_spec
  import anthill.prelude.String
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort Holder
    operation cyc_spec(a: b.T, b: a.T) -> String
  end
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("cyclic") || e.contains("cycle")),
        "a body-less SORT spec with a cyclic signature must be rejected; got: {errs:?}",
    );
}
