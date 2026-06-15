//! WI-461: a bare self-receiver IDENTITY body returning the receiver as a PROVIDED
//! sort threads the projection through provider-admissibility.
//!
//! `operation iterator(l: List) -> Stream[T = l.T, E = {}] = l` — the body `l : List`
//! is admissible-as-`Stream` via `List provides Stream[T, {}]`, but the BARE param's
//! element was not pinned to its projection `l.T` for the admissibility unify, so
//! `List`'s provided `Stream[T = <List.T>]` did not match the declared `Stream[T = l.T]`.
//! The fix refines the bare self-receiver body type to `List[T = l.T]` (the WI-374 member
//! tie: a value `l : List` has element `l.T`) and the existing `parameterized` cross-sort
//! provider path then threads it. The threading is REAL — a DIFFERENT receiver's
//! projection (`Stream[T = xs.T]`) or a concrete demand (`Stream[T = Int64]`) on a bare
//! receiver still fails (`l.T` is a neutral, equal only to itself).

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

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// The headline: a bare self-receiver identity body `iter2(l: List) -> Stream[T = l.T,
/// E = {}] = l` typechecks — the bare `l : List` is admissible as the declared
/// projection-threaded `Stream` via the member tie.
#[test]
fn bare_self_receiver_provided_return_threads() {
    let ok = r#"
namespace test.wi461.ok
  import anthill.prelude.{List, Stream}
  operation iter2(l: List) -> Stream[T = l.T, E = {}] = l
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "bare `l : List` must be admissible as Stream[T = l.T, {{}}] via the member tie; got: {:?}",
        load_errors(&[ok]),
    );
}

/// Soundness: a DIFFERENT receiver's projection is not threaded — `l` is not `xs`, so
/// `l.T` ≠ `xs.T` (two distinct neutrals) and returning `l` as `Stream[T = xs.T]` fails.
/// The error is the return-conformance mismatch (not an unrelated parse/import failure).
#[test]
fn bare_self_receiver_wrong_receiver_rejected() {
    let wrong = r#"
namespace test.wi461.wrongrecv
  import anthill.prelude.{List, Stream}
  operation iter3(l: List, xs: List) -> Stream[T = xs.T, E = {}] = l
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        errs.iter().any(|e| e.contains("iter3.return") && e.contains("Stream")),
        "returning `l` as Stream[T = xs.T] must be a return mismatch — l.T ≠ xs.T (the \
         threading is real); got: {errs:?}",
    );
}

/// Soundness: a bare receiver's element is the NEUTRAL `l.T`, not a wildcard — returning
/// `l` where a CONCRETE `Stream[T = Int64]` is declared is rejected (the bare carrier is
/// not silently coerced to any element).
#[test]
fn bare_self_receiver_concrete_demand_rejected() {
    let wrong = r#"
namespace test.wi461.conc
  import anthill.prelude.{List, Stream, Int64}
  operation iter4(l: List) -> Stream[T = Int64, E = {}] = l
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        errs.iter().any(|e| e.contains("iter4.return") && e.contains("Stream")),
        "returning a bare `l` as Stream[T = Int64] must be a return mismatch — l.T (neutral) \
         ≠ Int64; got: {errs:?}",
    );
}

/// EVAL: a bare iterator runs end-to-end — `collect(iter2([1,2,3]))` threads the element
/// and yields the three-element list IN ORDER, so positionally decoding the first three
/// elements gives `1*100 + 2*10 + 3 = 123` (pins element identity + order, not just count).
#[test]
fn bare_iterator_evals_through_collect() {
    let src = r#"
namespace test.wi461.eval
  import anthill.prelude.{List, Stream, Int64}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Stream.{collect}
  operation iter2(l: List) -> Stream[T = l.T, E = {}] = l
  operation gather() -> Int64 =
    match collect(iter2([1, 2, 3]))
      case cons(a, cons(b, cons(c, _))) -> a * 100 + b * 10 + c
      case _ -> 0 - 1
end
"#;
    assert!(
        load_errors(&[src]).is_empty(),
        "the bare-iterator eval fixture must typecheck; got: {:?}",
        load_errors(&[src]),
    );
    let mut interp = crate::common::interp_for(src);
    assert_eq!(
        run_int(&mut interp, "test.wi461.eval.gather"),
        123,
        "collect(iter2([1,2,3])) must yield [1,2,3] in order",
    );
}

/// A MULTI-type-param carrier providing a 2-param spec: the refinement pins EACH param to
/// its own projection (`Box2[A = b.A, B = b.B]`), so the correctly-ordered identity body
/// conforms — exercising the multi-binding loop and the cross-sort match where the carrier's
/// param names (`A`, `B`) DIFFER from the spec's (`X`, `Y`).
#[test]
fn multi_param_carrier_identity_threads_each_projection() {
    let ok = r#"
namespace test.wi461.multi
  sort Spec2
    sort X = ?
    sort Y = ?
  end
  sort Box2
    sort A = ?
    sort B = ?
    entity box2(fst: A, snd: B)
    provides Spec2[X = A, Y = B]
  end
  operation idok(b: Box2) -> Spec2[X = b.A, Y = b.B] = b
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "a 2-param carrier identity body must thread both projections in order; got: {:?}",
        load_errors(&[ok]),
    );
}

/// Soundness for the multi-param case: SWAPPING the projections (`Spec2[X = b.B, Y = b.A]`)
/// must be rejected — `b.A` ≠ `b.B`, so the cross-param mis-binding cannot slip through.
#[test]
fn multi_param_carrier_swapped_projection_rejected() {
    let wrong = r#"
namespace test.wi461.multiswap
  sort Spec2
    sort X = ?
    sort Y = ?
  end
  sort Box2
    sort A = ?
    sort B = ?
    entity box2(fst: A, snd: B)
    provides Spec2[X = A, Y = B]
  end
  operation idswap(b: Box2) -> Spec2[X = b.B, Y = b.A] = b
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        errs.iter().any(|e| e.contains("idswap.return") && e.contains("Spec2")),
        "a swapped multi-param projection must be a return mismatch (b.A ≠ b.B); got: {errs:?}",
    );
}
