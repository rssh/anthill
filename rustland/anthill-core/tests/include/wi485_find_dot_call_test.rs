//! WI-485 (WI-447 bare-form prereq, Gap I): a `find`-style spec op whose callback
//! param is a DENOTED arrow projecting the receiver's element (`pred: (x: s.T) -> Bool
//! @ {EffP, -Modify[x]}`) must thread `s.T` to the carrier's element when called on a
//! concrete carrier — both PLAIN (`findX(xs, cb)`) and DOT-CALL (`xs.findX(cb)`). When
//! the bare form leaves `s.T` un-grounded, a concrete named callback `is_big(n: Int64)`
//! clashes: `gt.b: expected s.T, got Int64` (is_big's body retyped against the
//! un-grounded expected param). Self-contained analogue of `wi443`'s stdlib find tests.

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

const FIXTURE: &str = r#"
namespace test.wi485.strm
  import anthill.prelude.{Option, Pair, Bool, Modify}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  sort Strm
    sort T = ?
    operation splitFirstX(s: Strm) -> Option[T = Pair[A = s.T, B = Strm[T = s.T]]]
    operation findX[EffP](s: Strm, pred: (x: s.T) -> Bool @ {EffP, -Modify[x]}) -> Option[T = s.T]
      effects EffP =
      match splitFirstX(s)
        case none() -> none
        case some(pair(h, rest)) -> if pred(h) then some(h) else findX(rest, pred)
  end
end
namespace test.wi485.lst
  import anthill.prelude.{Option, Pair, Bool}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import test.wi485.strm.{Strm}
  sort Lst
    sort T = ?
    provides Strm[T = T]
    entity lnil
    entity lcons(hd: T, tl: Lst)
    operation splitFirstX(xs: Lst) -> Option[T = Pair[A = xs.T, B = Lst[T = xs.T]]] =
      match xs
        case lnil() -> none
        case lcons(h, t) -> some(pair(h, t))
  end
end
"#;

/// PLAIN call form: `findX(xs, is_big)` on a `Lst[Int64]` threads `s.T` to `Int64`, so
/// the named callback `is_big(n: Int64)` conforms.
#[test]
fn find_plain_call_threads_callback_element() {
    let src = format!(
        r#"{FIXTURE}
namespace test.wi485.use_plain
  import anthill.prelude.{{Int64, Option, Bool}}
  import anthill.prelude.Ordered.{{gt}}
  import test.wi485.lst.{{Lst}}
  import test.wi485.strm.Strm.{{findX}}
  operation is_big(n: Int64) -> Bool = gt(n, 2)
  operation run(xs: Lst[T = Int64]) -> Option[T = Int64] = findX(xs, is_big)
end
"#
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "plain findX(xs, is_big) must thread s.T to Int64 for the callback param; got: {errs:?}",
    );
}

/// DOT-CALL form: `xs.findX(is_big)` — same threading requirement via the dot-call /
/// provided-spec dispatch path.
#[test]
fn find_dot_call_threads_callback_element() {
    let src = format!(
        r#"{FIXTURE}
namespace test.wi485.use_dot
  import anthill.prelude.{{Int64, Option, Bool}}
  import anthill.prelude.Ordered.{{gt}}
  import test.wi485.lst.{{Lst}}
  import test.wi485.strm.Strm.{{findX}}
  operation is_big(n: Int64) -> Bool = gt(n, 2)
  operation run(xs: Lst[T = Int64]) -> Option[T = Int64] = xs.findX(is_big)
end
"#
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "dot-call xs.findX(is_big) must thread s.T to Int64 for the callback param; got: {errs:?}",
    );
}

/// LAMBDA callback, PLAIN call: `findX(xs, lambda n -> gt(n, 2))`. The lambda param `n`
/// has no declared type — it must be inferred from the THREADED callback param `s.T`
/// (= Int64), so `gt(n, 2)` typechecks. The bare-form gap leaves `n : s.T`.
#[test]
fn find_plain_call_lambda_callback_infers_element() {
    let src = format!(
        r#"{FIXTURE}
namespace test.wi485.use_plain_lambda
  import anthill.prelude.{{Int64, Option, Bool}}
  import anthill.prelude.Ordered.{{gt}}
  import test.wi485.lst.{{Lst}}
  import test.wi485.strm.Strm.{{findX}}
  operation run(xs: Lst[T = Int64]) -> Option[T = Int64] = findX(xs, lambda n -> gt(n, 2))
end
"#
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "plain findX with a lambda must infer the lambda param from the threaded s.T=Int64; \
         got: {errs:?}",
    );
}

/// LAMBDA callback, DOT-CALL: `xs.findX(lambda n -> gt(n, 2))` — the wi443 repro shape.
#[test]
fn find_dot_call_lambda_callback_infers_element() {
    let src = format!(
        r#"{FIXTURE}
namespace test.wi485.use_dot_lambda
  import anthill.prelude.{{Int64, Option, Bool}}
  import anthill.prelude.Ordered.{{gt}}
  import test.wi485.lst.{{Lst}}
  import test.wi485.strm.Strm.{{findX}}
  operation run(xs: Lst[T = Int64]) -> Option[T = Int64] = xs.findX(lambda n -> gt(n, 2))
end
"#
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "dot-call xs.findX with a lambda must infer the lambda param from the threaded \
         s.T=Int64; got: {errs:?}",
    );
}
