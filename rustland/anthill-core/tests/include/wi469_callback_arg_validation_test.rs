//! WI-469 (WI-385 gap, pre-existing, surfaced by WI-460): a callback ARGUMENT
//! was not validated against a DENOTED-BEARING arrow parameter type. The WI-385
//! validator (`validate_arg_against_param`) gates on groundness, and a denoted
//! arrow whose EFFECTS row is non-ground (it carries the op's `EffP` type-param
//! and a binder-relative `-Modify[x]`) makes the WHOLE arrow non-ground — so the
//! gate skipped it, silently accepting a callback whose concrete PARAM or RESULT
//! element type is wrong (`(String) -> Bool` where `(Int64) -> Bool` is declared).
//!
//! The fix validates the arrow's CONCRETE param/result components even when the
//! overall arrow is non-ground (the effects-row alignment stays deferred to
//! dispatch). Param is contravariant, result covariant; a genuinely polymorphic
//! component is left for dispatch. This reproduces for BOTH a projection param
//! (`(x: s.T) -> Bool`, `s.T` eliminating to the concrete element) and a plain
//! concrete param (`(x: Int64) -> Bool`) — the gap is independent of WI-460's
//! projection-bearing arrows.

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

fn is_arrow_mismatch(errs: &[String]) -> bool {
    errs.iter().any(|e| e.contains("type mismatch") && e.contains("find2.pred"))
}

/// THE GAP (plain concrete arrow param): `find2`'s `pred` is declared
/// `(x: Int64) -> Bool @ {EffP, -Modify[x]}`; passing `badcb(x: String) -> Bool`
/// must be rejected — the callback accepts `String`, not the `Int64` the arrow is
/// called with.
#[test]
fn nonprojection_param_mismatch_rejected() {
    let src = r#"
namespace test.wi469.nonproj
  import anthill.prelude.{Stream, Option, Bool, Int64, String}
  operation find2[EffP](s: Stream, pred: (x: Int64) -> Bool @ {EffP, -Modify[x]}) -> Option[T = Int64] effects {s.E, EffP}
  operation badcb(x: String) -> Bool = true
  operation use_bad(es: Stream[T = Int64, E = {}]) -> Option[T = Int64] = find2[EffP = {}](es, badcb)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        is_arrow_mismatch(&errs),
        "a callback with the wrong concrete param type must be rejected (WI-469), got: {errs:?}",
    );
}

/// Same gap via a PROJECTION param (`(x: s.T) -> Bool`): when `s : Stream[T =
/// Int64]`, `s.T` eliminates to `Int64`, so `badcb(x: String)` is the same
/// mismatch. This is the WI-460 form (projection-bearing arrow) that brought this
/// pre-existing hole into focus.
#[test]
fn projection_param_mismatch_rejected() {
    let src = r#"
namespace test.wi469.proj
  import anthill.prelude.{Stream, Option, Bool, Int64, String}
  operation find2[EffP](s: Stream, pred: (x: s.T) -> Bool @ {EffP, -Modify[x]}) -> Option[T = s.T] effects {s.E, EffP}
  operation badcb(x: String) -> Bool = true
  operation use_bad(es: Stream[T = Int64, E = {}]) -> Option[T = Int64] = find2[EffP = {}](es, badcb)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        is_arrow_mismatch(&errs),
        "a callback with the wrong projection-eliminated param type must be rejected (WI-469), got: {errs:?}",
    );
}

/// The RESULT element type is checked too (covariant): a callback returning
/// `String` where the arrow result is `Bool` must be rejected.
#[test]
fn result_mismatch_rejected() {
    let src = r#"
namespace test.wi469.result
  import anthill.prelude.{Stream, Option, Bool, Int64, String}
  operation find2[EffP](s: Stream, pred: (x: Int64) -> Bool @ {EffP, -Modify[x]}) -> Option[T = Int64] effects {s.E, EffP}
  operation badret(x: Int64) -> String = "hi"
  operation use_badret(es: Stream[T = Int64, E = {}]) -> Option[T = Int64] = find2[EffP = {}](es, badret)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        is_arrow_mismatch(&errs),
        "a callback with the wrong concrete result type must be rejected (WI-469), got: {errs:?}",
    );
}

/// MUST NOT reject: a callback whose concrete param/result MATCH the declared
/// arrow loads clean — the fix narrows nothing for a correct callback. (The
/// non-ground effects row `{EffP, -Modify[x]}` is left to dispatch, unchanged.)
#[test]
fn valid_callback_accepted() {
    let src = r#"
namespace test.wi469.good
  import anthill.prelude.{Stream, Option, Bool, Int64, String}
  operation find2[EffP](s: Stream, pred: (x: Int64) -> Bool @ {EffP, -Modify[x]}) -> Option[T = Int64] effects {s.E, EffP}
  operation goodcb(x: Int64) -> Bool = true
  operation use_good(es: Stream[T = Int64, E = {}]) -> Option[T = Int64] = find2[EffP = {}](es, goodcb)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "a callback whose concrete param/result match must load clean (WI-469 must-not-reject), got: {errs:?}",
    );
}

/// MUST NOT reject: the projection form with a MATCHING callback (`s.T` =
/// `Int64`, callback param `Int64`) loads clean.
#[test]
fn valid_projection_callback_accepted() {
    let src = r#"
namespace test.wi469.goodproj
  import anthill.prelude.{Stream, Option, Bool, Int64, String}
  operation find2[EffP](s: Stream, pred: (x: s.T) -> Bool @ {EffP, -Modify[x]}) -> Option[T = s.T] effects {s.E, EffP}
  operation goodcb(x: Int64) -> Bool = true
  operation use_good(es: Stream[T = Int64, E = {}]) -> Option[T = Int64] = find2[EffP = {}](es, goodcb)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "a matching callback against a projection param must load clean (WI-469 must-not-reject), got: {errs:?}",
    );
}
