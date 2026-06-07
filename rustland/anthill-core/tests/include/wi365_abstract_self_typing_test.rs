//! WI-365 — abstract spec-op SELF-typing. A default `operation` body declared
//! *inside* an abstract sort, calling that sort's own self-receiver spec op,
//! must typecheck: the enclosing sort's element `T` and effect row `E` thread
//! through the abstract self-receiver call.
//!
//! The canonical instance is `stdlib/anthill/prelude/stream.anthill`:
//!
//!   operation collect(s: Stream) -> List[T] effects E =
//!     match splitFirst(s)
//!       case none() -> nil
//!       case some(pair(h, rest)) -> cons(head: h, tail: collect(rest))
//!
//! declared inside the abstract `Stream` sort. `s : Stream` is understood at
//! the sort's self type, so `splitFirst(s)` returns `Option[Pair[A = T, …]] @ E`
//! — the element threads (so `cons(h, …) : List[T]` conforms to the declared
//! return) and the effect row `E` matches the declared `effects E`. Before
//! WI-365 the effect comparison was by display NAME, and the declared row
//! variable (`Ref(Stream.E)` → "E") never matched the body's resolved form (the
//! `SortAlias` `Var` → "?_"), so the body spuriously reported `undeclared
//! effect: ?_`. The fix compares effect labels by structural identity
//! (`views_structurally_equal`) after canonicalization, not by rendered name.
//!
//! Because `Stream`'s bodies live in stdlib, this whole file's `try_load` of the
//! stdlib already exercises the DEFINITION side: if `Stream.collect`/`takeN`
//! failed to typecheck, the stdlib would not load and every case here would
//! fail at the shared `try_load`. The cases below additionally pin the
//! CONSUMPTION side — a `List` walked through the `Stream` interface — and the
//! element-soundness boundary.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra source → load errors (empty Vec on clean load).
fn try_load(extra: &str) -> Vec<load::LoadError> {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).err().unwrap_or_default()
}

fn errors_text(errs: &[load::LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

/// DEFINITION side. The stdlib (which now carries `Stream.collect` / `takeN`
/// default bodies over `splitFirst`) loads clean. If the abstract-self-receiver
/// bodies failed to thread `T` / `E`, the stdlib would not typecheck and this
/// (and every other stdlib-loading test) would fail.
#[test]
fn stream_default_bodies_typecheck_on_load() {
    let errs = try_load("namespace test.wi365.anchor\nend\n");
    assert!(
        errs.is_empty(),
        "stdlib (with Stream.collect/takeN default bodies over the abstract \
         self-receiver `splitFirst`) must typecheck; got load errors:\n{}",
        errors_text(&errs),
    );
}

/// CONSUMPTION side. A `List[Int64]` walked through the `Stream` spec op `collect`
/// — `List` provides `Stream`, so `collect` dispatches to `Stream`'s default
/// body, whose inner `splitFirst` resolves to `List`'s impl (the WI-357 concrete
/// path). The result is `List[Int64]`, so the `-> List[T = Int64]` op conforms.
#[test]
fn collect_consuming_list_as_stream_typechecks() {
    let src = r#"
namespace test.wi365.collect
  import anthill.prelude.{List, Int64}
  import anthill.prelude.Stream.{collect}

  operation drain(xs: List[T = Int64]) -> List[T = Int64] = collect(xs)
end
"#;
    let errs = try_load(src);
    assert!(
        errs.is_empty(),
        "consuming a List[Int64] through Stream.collect must yield List[Int64]; \
         got load errors:\n{}",
        errors_text(&errs),
    );
}

/// `takeN` likewise: it has a default body over `splitFirst`, so consuming a
/// `List[Int64]` through it typechecks to `List[Int64]`.
#[test]
fn take_n_consuming_list_as_stream_typechecks() {
    let src = r#"
namespace test.wi365.taken
  import anthill.prelude.{List, Int64}
  import anthill.prelude.Stream.{takeN}

  operation first2(xs: List[T = Int64]) -> List[T = Int64] = takeN(xs, 2)
end
"#;
    let errs = try_load(src);
    assert!(
        errs.is_empty(),
        "consuming a List[Int64] through Stream.takeN must yield List[Int64]; \
         got load errors:\n{}",
        errors_text(&errs),
    );
}

/// WI-367 (delivered): consumption-side element precision for a body-ful
/// self-receiver spec op.
///
/// `collect` over a `List[Int64]` is `List[Int64]`, so returning it where
/// `List[String]` is expected must be REJECTED. Before WI-367 it was NOT,
/// because the *consumption-side* element of a body-ful self-receiver spec op
/// was driven by WI-270 expected-type seeding rather than the carrier: the
/// declared return `drain -> List[String]` seeded `unify_types(collect.return =
/// List[T], List[String])` → bound `Stream.T := String` *before* the carrier
/// (`xs : List[Int64]`) was consulted, so `bind_spec_params_from_carrier` found
/// `Stream.T` already bound and skipped. WI-367 binds the spec element params
/// from the concrete carrier (ground truth) BEFORE expected-seeding, so the
/// element is `Int64` (the carrier's truth), `resolved_ret` is `List[Int64]`, and
/// the operation-return check rejects the differing `List[String]`.
#[test]
fn collect_wrong_element_return_is_rejected() {
    let src = r#"
namespace test.wi365.unsound
  import anthill.prelude.{List, Int64, String}
  import anthill.prelude.Stream.{collect}

  operation drain(xs: List[T = Int64]) -> List[T = String] = collect(xs)
end
"#;
    let errs = try_load(src);
    assert!(
        !errs.is_empty(),
        "collect on a List[Int64] is List[Int64], so returning it as List[String] \
         must be rejected; loaded clean instead",
    );
}
