//! WI-562 — a carrier's sort-level `requires` is threaded at EVERY dispatch
//! through it (correctly — diamond coherence), so a requirement that only SOME
//! of the carrier's operations need must NOT live on the sort.
//!
//! Regression: `List requires Eq[T]` (WI-325, so the abstract `member` body's
//! `eq(head, x)` type-checks) made `List[NonEq]` ill-formed for EVERY spec-op
//! dispatch through it — `nth(pts, i)` on a `List[Waypoint]` (Waypoint not Eq)
//! in `examples/webots-modelling/lf1/leader.anthill` failed with
//! `IndexedSeq.nth.dispatch: no impl matches`, aborting the lf1 load and
//! breaking `discharge.sh`. (A dispatch-layer "drop the unrelated self-requires"
//! filter is impossible: a carrier's genuine provision requirement — `CarrierB
//! requires DiamondA` providing `DiamondB` — is structurally identical to an
//! incidental one, so the resolver cannot tell them apart; the wi224 diamond-
//! coherence test pins that the carrier's requires ARE threaded.)
//!
//! Fix: the `Eq` requirement is OP-SCOPED on `List.member` (`operation
//! member(x: T, l: List) -> Bool requires Eq[T]`, WI-448) — kept on the SORT
//! param `T` so `member` still eta-expands normally — instead of on the `List`
//! sort. The typer (`kb/typing.rs`, before dispatch) lets an operation's OWN
//! op-scoped `requires` license its body's abstract spec-op calls. So a
//! `List[NonEq]` is well-formed for the element-agnostic ops while `member`'s
//! `eq` is still licensed in its body and resolves by the element's own sort at
//! eval.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::parse;

/// Load the stdlib plus `extra` in one batch and return any load-time errors.
/// `load_all`'s finalize runs the full check pipeline (`type_check_sorts` plus
/// `req_insertion`), mirroring `anthill check`.
fn type_check_user(extra: &str) -> Vec<LoadError> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter()
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
        Err(errs) => errs,
    }
}

fn errors_text(errs: &[LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

/// `nth` (an `IndexedSeq` op) on a `List` whose element type does NOT provide
/// `Eq` must type-check. Mirrors the lf1 `nth(state.waypoints.points, i)` call
/// where `points : List[T = Waypoint]` and `Waypoint` is not `Eq`. Before the
/// fix this failed with `IndexedSeq.nth.dispatch: no impl matches` because the
/// resolver threaded `List`'s sort-level `requires Eq[T]` (for `member`) into
/// the `nth` dispatch.
#[test]
fn nth_on_list_of_non_eq_element_dispatches() {
    let src = r#"
        namespace test.wi562
          import anthill.prelude.{Int64, Float, Option, List}
          import anthill.prelude.IndexedSeq.{nth}

          -- A plain entity with no `fact Eq[…]` — deliberately NOT an Eq.
          entity Waypoint(x: Float, y: Float)
          entity WSeq(points: List[T = Waypoint], current: Int64)

          sort Accessor
            operation at(s: WSeq) -> Option[Waypoint] =
              let pts = s.points
              let cur = s.current
              nth(pts, cur)
          end
        end
    "#;
    let errs = type_check_user(src);
    assert!(
        errs.is_empty(),
        "nth on a List[Waypoint] (Waypoint not Eq) must dispatch cleanly — \
         IndexedSeq.nth needs no Eq; got:\n{}",
        errors_text(&errs)
    );
}

/// The op-scoped-`requires` coverage that licenses `member`'s abstract `eq`
/// works for USER ops too: an op declaring `requires Eq[T]` whose body compares
/// its abstract argument type-checks — WITHOUT the enclosing sort having to
/// `requires Eq`. Genuinely exercises the typer's op-requires coverage: with no
/// covering requires (next test) the same body is rejected by WI-325.
#[test]
fn op_scoped_requires_licenses_abstract_eq_in_body() {
    let src = r#"
        namespace test.wi562b
          import anthill.prelude.{Bool, Eq}
          import anthill.prelude.Eq.{eq}

          sort Util
            sort T = ?
            operation same(x: T, y: T) -> Bool requires Eq[T] = eq(x, y)
          end
        end
    "#;
    let errs = type_check_user(src);
    assert!(
        errs.is_empty(),
        "an op-scoped `requires Eq[T]` must license the body's abstract \
         `eq(x, y)` without a sort-level requires; got:\n{}",
        errors_text(&errs)
    );
}

/// Negative control: the op-requires coverage does NOT disable the WI-325
/// abstract-spec-op safety check. The same body with NO covering `requires`
/// (neither op-scoped nor sort-level) is still rejected.
#[test]
fn abstract_spec_op_without_covering_requires_still_rejected() {
    let src = r#"
        namespace test.wi562c
          import anthill.prelude.{Bool, Eq}
          import anthill.prelude.Eq.{eq}

          sort Util
            sort T = ?
            operation same(x: T, y: T) -> Bool = eq(x, y)
          end
        end
    "#;
    let errs = type_check_user(src);
    let text = errors_text(&errs);
    assert!(
        !errs.is_empty(),
        "a spec-op call on an abstract param with NO covering `requires` must \
         still be rejected (WI-325); got a clean load"
    );
    assert!(
        text.contains("requires PartialEq"),
        "the diagnostic should point at the missing PartialEq requirement (WI-644: `eq`'s spec is the PartialEq base); got:\n{text}"
    );
}
