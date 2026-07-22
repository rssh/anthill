//! WI-762 — the distributive projection is recognized by PROVENANCE, not by shape.
//!
//! `convert.rs` desugars `r.(f1, f2)` to `(f1: r.f1, f2: r.f2)` — a term IDENTICAL to
//! that tuple written by hand — and now MARKS the result (`SimpleTermStore::projections`
//! → `Expr::Constructor::from_projection`). The typer reads that mark instead of
//! re-deriving projection-hood from the fields' shape and a SOURCE-SPAN comparison of
//! their receivers.
//!
//! Three inferences were retired with it: `projection_receivers_same` (receiver IDENTITY
//! by span), the `projection_receiver_type` fallback in the projection path (receiver TYPE
//! by stamp), and `lowered_projection_receiver` (the LOWERED receiver by reading
//! `pos_args[0]` of whatever a sibling field typed into). The last two are replaced by
//! what the `DotApply` frame already knows and now writes down: the receiver's lowered
//! twin (`set_lowered_receiver`, stored WEAKLY — the leaf case lowers to the node itself,
//! so a strong handle would be an `Rc` cycle) plus the type stamp it already left there.
//!
//! THE DELIBERATE NARROWING is what this file exists to pin. A hand-written
//! `(name: r.name, age: r.age)` is no longer read as a projection even when its two
//! receivers are the same let-bound variable — the case the retired LEAF-SYMBOL rung used
//! to catch. Proposal 052:182 introduced that shape-based reading as the stopgap "until
//! `.( )` lands"; `.( )` landed as WI-639. 052:184-187 states the rule that replaces it:
//! projection is the distribute-dot, and anything computed per row is written functionally
//! with `.map`, which yields a `Stream`, not a `Relation`.
//!
//! MEASURED before/after, by running this exact file against a clean worktree at the
//! pre-WI-762 commit rather than reasoning about it: BOTH hand-written tests below FAIL
//! there and both controls pass. The old typer reported
//!
//!     type mismatch in handwritten.return (op-return):
//!       expected (name: Relation[T = String], age: Relation[T = Int64]),
//!       got Relation[E = …, T = (name: String, age: Int64)]
//!
//! — i.e. the leaf rung had projected the hand-written tuple. After WI-762 that is
//! inverted: the TUPLE annotation type-checks and the projected one is a loud mismatch.
//! Asserting both halves is what keeps either from passing vacuously.

use crate::common::{interp_for, list_heads, try_load_kb_with};
use anthill_core::eval::Value;

/// Shared preamble: a two-column relation `person_row(name, age)`.
const REL: &str = r#"
  import anthill.prelude.{String, Int64, List, Bool, Option, Relation}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
"#;

/// A hand-written tuple of column accesses on ONE let-bound relation is a TUPLE — two
/// independent single-column relations — and its type says so.
///
/// This is the narrowing. Pre-WI-762 the leaf-symbol rung read `rel` == `rel` and turned
/// this into `Relation[T = (name: String, age: Int64)]`, so this annotation did NOT
/// type-check. It does now.
#[test]
fn wi762_handwritten_tuple_is_a_tuple_of_relations() {
    let src = format!(
        r#"
namespace test.wi762hand
{REL}
  operation handwritten() -> (name: Relation[T = String], age: Relation[T = Int64]) effects Error =
    let rel = person_row
    let cols = (name: rel.name, age: rel.age)
    cols
end
"#
    );
    if let Err(e) = try_load_kb_with(&src) {
        panic!(
            "a hand-written tuple of column accesses must type as a TUPLE of independent \
             single-column relations, got: {}",
            e.join("\n")
        );
    }
}

/// The other half, so the test above cannot pass by the annotation being unchecked: the
/// SAME source annotated as a PROJECTED relation is now a loud mismatch.
#[test]
fn wi762_handwritten_tuple_is_not_a_projected_relation() {
    let src = format!(
        r#"
namespace test.wi762handproj
{REL}
  operation handwritten() -> Relation[T = (name: String, age: Int64)] effects Error =
    let rel = person_row
    let cols = (name: rel.name, age: rel.age)
    cols
end
"#
    );
    match try_load_kb_with(&src) {
        Ok(_) => panic!(
            "a hand-written tuple was read as a PROJECTION — the shape-based reading \
             WI-762 retired (proposal 052:182's pre-`.( )` stopgap)"
        ),
        Err(e) => {
            let joined = e.join("\n");
            assert!(
                joined.contains("Relation"),
                "expected a relation/tuple type mismatch naming the tuple reading, got: {joined}"
            );
        }
    }
}

/// THE CONTROL that makes both tests above meaningful: the same two columns off the same
/// let-bound receiver, written as the distribute-dot, DO project — and evaluate. If the
/// provenance mark failed to arrive, this would type as the tuple-of-relations above and
/// `takeN` would have no such member.
#[test]
fn wi762_desugared_projection_still_projects_and_runs() {
    let src = format!(
        r#"
namespace test.wi762desugared
{REL}
  operation cols() -> List[(name: String, age: Int64)] effects Error =
    let rel = person_row
    let cols = rel.(name, age)
    cols.takeN(9)
end
"#
    );
    let mut interp = interp_for(&src);
    let r = interp.call("test.wi762desugared.cols", &[]).expect("cols runs");
    let rows = list_heads(&r);
    assert_eq!(rows.len(), 2, "both rows project to the (name, age) schema");
    assert!(
        rows.iter().all(|x| matches!(x, Value::Tuple { .. })),
        "each projected row is a named tuple, not a bare column: {rows:?}"
    );
}

/// A COMPUTED receiver still resolves through the producer-written record that replaced
/// `lowered_projection_receiver`. The raw receiver occurrence is an `Expr::DotApply`, which
/// eval cannot run — only the WI-722 macro's `where_run` rewrite can — so if the record
/// carried the raw node instead of the lowered twin this would raise `unhandled Expr
/// variant in eval: DotApply` rather than returning a row.
#[test]
fn wi762_computed_receiver_projects_through_the_lowered_record() {
    let src = format!(
        r#"
namespace test.wi762computed
{REL}
  import anthill.prelude.Relation.{{where}}
  operation youngCols() -> List[(name: String, age: Int64)] effects Error =
    let filtered = person_row.where(lambda c -> eq(c.age, 25))
    let cols = filtered.(name, age)
    cols.takeN(9)
end
"#
    );
    let mut interp = interp_for(&src);
    let r = interp.call("test.wi762computed.youngCols", &[]).expect("youngCols runs");
    let rows = list_heads(&r);
    assert_eq!(rows.len(), 1, "only bob (age 25) survives the filter, then projects");
    assert!(
        matches!(rows[0], Value::Tuple { .. }),
        "the surviving row is a projected named tuple: {:?}",
        rows[0]
    );
}
