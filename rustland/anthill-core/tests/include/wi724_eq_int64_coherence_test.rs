//! WI-724 — `eq` on an `Int64` value type-checks with a UNIQUE impl (no spurious
//! coherence ambiguity).
//!
//! The ticket reported `eq(c, 30)` with `c : Int64` failing to load with
//! "`PartialEq.eq.dispatch` … multiple impls match (coherence rule)", blocking the
//! WI-714 `where`/`join` algebra over Int64 columns.
//!
//! ROOT CAUSE (empirically established, at odds with the ticket's own guess of a
//! stdlib provides-overlap): the failure was an ABSTRACT row-lambda binder, not a
//! duplicated `PartialEq[Int64]` provision. When `c` typed as an unresolved
//! projection var (the pre-WI-723 `r.T` binder gap), the per-call value handed to
//! `eq`'s `PartialEq.T` was abstract, and dispatch's `types_lesseq` candidate match
//! accepts an abstract per-call value against EVERY concrete provider
//! (`Int64`/`String`/`Bool`/`BigInt`/`Set`/`Map`/`TotalFloat`) — so all of them
//! matched → "multiple impls". There is exactly ONE `fact PartialEq[T = Int64]`; the
//! numeric hierarchy (`Eq`/`Ord`/`Numeric requires … PartialEq`) is resolved by
//! the requires-recursion in `resolve_inner`, not by collecting a second candidate.
//!
//! WI-723 (row-lambda binder types at the concrete relation schema) fixed this as a
//! side effect: with `c : Int64` concrete, the per-call value is concrete `Int64`,
//! which `types_lesseq`-matches only the `Int64` provider → a UNIQUE dispatch.
//! Verified against `a73d2297` (WI-723's parent): the exact scenario there produces
//! the exact ticket error; on WI-723 it loads clean.
//!
//! This file GUARDS that resolution. The sibling `wi723_row_lambda_binder_test`
//! covers the String column and the *mismatching* `eq(c.age, "thirty")` case — which
//! fail on a type mismatch and so MASK this coherence path. The valid Int64
//! comparison exercised here is the one that used to flip dispatch to `Ambiguous`.

use crate::common::try_load_kb_with;

/// A scalar value-context `eq(30, 30)` on two Int64 literals resolves to the unique
/// `PartialEq[Int64]` impl (ticket acceptance, part 1).
#[test]
fn wi724_eq_int64_literal_scalar_is_unique() {
    let source = r#"
namespace test.wi724.scalar
  import anthill.prelude.{Bool, Int64}
  import anthill.prelude.PartialEq.{eq}
  const both_thirty: Bool = eq(30, 30)
end
"#;
    if let Err(errs) = try_load_kb_with(source) {
        panic!(
            "eq(30, 30) must resolve to a unique PartialEq[Int64] impl; got {} error(s):\n{}",
            errs.len(),
            errs.join("\n"),
        );
    }
}

/// The ticket scenario, in its post-WI-20260818-YQB1Y spelling: a single-column relation,
/// whose row is now `(age: Int64)`, so the lambda is `eq(c.age, 30)` with `c.age : Int64`
/// (ticket acceptance, part 2). The coherence question is unchanged — one `PartialEq[Int64]`
/// impl for an `Int64` reached through a row binder — only the route to the `Int64` moved
/// from the bare binder to its column, because the schema no longer 1-collapses.
#[test]
fn wi724_eq_int64_single_column_row_binder_is_unique() {
    let source = r#"
namespace test.wi724.single
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  -- ONE free head var → Relation[(age: Int64)], so `c.age` is the Int64 and
  -- `eq(c.age, 30)` is a scalar Int64 comparison.
  rule ages(?age) :- person(age: ?age)

  operation probe() -> Bool effects Error =
    let r = ages.where(lambda c -> eq(c.age, 30))
    r.isEmpty
end
"#;
    if let Err(errs) = try_load_kb_with(source) {
        panic!(
            "eq(c.age, 30) with c.age : Int64 (single-column relation) must type-check with a \
             unique impl — this is the exact WI-724 coherence scenario; got {} error(s):\n{}",
            errs.len(),
            errs.join("\n"),
        );
    }
}

/// The valid Int64 COLUMN comparison `eq(c.age, 30)` in a two-column row lambda
/// (`c.age : Int64`, `30 : Int64`) type-checks — the coherence-prone case the
/// WI-723 suite omitted (it tests only the mismatching `eq(c.age, "thirty")`).
#[test]
fn wi724_eq_int64_column_valid_comparison_is_unique() {
    let source = r#"
namespace test.wi724.column
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation probe() -> Bool effects Error =
    let r = person_row.where(lambda c -> eq(c.age, 30))
    r.isEmpty
end
"#;
    if let Err(errs) = try_load_kb_with(source) {
        panic!(
            "eq(c.age, 30) — a VALID Int64 column comparison — must type-check with a \
             unique impl; got {} error(s):\n{}",
            errs.len(),
            errs.join("\n"),
        );
    }
}
