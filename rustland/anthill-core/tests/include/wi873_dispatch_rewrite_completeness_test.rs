//! WI-873 — the dispatch-rewrite table holds EVERY classified call site, not one
//! entry per spec op for the whole image.
//!
//! ## What was wrong
//!
//! `req_insertion::run` walks operation bodies, which are `NodeOccurrence` trees —
//! there is no "original apply `TermId`" to key a rewrite by, so `materialize_apply`
//! SYNTHESIZED one: `apply(fn = Ref(functor), args = nil())`. Terms are hash-consed,
//! so that key named the CALLEE and nothing else, and every call site of one spec op
//! in the image collapsed onto it. The recorders open with
//! `if kb.dispatch_rewrites.contains_key(&original_apply) { return }` — meant as
//! idempotence for a re-run of the pass — and that guard then dropped every site
//! after the first. Which one survived was decided by `op_records`' `HashMap` order,
//! i.e. per process.
//!
//! MEASURED at this ticket's head, before the fix: stdlib + one fixture classifies
//! **47** call sites and recorded **16** entries — one per distinct functor — and the
//! total stayed at 16 whether zero, one, or two fixtures deferring `PartialEq.eq`
//! were loaded beside it. A count that does not move when a fixture indisputably adds
//! a rewrite is the measurement that says entries are LOST rather than merely ordered.
//!
//! ## What this file pins
//!
//! The count MOVES, per fixture, and each fixture's own rewrite is present and
//! selectable by its enclosing operation. `size_grows_per_fixture` is the ticket's
//! own acceptance clause; the two `each_fixture_keeps_its_own_*` tests are what makes
//! the growth mean something — a count can grow while still holding the wrong entries.
//!
//! ## CONTROL — what fails when the fix is backed out
//!
//! Backed out by MUTATING the key rather than deleting anything: `RawClassified::site`
//! collapsed to `CallSite { op: functor, functor, span: <zero> }`, which is exactly
//! what the pre-fix `apply(fn = Ref(functor), args = nil())` key named. MEASURED, not
//! predicted:
//!
//! - `size_grows_per_fixture` FAILS — `baseline 16, with fixture 16`. That 16 is the
//!   ticket's own number, so the mutation reproduces the reported defect and not some
//!   other one.
//! - `each_fixture_keeps_its_own_requirement_param` FAILS — `got 0` for
//!   `Wi873OwnA.useEqA`. Zero rather than one because the collapsed key files every
//!   rewrite under the functor, so no entry answers to the fixture's operation at all.
//! - `two_sites_in_one_body_are_two_entries` FAILS — `got 0`, same reason.
//! - `a_body_with_no_deferred_call_records_nothing` PASSES either way, by design —
//!   it is the negative control that says the counting itself is not inventing
//!   entries, so it must be insensitive to the fix.
//! - `a_simp_expansion_with_two_calls_is_two_entries` measures a DIFFERENT axis and
//!   needs its own back-out (drop `nth_at_span` from the key): it fails at `got 1`,
//!   while the four above pass. Conversely it passes under the collapsed-key mutation
//!   above for the wrong reason — `got 0` there too, but so does everything. Two
//!   coordinates, two back-outs.
//!
//! The four repaired call sites elsewhere fail under the same mutation
//! (`wi222_defer_rewrite_test` ×3, `wi227_projection_search_test` ×1), while six of
//! their siblings in those two files pass either way.
//!
//! Reference: `docs/design/operation-call-model.md` §"Names model";
//! `anthill_core::kb::CallSite`.

use anthill_core::kb::KnowledgeBase;

use crate::common::{defer_dict_param_name, load_kb_with, rewrite_in_op};

/// One sort deferring `PartialEq.eq` through its own `requires` chain. Parameterized
/// by namespace + sort so several can be loaded side by side in ONE image — which is
/// the configuration the defect lived in, and a single-fixture load could not see.
fn deferring_sort(ns: &str, sort: &str, op: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, PartialEq}}
  sort {sort}
    sort T = ?
    requires PartialEq[T]
    operation {op}(a: T, b: T) -> Bool = eq(a, b)
  end
end
"#
    )
}

fn rewrite_count(kb: &KnowledgeBase) -> usize {
    kb.dispatch_rewrites_iter().count()
}

#[test]
fn size_grows_per_fixture() {
    // THE TICKET'S ACCEPTANCE CLAUSE, spelled as a difference rather than a constant:
    // the absolute totals are stdlib-dependent (39 at the time of writing) and would
    // make this a change-detector, while the DELTA is exactly the claim — one more
    // classified deferral, one more entry.
    let none = load_kb_with("namespace test.wi873.none\nend\n");
    let one = load_kb_with(&deferring_sort("test.wi873.one", "Wi873One", "useEq"));
    let two = load_kb_with(&format!(
        "{}\n{}",
        deferring_sort("test.wi873.two_a", "Wi873TwoA", "useEqA"),
        deferring_sort("test.wi873.two_b", "Wi873TwoB", "useEqB"),
    ));

    let (n0, n1, n2) = (
        rewrite_count(&none),
        rewrite_count(&one),
        rewrite_count(&two),
    );
    assert_eq!(
        n1,
        n0 + 1,
        "one sort deferring `PartialEq.eq` must add exactly one rewrite \
         (baseline {n0}, with fixture {n1})"
    );
    assert_eq!(
        n2,
        n0 + 2,
        "two such sorts must add two rewrites — one each, not one shared \
         (baseline {n0}, with both {n2})"
    );
}

#[test]
fn each_fixture_keeps_its_own_requirement_param() {
    // The count growing is not enough: it must grow by the RIGHT entries. Two sorts,
    // structurally identical apart from their names, both deferring the same stdlib
    // spec op — the exact pair whose rewrites used to collide. Each must be findable
    // through its OWN operation, and each must name its OWN chain slot.
    let kb = load_kb_with(&format!(
        "{}\n{}",
        deferring_sort("test.wi873.own_a", "Wi873OwnA", "useEqA"),
        deferring_sort("test.wi873.own_b", "Wi873OwnB", "useEqB"),
    ));

    for op_qn in [
        "test.wi873.own_a.Wi873OwnA.useEqA",
        "test.wi873.own_b.Wi873OwnB.useEqB",
    ] {
        let rewritten = rewrite_in_op(&kb, op_qn, "anthill.prelude.PartialEq.eq");
        let name = defer_dict_param_name(&kb, rewritten);
        // Each sort's chain names `PartialEq` once, so `synth_req_names` mints the
        // bare base with no disambiguating suffix — and it is the sort's own, not a
        // neighbour's, which is what a suffix here would betray.
        assert_eq!(
            kb.local_name_of(name),
            "__req_partialeq",
            "`{op_qn}`'s dispatching dict must read its own chain slot 0"
        );
    }
}

#[test]
fn two_sites_in_one_body_are_two_entries() {
    // The narrowest form of the defect: ONE operation, TWO calls to the same spec op.
    // Nothing about the enclosing sort distinguishes them — only the call sites do —
    // so this is what a key built from the callee alone can never separate, and it
    // stays wrong under any repair that keys by the sort or the operation instead.
    let src = r#"
namespace test.wi873.twice
  import anthill.prelude.{Bool, PartialEq}
  sort Wi873Twice
    sort T = ?
    requires PartialEq[T]
    operation bothEq(a: T, b: T, c: T) -> Bool = and(eq(a, b), eq(b, c))
  end
end
"#;
    let kb = load_kb_with(src);
    let op_sym = kb
        .try_resolve_symbol("test.wi873.twice.Wi873Twice.bothEq")
        .expect("bothEq registered");
    let eq_sym = kb
        .try_resolve_symbol("anthill.prelude.PartialEq.eq")
        .expect("PartialEq.eq registered");

    let sites: Vec<_> = kb
        .dispatch_rewrites_iter()
        .filter(|(site, r)| site.op == op_sym && r.spec_op == eq_sym)
        .collect();
    assert_eq!(
        sites.len(),
        2,
        "`bothEq` calls `eq` twice, so two rewrites must be recorded; got {} — \
         a single entry means the two sites still share one key",
        sites.len()
    );
    // And they are two DISTINCT sites, not one site recorded twice: the spans differ.
    assert_ne!(
        sites[0].0.span, sites[1].0.span,
        "the two entries must be the two call sites, distinguished by span"
    );
    // Both name the same requirement param — the sort has one `PartialEq` slot and
    // both calls defer through it. Said explicitly so the reader does not take the
    // two entries as evidence of two different dictionaries.
    for (site, r) in &sites {
        assert_eq!(
            kb.local_name_of(defer_dict_param_name(&kb, r.rewritten)),
            "__req_partialeq",
            "both sites defer through `Wi873Twice`'s single chain slot (span {:?})",
            site.span
        );
    }
}

#[test]
fn a_simp_expansion_with_two_calls_is_two_entries() {
    // THE SAME DEFECT, ONE COORDINATE OVER — found in review of this ticket's first
    // patch, whose key was `(op, functor, span)`. A SPAN DOES NOT IDENTIFY A CALL:
    // `simp_rewrite::substitute_to_occurrence` builds every node of a `[simp]` RHS
    // from the single redex occurrence, and `NodeOccurrence::synthesized_expr`
    // inherits that occurrence's span — so the two `eq` calls below land in `drive`'s
    // body at ONE span, with the same op and the same functor. Under that key the
    // second rewrite was dropped exactly as the synthesized-apply key had dropped
    // whole call sites, and `CallSite::nth_at_span` is what separates them.
    //
    // CONTROL, measured: stamping every entry `0` (i.e. dropping `nth_at_span` from
    // the key while leaving everything else) fails this test at `got 1`, and the four
    // other tests in this file pass — which is why this is its own arm rather than an
    // assertion inside one of them. The collapsed-key back-out those four use fails
    // this one too, at `got 0`, so it says nothing specific about this axis.
    let src = r#"
namespace test.wi873.simp
  import anthill.prelude.{Bool, PartialEq}
  sort Wi873Simp
    sort T = ?
    requires PartialEq[T]
    operation both(a: T, b: T) -> Bool = true
    rule both(?a, ?b) <=> and(eq(?a, ?b), eq(?b, ?a)) [simp]
    operation drive(a: T, b: T) -> Bool = both(a, b)
  end
end
"#;
    let kb = load_kb_with(src);
    let op_sym = kb
        .try_resolve_symbol("test.wi873.simp.Wi873Simp.drive")
        .expect("drive registered");
    let eq_sym = kb
        .try_resolve_symbol("anthill.prelude.PartialEq.eq")
        .expect("PartialEq.eq registered");

    let sites: Vec<_> = kb
        .dispatch_rewrites_iter()
        .filter(|(site, r)| site.op == op_sym && r.spec_op == eq_sym)
        .collect();
    assert_eq!(
        sites.len(),
        2,
        "the `[simp]` RHS expands to two `eq` calls in `drive`'s body, so two \
         rewrites must be recorded; got {}",
        sites.len()
    );
    // ASSERTED, because it is the whole point: these two are indistinguishable by
    // span. If a future change gave synthesized occurrences their own spans this
    // would fail, and the test would then be measuring a different thing under the
    // same name rather than silently going slack.
    assert_eq!(
        sites[0].0.span, sites[1].0.span,
        "the two expanded calls must share the redex's span — that is the collision \
         `nth_at_span` exists to break"
    );
    let mut nths = [sites[0].0.nth_at_span, sites[1].0.nth_at_span];
    nths.sort();
    assert_eq!(
        nths,
        [0, 1],
        "the group must be numbered 0, 1 — anything else means the stamp is not \
         scoped to the colliding group"
    );
}

#[test]
fn a_body_with_no_deferred_call_records_nothing() {
    // NEGATIVE CONTROL, insensitive to the fix by design. A sort with a `requires`
    // chain whose body never calls through it adds no entry — so the growth the first
    // test measures comes from CLASSIFIED CALLS and not from loading a sort at all.
    let base = load_kb_with("namespace test.wi873.base\nend\n");
    let src = r#"
namespace test.wi873.silent
  import anthill.prelude.{Bool, PartialEq}
  sort Wi873Silent
    sort T = ?
    requires PartialEq[T]
    operation ignore(a: T, b: T) -> Bool = true
  end
end
"#;
    let quiet = load_kb_with(src);
    assert_eq!(
        rewrite_count(&quiet),
        rewrite_count(&base),
        "a sort that declares `requires` but defers nothing must add no rewrite"
    );
}
