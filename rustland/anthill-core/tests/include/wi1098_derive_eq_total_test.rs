//! WI-1098 — DERIVE `Eq` for a TOTAL composite: the symmetric half of the `NonEq`
//! derivation `eq_derive` already did.
//!
//! An entity whose fields are all lawfully `Eq` HAS a lawful structural equality, and
//! the compiler already decides so — `eq_derive`'s fixpoint classifies every composite
//! carrier as Total or Partial, and asserted a provision for the Partial half only. So
//! a `provides`-less `sort Colour { entity red; entity green }` loaded clean and then
//! died INSIDE the evaluator at the first `requires Eq[T]` it reached:
//!
//!   List.contains(cons(head: red, tail: nil), red)
//!     => Internal("DeferToRequirement: requirement param `__req_eq` not bound in
//!        caller frame (running `anthill.prelude.List.contains`, requires-chain owner
//!        `anthill.prelude.List.contains`; frame binds [])")
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ──────────────────────────────
//!
//! Each claim below was MEASURED by backing the named change out and re-running this
//! file, not predicted from reading it.
//!
//! Backing out `eq_derive::derive_total_eq` (its `load.rs` call) fails FIVE of the
//! nine here — `contains_answers_for_a_provisionless_entity` (the headline; reverts to
//! the `Internal(DeferToRequirement …)` above at BOTH the eval and the resolver
//! entry), `a_recursive_composite_answers` (same error, one level of recursion in),
//! `a_total_composite_derives_eq_and_partialeq`, and the two that carry a DERIVED row
//! as their positive neighbour: `a_float_composite_still_derives_noneq_and_not_eq`
//! (its `Plain`) and `a_float_behind_a_parametric_field_is_not_claimed_lawful` (its
//! `HoldInt`). Those two are absence assertions, and the neighbour is what stops them
//! passing on a KB where the derivation never ran at all.
//!
//! Backing out only the `build_sort_ops_table(kb)` refresh beside the derivation —
//! the delta that makes the derived provision inherit the spec's `eq` onto its
//! carrier — fails `a_direct_eq_call_at_a_derived_carrier_still_dispatches` with
//! `type mismatch in PartialEq.eq.dispatch: no impl matches`, and nothing else here.
//! That is not a hypothetical ordering note: it is what the first cut did, and it
//! broke seven `wi664_composite_eq_test` cases that had loaded clean for a year.
//!
//! Backing out only the PARAMETRIC-FIELD guard in `total_composites` fails
//! `a_float_behind_a_parametric_field_is_not_claimed_lawful`, and nothing else. With
//! the guard `HoldFloatPair` derives nothing; without it it derives `Eq`+`PartialEq` —
//! a lawfulness claim over a `Float` the classifier cannot see through `Pair`.
//!
//! Backing out only the BOUNDARY exclusion from the seed fails
//! `a_dispatched_eq_is_not_shadowed_by_a_derived_provision`, and nothing else: `Pebble`
//! picks up BOTH `("Pebble", "Eq")` and `("Pebble", "PartialEq")` beside the witness's
//! own row.
//!
//! `declaring_neq_on_a_derived_carrier_is_an_override_not_a_capture` records a
//! CONSEQUENCE this ticket did not set out to produce and which is nonetheless right;
//! its own doc carries the two measurements.
//!
//! PASSES EITHER WAY BY DESIGN — a regression guard, not this ticket's evidence:
//! `the_explicit_provides_twin_still_works` (CONTROL 2, the spelling that already
//! worked). It is here because the derivation must be IDEMPOTENT against it, not
//! because it demonstrates the derivation. `a_dispatched_eq_is_not_shadowed…`'s
//! DISPATCH half is the same (WI-837 shipped it); only its provision rows move.
//!
//! OUT OF SCOPE, and left underivable rather than falsely claimed: a composite whose
//! field is PARAMETRIC (`Option[Float]`, `Pair[A, B]`, `List`) and a parametric sort
//! itself — both need a CONDITIONAL provision (`provides Eq[Pair] :- Eq[A], Eq[B]`),
//! which this ticket does not derive. That is the same boundary the module header
//! already draws for the `NonEq` half ("entities + named tuples with CONCRETE
//! fields"), met here in the direction where being wrong is a false CLAIM rather
//! than a missed one. A carrier whose `eq` is DISPATCHED is left alone too — see
//! `a_dispatched_eq_is_not_shadowed_by_a_derived_provision` for what that costs.

use anthill_core::eval::value::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

// ── fixtures ────────────────────────────────────────────────────────────────

/// The MEASURED program, verbatim: an entity that says nothing at all about
/// equality, used where `List.contains` demands `requires Eq[T]`.
const NO_PROVIDES: &str = r#"
namespace wi1098.noprov
  import anthill.prelude.{Bool, Int64, List, Eq}
  import anthill.prelude.List.{cons, nil, contains}
  import anthill.prelude.PartialEq.{eq}
  sort Colour
    entity red
    entity green
    entity blue
  end
  sort Driver
    -- `blue` is ABSENT from the list: the negative twin, so a derivation that made
    -- `contains` vacuously true would fail here rather than pass everywhere.
    operation hasRed(n: Int64) -> Int64 =
      if contains(cons(head: red, tail: cons(head: green, tail: nil)), red) then 1 else 0
    operation hasBlue(n: Int64) -> Int64 =
      if contains(cons(head: red, tail: cons(head: green, tail: nil)), blue) then 1 else 0
  end
  -- The RESOLVER entry (wi625's shape): a rule whose `requires(Eq[T])` guard is
  -- witnessed TRANSITIVELY by the `contains` call. The guard fires only if the
  -- element carrier provides `Eq`, so this drives the derived provision from the
  -- SLD side rather than through the interpreter. A bare `contains(?xs, ?x)` goal is
  -- NOT this route and answers nothing even at `Int64` — measured.
  rule hasElem(?xs, ?x) :- requires(Eq[T]), eq(contains(?xs, ?x), true)
end
"#;

/// CONTROL 2 — the same program with the two provision lines written by hand. The
/// ONLY difference from `NO_PROVIDES`, which is what makes it a control.
const WITH_PROVIDES: &str = r#"
namespace wi1098.withprov
  import anthill.prelude.{Bool, Int64, List, Eq, PartialEq}
  import anthill.prelude.List.{cons, nil, contains}
  sort Colour
    entity red
    entity green
    entity blue
    provides PartialEq[T = Colour]
    provides Eq[T = Colour]
  end
  sort Driver
    operation hasRed(n: Int64) -> Int64 =
      if contains(cons(head: red, tail: cons(head: green, tail: nil)), red) then 1 else 0
    operation hasBlue(n: Int64) -> Int64 =
      if contains(cons(head: red, tail: cons(head: green, tail: nil)), blue) then 1 else 0
  end
end
"#;

/// The fixpoint exists for recursion, so the derivation is driven over one: `Tree` is
/// `Eq` iff `Tree` is `Eq`, which no LEAST fixpoint decides and the greatest one does.
const RECURSIVE: &str = r#"
namespace wi1098.rec
  import anthill.prelude.{Bool, Int64, List}
  import anthill.prelude.List.{cons, nil, contains}
  sort Tree
    entity leaf
    entity node(l: Tree, r: Tree)
  end
  sort Driver
    operation hasNode(n: Int64) -> Int64 =
      if contains(cons(head: node(l: leaf, r: leaf), tail: nil), node(l: leaf, r: leaf))
      then 1 else 0
    operation hasDeeper(n: Int64) -> Int64 =
      if contains(cons(head: node(l: leaf, r: leaf), tail: nil),
                  node(l: node(l: leaf, r: leaf), r: leaf))
      then 1 else 0
  end
end
"#;

// ── helpers ─────────────────────────────────────────────────────────────────

fn eval_int(src: &str, op: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(op, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{op}: expected an Int, got {other:?}"),
    }
}

/// `(carrier short name, spec short name)` for every provision filed under `ns`.
fn provisions_under(kb: &KnowledgeBase, ns: &str) -> Vec<(String, String)> {
    let prefix = format!("{ns}.");
    let short = |s: &str| s.rsplit('.').next().unwrap_or("").to_string();
    let mut out: Vec<(String, String)> = crate::common::sort_provisions(kb)
        .into_iter()
        .filter(|(c, _)| c.starts_with(&prefix))
        .map(|(c, s)| (short(&c), short(&s)))
        .collect();
    out.sort();
    out
}

/// A `List` of already-built element terms.
fn list_of(kb: &mut KnowledgeBase, elems: &[TermId]) -> TermId {
    let nil = kb
        .try_resolve_symbol("anthill.prelude.List.nil")
        .expect("List.nil");
    let cons = kb
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons");
    let head = kb.intern("head");
    let tail = kb.intern("tail");
    let mut list = kb.alloc(Term::Fn {
        functor: nil,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    for &e in elems.iter().rev() {
        list = kb.alloc(Term::Fn {
            functor: cons,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(head, e), (tail, list)]),
        });
    }
    list
}

fn ref_term(kb: &mut KnowledgeBase, qualified: &str) -> TermId {
    let sym = kb
        .try_resolve_symbol(qualified)
        .unwrap_or_else(|| panic!("symbol {qualified} not in KB"));
    kb.alloc(Term::Ref(sym))
}

fn goal(kb: &mut KnowledgeBase, functor: &str, args: &[TermId]) -> TermId {
    let f = kb
        .try_resolve_symbol(functor)
        .unwrap_or_else(|| panic!("symbol {functor} not in KB"));
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

// ── AXIS 1: the headline — a provision-less entity discharges `requires Eq[T]` ──

/// THE ACCEPTANCE. `List.contains` over a `provides`-less entity ANSWERS, at both
/// entry points, and the negative twin answers the other way — so a derivation that
/// made `contains` vacuously true would fail the `hasBlue` half.
///
/// The two entries are not redundancy: the ticket's crash was reported from
/// `bridge_op_to_eval` (the RESOLVER lending its KB to a scratch interpreter), and
/// a plain `interp.call` reaches the same classification by the other road. Both
/// raised the identical `Internal` before this change.
#[test]
fn contains_answers_for_a_provisionless_entity() {
    assert_eq!(
        eval_int(NO_PROVIDES, "wi1098.noprov.Driver.hasRed"),
        1,
        "contains([red, green], red) must answer TRUE — the derived `Eq[Colour]` is \
         what supplies `contains`'s `__req_eq` dictionary"
    );
    assert_eq!(
        eval_int(NO_PROVIDES, "wi1098.noprov.Driver.hasBlue"),
        0,
        "contains([red, green], blue) must answer FALSE — without this, a derivation \
         that made every `contains` succeed would pass the positive half"
    );

    // The RESOLVER entry, over the same carrier.
    let mut kb = crate::common::load_kb_with(NO_PROVIDES);
    let red = ref_term(&mut kb, "wi1098.noprov.Colour.red");
    let green = ref_term(&mut kb, "wi1098.noprov.Colour.green");
    let blue = ref_term(&mut kb, "wi1098.noprov.Colour.blue");
    let list = list_of(&mut kb, &[red, green]);
    let g = goal(&mut kb, "wi1098.noprov.hasElem", &[list, red]);
    let sols = kb.resolve(&[g], &ResolveConfig::default());
    assert_eq!(
        sols.len(),
        1,
        "the resolver's `hasElem([red, green], red)` must decide TRUE — the \
         `requires(Eq[T])` guard fires only at a carrier that provides `Eq`, and this \
         is the entry the ticket measured the panic from"
    );
    assert!(
        sols[0].residual.is_empty(),
        "a DEFINITE solution, not a residual: the bridge ran `contains` rather than \
         suspending, which is the difference between deciding and deferring"
    );
    let list2 = list_of(&mut kb, &[red, green]);
    let g2 = goal(&mut kb, "wi1098.noprov.hasElem", &[list2, blue]);
    assert_eq!(
        kb.resolve(&[g2], &ResolveConfig::default()).len(),
        0,
        "blue is not in [red, green] — and the guard FIRING is what makes this a \
         verdict rather than a block (wi625's `NoEq` twin is the same goal shape at a \
         carrier that provides no `Eq`, and answers 0 for the other reason)"
    );
}

/// The provision rows the derivation asserts, read off the relation — `PartialEq`
/// AND `Eq`, because `Eq requires PartialEq` and a bare `Eq` would fail
/// `check_provider_requires`.
#[test]
fn a_total_composite_derives_eq_and_partialeq() {
    let kb = crate::common::load_kb_with(NO_PROVIDES);
    assert_eq!(
        provisions_under(&kb, "wi1098.noprov"),
        vec![
            ("Colour".to_string(), "Eq".to_string()),
            ("Colour".to_string(), "PartialEq".to_string()),
        ],
        "a Total composite derives exactly the lawful pair — and `Driver`, which has \
         no constructors, is not a composite carrier and derives nothing"
    );
}

/// A RECURSIVE composite, which is why the classification is a fixpoint at all.
#[test]
fn a_recursive_composite_answers() {
    assert_eq!(
        eval_int(RECURSIVE, "wi1098.rec.Driver.hasNode"),
        1,
        "contains([node(leaf, leaf)], node(leaf, leaf)) must answer TRUE — `Tree` is \
         `Eq` iff `Tree` is, decidable only coinductively"
    );
    assert_eq!(
        eval_int(RECURSIVE, "wi1098.rec.Driver.hasDeeper"),
        0,
        "a DIFFERENT tree is not in the list — the recursive derivation must still \
         discriminate"
    );
    let kb = crate::common::load_kb_with(RECURSIVE);
    assert_eq!(
        provisions_under(&kb, "wi1098.rec"),
        vec![
            ("Tree".to_string(), "Eq".to_string()),
            ("Tree".to_string(), "PartialEq".to_string()),
        ],
    );
}

/// A DIRECT `PartialEq.eq(a, b)` call at a derived carrier dispatches.
///
/// This is the case the first cut got wrong, and it is worth its own test because it
/// fails for a reason none of the others expose: the provision was asserted where the
/// `NonEq` half is asserted, so `build_sort_ops_table` never inherited `PartialEq`'s
/// `eq` onto the carrier, and `dispatch_spec_op_cached` resolved the provision, asked
/// `sort_ops_lookup(Colour, eq)`, got `None`, and answered `NoMatch`. A carrier with
/// NO provision at all takes the permissive `NoCandidates` fall-through instead and
/// reaches the builtin — so deriving a provision made a working call stop working.
#[test]
fn a_direct_eq_call_at_a_derived_carrier_still_dispatches() {
    let src = r#"
namespace wi1098.direct
  import anthill.prelude.{Bool, Int64}
  import anthill.prelude.PartialEq.{eq}
  sort C
    entity c(a: Int64, b: Int64)
  end
  sort Driver
    operation same(n: Int64) -> Int64 = if eq(c(a: 1, b: 2), c(a: 1, b: 2)) then 1 else 0
    operation diff(n: Int64) -> Int64 = if eq(c(a: 1, b: 2), c(a: 1, b: 9)) then 1 else 0
  end
end
"#;
    assert_eq!(eval_int(src, "wi1098.direct.Driver.same"), 1);
    assert_eq!(
        eval_int(src, "wi1098.direct.Driver.diff"),
        0,
        "the derived equality still DISCRIMINATES — without this, a dispatch that \
         answered `true` unconditionally would satisfy the positive half"
    );
}

// ── AXIS 2: the controls this must not break ────────────────────────────────

/// CONTROL 2 — the explicit-`provides` twin still works, and the derivation does not
/// double-file it into a duplicate-provision error.
///
/// PASSES EITHER WAY BY DESIGN: this spelling worked before the change. What it
/// measures is IDEMPOTENCE — the derivation skips a carrier that already provides.
#[test]
fn the_explicit_provides_twin_still_works() {
    assert_eq!(eval_int(WITH_PROVIDES, "wi1098.withprov.Driver.hasRed"), 1);
    assert_eq!(eval_int(WITH_PROVIDES, "wi1098.withprov.Driver.hasBlue"), 0);
    let kb = crate::common::load_kb_with(WITH_PROVIDES);
    assert_eq!(
        provisions_under(&kb, "wi1098.withprov"),
        vec![
            ("Colour".to_string(), "Eq".to_string()),
            ("Colour".to_string(), "PartialEq".to_string()),
        ],
        "ONE row per spec: the derivation must not re-file what the author wrote"
    );
}

/// CONTROL 3 — a `Float`-field composite still derives `NonEq` and NOT `Eq`. This is
/// the row that fails if the derivation is asserted for every composite rather than
/// for the Total ones, and the one `check_eq_noneq_exclusive` would turn into a load
/// error against a program nobody wrote.
///
/// PASSES EITHER WAY BY DESIGN for the `NonEq` half (WI-664 shipped it); the `Eq`
/// ABSENCE is what this ticket adds, and it is asserted as an exact row set rather
/// than a `!contains`, so a third row appearing is also a failure.
#[test]
fn a_float_composite_still_derives_noneq_and_not_eq() {
    let src = r#"
namespace wi1098.floaty
  import anthill.prelude.{Float, Int64}
  sort Point
    entity pt(x: Float, y: Float)
  end
  sort Plain
    entity pl(x: Int64, y: Int64)
  end
end
"#;
    let kb = crate::common::load_kb_with(src);
    assert_eq!(
        provisions_under(&kb, "wi1098.floaty"),
        vec![
            ("Plain".to_string(), "Eq".to_string()),
            ("Plain".to_string(), "PartialEq".to_string()),
            ("Point".to_string(), "NonEq".to_string()),
            ("Point".to_string(), "PartialEq".to_string()),
        ],
        "the two halves of ONE classification, in the same program: the Float \
         composite is Partial and the Int64 one Total. `Plain` is the neighbour that \
         keeps this from passing on a KB where the derivation never ran at all"
    );
}

/// A carrier whose `eq` is DISPATCHED (the `TotalFloat` shape, spelled through a
/// witness sort) keeps dispatching to that impl, and no derived `Eq` is filed over it.
///
/// The supplied `eq` DISAGREES with structural equality — it calls any two pebbles
/// equal — so the answer says which impl ran. Written the agreeing way the test would
/// pass with the carrier's `eq` never consulted at all.
///
/// THE WITNESS SPELLING IS NOT A CONVENIENCE. A bare `operation eq` on a sort that
/// neither provides nor requires `PartialEq` is refused by WI-999's name-capture check
/// ("a declaration may not capture a name it does not override"), so the population of
/// "declares its own `eq`, provides nothing" is not reachable; every boundary carries a
/// provision of some kind. `Pebble` here provides `PartialEq` and NOT `Eq`.
///
/// The dispatch half PASSES EITHER WAY BY DESIGN (WI-837 shipped it). The PROVISION
/// half is this ticket's, and the BOUNDARY exclusion is what decides it — `Pebble`'s
/// only field is an `Int64`, so without that exclusion it would be seeded Total and
/// derive `Eq`, asserting REFLEXIVITY of an `eq` the compiler has not read. MEASURED:
/// removing the `!boundary.contains` clause from `total_composites`' seed adds
/// `("Pebble", "Eq")` to the rows below.
#[test]
fn a_dispatched_eq_is_not_shadowed_by_a_derived_provision() {
    let src = r#"
namespace wi1098.boundary
  import anthill.prelude.{Bool, Int64, PartialEq}
  import anthill.prelude.PartialEq.{eq}
  sort Pebble
    entity pebble(n: Int64)
  end
  sort PebbleEq
    provides PartialEq[T = Pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = true
  end
  sort Driver
    operation distinct(n: Int64) -> Int64 =
      if eq(pebble(n: 1), pebble(n: 2)) then 1 else 0
  end
end
"#;
    assert_eq!(
        eval_int(src, "wi1098.boundary.Driver.distinct"),
        1,
        "the DISPATCHED `eq` decides: structurally-distinct pebbles compare EQUAL \
         because that is what it says. A structural verdict would be 0"
    );
    let kb = crate::common::load_kb_with(src);
    assert_eq!(
        provisions_under(&kb, "wi1098.boundary"),
        vec![("PebbleEq".to_string(), "PartialEq".to_string())],
        "exactly the provision the author wrote, and it files under the WITNESS \
         (WI-1069: the provider and the carrier are two questions) — so `Pebble` \
         itself carries NO row, which is the assertion: a boundary derives nothing"
    );
}

// ── AXIS 3: the scope boundary, in the direction where being wrong is a CLAIM ──

/// A `Float` reached only THROUGH a parametric container is NOT claimed lawful.
///
/// `sort_functor_of_view` resolves a field's type to its BASE sort, so the classifier
/// sees `Pair`, not `Pair[A = Float]` — the documented parametric-container gap. On
/// the `NonEq` side that gap is conservative (a missed refusal); on the `Eq` side it
/// would be a false CLAIM, so a parametric field disqualifies the composite outright.
///
/// MEASURED both ways. With the guard, `HoldFloatPair` derives NOTHING; with it
/// removed it derives `Eq`+`PartialEq` — over a `Float`. The two neighbours are the
/// controls: `HoldFloat` proves the classifier DOES see a direct `Float` in this same
/// program, and `HoldInt` proves the derivation fires here at all.
#[test]
fn a_float_behind_a_parametric_field_is_not_claimed_lawful() {
    let src = r#"
namespace wi1098.paramfield
  import anthill.prelude.{Int64, Float, Pair}
  sort HoldFloatPair
    entity hfp(p: Pair[A = Float, B = Int64])
  end
  sort HoldFloat
    entity hf(v: Float)
  end
  sort HoldInt
    entity hi(v: Int64)
  end
end
"#;
    let kb = crate::common::load_kb_with(src);
    assert_eq!(
        provisions_under(&kb, "wi1098.paramfield"),
        vec![
            ("HoldFloat".to_string(), "NonEq".to_string()),
            ("HoldFloat".to_string(), "PartialEq".to_string()),
            ("HoldInt".to_string(), "Eq".to_string()),
            ("HoldInt".to_string(), "PartialEq".to_string()),
        ],
        "`HoldFloatPair` must derive NOTHING — neither the `Eq` its non-partial \
         classification would suggest nor the `NonEq` the hidden `Float` would"
    );
}

/// A carrier somebody has ALREADY spoken for derives nothing — even when the provision
/// is filed under a WITNESS rather than under the carrier itself.
///
/// FOUND BY REVIEW, MEASURED, and it was a FALSE CLAIM rather than a missed one. The
/// three carrier tests the seed already made — `boundary`, `partial`, `sort_provides` —
/// all key on `sort_ref`, i.e. on the PROVIDER, and a witness names its carrier only in
/// the spec's `T` binding (WI-1069: provider and carrier are two questions). So:
///
///   * `sort WrapperNonEq { provides NonEq[T = Wrapper]; operation nonEqRefl() … }`
///     put `WrapperNonEq` in `partial` and left `Wrapper` seeded Total, and the
///     derivation asserted `provides Eq[Wrapper]` — REFLEXIVITY of an equality the
///     author had just witnessed as non-reflexive. `check_eq_noneq_exclusive` stayed
///     silent because it groups by `sort_ref` too, so nothing anywhere refused it.
///   * `sort CW { provides PartialEq[T = C] }` binding no `eq` left `C` non-boundary
///     with `sort_provides(C, PartialEq)` false, so the derivation filed a SECOND
///     `(PartialEq, C)` claim beside the author's.
///
/// Both rows are the ones that come back if the `spoken_for` clause is removed from
/// the seed in `total_composites`, and nothing else in this file moves.
#[test]
fn a_carrier_a_witness_already_speaks_for_derives_nothing() {
    let noneq_witness = r#"
namespace wi1098.wit
  import anthill.prelude.{Int64, NonEq, PartialEq}
  sort Wrapper
    entity w(n: Int64)
  end
  sort WrapperNonEq
    provides PartialEq[T = Wrapper]
    provides NonEq[T = Wrapper]
    operation nonEqRefl() -> Wrapper = w(n: 0)
  end
end
"#;
    let kb = crate::common::load_kb_with(noneq_witness);
    assert_eq!(
        provisions_under(&kb, "wi1098.wit"),
        vec![
            ("WrapperNonEq".to_string(), "NonEq".to_string()),
            ("WrapperNonEq".to_string(), "PartialEq".to_string()),
        ],
        "`Wrapper` is witnessed NON-reflexive; deriving `Eq` for it would contradict \
         that, and no later check would catch it — both rows here are the author's"
    );

    let bare_partialeq_witness = r#"
namespace wi1098.wit2
  import anthill.prelude.{Int64, PartialEq}
  sort C
    entity c(n: Int64)
  end
  sort CW
    provides PartialEq[T = C]
  end
end
"#;
    let kb2 = crate::common::load_kb_with(bare_partialeq_witness);
    assert_eq!(
        provisions_under(&kb2, "wi1098.wit2"),
        vec![("CW".to_string(), "PartialEq".to_string())],
        "ONE claim about `C`'s equality, the one written — a derived second would put \
         two candidates in the coherence group where the author put one"
    );
}

/// `Eq` ⊥ `NonEq` over the WHOLE SHIPPED CORPUS, asserted rather than assumed.
///
/// The two halves are disjoint by construction — one fixpoint puts a sort in exactly
/// one class, and `total_composites` excludes the `Partial` set from its seed — but
/// "by construction" is the claim, not the evidence. A carrier that picked up both
/// would be a `check_eq_noneq_exclusive` load error blaming a program nobody wrote,
/// and the two halves are asserted at DIFFERENT points in the pipeline, which is
/// exactly the shape that drifts. This reads every provision in a full stdlib load
/// and reports the intersection.
///
/// The counts are asserted non-trivial for the reason the corpus test in
/// `wi860_default_provider_relations_test` states: an intersection of two empty sets
/// is also empty, so an emptiness assertion over a build where nothing derived would
/// pass while measuring nothing.
#[test]
fn no_carrier_derives_both_eq_and_noneq_over_the_corpus() {
    let kb = crate::common::load_kb_with("namespace wi1098.corpus\nend\n");
    let rows = crate::common::sort_provisions(&kb);
    let carriers = |spec: &str| -> std::collections::BTreeSet<String> {
        rows.iter()
            .filter(|(_, s)| s == spec)
            .map(|(c, _)| c.clone())
            .collect()
    };
    let eq = carriers("anthill.prelude.Eq");
    let noneq = carriers("anthill.prelude.NonEq");
    assert!(
        eq.len() > 20 && !noneq.is_empty(),
        "both sides must be non-trivial or the intersection below proves nothing; \
         Eq carriers = {}, NonEq carriers = {}",
        eq.len(),
        noneq.len()
    );
    let both: Vec<&String> = eq.intersection(&noneq).collect();
    assert!(
        both.is_empty(),
        "a carrier may not provide both the lawful `Eq` and the witnessed `NonEq` \
         (WI-658); the two derivations disagreed about {both:?}"
    );
}

/// A CONSEQUENCE, measured rather than intended, and correct: WI-999's name-capture
/// refusal is EXCUSED for `neq` on a derived carrier.
///
/// WI-999 refuses a declaration that captures a name already resolving in its scope,
/// and excuses it when the sort provides or requires the sort that OWNS the name.
/// `PartialEq` owns `eq` and `neq`, so a total composite that now derives
/// `provides PartialEq` turns a capture into an override — which is WI-999's own
/// rule, applied to a premise this ticket made true.
///
/// MEASURED both ways, with the import present so the name genuinely resolves:
/// backing the derivation out, `operation neq` is refused with "'C' neither provides
/// nor requires the sort that owns 'anthill.prelude.PartialEq.neq'"; with it, `C`
/// does provide it and the declaration stands.
///
/// `operation eq` stays REFUSED either way, and the two halves agree for one reason:
/// a sort declaring `eq` is a lawful-Eq BOUNDARY, so nothing is derived for it and
/// WI-999's premise is untouched. That is the row that would move if the boundary
/// exclusion were dropped.
#[test]
fn declaring_neq_on_a_derived_carrier_is_an_override_not_a_capture() {
    let program = |ns: &str, member: &str| {
        format!(
            r#"
namespace wi1098.{ns}
  import anthill.prelude.{{Bool, Int64}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort C
    entity c(n: Int64)
    {member}
  end
end
"#
        )
    };
    let errs = |src: &str| {
        crate::common::try_load_kb_with(src)
            .err()
            .unwrap_or_default()
    };
    assert!(
        errs(&program("ovneq", "operation neq(a: C, b: C) -> Bool = true")).is_empty(),
        "a derived `provides PartialEq` makes an `neq` declaration an OVERRIDE"
    );
    let eq_errs = errs(&program("capeq", "operation eq(a: C, b: C) -> Bool = true"));
    assert!(
        eq_errs.iter().any(|e| e.contains("captures a name")),
        "declaring `eq` makes the sort a BOUNDARY, so nothing is derived for it and \
         WI-999's capture refusal still stands; got {eq_errs:?}"
    );
}

/// A PARAMETRIC sort derives nothing either: `List`/`Option`'s lawful equality is
/// conditional on its element's, and an unconditional `Eq[List]` would claim
/// `List[Float]` lawful. Driven over the SHIPPED stdlib rather than a fixture,
/// because that is where the population this change touches actually lives.
///
/// `Duration` is the positive neighbour, in the same scan and the same KB: a
/// non-parametric prelude composite (`duration(millis: Int64, label: String)`) that
/// DOES pick up the derived pair. Without it the absence below would also hold on a
/// build where the derivation never ran.
#[test]
fn a_parametric_sort_is_not_derived() {
    let kb = crate::common::load_kb_with("namespace wi1098.empty\nend\n");
    let rows = crate::common::sort_provisions(&kb);
    let equality_of = |carrier: &str| -> Vec<String> {
        let mut v: Vec<String> = rows
            .iter()
            .filter(|(c, s)| {
                c == carrier
                    && matches!(
                        s.as_str(),
                        "anthill.prelude.Eq" | "anthill.prelude.PartialEq"
                    )
            })
            .map(|(_, s)| s.rsplit('.').next().unwrap_or("").to_string())
            .collect();
        v.sort();
        v
    };
    assert_eq!(
        equality_of("anthill.prelude.Duration"),
        vec!["Eq".to_string(), "PartialEq".to_string()],
        "the NEIGHBOUR: a non-parametric prelude composite derives the lawful pair, so \
         the two absences below are about being parametric and not about the \
         derivation being off"
    );
    for parametric in ["anthill.prelude.List", "anthill.prelude.Option"] {
        assert!(
            equality_of(parametric).is_empty(),
            "a parametric container may not be claimed unconditionally lawful — its \
             equality is conditional on its arguments' (`provides Eq[Pair] :- Eq[A], \
             Eq[B]`), which this ticket does not derive; {parametric} got {:?}",
            equality_of(parametric)
        );
    }
}
