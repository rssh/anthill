//! WI-857 — ONE requirement-dictionary layout, one owner.
//!
//! A dictionary for spec `S` supplied by provider `P` bundles its sub-requirements
//! in a single order (`kb::typing::DictLayout`):
//!
//!   [ S's own direct `requires` … ]  ++  [ P's own direct `requires` … ]
//!
//! Before this ticket the PRODUCER (`candidate_sub_goals_owned`, now `dict_sub_goals`
//! over the two halves) emitted only the
//! second half while two CONSUMERS indexed the first: `expand_dispatching_dict`
//! named the callee's frame slots from whatever chain the dispatched target's parent
//! declared, and `requirement_at_sort` projected the required spec's own chain. The
//! two agreed only when the provider was a chain-free witness sort — dispatch then
//! landed on that witness's member, whose parent chain is empty. For a
//! CARRIER-KEYED provision (`fact Ord[T = Int64]`, provider `Int64`, which
//! declares no `requires`) the dictionary arrived arity 0 where the spec's two slots
//! were wanted, so EVERY spec whose own chain is non-empty died at eval.
//!
//! What this file pins, in the order the ticket states it:
//!
//!  1. the two 058-free reproducers — `requires Eq[T]` reaching `PartialEq.eq`
//!     transitively, and `requires Ord[T]` reaching `WeakOrd.compare` — RUN;
//!  2. the two controls that identified the trigger still run: the spec whose own
//!     chain is EMPTY (`PartialEq`), and a chain-free WITNESS provider;
//!  3. the parametric, chain-bearing witness (the ticket's feedback, probe `q4e`) —
//!     the shape where BOTH halves are non-empty at once — runs on both routes;
//!  4. the LOCALITY rule: inside provider `W`'s dictionary, a sub-goal `W` itself
//!     provides resolves to `W`'s own provision before any global search;
//!  5. the layout's own shape, read off `resolve` directly, including that a
//!     spec-half slot with no provider is RECORDED (`Unavailable`) rather than
//!     dropped — and that reading such a slot is LOUD.
//!
//! Everything here is driven end-to-end (`interp.call`), because the defect was
//! invisible to the load: every reproducer below loaded clean before the fix.

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;
use anthill_core::kb::typing::{
    dict_layout, resolve, ResolutionResult, ResolutionScope, ResolvedRequiresNode, SortGoal,
};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// Run `entry(0)` on a FRESH interpreter — a trapped call poisons later calls on a
/// shared one. `interp_for` panics on a dirty load, so a value assertion is also a
/// clean-load assertion.
fn eval_int(src: &str, entry: &str, why: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}"),
    }
}

fn eval_err(src: &str, entry: &str, needle: &str, why: &str) {
    let mut interp = crate::common::interp_for(src);
    let err = match interp.call(entry, &[Value::Int(0)]) {
        Err(e) => format!("{e}"),
        Ok(v) => panic!("{why}; expected a failure, got {v:?}"),
    };
    assert!(
        err.contains(needle),
        "{why}; expected {needle:?}, got: {err}"
    );
}

// ── (1)+(2) the ticket's reproducers and their controls ───────────────────

/// The ticket's own minimal program, all four holders in ONE load so the passing and
/// the previously-failing cases share every other variable.
///
/// `HolderPE` is the CONTROL: `PartialEq`'s own `requires` chain is empty, so
/// producer and consumer agreed about it even before the fix, and it ran. `HolderEq`
/// and `HolderOrd` are the reproducers, and they differ from the control ONLY in the
/// chain depth of the spec they require — which is what identifies the trigger as the
/// spec's chain and not the shape of the holder.
///
/// `HolderEq` exercises the `requirement_at_sort` consumer (the body's `PartialEq.eq`
/// is reached TRANSITIVELY, through `Eq`, so it reads `__req_eq` and projects slot 0)
/// and `HolderOrd` the `expand_dispatching_dict` one (`WeakOrd.compare` dispatches
/// onto the SPEC's op, since `Int64` supplies no member, so the frame is named from
/// `Ord`'s two-entry chain). Those were the two distinct death sites.
const HOLDERS: &str = r#"
namespace wi857.holder
  import anthill.prelude.{Int64, Bool, PartialEq, Eq, Ord, WeakOrd}

  sort HolderPE
    sort T = ?
    requires PartialEq[T]
    operation same(a: T, b: T) -> Bool = PartialEq.eq(a, b)
  end

  sort HolderEq
    sort T = ?
    requires Eq[T]
    operation same(a: T, b: T) -> Bool = PartialEq.eq(a, b)
  end

  sort HolderOrd
    sort T = ?
    requires Ord[T]
    operation cmp(a: T, b: T) -> Int64 = WeakOrd.compare(a, b)
  end

  sort Driver
    operation viaPartialEq(n: Int64) -> Int64 = if HolderPE.same(7, 7) then 1 else 0
    operation viaEq(n: Int64) -> Int64 = if HolderEq.same(7, 7) then 1 else 0
    operation viaEqFalse(n: Int64) -> Int64 = if HolderEq.same(7, 8) then 1 else 0
    operation viaOrd(n: Int64) -> Int64 = HolderOrd.cmp(7, 3)
  end
end
"#;

#[test]
fn a_requires_partialeq_holder_runs_the_control() {
    assert_eq!(
        eval_int(
            HOLDERS,
            "wi857.holder.Driver.viaPartialEq",
            "the CONTROL must pass"
        ),
        1,
        "`PartialEq`'s own chain is empty, so this ran before the fix too — it is here \
         to make the two assertions below non-vacuous",
    );
}

#[test]
fn a_requires_eq_holder_reaches_partialeq_transitively() {
    // Before: Internal("DeferToRequirement: projection index 0 out of range
    // (requirement `__req_eq` bundles 0 sub-requirement(s))"). The `Eq[Int64]`
    // dictionary now bundles its spec half — `PartialEq[Int64]` — at slot 0, which is
    // exactly what the projection reads.
    assert_eq!(
        eval_int(
            HOLDERS,
            "wi857.holder.Driver.viaEq",
            "the `Eq` reproducer must run"
        ),
        1,
        "eq(7, 7) is true",
    );
    // …and it DECIDES, rather than answering the same way regardless: a dictionary
    // that dispatched somewhere wrong could still return a Bool.
    assert_eq!(
        eval_int(
            HOLDERS,
            "wi857.holder.Driver.viaEqFalse",
            "the negative arm"
        ),
        0,
        "eq(7, 8) is false — without this the test would pass on a constant `true`",
    );
}

#[test]
fn a_requires_ordered_holder_dispatches_the_specs_own_op() {
    // Before: Internal("… dispatching dict for anthill.prelude.WeakOrd.compare has
    // arity 0 but its requires chain has 2 entries"). `Int64` supplies no `compare`
    // member, so dispatch lands on the spec's own builtin and the frame is named from
    // `Ord`'s chain (`Eq`, `PartialOrd`) — which the dictionary now carries.
    assert_eq!(
        eval_int(
            HOLDERS,
            "wi857.holder.Driver.viaOrd",
            "the `Ord` reproducer"
        ),
        1,
        "compare(7, 3) is 1 for the prelude's ascending Int64 order",
    );
}

/// The ticket's SECOND control: a WITNESS sort supplying the op. This ran before the
/// fix — dispatch lands on `Ascending.compare`, whose parent's chain is empty, so the
/// consumer asked for 0 names and got the 0-arity dictionary — and it must still run,
/// because the fix changes what that dictionary CONTAINS (it now also carries
/// `Ord`'s two spec-half slots) and therefore where the witness's frame slice
/// starts. Getting the slice wrong here would be silent: `Ascending` declares no
/// `requires`, so a mis-offset would only show up as a wrong value.
#[test]
fn a_chain_free_witness_provider_still_runs() {
    let src = r#"
namespace wi857.witness
  import anthill.prelude.{Int64, Ord, WeakOrd}
  import anthill.prelude.Numeric.{sub}

  sort Descending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end

  sort Driver
    operation viaWitness(n: Int64) -> Int64 = WeakOrd.compare[WeakOrd = Descending](7, 3)
  end
end
"#;
    assert_eq!(
        eval_int(
            src,
            "wi857.witness.Driver.viaWitness",
            "the witness control"
        ),
        -4,
        "`Descending.compare` is `sub(b, a)` = 3 - 7; the prelude's own ascending \
         `Ord[Int64]` would answer 1, so the value also proves the witness — not \
         the carrier — supplied the op",
    );
}

// ── (3) the parametric, chain-bearing witness — BOTH halves at once ───────

/// The ticket's feedback addition (probe `q4e`), and the only shape in which the
/// spec half and the provider half are BOTH non-empty, so it is the one that pins
/// the order of the two and the slice boundary between them.
///
/// `Duo` provides `PartialEq`/`Eq` for itself componentwise (so its dictionary's
/// provider half is `Eq[A]`, `Eq[B]`); `LexFst` is a witness bundling
/// `PartialOrd[Duo]` + `Ord[Duo]` with its OWN chain `Ord[A]`, `Ord[B]`.
/// The `Ord[Duo[Int64, Int64]]` dictionary therefore carries four slots: the spec
/// half (`Eq[Duo]`, `PartialOrd[Duo]`) then the provider half (`Ord[Int64]`
/// twice) — and `LexFst.compare`'s frame must read the SECOND pair. It loaded clean
/// and died `arity 0 but its requires chain has 2 entries` on both routes before.
const PARAMETRIC_WITNESS: &str = r#"
namespace wi857.parametric
  import anthill.prelude.{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}

  enum Duo
    import anthill.prelude.{PartialEq, Eq}
    sort A = ?
    sort B = ?
    requires Eq[T = A]
    requires Eq[T = B]
    entity duo(l: A, r: B)
    provides PartialEq[T = Duo]
    provides Eq[T = Duo]
    operation eq(a: Duo, b: Duo) -> Bool =
      match a
        case duo(al, ar) ->
          match b
            case duo(bl, br) ->
              if PartialEq.eq(al, bl) then PartialEq.eq(ar, br) else false
  end

  sort LexFst
    import anthill.prelude.PartialOrd.{lt, gt}
    sort A = ?
    sort B = ?
    requires Ord[T = A]
    requires Ord[T = B]
    provides PartialOrd[T = Duo[A = A, B = B]]
    provides Ord[T = Duo[A = A, B = B]]
    operation compare(a: Duo[A = A, B = B], b: Duo[A = A, B = B]) -> Int64 =
      match a
        case duo(al, ar) ->
          match b
            case duo(bl, br) ->
              let c = WeakOrd.compare(al, bl)
              if lt(c, 0) then c
              else if gt(c, 0) then c
              else WeakOrd.compare(ar, br)
  end

  sort Driver
    operation searched(n: Int64) -> Int64 =
      WeakOrd.compare(duo(l: 1, r: 9), duo(l: 2, r: 1))
    operation tiebreaks(n: Int64) -> Int64 =
      WeakOrd.compare(duo(l: 5, r: 9), duo(l: 5, r: 1))
  end
end
"#;

#[test]
fn a_parametric_chain_bearing_witness_threads_both_halves() {
    assert_eq!(
        eval_int(
            PARAMETRIC_WITNESS,
            "wi857.parametric.Driver.searched",
            "q4e's route"
        ),
        -1,
        "first components 1 < 2, so the lexicographic answer is negative",
    );
    // The SECOND component decides only when the first ties — which is the branch
    // that dispatches `WeakOrd.compare` through the witness's SECOND chain slot. A
    // slice off by one would take slot 0's dictionary here and still be a valid
    // `Ord[Int64]`, so `searched` alone would not catch it.
    assert_eq!(
        eval_int(
            PARAMETRIC_WITNESS,
            "wi857.parametric.Driver.tiebreaks",
            "the tie branch"
        ),
        1,
        "first components tie at 5, so the second decides: 9 > 1",
    );
}

// ── (4) the locality rule ─────────────────────────────────────────────────

/// 058 §3.8's LOCALITY rule, which the settlement had to include: when constructing
/// provider `W`'s dictionary, a sub-goal `W` itself provides resolves to `W`'s OWN
/// provision before any global search.
///
/// It becomes necessary exactly BECAUSE the spec half is now bundled. `Ord
/// requires PartialOrd[T]`, and the lawful form of an alternative ordering is a
/// `PartialOrd` + `Ord` BUNDLE (`ordered.anthill` derives the inherited
/// `gt`/`lt` from `compare`, so a lone `Ord` witness's dictionary would
/// contradict itself). So with two coexisting bundles, `PartialOrd[Duo]` has one
/// candidate inside EACH of them and a global search TIES — the only right answer is
/// witness-local. The rule keys on the SELECTED provider and never on caller scope,
/// so it does not make a program's meaning depend on its imports.
///
/// Driven, not asserted structurally: both witnesses coexist, each is selected by
/// name, and each must compute ITS OWN answer. A tie would refuse the load, and
/// picking the wrong witness's `PartialOrd` would still load.
#[test]
fn a_sub_goal_the_provider_supplies_resolves_witness_local() {
    let src = r#"
namespace wi857.locality
  import anthill.prelude.{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}
  import anthill.prelude.Numeric.{sub}
  
  enum Duet
    import anthill.prelude.{PartialEq, Eq}
    sort A = ?
    sort B = ?
    requires Eq[T = A]
    requires Eq[T = B]
    entity pr(l: A, r: B)
    provides PartialEq[T = Duet]
    provides Eq[T = Duet]
    operation eq(a: Duet, b: Duet) -> Bool =
      match a
        case pr(al, ar) ->
          match b
            case pr(bl, br) ->
              if PartialEq.eq(al, bl) then PartialEq.eq(ar, br) else false
  end

  sort ByFst
    sort A = ?
    sort B = ?
    requires Ord[T = A]
    requires Ord[T = B]
    provides PartialOrd[T = Duet[A = A, B = B]]
    provides Ord[T = Duet[A = A, B = B]]
    operation compare(a: Duet[A = A, B = B], b: Duet[A = A, B = B]) -> Int64 =
      match a
        case pr(al, ar) ->
          match b
            case pr(bl, br) -> WeakOrd.compare(al, bl)
  end

  sort BySnd
    sort A = ?
    sort B = ?
    requires Ord[T = A]
    requires Ord[T = B]
    provides PartialOrd[T = Duet[A = A, B = B]]
    provides Ord[T = Duet[A = A, B = B]]
    operation compare(a: Duet[A = A, B = B], b: Duet[A = A, B = B]) -> Int64 =
      match a
        case pr(al, ar) ->
          match b
            case pr(bl, br) -> WeakOrd.compare(ar, br)
  end

  sort Driver
    operation byFst(n: Int64) -> Int64 =
      WeakOrd.compare[WeakOrd = ByFst](pr(l: 1, r: 9), pr(l: 2, r: 1))
    operation bySnd(n: Int64) -> Int64 =
      WeakOrd.compare[WeakOrd = BySnd](pr(l: 1, r: 9), pr(l: 2, r: 1))
  end
end
"#;
    assert_eq!(
        eval_int(src, "wi857.locality.Driver.byFst", "ByFst selected"),
        -1,
        "first components 1 < 2",
    );
    assert_eq!(
        eval_int(src, "wi857.locality.Driver.bySnd", "BySnd selected"),
        1,
        "second components 9 > 1 — the SAME pairs through the other witness, so an \
         equal answer would mean the selection did not reach the dictionary",
    );
}

// ── (5) the layout itself, and the recorded absence ───────────────────────

fn goal_at(kb: &mut KnowledgeBase, spec_qn: &str, carrier_qn: &str) -> SortGoal {
    let spec = kb
        .try_resolve_symbol(spec_qn)
        .unwrap_or_else(|| panic!("{spec_qn}"));
    let carrier = kb
        .try_resolve_symbol(carrier_qn)
        .unwrap_or_else(|| panic!("{carrier_qn}"));
    let carrier_ref = kb.alloc(Term::Ref(carrier));
    let t = kb.intern("T");
    SortGoal {
        spec_sort: spec,
        bindings: SmallVec::from_slice(&[(t, carrier_ref)]),
        carrier: None,
    }
}

/// The layout is a PUBLIC, shared reading — `dict_layout` is the one owner both the
/// producer and every consumer call — so read it directly and check it against what
/// `resolve` actually builds. If these two ever diverge, the arity cross-check in
/// `expand_dispatching_dict` fires at eval, which is the failure WI-857 was.
#[test]
fn the_layout_counts_what_resolve_bundles() {
    let mut kb = crate::common::load_kb_with(
        "namespace wi857.shape\n  import anthill.prelude.{Int64}\nend\n",
    );
    for (spec_qn, expect_spec_half) in [
        ("anthill.prelude.PartialEq", 0),
        ("anthill.prelude.Eq", 1),
        // WI-1109: 3, not 2 — `Ord` now declares `Eq`, `PartialOrd` AND `WeakOrd`,
        // the last being the floor split out of it. The count IS the assertion here.
        ("anthill.prelude.Ord", 3),
    ] {
        let goal = goal_at(&mut kb, spec_qn, "anthill.prelude.Int64");
        let scope = ResolutionScope {
            available_requires: &[],
            sigma: None,
            selected: &[],
        };
        let tree = match resolve(&mut kb, &goal, &scope) {
            ResolutionResult::Resolved(t) => t,
            other => panic!("{spec_qn}[T = Int64] must resolve; got {other:?}"),
        };
        let provider = tree.impl_sort().expect("a resolved provision pins an impl");
        let layout = dict_layout(&mut kb, goal.spec_sort, provider);
        assert_eq!(
            layout.arity(),
            expect_spec_half,
            "{spec_qn} declares {expect_spec_half} `requires`, and `Int64` — a \
             carrier-keyed provider — declares none, so the whole dictionary IS the \
             spec half: {}",
            layout.describe(&kb),
        );
        let bundled = match &tree {
            ResolvedRequiresNode::Conditional {
                sub_resolutions, ..
            } => sub_resolutions.len(),
            ResolvedRequiresNode::Leaf { .. } => 0,
            other => panic!("expected Leaf/Conditional; got {other:?}"),
        };
        assert_eq!(
            bundled,
            layout.arity(),
            "the producer must bundle exactly what the layout counts for {spec_qn}",
        );
    }
}

/// The fixture for the two tests below — the shape in which a spec-half slot can have
/// NO provider yet the program still LOADS.
///
/// `check_provider_requires` (WI-343/WI-356) is binding-precise only where σ grounds
/// every binding; where one stays abstract it falls back to a base-level existence
/// check — "some sort named in the provision provides the required spec", at ANY
/// bindings. `WTop`'s provision `Top[T = Wrap[E = E]]` keeps `E` abstract, and `Wrap`
/// does provide `Base` — at `T = Int64`, not at `T = Wrap[…]`. So the load passes and
/// `Base[T = Wrap[E = Int64]]` still has no provider at the call's bindings.
///
/// That gap is not contrived: it is the stdlib's normal state. `FiniteCollection
/// requires Iterable[C = C]` holds for a `List` carrier only through `List provides
/// Stream provides Iterable`, which no `Iterable[C = List[…]]` provision matches — and
/// the same for `MutableCollection`, `PersistentCollection`, and every `Stream` op
/// dispatched on a non-`Stream` carrier. Demanding the spec half resolve broke 33
/// tests (MEASURED), which is why it is recorded instead.
///
/// (A tighter fixture is not available: with every binding GROUND, or with the
/// required spec provided by nothing at all, the load check refuses the program
/// outright — `fact Eq[T = Odd]` without `PartialEq[Odd]`, and even `fact Eq[T =
/// List[T = A]]` without a list `PartialEq`, are both load errors. MEASURED while
/// writing this file.)
const UNPROVIDED_SPEC_HALF: &str = r#"
namespace wi857.gap
  import anthill.prelude.{Int64}

  sort Base
    sort T = ?
    operation b(x: T) -> Int64
  end

  enum Wrap
    import anthill.prelude.{Int64}
    sort E = ?
    entity wrap(v: E)
    -- Wrap provides Base — for Int64. NOT for a Wrap.
    provides Base[T = Int64]
    operation b(x: Int64) -> Int64 = x
  end

  sort Top
    sort T = ?
    requires Base[T = T]
    operation t(x: T) -> Int64
  end

  sort WTop
    sort E = ?
    provides Top[T = Wrap[E = E]]
    operation t(x: Wrap[E = E]) -> Int64 = 7
  end

  sort Holder
    sort T = ?
    requires Top[T]
    -- Reached TRANSITIVELY (Holder -> Top -> Base), so this reads `__req_top` and
    -- projects slot 0 — exactly the spec-half slot with no provider.
    operation via(x: T) -> Int64 = Base.b(x)
  end

  sort Driver
    operation go(n: Int64) -> Int64 = Holder.via(wrap(v: 5))
  end
end
"#;

/// A spec-half slot whose goal has NO provider is RECORDED, not dropped: dropping it
/// would shorten the dictionary and silently shift the provider half into its place,
/// and refusing it would reject the programs the fixture's note describes.
#[test]
fn an_unprovided_spec_half_slot_is_recorded_not_dropped() {
    let mut kb = crate::common::load_kb_with(UNPROVIDED_SPEC_HALF);
    // Goal `Top[T = Wrap[E = Int64]]` — what `Driver.go`'s call pins.
    let wrap = kb.try_resolve_symbol("wi857.gap.Wrap").expect("Wrap");
    let int64 = kb
        .try_resolve_symbol("anthill.prelude.Int64")
        .expect("Int64");
    let int_ref = kb.alloc(Term::Ref(int64));
    let e = kb.intern("E");
    let t = kb.intern("T");
    let wrap_int = kb.alloc(Term::Fn {
        functor: wrap,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(e, int_ref)]),
    });
    let top = kb.try_resolve_symbol("wi857.gap.Top").expect("Top");
    let goal = SortGoal {
        spec_sort: top,
        bindings: SmallVec::from_slice(&[(t, wrap_int)]),
        carrier: None,
    };
    let scope = ResolutionScope {
        available_requires: &[],
        sigma: None,
        selected: &[],
    };
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::Resolved(ResolvedRequiresNode::Conditional {
            impl_sort,
            sub_resolutions,
            ..
        }) => {
            assert_eq!(kb.qualified_name_of(impl_sort), "wi857.gap.WTop");
            assert_eq!(
                sub_resolutions.len(),
                1,
                "`Top`'s chain is one entry and `WTop` declares no `requires`, so the \
                 dictionary is the spec half alone: {sub_resolutions:?}",
            );
            match &sub_resolutions[0] {
                ResolvedRequiresNode::Unavailable { spec_sort } => assert_eq!(
                    kb.qualified_name_of(*spec_sort),
                    "wi857.gap.Base",
                    "the recorded absence must name the requirement it is missing",
                ),
                other => panic!(
                    "nothing provides `Base[T = Wrap[E = Int64]]`, so the slot must be \
                     Unavailable — neither dropped nor filled with a provider that \
                     does not exist; got {other:?}"
                ),
            }
        }
        other => panic!(
            "the dictionary must still BUILD — refusing here would reject programs \
             that never read the slot; got {other:?}"
        ),
    }
}

/// …and the other half of that decision: a recorded absence that IS read is LOUD.
/// Without this the tolerance above would be a silent skip — the read would fall
/// through to `Base.b` itself, which for a bodyless spec op means a value-directed
/// rescue or an unattributable `OperationBodyMissing`, and for a BUILTIN spec op
/// (`PartialEq.eq`) means quietly taking the host's structural answer where a
/// provider's was wanted.
#[test]
fn reading_an_unprovided_spec_half_slot_is_loud() {
    eval_err(
        UNPROVIDED_SPEC_HALF,
        "wi857.gap.Driver.go",
        "pins no provider",
        "reading a slot the dictionary recorded as unprovided must name it",
    );
}
