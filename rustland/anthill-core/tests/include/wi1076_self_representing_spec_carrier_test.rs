//! WI-1076 — A SELF-REPRESENTING SPEC HAS NO CARRIER PARAMETER, so reading its FIRST
//! type parameter as the carrier reads its ELEMENT type instead.
//!
//! `provision_carrier_binding` (`kb/typing.rs`) took the carrier parameter
//! POSITIONALLY — `sort_type_params_as_pairs(spec).first()`. That is right for every
//! spec that HAS a carrier parameter (`Iterable[C = …]`, `Eq[T = …]`) and wrong for a
//! SELF-REPRESENTING one, whose operations take the spec sort ITSELF as receiver
//! (`Stream.head(s: Stream)`) and which therefore declares no carrier parameter at all.
//! Its first parameter is the element type, so the provision was recorded at the
//! ELEMENT and the provider was classified a WITNESS for it.
//!
//! RE-MEASURED over the loaded stdlib by dumping every `provision_carrier` and
//! `self_provides` row with the fix on and off and diffing the two sets — SEVEN
//! provisions change and nothing else does. (The ticket said six; it had missed
//! `LogicalStream provides Stream`. The diff is the count, not the census I wrote by
//! hand.) Every one is a sort declaring that it IS a stream:
//!
//! ```text
//!   before                              after
//!   FilteredStream | Stream | T         FilteredStream | Stream | FilteredStream
//!   FiniteStream   | Stream | T         FiniteStream   | Stream | FiniteStream
//!   List           | Stream | T         List           | Stream | List
//!   LogicalStream  | Stream | T         LogicalStream  | Stream | LogicalStream
//!   MappedStream   | Stream | T         MappedStream   | Stream | MappedStream
//!   List           | FiniteStream  | T  List           | FiniteStream  | List
//!   Relation       | LogicalStream | T  Relation       | LogicalStream | Relation
//! ```
//!
//! and the same rows appear as new `self_provides` rows — the inferred-default rows
//! 058 §3.6 was missing. ALL SEVEN are closed, but only six of them by this code: the
//! seventh, `Relation provides LogicalStream`, was closed by fixing the DECLARATION
//! that misled the reader — `pure(x: T)` reused the sort's type parameter for a value
//! it merely lifts, and is now `pure[A](x: A) -> LogicalStream[A, {}]`. That was wrong
//! from the first day rather than a limit of its vintage — a shared logical variable
//! said the same thing, and the neighbouring `mplus` used one in the same commit.
//! No other row in either relation moved.
//!
//! THE FIX ASKS WHICH PARAMETER THE OPERATIONS TAKE (`spec_carrier_param`): the first
//! declared type parameter some declared operation takes as a parameter, or `None` when
//! none do. "Takes" is a WIDER test than "receives on" — and WI-1077 DECIDED that the
//! wider one is the rule (option (c)), so the two shapes where they differ are intended
//! behaviour rather than a gap owed a fix. Pinned here by
//! `an_accepted_element_declared_first_still_wins_over_the_carrier_param` and, for the
//! self-receiving face, by `wi1077_accepts_vs_receives_test`, so the documented rule and
//! the implemented one cannot drift apart unnoticed. Where a spec reuses its own type parameter by ACCIDENT the repair
//! is the declaration, not the predicate
//! (`the_producer_argument_case_is_closed_by_its_own_type_parameter`).
//! `provision_carrier_binding` answers `None` for a spec with no such parameter, which every
//! consumer already reads as "not a witness, the carrier IS the provider" — the
//! `dispatch_carrier` builtin mints the provider, `defaults.rs` emits the INFERRED
//! default row, the dot-call witness match declines, and
//! `requires_edge_is_carrier_preserving` reads it as "not carrier-preserving", which is
//! the same rule from the other side.
//!
//! WHY NOT THE STRICTER `spec_is_self_representing` (WI-614), which asks whether any
//! operation takes the SORT itself and would close `LogicalStream` too: it was written,
//! measured, and REJECTED. A spec may declare BOTH a carrier parameter and a
//! self-receiving operation, and gating on self-representation discarded such a spec's
//! explicit `C = Box` binding and REFUSED A PROGRAM THAT LOADS
//! (`a_spec_with_both_a_carrier_param_and_a_self_receiver_keeps_its_binding` is that
//! fixture). The two predicates fail in opposite directions and only one direction can
//! break working code: answering "carrier parameter" when the truth is
//! "self-representing" leaves a provision where it already was; answering
//! "self-representing" when the spec HAS a carrier parameter throws a written binding
//! away.
//!
//! A WITNESS FOR A GENUINELY SELF-REPRESENTING SPEC CANNOT EXIST: dispatch is directed
//! by the receiver VALUE's own sort, there being no parameter position that names a
//! carrier, so a sort claiming one is claiming to BE one. "Provider ≠ carrier" is not
//! merely unobserved there — it is unsayable.
//!
//! WHAT FAILS WHEN THE FIX IS BACKED OUT — measured, one back-out, not predicted:
//! `a_self_representing_spec_records_its_provider_as_the_carrier`,
//! `the_stdlib_stream_provisions_read_their_provider`, and
//! `a_supplier_tie_on_a_self_representing_spec_is_now_refused`. The other four pass
//! either way BY DESIGN and are the controls: the carrier-param half of the pair, the
//! WITNESS row (which would break if the fix made every provision a self-provision —
//! the likeliest way to be wrong), the mixed-shape row (which the REJECTED predicate
//! breaks), and the residue row.
//!
//! REFERENCE: WI-1069 (settled what a `provides` clause's bindings mean, and measured
//! this residue), WI-614 (`spec_is_self_representing`), WI-860
//! (`provision_carrier_binding`, the shared owner; the relation-vs-index agreement test
//! that guards a drift here), WI-450 (the witness kind), proposal 058 §3.6,
//! kernel-language §5.1.

use crate::wi860_default_provider_relations_test::relation_rows;
use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

/// BOTH SPEC SHAPES IN ONE PROGRAM, which is the ticket's acceptance: the two cannot be
/// conflated again if one fixture drives both.
///
/// `Feed` is SELF-REPRESENTING — `next(f: Feed)` receives the spec sort itself, so
/// `Feed`'s single type parameter `T` is its ELEMENT and it has no carrier parameter.
/// `Holder` is CARRIER-PARAMETERIZED — `peek(c: C)` receives the parameter, so `C` is
/// the carrier and `Element` is not. `Box` provides both, so one carrier, one program,
/// and the only difference between the two rows is the shape of the spec.
const BOTH_SHAPES: &str = r#"namespace test.wi1076.both
  import anthill.prelude.Int64

  sort Feed
    sort T = ?
    operation next(f: Feed) -> Int64
  end

  sort Holder
    sort C = ?
    sort Element = ?
    operation peek(c: C) -> Int64
  end

  sort Box
    import anthill.prelude.Int64
    entity box(n: Int64)
    provides Feed[T = Int64]
    provides Holder[C = Box, Element = Int64]
    operation next(f: Box) -> Int64 = 1
    operation peek(c: Box) -> Int64 = 2
  end
end
"#;

/// `provision_carrier(?P, ?S, ?C)` rows for one spec, by its short name.
///
/// `pub(crate)` for WI-1077, which drives the RESIDUE this file records — the shapes
/// `spec_carrier_param` answers by "accepts" where "receives on" would decide. One reader of
/// one relation, so the two files cannot disagree about what a carrier row is.
pub(crate) fn carrier_rows(kb: &mut KnowledgeBase, spec: &str) -> Vec<String> {
    let needle = format!("| {spec} |");
    relation_rows(kb, "provision_carrier", 3)
        .into_iter()
        .filter(|r| r.contains(&needle))
        .collect()
}

/// THE ACCEPTANCE. A self-representing spec's provision records the PROVIDER as its
/// carrier — not the binding, which names the element type.
///
/// Before the fix this answered `Box | Feed | Int64`: the provision was filed at
/// `Int64`, and `Box` — a sort declaring that it IS a `Feed` — was classified a witness
/// FOR `Int64`. Both halves are driven, because the classification and the defaults
/// substrate read it through different relations and a fix reaching only one would be
/// the WI-838 shape.
#[test]
fn a_self_representing_spec_records_its_provider_as_the_carrier() {
    let mut kb = crate::common::load_kb_with(BOTH_SHAPES);
    assert_eq!(
        carrier_rows(&mut kb, "Feed"),
        vec!["Box | Feed | Box".to_string()],
        "`Feed.next(f: Feed)` receives the spec sort itself, so `Feed` has no carrier \
         parameter and `T = Int64` is its ELEMENT — the carrier is the provider"
    );
    assert!(
        relation_rows(&mut kb, "self_provides", 2).contains(&"Box | Feed".to_string()),
        "a carrier that IS what it provides must self-provide it — this is the row \
         058 §3.6 infers a default from, and it was absent: {:?}",
        relation_rows(&mut kb, "self_provides", 2)
    );
}

/// CONTROL — the other half of the same program, and the row that would break if the
/// fix had simply made every provision answer its provider.
///
/// `Holder.peek(c: C)` receives the PARAMETER, so `C` is a real carrier parameter and
/// its binding is what the provision dispatches at. Here provider and carrier coincide
/// because `Box` provides for itself; the witness row below is where they must not.
///
/// Passes either way by design.
#[test]
fn a_carrier_parameterized_spec_still_reads_its_binding() {
    let mut kb = crate::common::load_kb_with(BOTH_SHAPES);
    assert_eq!(
        carrier_rows(&mut kb, "Holder"),
        vec!["Box | Holder | Box".to_string()],
        "`C = Box` is a carrier-parameter binding and must still be read as one"
    );
    assert!(
        relation_rows(&mut kb, "self_provides", 2).contains(&"Box | Holder".to_string()),
        "the carrier-parameterized provision self-provides too, by its binding"
    );
}

/// CONTROL — the row that proves the fix did not retire the WITNESS kind.
///
/// A separate sort supplies `Holder` for `Box`. Its carrier must still come from the
/// binding and must still differ from its provider, so `provision_carrier` answers the
/// pair and `self_provides` does NOT hold for the witness.
///
/// Passes either way by design, and it is the sharpest control available: the fix's
/// most plausible failure mode is collapsing every provision into a self-provision, and
/// this row is what that would break.
#[test]
fn a_witness_for_a_carrier_parameterized_spec_is_still_a_witness() {
    let src = r#"namespace test.wi1076.witness
  import anthill.prelude.Int64

  sort Holder
    sort C = ?
    sort Element = ?
    operation peek(c: C) -> Int64
  end

  sort Box
    entity box(n: Int64)
  end

  sort BoxHolder
    import anthill.prelude.Int64
    provides Holder[C = Box, Element = Int64]
    operation peek(c: Box) -> Int64 = 2
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        carrier_rows(&mut kb, "Holder"),
        vec!["BoxHolder | Holder | Box".to_string()],
        "a witness for a carrier-parameterized spec keeps its provider/carrier split"
    );
    assert!(
        !relation_rows(&mut kb, "self_provides", 2).contains(&"BoxHolder | Holder".to_string()),
        "a witness is not a self-provider — the fix must not collapse the two"
    );
}

/// THE STDLIB RE-MEASUREMENT the ticket asks for, as a live assertion rather than a
/// number in a comment: every `Stream`-family provision in the shipped library reads
/// its own provider as its carrier.
///
/// These seven are the population that motivated the ticket. The `Stream` rows are
/// asserted as the FULL SET rather than with `contains`, so a provision that silently
/// stopped being recorded fails here instead of passing quietly — the failure mode a
/// `contains` on a relation cannot see. (The set is five, not four: `LogicalStream`
/// provides `Stream` too, which the ticket's hand-written census missed and this
/// assertion caught on its first run.)
#[test]
fn the_stdlib_stream_provisions_read_their_provider() {
    let mut kb = crate::common::load_kb_with(
        "namespace test.wi1076.stdlib\n  import anthill.prelude.Int64\nend\n",
    );
    assert_eq!(
        carrier_rows(&mut kb, "Stream"),
        vec![
            "FilteredStream | Stream | FilteredStream".to_string(),
            "FiniteStream | Stream | FiniteStream".to_string(),
            "List | Stream | List".to_string(),
            "LogicalStream | Stream | LogicalStream".to_string(),
            "MappedStream | Stream | MappedStream".to_string(),
            // WI-1109: `Relation provides LogicalStream[T = T, E = E]` and
            // `LogicalStream provides Stream[T = T, E = E]` are both IDENTITY
            // forwardings, so `derive_forwarded_provisions` materializes the row that
            // was already true transitively — `sort_provides(Relation, Stream)`
            // answered true before it. A truthful row, not a new claim.
            "Relation | Stream | Relation".to_string(),
        ],
        "`Stream` is self-representing (`splitFirst(s: Stream)`), so each carrier that \
         declares it IS a stream must record ITSELF — before the fix every row here \
         read the element parameter `T`"
    );
    assert_eq!(
        carrier_rows(&mut kb, "FiniteStream"),
        vec!["List | FiniteStream | List".to_string()],
    );
    let selves = relation_rows(&mut kb, "self_provides", 2);
    for row in [
        "FilteredStream | Stream",
        "FiniteStream | Stream",
        "List | FiniteStream",
        "List | Stream",
        "LogicalStream | Stream",
        "MappedStream | Stream",
    ] {
        assert!(
            selves.contains(&row.to_string()),
            "`{row}` must hold — 058 §3.6 infers a carrier's default from exactly this, \
             and all of these were absent"
        );
    }
}

/// THE SEVENTH ROW — closed, and NOT by the classifier. The declaration was wrong.
///
/// `LogicalStream.pure` was written `pure(x: T) -> LogicalStream`, reusing the SORT's
/// type parameter `T` for a value the operation merely lifts. That is what made `T`
/// answer as a carrier parameter: an operation taking `x: T` is indistinguishable, to
/// [`spec_carrier_param`], from one receiving on a carrier. It is now `pure[A](x: A) ->
/// LogicalStream[A, {}]`, with `A` the OPERATION's own bracket parameter, and the
/// question stops being asked — `LogicalStream` takes none of its own type parameters,
/// so it has no carrier parameter and its provisions record their provider.
///
/// IT WAS WRONG FROM THE FIRST DAY, and the vintage is not the excuse it looks like.
/// `pure` was written 2026-02-23 (`9e6b81c1`) and stdlib's first OPERATION type
/// parameter landed 2026-06-10 (WI-424) — but a shared LOGICAL VARIABLE says the same
/// thing and needed nothing new. `pure(x: ?A) -> LogicalStream[?A, {}]` type-checks
/// today (measured, same refusal), and the neighbour `mplus(a: LogicalStream{T = ?A}, b:
/// LogicalStream{T = ?A})` was written that way IN THE SAME COMMIT, six lines below.
/// Types are terms and they unify, so operation-level polymorphism was always
/// expressible here; `pure` simply reached for the sort's parameter instead.
///
/// This is the repair WI-1077 settled on preferring wherever it applies — a declaration
/// saying what it means, rather than a predicate inferring it. Where the reuse is
/// INTENDED there is nothing to repair: `Set.insert(s: Set, x: T)` genuinely takes the
/// sort's element, its provision files THERE by the rule, and that face is driven by
/// `wi1077_accepts_vs_receives_test` while
/// `an_accepted_element_declared_first_still_wins_over_the_carrier_param`
/// below is that face.
#[test]
fn the_producer_argument_case_is_closed_by_its_own_type_parameter() {
    let mut kb = crate::common::load_kb_with(
        "namespace test.wi1076.residue\n  import anthill.prelude.Int64\nend\n",
    );
    assert_eq!(
        carrier_rows(&mut kb, "LogicalStream"),
        vec!["Relation | LogicalStream | Relation".to_string()],
        "`pure[A](x: A)` takes the OPERATION's parameter, not the sort's, so \
         `LogicalStream` has no carrier parameter and `Relation` is its own carrier"
    );
    assert!(
        relation_rows(&mut kb, "self_provides", 2).contains(&"Relation | LogicalStream".to_string()),
        "and the inferred default row 058 §3.6 wants is now present"
    );
}

/// THE DECLARATION FIX'S OWN CONTROL, and it is not about carriers at all — reusing the
/// SORT's type parameter for a value an operation merely lifts also lost the type.
///
/// `pure(x: T) -> LogicalStream` returned a BARE `LogicalStream`, which §4.4's expansion
/// reads as `LogicalStream[T = ?, E = ?]` — a FRESH variable, unrelated to the `T` the
/// argument was typed at. So `pure(1)` produced a stream whose element type was
/// unconstrained and unified with anything. MEASURED, by running this case against both
/// signatures: under the old one an `Int64` lifted into a `String`-element stream LOADS
/// CLEAN; under `pure[A](x: A) -> LogicalStream[A, {}]` it is refused naming both types.
///
/// Fails when the signature is reverted — which is what makes it the control for the
/// declaration half of this change, the carrier rows being the control for the code
/// half.
#[test]
fn pures_own_type_parameter_threads_its_argument_type() {
    let src = r#"namespace test.wi1076.purethreads
  import anthill.prelude.{LogicalStream, Int64, String}
  import anthill.prelude.LogicalStream.{pure}
  operation lift() -> LogicalStream[T = String, E = {}] = pure(1)
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("LogicalStream[T = String")
            && e.contains("LogicalStream[T = Int64")),
        "`pure`'s result must carry its ARGUMENT's type, so lifting an `Int64` into a \
         `String`-element stream is refused naming both — with the bare `-> \
         LogicalStream` return this loaded clean: {errs:?}"
    );
}

/// THE ALGEBRA, DRIVEN — `mplus` of an EMPTY stream and a NON-EMPTY one, which is the
/// interaction the `pure` signature change is really about and which no row above
/// reaches.
///
/// `empty() -> LogicalStream[?A]` leaves its element open; `pure(1)` now fixes its own
/// to `Int64`; `mplus(a: LogicalStream[?A], b: LogicalStream[?A]) -> LogicalStream[?A]`
/// SHARES one variable across both arguments and the result. So combining them must
/// unify the open element with the concrete one and answer `LogicalStream[T = Int64]`.
/// Written inside a sort that `requires LogicalStream[…]`, which is what lets an
/// abstract spec's operations be called at all.
///
/// THE MISMATCH ARM IS WHY THIS MEANS ANYTHING: `mplus(pure(1), pure("s"))` must be
/// REFUSED naming both element types. Without it, an `mplus` that simply dropped its
/// element constraint would satisfy the first arm just as well — the WI-1069 lesson
/// about an instrument that cannot tell agreement from indifference.
#[test]
fn mplus_unifies_an_empty_stream_with_a_non_empty_one() {
    let ok = r#"namespace test.wi1076.mplusok
  import anthill.prelude.{LogicalStream, Int64}
  sort Q
    import anthill.prelude.{LogicalStream, Int64}
    import anthill.prelude.LogicalStream.{empty, pure, mplus}
    requires LogicalStream[T = Int64, E = {}]
    operation combine() -> LogicalStream[T = Int64, E = {}] = mplus(empty(), pure(1))
  end
end
"#;
    assert!(
        crate::common::try_load_kb_with(ok).is_ok(),
        "an empty stream must combine with an `Int64` one — `empty`'s open element \
         unifies with `pure(1)`'s through `mplus`'s shared `?A`"
    );

    let bad = r#"namespace test.wi1076.mplusbad
  import anthill.prelude.{LogicalStream, Int64, String}
  sort Q
    import anthill.prelude.{LogicalStream, Int64, String}
    import anthill.prelude.LogicalStream.{pure, mplus}
    requires LogicalStream[T = Int64, E = {}]
    operation combine() -> LogicalStream[T = Int64, E = {}] = mplus(pure(1), pure("s"))
  end
end
"#;
    let errs = crate::common::try_load_kb_with(bad).err().unwrap_or_default();
    // WI-1082 — matched on the ELEMENT bindings rather than on `LogicalStream[T = …`, because
    // the order bindings render in is not part of the type. `mplus`'s parameter partially
    // writes the sort (`LogicalStream[T = ?A]`), so the tie now materializes its elided `E`
    // and `rigidify_unwritten_sort_params` rebuilds the application in the SORT's declared
    // parameter order — the message reads `LogicalStream[E = {empty_row}, T = Int64]`. It
    // still names both elements, which is the whole of what this control asserts.
    assert!(
        errs.iter()
            .any(|e| e.contains("T = Int64") && e.contains("T = String")),
        "`mplus` shares ONE element variable, so two different element types are \
         refused naming both — this is the control for the arm above: {errs:?}"
    );
}

/// THE SAME RULE FROM THE CARRIER-PARAMETERIZED SIDE, pinned because the claim
/// "declaration order retires the positional assumption" is true only while no operation
/// takes the earlier parameter — and a review found me asserting it without that clause.
///
/// `Holder` declares `Element` before `C` and `has(c: C, e: Element)` ACCEPTS the
/// element, so `Element` answers and the explicit `C = Box` binding is discarded exactly
/// as the old positional read discarded it. Not a regression — the positional read gave
/// the same answer — but the shipped rule must not be described as if it did not.
///
/// WI-1077 DECIDED THIS IS THE RULE, not a residue awaiting a fix (option (c), user
/// 2026-08-11): the carrier parameter stays INFERRED, "takes as a parameter" is the
/// question asked, and no surface is added to say otherwise. The verdict below is
/// therefore permanent rather than provisional — an earlier version of this row said
/// "change this row when WI-1077 lands", and what landed keeps it. Its sibling face — a
/// spec that RECEIVES on its own sort and also accepts its element — is driven by
/// `wi1077_accepts_vs_receives_test`, which had no coverage at all until that ticket.
///
/// Passes with the ticket backed out. It is here to keep the documented rule and the
/// implemented one from drifting apart, which is the failure this file exists to record.
#[test]
fn an_accepted_element_declared_first_still_wins_over_the_carrier_param() {
    let src = r#"namespace test.wi1076.accepts
  import anthill.prelude.{Int64, Bool}

  sort Holder
    sort Element = ?
    sort C = ?
    operation peek(c: C) -> Int64
    operation has(c: C, e: Element) -> Bool
  end

  sort Box
    entity box(n: Int64)
  end

  sort BoxHolder
    import anthill.prelude.{Int64, Bool}
    provides Holder[C = Box, Element = Int64]
    operation peek(c: Box) -> Int64 = 2
    operation has(c: Box, e: Int64) -> Bool = true
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        carrier_rows(&mut kb, "Holder"),
        vec!["BoxHolder | Holder | Int64".to_string()],
        "THE RULE (WI-1077 option (c)): `has(c: C, e: Element)` merely ACCEPTS the \
         element, but `spec_carrier_param` cannot tell that from receiving on it, so the \
         earlier-declared `Element` answers and `C = Box` is discarded. Inferred by \
         design — the repair for an UNINTENDED reuse is the declaration, as \
         `LogicalStream.pure` was repaired"
    );
}

/// THE ONE BEHAVIOUR THIS TICKET DELIBERATELY WIDENS, pinned so it cannot be undone by
/// accident — and it was a recorded open question, not a surprise.
///
/// `concrete_self_receiver_override` and the WI-1042 supplier-tie arm both carried a
/// REACH note saying the tie refusal could never fire on a self-representing spec,
/// because every such provision was filed at the spec's first type parameter and so no
/// route-2 supplier reached the carrier — and that closing it "must be a decision taken
/// there, not a side effect". Filing the provision at its provider closes it.
///
/// The decision is to let the refusal reach: `Box` supplies `Feed.next` TWICE — its own
/// member and its provision's `next = boxNext` binding — and before this ticket one of
/// the two was invisible, so route order silently picked the member. That is exactly
/// what WI-1010's rule forbids. Making it loud is the same treatment the carrier-param
/// shape already gets.
///
/// MEASURED INERT ON THE LIBRARY: the full workspace is green, so no stdlib provision
/// writes an op binding beside its carrier's own member. Fails when the ticket is backed
/// out — the program loads and answers the member silently.
#[test]
fn a_supplier_tie_on_a_self_representing_spec_is_now_refused() {
    let src = r#"namespace test.wi1076.tie
  import anthill.prelude.Int64

  sort Feed
    sort T = ?
    operation peek(f: Feed) -> Int64
    operation next(f: Feed) -> Int64 = 1
  end

  operation boxNext(f: Box) -> Int64 = 3

  sort Box
    import anthill.prelude.Int64
    entity box(n: Int64)
    provides Feed[T = Int64, next = boxNext]
    operation peek(f: Box) -> Int64 = 0
    operation next(f: Box) -> Int64 = 2
  end

  operation probe() -> Int64 = Feed.next(box(n: 5))
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("ambiguous dispatch")
            && e.contains("2 implementations are supplied")
            && e.contains("Box.next")
            && e.contains("boxNext")),
        "two suppliers for one op on a self-representing carrier must be REFUSED, \
         naming both by supply route — not settled by route order: {errs:?}"
    );
}

/// THE CONTROL THE REVIEW FOUND MISSING, and the reason this file does not use the
/// stricter `spec_is_self_representing` predicate.
///
/// A spec may declare BOTH a carrier parameter its operations receive on AND an
/// operation taking the spec sort itself. Gating on self-representation classified this
/// one as self-representing, discarded the explicit `C = Box` binding, filed the
/// witness's dictionary under the witness, and REFUSED THE LOAD with a `requires
/// Holder[Element = …]` mismatch — measured on this fixture. The carrier must come from
/// the binding, and the call must still reach the witness's member.
///
/// Fails under `spec_is_self_representing`; passes under the shipped predicate and
/// passes with the whole ticket backed out.
#[test]
fn a_spec_with_both_a_carrier_param_and_a_self_receiver_keeps_its_binding() {
    let src = r#"namespace test.wi1076.mixed
  import anthill.prelude.Int64

  sort Holder
    sort C = ?
    sort Element = ?
    operation peek(c: C) -> Int64
    operation joinTwo(a: Holder, b: Holder) -> Int64
  end

  sort Box
    entity box(n: Int64)
  end

  sort BoxHolder
    import anthill.prelude.Int64
    provides Holder[C = Box, Element = Int64]
    operation peek(c: Box) -> Int64 = 2
    operation joinTwo(a: Holder, b: Holder) -> Int64 = 3
  end

  operation probe() -> Int64 = Holder.peek(box(n: 5))
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        carrier_rows(&mut kb, "Holder"),
        vec!["BoxHolder | Holder | Box".to_string()],
        "`peek(c: C)` receives on `C`, so `C` is a real carrier parameter and the \
         explicit `C = Box` binding decides — a self-receiving sibling operation does \
         not repeal it"
    );
    match crate::common::interp_for(src)
        .call("test.wi1076.mixed.probe", &[])
        .expect("the mixed-shape program must still load AND run")
    {
        Value::Int(i) => assert_eq!(i, 2, "the call must reach the witness's `peek`"),
        other => panic!("expected Int, got {other:?}"),
    }
}

/// The capability, not the bookkeeping: a self-representing spec's operation still
/// dispatches on the provider, and answers through the provider's own member.
///
/// Driven because every other assertion in this file reads the fact layer, and a
/// classification that is right on paper while dispatch regressed would satisfy all of
/// them. Passes either way — dispatch on a self-representing spec is value-directed and
/// never consulted the carrier binding, which is precisely why the defect stayed silent.
#[test]
fn a_self_representing_specs_operation_still_dispatches() {
    let src = format!(
        "{}\nnamespace test.wi1076.drive\n  import anthill.prelude.Int64\n  \
         import test.wi1076.both.{{Feed, Box}}\n  \
         import test.wi1076.both.Box.{{box}}\n  \
         operation probe() -> Int64 = Feed.next(box(n: 5))\nend\n",
        BOTH_SHAPES
    );
    match crate::common::interp_for(&src)
        .call("test.wi1076.drive.probe", &[])
        .expect("call probe")
    {
        Value::Int(i) => assert_eq!(i, 1, "`Feed.next` must reach `Box.next`"),
        other => panic!("expected Int, got {other:?}"),
    }
}
