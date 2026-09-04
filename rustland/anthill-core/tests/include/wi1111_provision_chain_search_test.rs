//! WI-1111 — INSTANCE SEARCH OVER CHAINS OF PARAMETRIZED `requires` AND `provides`: is a
//! multi-hop answer found, and found with the right bindings?
//!
//! WHAT THE TICKET ASKED. WI-1110 established that a spec's `provides` is a CONVERSION —
//! "hold an `Ord[T]` and you can obtain a `WeakOrd[T]`" — and took it out of the provider
//! search on the argument that [`derive_forwarded_provisions`] RELOCATES its answer to the
//! real carriers. The user's point was that the relation is more general than the one hop
//! that argument reasoned about: a goal may be answerable only through a CHAIN of
//! `requires` and `provides` edges, parametrized at every hop, with the actual provider at
//! the far end. Five questions, each answered here by a fixture that DRIVES a call or
//! reads the candidate list, never by a clean load (WI-948).
//!
//! ═══ THE FIVE ANSWERS, MEASURED ═══
//!
//! **1. A NON-IDENTITY FORWARDING WAS ANSWERED BY A SORT THAT COULD NOT RUN IT.** The
//! third of the ticket's three branches, and the worst one. `sort F { sort A = ?
//! provides Sp[X = A] }` is a renaming, `provides Sp[X = B, Y = A]` a permutation; neither
//! was an identity forwarding, so nothing was derived for a carrier of `F` AND nothing
//! classified the row a conversion. `F` itself became the `impl_sort` — its own parameters
//! being wildcards, the permuting form answered the MIRRORED goal too — the program loaded
//! clean, and it died at eval with `OperationBodyMissing`. FIXED by teaching the
//! derivation to TRANSLATE bindings rather than copy them ([`forwarding_param_map`]);
//! `Car provides F[A = Car]` now derives `Car provides Sp[X = Car]` and the call answers.
//!
//! **2. DEPTH SETTLES; BREADTH DID NOT.** Three identity hops already worked — the
//! bounded fixpoint doubles its reach per round, so depth was never the limit. The limit
//! was sideways: the per-round pending set keyed on the (carrier, target) PAIR alone, so a
//! carrier providing one forwarder at N distinct bindings derived one per round and NINE
//! exhausted `ROUNDS = 8` — a `debug_assert` panic in a debug build, silently missing rows
//! in a release one. FIXED by making that test binding-aware. A RENAMING middle hop was
//! question 1's defect one floor down and is fixed with it.
//!
//! **3. THE BINDINGS COMPOSE, AND A DERIVED SPEC-TO-SPEC ROW WAS WI-1110's DEFECT ONE
//! FLOOR UP.** Composition end to end is correct — a permutation answers the right goal
//! and NOT its mirror. But a two-floor tower makes the derivation assert a row whose
//! carrier is itself a SPEC (`Top provides Low[T = T, E = E]`), and the WI-1110 skip
//! cannot see it: [`self_supplied_entries`] deliberately reads no derived row back into
//! the chain, so [`chain_has_conversion`] answers `false` for exactly these. MEASURED:
//! `Low[T = Car, E = Bool]` offered `["Top", "Car"]`, and the goals no carrier answers
//! offered `["Top"]` ALONE. FIXED by asking a derived row through its ORIGIN edge.
//!
//! **3b. AND A FOURTH SHAPE FELL OUT OF BUILDING THAT FIXTURE** — one name, two questions.
//! [`provision_is_conversion`]'s conjunct 2 read `spec_carrier_param_or_sole(..) == None`
//! as "the target is SELF-REPRESENTING", when that `None` also means "no operation names a
//! carrier AND there is not exactly one parameter to be it" — an OPLESS MULTI-PARAMETER
//! floor, which is a constraint like any other. Conflated, `Top provides Mid[T = T, E = E]`
//! was no conversion and `Top` stayed in the search. Split, and `spec_is_self_representing`
//! is now asked directly.
//!
//! **4. THE `requires` CHAIN COMPOSES ACROSS HOPS AND MEETS THE PROVIDER ROUTE.** Working
//! before this ticket and unchanged by it, in both spellings the user named: a chain of
//! parametrized `requires`, and a chain of `requires` whose last link is a conversion.
//! Pinned here because nothing else drove more than one hop of it.
//!
//! **5. THE KERNEL KEEPS EAGER DERIVATION + A SEARCH-FILLED SLOT + THE CANDIDATE
//! EXCLUSION.** See `q5_*` below for the three measurements the ticket demanded and the
//! argument they support.
//!
//! ═══ AND TWO MORE THE REVIEW FOUND, BOTH DELETING AN ANSWER ═══
//!
//! Both were raised by `/code-review` against this very change, both were REPRODUCED
//! before being believed, and both are the same failure this ticket exists to prevent —
//! the exclusion fires while the relocation does not.
//!
//! **6. A BINDING KEY THAT THREW THE ARGUMENTS AWAY.** `binding_key_named` matched
//! `Term::Fn { functor, .. }` and kept only the base, so `Box[E = Int64]` and
//! `Box[E = Bool]` keyed ALIKE; a hand-written row at one argument read as COVERING the
//! derived row needed at another, so the derivation skipped it. MEASURED: the LOAD failed
//! — `'C' provides 'Top', which requires 'Low', but 'C' does not provide 'Low'`. Fixed by
//! descending into the arguments ([`binding_value_key`]); driven by
//! `a_sibling_row_at_other_arguments_does_not_suppress_the_derived_one_row`.
//!
//! **7. THE ONE SHAPE WI-1110 SANCTIONS PUT THE SPEC BACK IN THE SEARCH.** A sort writing
//! BOTH `requires A[T]` and `provides A[T = T]` gets one slot, and `direct_requires` keeps
//! the `requires` one — supply `Required`. `chain_has_conversion` read the CHAIN, found no
//! `SelfSupplied` entry, and answered `false`, so the conversion went back into the
//! candidate list: WI-1110's headline defect, through the shape its own comment allows.
//! MEASURED — `Low[T = Car]` offered `["High", "Car"]` with the `requires` written,
//! `["Car"]` without. Fixed by asking [`self_supplied_entries`] rather than the layout the
//! dedup collapses; driven by `a_sort_writing_both_clauses_is_still_not_a_candidate`.
//!
//! ═══ WHICH TESTS FAIL WHEN EACH HALF IS BACKED OUT — RUN, not predicted ═══
//!
//! The fix has four separable halves, and the scope each was measured at is stated with
//! it, because they differ. A got a FULL WORKSPACE run (29 binaries, 4886 tests). B, C and
//! D were backed out TOGETHER against the full `wi_tests` binary — 2881 passed, 4 failed,
//! all four here — which is what says they break nothing else in the tree; each was then
//! backed out ALONE to attribute the four.
//!
//!   * **A — `is_param_forwarding` narrowed back to the identity test** (add
//!     `&& ln == kb.local_name_of(*name)`): **8 fail, all of them here** —
//!     `a_renamed_forwarding_reaches_the_carriers_operation`,
//!     `a_renamed_forwarding_offers_the_carrier_not_the_spec`,
//!     `a_renamed_forwarding_that_no_carrier_answers_is_refused_truthfully`,
//!     `a_renamed_conversion_relocates_its_requirement_to_the_carrier`,
//!     `the_same_carrier_paying_the_relocated_requirement_loads_and_runs`,
//!     `a_permuted_forwarding_composes_both_bindings`,
//!     `a_permuted_forwarding_does_not_answer_the_mirrored_goal`,
//!     `a_renaming_middle_floor_still_reaches_the_bottom`. Nothing outside this file
//!     changed, and that is not luck: the corpus contains no renaming or permuting
//!     forwarding at
//!     all — MEASURED by classifying every `SortProvidesInfo` row over stdlib + host
//!     bindings, of which 18 are non-identity and every one is MIXED (a concrete binding
//!     beside a parameter) and a witness (`supplies_ops = true`). That zero is why this
//!     file is the only instrument. (The workspace run predates the two relocation
//!     fixtures, so it established the ZERO-elsewhere half over 4886 tests; the
//!     eight-strong list is from re-running back-out A against the finished file.)
//!   * **B — the binding-aware pending test reverted to the (carrier, target) key**:
//!     `nine_bindings_of_one_forwarder_all_derive` alone, and it does not merely assert —
//!     it PANICS inside the loader, `"WI-1109: forwarded-provision derivation did not
//!     settle in 8 rounds"`.
//!   * **C — the derived-origin skip in `collect_provides_candidates` removed**: THREE —
//!     `a_derived_spec_to_spec_row_is_not_a_candidate`,
//!     `a_two_floor_tower_answers_only_at_the_carriers_bindings`, and
//!     `an_opless_multi_parameter_floor_is_still_a_conversion`.
//!   * **D — conjunct 2 of `provision_is_conversion` restored to the conflated
//!     `spec_carrier_param_or_sole(..)?`**: ONE —
//!     `an_opless_multi_parameter_floor_is_still_a_conversion`.
//!
//! **C AND D ARE A PAIR, WHICH THE MEASUREMENT SHOWED AND THE PREDICTION DID NOT.** The
//! opless fixture fails under EITHER back-out, because the two fixes compose on it: D is
//! what makes `Top provides Mid` a conversion, which is what puts the `Mid` entry in
//! `Top`'s chain, which is what `chain_has_conversion` reads when C asks the derived
//! `Top provides Low` row through its origin. Neither alone suffices and the file says so
//! rather than filing one test under two independent causes.
//!
//! WHICH PASS EITHER WAY, BY DESIGN: `a_forwarder_that_carries_the_operation_still_
//! answers` is the CONTROL on the widening — a renamed forwarding that IS a witness
//! (`supplies_any_operation_of`) must keep answering, and it does under back-out A too.
//! The `a_two_hop_requires_chain…` / `a_requires_chain_ending_in_a_conversion…` pair are
//! question 4's answer and pass on the tree WI-1110 shipped; the three `q5_*` measurements,
//! `a_conditional_forwarding_derives_nothing_even_when_it_renames` and
//! `the_direct_call_mask_is_not_this_tickets` likewise pin what already worked — the last
//! two are BOUNDARY pins, and pass under all four back-outs by construction.
//!
//! AND ONE ASSERTION HERE WAS MEASURED VACUOUS BEFORE IT WAS BELIEVED.
//! `a_renamed_conversion_relocates_its_requirement_to_the_carrier` first asked only that
//! some error mention `provides 'Low'` and `requires 'Base'`; under back-out A it PASSED,
//! because the message about `F` — no longer excused, and itself unable to provide `Base`
//! — contains both. It now names the CARRIER and asserts `F` is excused, and each half
//! fails on its own. A back-out is how that was found; reading the test was not.
//!
//! THE DIRECT-CALL MASK, PINNED SO IT IS NOT MISREAD AS THIS TICKET'S. A spec-op call at a
//! CONCRETE receiver, written in a sort that declares no `requires`, is not checked at
//! load — it loads clean and traps at eval — whatever the candidate list says, and even
//! when the list is EMPTY. That is WI-1110's shape A (`check_one_spec_op_requirement`'s
//! call-site half; WI-876 measured it for `PartialOrd.gt`, WI-879 owns it), and
//! `the_direct_call_mask_is_not_this_tickets` pins it so a later reader does not read a
//! trap here as a candidate defect. Every refusal fixture below therefore goes through a
//! holder that DOES declare the requirement — WI-1110's shape C.

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;
use anthill_core::kb::typing::{
    dict_layout, dispatch_candidate_impl_sorts, direct_requires_chain, resolve, ResolutionResult,
    ResolutionScope, ResolvedRequiresNode, SortGoal,
};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

// ─────────────────────────────────────────────────────────────────────────────
// Q1 — a non-identity forwarding
// ─────────────────────────────────────────────────────────────────────────────

/// `F` renames: `Sp`'s `X` is `F`'s `A`. `Car` is an `F` at `A = Car` and carries `probe`,
/// so `Car` IS an `Sp` at `X = Car` and the call must reach ITS body.
///
/// BEFORE: loaded clean and trapped with `OperationBodyMissing: Sp.probe` — the goal was
/// answered by `F`, which declares no `probe` at all.
#[test]
fn a_renamed_forwarding_reaches_the_carriers_operation() {
    assert_eq!(
        eval_int(RENAME_SRC, "wi1111.rename.D.go"),
        7,
        "`F provides Sp[X = A]` plus `Car provides F[A = Car]` must derive `Car provides \
         Sp[X = Car]`, so the dispatch reaches `Car.probe`",
    );
}

/// And the candidate list says the same thing from the other side: the FORWARDER is gone
/// (it is a conversion now that its answer is relocated) and the CARRIER is the answer.
#[test]
fn a_renamed_forwarding_offers_the_carrier_not_the_spec() {
    let mut kb = crate::common::load_kb_with(RENAME_SRC);
    let cands = candidates(&mut kb, "wi1111.rename.Sp", &[("X", "wi1111.rename.Car")]);
    assert_eq!(
        cands,
        vec!["wi1111.rename.Car".to_string()],
        "`F` declares no operation of `Sp` and nothing has type `F`; the carrier is the \
         only answer",
    );
}

const RENAME_SRC: &str = r#"
namespace wi1111.rename
  import anthill.prelude.{Int64}
  sort Sp
    sort X = ?
    operation probe(a: X) -> Int64
  end
  sort F
    sort A = ?
    provides Sp[X = A]
  end
  enum Car
    entity car(v: Int64)
    provides F[A = Car]
    operation probe(a: Car) -> Int64 = 7
  end
  sort Holder
    sort T = ?
    requires Sp[T]
    operation call(a: T) -> Int64 = Sp.probe(a)
  end
  sort D
    operation go(n: Int64) -> Int64 = Holder.call(Car.car(1))
  end
end
"#;

/// THE REFUSAL, and it must be TRUTHFUL — the ticket's own acceptance. A carrier that
/// provides nothing gets told nothing provides `Sp`, naming the sort and the binding; not
/// a cycle, and not some unrelated missing requirement.
#[test]
fn a_renamed_forwarding_that_no_carrier_answers_is_refused_truthfully() {
    let errs = load_errs(&RENAME_SRC.replace(
        "Holder.call(Car.car(1))",
        "Holder.call(Other.other(1))",
    ).replace(
        "  sort D\n",
        "  enum Other\n    entity other(v: Int64)\n  end\n  sort D\n",
    ));
    assert!(
        errs.iter().any(|e| e.contains("no impl provides wi1111.rename.Sp")),
        "the refusal must say nothing provides `Sp`; got {errs:?}",
    );
    assert!(
        !errs.iter().any(|e| e.contains("construction is cyclic")),
        "and it must not be a cycle — that is the wart WI-1110 removed for the identity \
         case and this ticket must not reintroduce sideways; got {errs:?}",
    );
}

/// THE CONTROL ON THE WIDENING, and the one that decides it is a widening rather than a
/// replacement. A renamed forwarding that CARRIES the target's operation is a parametric
/// WITNESS, not a conversion — `supplies_any_operation_of` is what tells them apart — so
/// it must stay in the search and answer for itself. Passes with the identity test
/// restored too, which is exactly what a control is for.
#[test]
fn a_forwarder_that_carries_the_operation_still_answers() {
    let src = r#"
namespace wi1111.witness
  import anthill.prelude.{Int64}
  sort Sp
    sort X = ?
    operation probe(a: X) -> Int64
  end
  sort F
    sort A = ?
    provides Sp[X = A]
    operation probe(a: A) -> Int64 = 99
  end
  sort D
    operation go(n: Int64) -> Int64 = Sp.probe(3)
  end
end
"#;
    assert_eq!(
        eval_int(src, "wi1111.witness.D.go"),
        99,
        "`F` declares `probe`, so it IS an `Sp` dictionary however abstractly its \
         provision is written, and the widened forwarding predicate must not swallow it",
    );
}

/// THE OBLIGATION RELOCATES THROUGH A RENAME TOO, and this is the half the widening could
/// have silently dropped. `is_conversion_edge_named` excuses a conversion from
/// `check_provider_requires` on WI-1110's argument that the obligation belongs to the
/// eventual CARRIER; widening what counts as a conversion widens what is excused, so the
/// carrier had better still be asked. `Low requires Base[X]` and `F provides Low[X = A]`,
/// so a carrier of `F` that provides no `Base` must be told — and told about `Base`, named
/// as `Low`'s requirement, which is where it is written.
/// THE ASSERTION NAMES THE CARRIER, and that was not a stylistic choice: the first cut
/// asked only that some error contain `provides 'Low'` and `requires 'Base'`, and MEASURED
/// under the back-out it PASSED — because the message about `F` (no longer excused, and
/// itself unable to provide `Base`) contains both substrings. It agreed with the build it
/// was supposed to discriminate against. Both halves below are needed and each fails on
/// its own under the back-out.
#[test]
fn a_renamed_conversion_relocates_its_requirement_to_the_carrier() {
    let errs = load_errs(&relocate_src("wi1111.reloc", "", ""));
    assert!(
        errs.iter().any(|e| {
            e.contains("'wi1111.reloc.Car' provides 'wi1111.reloc.Low'")
                && e.contains("requires 'wi1111.reloc.Base'")
        }),
        "the requirement travels from `Low` to `Car` through the RENAMED conversion, so \
         THE CARRIER — not the spec that forwards — must be the one told about `Base`; \
         got {errs:?}",
    );
    assert!(
        !errs
            .iter()
            .any(|e| e.contains("'wi1111.reloc.F' provides 'wi1111.reloc.Low'")),
        "and `F` itself must be EXCUSED: asking a spec to satisfy the requirement it \
         merely forwards is the wrong question, and answering it is what forced `Ord` to \
         restate `requires Eq` in WI-1109; got {errs:?}",
    );
}

/// THE CONTROL FOR IT — and without it the assertion above is satisfied by a build that
/// refuses every carrier. The same carrier with `Base` paid loads clean and its `probe`
/// runs, reached through `requires Low` at an abstract element.
#[test]
fn the_same_carrier_paying_the_relocated_requirement_loads_and_runs() {
    let src = relocate_src(
        "wi1111.relocok",
        "    provides Base[T = Car]\n    operation baseOp(a: Car) -> Int64 = 3\n",
        "  sort Holder\n    sort T = ?\n    requires Low[T]\n    \
         operation call(a: T) -> Int64 = Low.probe(a)\n  end\n  \
         sort D\n    operation go(n: Int64) -> Int64 = Holder.call(Car.car(1))\n  end\n",
    );
    assert_eq!(
        eval_int(&src, "wi1111.relocok.D.go"),
        7,
        "with `Base` provided the renamed conversion carries `Low` to the carrier and the \
         call answers",
    );
}

fn relocate_src(ns: &str, carrier_extra: &str, tail: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Base
    sort T = ?
    operation baseOp(a: T) -> Int64
  end
  sort Low
    sort X = ?
    requires Base[X]
    operation probe(a: X) -> Int64
  end
  sort F
    sort A = ?
    provides Low[X = A]
  end
  enum Car
    entity car(v: Int64)
    provides F[A = Car]
{carrier_extra}    operation probe(a: Car) -> Int64 = 7
  end
{tail}end
"#
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Q3 — do the bindings compose end to end?
// ─────────────────────────────────────────────────────────────────────────────

/// A PERMUTATION is the sharpest form of the question: `Top provides Low[T = B, E = A]`
/// crosses the two parameters, so a derivation that COPIES rather than translates gets
/// both bindings wrong in a way a single-parameter fixture cannot see. `Car provides
/// Top[A = Bool, B = Car]` must therefore derive `Car provides Low[T = Car, E = Bool]`.
#[test]
fn a_permuted_forwarding_composes_both_bindings() {
    let mut kb = crate::common::load_kb_with(PERMUTE_SRC);
    let cands = candidates(
        &mut kb,
        "wi1111.permute.Low",
        &[("T", "wi1111.permute.Car"), ("E", "anthill.prelude.Bool")],
    );
    assert_eq!(
        cands,
        vec!["wi1111.permute.Car".to_string()],
        "the crossed bindings must arrive uncrossed at the bottom floor",
    );
    assert_eq!(
        eval_int(PERMUTE_SRC, "wi1111.permute.D.go"),
        7,
        "and the call must reach the carrier's own `probe`",
    );
}

/// THE CONTROL FOR IT, and without this the assertion above measures almost nothing: a
/// derivation that bound both parameters to EVERYTHING would satisfy it. The mirrored goal
/// must have no answer at all.
#[test]
fn a_permuted_forwarding_does_not_answer_the_mirrored_goal() {
    let mut kb = crate::common::load_kb_with(PERMUTE_SRC);
    let cands = candidates(
        &mut kb,
        "wi1111.permute.Low",
        &[("T", "anthill.prelude.Bool"), ("E", "wi1111.permute.Car")],
    );
    assert!(
        cands.is_empty(),
        "`Car` is the ELEMENT of `Low`'s `T` and `Bool` of its `E`; the mirror is a goal \
         nothing answers, and before this ticket the forwarder answered it; got {cands:?}",
    );
}

const PERMUTE_SRC: &str = r#"
namespace wi1111.permute
  import anthill.prelude.{Int64, Bool}
  sort Low
    sort T = ?
    sort E = ?
    operation probe(a: T, b: E) -> Int64
  end
  sort Top
    sort A = ?
    sort B = ?
    provides Low[T = B, E = A]
  end
  enum Car
    entity car(v: Int64)
    provides Top[A = Bool, B = Car]
    operation probe(a: Car, b: Bool) -> Int64 = 7
  end
  sort D
    operation go(n: Int64) -> Int64 = Low.probe(Car.car(1), true)
  end
end
"#;

/// THE TWO MACHINERIES THE TICKET CONTRASTED, and the line between them is where the
/// derivation STOPS. A conditional provision composes CONDITIONS (`Pair provides
/// Ord[Pair] :- Ord[A], Ord[B]`); a forwarding composes SUBSTITUTIONS.
/// `forwarded_rows_to_derive` derives nothing through a conditional row — deliberately,
/// because the `:- goals` tail rides in separate `ProvidesConditionInfo` facts and copying
/// the head alone would claim the lower floor UNCONDITIONALLY, which is the over-claim
/// `ProvisionConditionsTooWeak` exists to refuse. WI-1111's widening does not move that
/// line: a conditional row that RENAMES is a forwarding by shape and still derives
/// nothing.
///
/// PINNED RATHER THAN FIXED, with the reason and the increment already stated at
/// [`derive_forwarded_provisions`]: deriving a conditional row means asserting a RULE with
/// the source's body translated through the map, not a fact, and that is a different pass.
/// What this fixture buys is that the boundary is where the comment says it is, so an
/// increment that moves it flips a test instead of sliding past one.
#[test]
fn a_conditional_forwarding_derives_nothing_even_when_it_renames() {
    let src = r#"
namespace wi1111.condfwd
  import anthill.prelude.{Int64}
  sort Guard
    sort G = ?
    operation guardOp(a: G) -> Int64
  end
  sort Low
    sort X = ?
    operation probe(a: X) -> Int64
  end
  sort F
    sort A = ?
    provides Low[X = A] :- Guard[A]
  end
  enum Car
    entity car(v: Int64)
    provides F[A = Car]
    provides Guard[G = Car]
    operation probe(a: Car) -> Int64 = 7
    operation guardOp(a: Car) -> Int64 = 1
  end
end
"#;
    let kb = crate::common::load_kb_with(src);
    let derived: Vec<_> = crate::common::sort_provisions(&kb)
        .into_iter()
        .filter(|(c, s)| c == "wi1111.condfwd.Car" && s == "wi1111.condfwd.Low")
        .collect();
    assert!(
        derived.is_empty(),
        "a conditional forwarding derives nothing — the tail is not on the row, so the \
         derived one would claim `Low` unconditionally; got {derived:?}",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Q2 — depth, and the derived spec-to-spec row it produces
// ─────────────────────────────────────────────────────────────────────────────

/// THREE FLOORS, all identity. This already worked and is pinned because nothing else
/// drove more than one hop: the fixpoint doubles its reach per round, so `Car provides
/// A0` reaches `C0` in two.
#[test]
fn three_identity_floors_reach_the_bottom() {
    assert_eq!(
        eval_int(TOWER3_SRC, "wi1111.tower3.D.go"),
        7,
        "`Car provides A0` must reach `C0.probe` through `A0 provides B0 provides C0`",
    );
}

/// AND THE DEFECT THE DEPTH PRODUCES. Deriving through a tower asserts `A0 provides
/// C0[T = T]` — a row whose CARRIER is a spec and whose shape is a conversion's. The
/// WI-1110 skip cannot see it, because `self_supplied_entries` deliberately reads no
/// derived row back into the chain; MEASURED, `A0` was offered beside the real carrier.
#[test]
fn a_derived_spec_to_spec_row_is_not_a_candidate() {
    let mut kb = crate::common::load_kb_with(TOWER3_SRC);
    let cands = candidates(&mut kb, "wi1111.tower3.C0", &[("T", "wi1111.tower3.Car")]);
    assert_eq!(
        cands,
        vec!["wi1111.tower3.Car".to_string()],
        "`A0` holds a `C0` dictionary inside its `B0` slot; it is not one",
    );
}

/// THE CONTROL FOR IT — the goal at a sort that provides nothing must have NO answer.
/// This is the half that makes the skip a fix rather than a cosmetic reordering: with the
/// derived row offered, the ONLY candidate for this goal was a spec declaring no
/// operation, so a dispatch that must be refused resolved instead.
#[test]
fn a_two_floor_tower_answers_only_at_the_carriers_bindings() {
    let mut kb = crate::common::load_kb_with(TOWER3_SRC);
    let cands = candidates(&mut kb, "wi1111.tower3.C0", &[("T", "anthill.prelude.Bool")]);
    assert!(
        cands.is_empty(),
        "nothing provides `C0` at `Bool`; got {cands:?}",
    );
}

const TOWER3_SRC: &str = r#"
namespace wi1111.tower3
  import anthill.prelude.{Int64, Bool}
  sort C0
    sort T = ?
    operation probe(a: T) -> Int64
  end
  sort B0
    sort T = ?
    provides C0[T = T]
  end
  sort A0
    sort T = ?
    provides B0[T = T]
  end
  enum Car
    entity car(v: Int64)
    provides A0[T = Car]
    operation probe(a: Car) -> Int64 = 7
  end
  sort Holder
    sort T = ?
    requires C0[T]
    operation call(a: T) -> Int64 = C0.probe(a)
  end
  sort D
    operation go(n: Int64) -> Int64 = Holder.call(Car.car(1))
  end
end
"#;

/// A RENAMING MIDDLE FLOOR — question 2's "where does the answer stop being found". It
/// stopped at the rename, silently: the tower loaded clean and trapped at eval. It is
/// question 1's defect one floor down and is fixed with it.
#[test]
fn a_renaming_middle_floor_still_reaches_the_bottom() {
    let src = r#"
namespace wi1111.midrename
  import anthill.prelude.{Int64}
  sort C0
    sort T = ?
    operation probe(a: T) -> Int64
  end
  sort B0
    sort U = ?
    provides C0[T = U]
  end
  sort A0
    sort U = ?
    provides B0[U = U]
  end
  enum Car
    entity car(v: Int64)
    provides A0[U = Car]
    operation probe(a: Car) -> Int64 = 7
  end
  sort Holder
    sort T = ?
    requires C0[T]
    operation call(a: T) -> Int64 = C0.probe(a)
  end
  sort D
    operation go(n: Int64) -> Int64 = Holder.call(Car.car(1))
  end
end
"#;
    assert_eq!(
        eval_int(src, "wi1111.midrename.D.go"),
        7,
        "the middle floor renames `T` to `U`; the answer must still travel",
    );
}

/// AN OPLESS MULTI-PARAMETER FLOOR. `Mid` declares no operation and has two type
/// parameters, so `spec_carrier_param_or_sole` can name no carrier for it — and WI-1110's
/// conjunct 2 read that `None` as "not a conversion", which is the OTHER thing that
/// `None` means (a self-representing spec, which this is not). MEASURED: `Top` answered
/// `Low[T = Car, E = Int64]` and the mirrored goal with `["Top"]` alone.
#[test]
fn an_opless_multi_parameter_floor_is_still_a_conversion() {
    let mut kb = crate::common::load_kb_with(OPLESS_SRC);
    for (label, t, e) in [
        ("a binding the carrier does not have", "wi1111.opless.Car", "anthill.prelude.Int64"),
        ("a sort that provides nothing", "wi1111.opless.Other", "anthill.prelude.Bool"),
    ] {
        let cands = candidates(&mut kb, "wi1111.opless.Low", &[("T", t), ("E", e)]);
        assert!(
            cands.is_empty(),
            "{label}: a spec with no members must not be the answer; got {cands:?}",
        );
    }
    let cands = candidates(
        &mut kb,
        "wi1111.opless.Low",
        &[("T", "wi1111.opless.Car"), ("E", "anthill.prelude.Bool")],
    );
    assert_eq!(
        cands,
        vec!["wi1111.opless.Car".to_string()],
        "and the real carrier must still answer, or the split has emptied the search \
         space instead of cleaning it",
    );
}

const OPLESS_SRC: &str = r#"
namespace wi1111.opless
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Option.{some}
  sort Low
    sort T = ?
    sort E = ?
    operation probe(a: T, b: E) -> Int64
  end
  sort Mid
    sort T = ?
    sort E = ?
    provides Low[T = T, E = E]
  end
  sort Top
    sort T = ?
    sort E = ?
    provides Mid[T = T, E = E]
  end
  enum Car
    entity car(v: Int64)
    provides Top[T = Car, E = Bool]
    operation probe(a: Car, b: Bool) -> Int64 = 7
  end
  enum Other
    entity other(v: Int64)
  end
end
"#;

/// BREADTH, not depth — the limit the fixpoint actually had. One carrier providing one
/// forwarder at NINE distinct bindings derived one row per round, so `ROUNDS = 8` ran out:
/// this fixture PANICS INSIDE THE LOADER with "did not settle in 8 rounds" when the
/// pending test is keyed on the (carrier, target) pair again — and in a release build,
/// where the `debug_assert` is compiled out, the ninth row is simply missing and every
/// reader answers as though the provision does not exist.
#[test]
fn nine_bindings_of_one_forwarder_all_derive() {
    const N: usize = 9;
    let mut src = String::from(
        "namespace wi1111.breadth\n  import anthill.prelude.{Int64}\n  \
         sort Low\n    sort T = ?\n    operation probe(a: T) -> Int64\n  end\n  \
         sort High\n    sort T = ?\n    provides Low[T = T]\n  end\n",
    );
    for i in 0..N {
        src.push_str(&format!("  enum C{i}\n    entity c{i}(v: Int64)\n  end\n"));
    }
    src.push_str("  sort Multi\n");
    for i in 0..N {
        src.push_str(&format!("    provides High[T = C{i}]\n"));
    }
    src.push_str("  end\nend\n");

    let kb = crate::common::load_kb_with(&src);
    let derived = crate::common::sort_provisions(&kb)
        .into_iter()
        .filter(|(c, s)| c == "wi1111.breadth.Multi" && s == "wi1111.breadth.Low")
        .count();
    assert_eq!(
        derived, N,
        "every binding of the forwarder must derive its own `Low` row, in ONE round",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Q4 — a chain of parametrized `requires`, and one whose last link provides
// ─────────────────────────────────────────────────────────────────────────────

/// THE USER'S OWN PHRASING, first half: does the caller-chain route compose across more
/// than one hop of parametrized `requires`, and does it meet the provider route at the
/// end? `High requires Mid[T]`, `Mid requires Low[T]`, and the body reaches `Low.probe`
/// two levels down. Working before this ticket; pinned because nothing drove two hops.
///
/// THE ANSWER DISCRIMINATES, which is the whole point of asserting a VALUE here: two
/// carriers provide `Low` with different bodies, and only the one the call site names may
/// come back.
#[test]
fn a_two_hop_requires_chain_reaches_the_provider() {
    assert_eq!(
        eval_int(REQ_CHAIN_SRC, "wi1111.reqchain.D.first"),
        7,
        "`Low[T = Car]` must reach `Car.probe`",
    );
    assert_eq!(
        eval_int(REQ_CHAIN_SRC, "wi1111.reqchain.D.second"),
        11,
        "and `Low[T = Dar]` must reach `Dar`'s — the chain carries the BINDING, not just \
         some dictionary",
    );
}

const REQ_CHAIN_SRC: &str = r#"
namespace wi1111.reqchain
  import anthill.prelude.{Int64}
  sort Low
    sort T = ?
    operation probe(a: T) -> Int64
  end
  sort Mid
    sort T = ?
    requires Low[T]
  end
  sort High
    sort T = ?
    requires Mid[T]
    operation go(a: T) -> Int64 = Low.probe(a)
  end
  enum Car
    entity car(v: Int64)
    provides Low[T = Car]
    operation probe(a: Car) -> Int64 = 7
  end
  enum Dar
    entity dar(v: Int64)
    provides Low[T = Dar]
    operation probe(a: Dar) -> Int64 = 11
  end
  sort MidCar
    provides Mid[T = Car]
  end
  sort MidDar
    provides Mid[T = Dar]
  end
  sort D
    operation first(n: Int64) -> Int64 = High.go(Car.car(1))
    operation second(n: Int64) -> Int64 = High.go(Dar.dar(1))
  end
end
"#;

/// THE USER'S OWN PHRASING, second half: a chain of `requires` whose LAST LINK PROVIDES.
/// `User requires Top[T]`, `Top requires MidC[T]`, and `MidC provides Low[T = T]` is a
/// conversion — a `SelfSupplied` chain entry, not a `requires` one. The body's `Low.probe`
/// has to travel two `requires` hops and then a conversion, and meet a carrier at the end.
#[test]
fn a_requires_chain_ending_in_a_conversion_reaches_the_provider() {
    let src = r#"
namespace wi1111.reqconv
  import anthill.prelude.{Int64}
  import anthill.prelude.Option.{some}
  sort Low
    sort T = ?
    operation probe(a: T) -> Int64
  end
  sort MidC
    sort T = ?
    provides Low[T = T]
  end
  sort Top
    sort T = ?
    requires MidC[T]
  end
  sort User
    sort T = ?
    requires Top[T]
    operation go(a: T) -> Int64 = Low.probe(a)
  end
  enum Car
    entity car(v: Int64)
    provides MidC[T = Car]
    operation probe(a: Car) -> Int64 = 7
  end
  sort TopCar
    provides Top[T = Car]
  end
  sort D
    operation run(n: Int64) -> Int64 = User.go(Car.car(1))
  end
end
"#;
    assert_eq!(
        eval_int(src, "wi1111.reqconv.D.run"),
        7,
        "`requires Top` -> `requires MidC` -> `provides Low` must reach `Car.probe`",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Q5 — eager derivation, lazy edge-following, or a projection-filled slot?
// ─────────────────────────────────────────────────────────────────────────────
//
// THE ANSWER: THE KERNEL KEEPS WHAT SHIPS — eager derivation, a slot filled by SEARCH,
// and the candidate exclusion. Recorded at `SupplySource` and at `is_conversion_edge_at`
// so the next reader finds the argument instead of re-deriving it. The three measurements
// the ticket demanded are the three tests below, and the argument they support is:
//
//  1. THE EXCLUSION ANSWERS A QUESTION NO SLOT-FILLING CHANGE CAN. The user's case was
//     that a projected slot starts no search, so the edge is traversed once, so the cycle
//     and perhaps the exclusion dissolve. The cycle does — but the exclusion does not,
//     and WI-1110 already measured why: with the skip removed, `WeakOrd[T = <rigid>]`
//     offered `[Ord]` ALONE. A conversion is in the provider relation whatever fills the
//     slot, so at an ABSTRACT element it is still the only candidate and the vacuous
//     dispatch still resolves. `wi1110`'s `a_weakord_dispatch_with_no_requires_is_refused`
//     is the driver, and no change to how a slot is filled touches it. WI-1111 then
//     measured that the exclusion had FOUR reachable holes (rename, permutation, derived
//     spec-to-spec row, opless multi-parameter floor) — so it needed completing, which is
//     the opposite of needing removing.
//  2. THE EAGER ROWS HAVE A SECOND READER A LAZY EDGE CANNOT SERVE (`q5_the_derived_row_
//     is_what_makes_the_operation_dispatch`).
//  3. THE SLOT IS FILLED BY THOSE SAME ROWS (`q5_the_self_supplied_slot_carries_the_
//     carriers_own_dictionary`), so projection would add a third path without removing
//     either of the first two.
//  4. AND THE LAYOUT COUNT IS 1, WITH THE VALUE FLOWING THROUGH IT (`q5_the_conversion_
//     slot_is_one_slot_and_the_value_flows_through_it`). Making it 0 means teaching
//     `DictLayout::slots_for`, `synth_req_names` and eval's frame push to project — three
//     sites, to remove a slot that measurably works.

/// MEASUREMENT (3) AND THE ONE THAT DECIDES IT. `Rev` writes `provides Ord[T = Rev]` and
/// NOTHING about `WeakOrd`; `Holder requires Ord[T]` and its body calls `WeakOrd.compare`.
/// The value that comes back is `Rev`'s own REVERSED order, so this asserts the whole
/// path: the conversion put a `WeakOrd` slot in `Ord`'s chain, the slot was filled by
/// SEARCH, the search found the row `derive_forwarded_provisions` materialized for `Rev`,
/// and the dictionary that arrived at eval was `Rev`'s and not `Int64`'s.
///
/// THE REVERSAL IS THE CONTROL. `9 vs 4` under any natural order is positive; `Rev`'s
/// answers negative. A build that lost the dictionary and fell back to the element's own
/// order would return a positive number and this test would catch it — an assertion on
/// "it ran" would not.
#[test]
fn q5_the_self_supplied_slot_carries_the_carriers_own_dictionary() {
    assert!(
        eval_int(Q5_SRC, "wi1111.q5.D.go") < 0,
        "`Rev` orders backwards, so 9 vs 4 must come back NEGATIVE — a positive answer \
         means some other `WeakOrd` dictionary filled the slot",
    );
}

/// MEASUREMENT (2). The same carrier, asked for the DISPATCH rather than the slot:
/// `WeakOrd.compare` on a `Rev` value resolves only because `build_sort_ops_table`
/// inherited `WeakOrd`'s surface onto `Rev` when it gained its derived row (load.rs, at
/// the `build_sort_ops_table (derived-provision delta)` mark). A LAZY spec-to-spec edge
/// populates no table: it would answer the resolver and leave `sort_ops_lookup(Rev,
/// compare)` `None`, which is `NoMatch` at every call site. That is why dropping the
/// eager derivation is not free even if the search stops needing it.
#[test]
fn q5_the_derived_row_is_what_makes_the_operation_dispatch() {
    assert!(
        eval_int(Q5_SRC, "wi1111.q5.D.direct") < 0,
        "a direct `WeakOrd.compare` on a carrier that wrote only `provides Ord` must \
         dispatch to ITS `compare`",
    );
}

/// MEASUREMENT (1) — the layout count, which has moved twice already (wi857's
/// `the_layout_counts_what_resolve_bundles`: 2 -> 3 -> 1) and which a projection-filled
/// slot would move a third time, to 0. Read here at the CARRIER rather than at `Int64` so
/// it is this ticket's fixture and not a second copy of wi857's, and cross-checked against
/// what `resolve` actually bundles — the two diverging is the failure WI-857 was.
#[test]
fn q5_the_conversion_slot_is_one_slot_and_the_value_flows_through_it() {
    let mut kb = crate::common::load_kb_with(Q5_SRC);
    let ord = kb.try_resolve_symbol("anthill.prelude.Ord").expect("Ord");
    let chain = direct_requires_chain(&mut kb, ord);
    assert_eq!(
        chain.len(),
        1,
        "`Ord`'s whole content is the conversion `provides WeakOrd[T = T]`, which is ONE \
         chain slot: {:?}",
        chain
            .iter()
            .map(|e| kb.qualified_name_of(e.required_sort).to_string())
            .collect::<Vec<_>>(),
    );
    let goal = goal_at(&mut kb, "anthill.prelude.Ord", "wi1111.q5.Rev");
    let scope = ResolutionScope {
        available_requires: &[],
        sigma: None,
        selected: &[],
    };
    let tree = match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::Resolved(t) => t,
        other => panic!("`Ord[T = Rev]` must resolve; got {other:?}"),
    };
    let provider = tree.impl_sort().expect("a resolved provision pins an impl");
    let layout = dict_layout(&mut kb, goal.spec_sort, provider);
    let bundled = match &tree {
        ResolvedRequiresNode::Conditional { sub_resolutions, .. } => sub_resolutions.len(),
        ResolvedRequiresNode::Leaf { .. } => 0,
        other => panic!("expected Leaf/Conditional; got {other:?}"),
    };
    assert_eq!(layout.arity(), 1, "one conversion, one slot: {}", layout.describe(&kb));
    assert_eq!(
        bundled,
        layout.arity(),
        "and the producer must bundle exactly what the layout counts — a projected slot \
         would have to make BOTH of these 0 and grow a projection path instead",
    );
}

const Q5_SRC: &str = r#"
namespace wi1111.q5
  import anthill.prelude.{Ord, WeakOrd, PartialOrd, PartialEq, Eq, Int64, Bool}
  enum Rev
    entity rev(v: Int64)
    provides Eq[T = Rev]
    provides PartialOrd[T = Rev]
    provides Ord[T = Rev]
    operation eq(a: Rev, b: Rev) -> Bool =
      match a
        case rev(x) ->
          match b
            case rev(y) -> PartialEq.eq(x, y)
    operation compare(a: Rev, b: Rev) -> Int64 =
      match a
        case rev(x) ->
          match b
            case rev(y) -> WeakOrd.compare(y, x)
  end
  sort Holder
    sort T = ?
    requires Ord[T]
    operation cmp(a: T, b: T) -> Int64 = WeakOrd.compare(a, b)
  end
  sort D
    operation go(n: Int64) -> Int64 = Holder.cmp(Rev.rev(9), Rev.rev(4))
    operation direct(n: Int64) -> Int64 = WeakOrd.compare(Rev.rev(9), Rev.rev(4))
  end
end
"#;

// ─────────────────────────────────────────────────────────────────────────────
// the mask, pinned so it is not read as this ticket's
// ─────────────────────────────────────────────────────────────────────────────

/// A spec-op call at a CONCRETE receiver, in a sort that declares no `requires`, is not
/// checked at load — it loads clean and traps at eval — EVEN WHEN NOTHING PROVIDES THE
/// SPEC AT ALL. That is not a candidate defect and no change in this ticket touches it:
/// it is the call-site half of a spec-op requirement, unchecked while the op is still
/// reachable that way (WI-1110's shape A; WI-876 measured the same for `PartialOrd.gt`;
/// WI-879 owns it). PINNED rather than described, so that when WI-879 lands this test
/// fails and says where to look.
#[test]
fn the_direct_call_mask_is_not_this_tickets() {
    let src = r#"
namespace wi1111.mask
  import anthill.prelude.{Int64}
  sort Sp
    sort X = ?
    operation probe(a: X) -> Int64
  end
  enum Other
    entity other(v: Int64)
  end
  sort D
    operation go(n: Int64) -> Int64 = Sp.probe(Other.other(1))
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let cands = candidates(&mut kb, "wi1111.mask.Sp", &[("X", "wi1111.mask.Other")]);
    assert!(
        cands.is_empty(),
        "the search is truthful: nothing provides `Sp` at `Other`; got {cands:?}",
    );
    let mut interp = crate::common::interp_for(src);
    let r = interp.call("wi1111.mask.D.go", &[Value::Int(0)]);
    assert!(
        r.is_err(),
        "and the LOAD accepted it anyway, so the trap is at eval — when WI-879 closes the \
         call-site half this becomes a load error and this test must be rewritten to \
         assert the refusal; got {r:?}",
    );
}

// ── helpers ──────────────────────────────────────────────────────────────────

/// The impl sorts offered for `<spec>[<bindings>]`, by qualified name. WI-1110's
/// `dispatch_candidate_impl_sorts` — a diagnostic reader, carrying no policy of its own —
/// generalized from one binding to several, because half this ticket's shapes need two.
fn candidates(kb: &mut KnowledgeBase, spec_qn: &str, bindings: &[(&str, &str)]) -> Vec<String> {
    let spec = kb
        .try_resolve_symbol(spec_qn)
        .unwrap_or_else(|| panic!("{spec_qn} registered"));
    let mut bs: SmallVec<[(anthill_core::intern::Symbol, anthill_core::kb::term::TermId); 2]> =
        SmallVec::new();
    for (key, value) in bindings {
        let vs = kb
            .try_resolve_symbol(value)
            .unwrap_or_else(|| panic!("{value} registered"));
        let vt = kb.alloc(Term::Ref(vs));
        let ks = kb.intern(key);
        bs.push((ks, vt));
    }
    let goal = SortGoal {
        spec_sort: spec,
        bindings: bs,
        carrier: None,
    };
    dispatch_candidate_impl_sorts(kb, &goal)
        .into_iter()
        .map(|s| kb.qualified_name_of(s).to_string())
        .collect()
}

fn goal_at(kb: &mut KnowledgeBase, spec_qn: &str, carrier_qn: &str) -> SortGoal {
    let spec = kb.try_resolve_symbol(spec_qn).unwrap_or_else(|| panic!("{spec_qn}"));
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

/// A FRESH interpreter per call — a reused one poisons later calls (WI-1057's measured
/// footgun), and `interp_for` panics on a dirty load, so a value assertion is also a
/// clean-load assertion.
fn eval_int(src: &str, entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Int(v)) => v,
        other => panic!("{entry} must answer an Int64; got {other:?}"),
    }
}

fn load_errs(src: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => panic!("expected load errors, got a clean load"),
        Err(errs) => errs,
    }
}

// ── review findings, verified before believed ────────────────────────────────

/// REVIEW FINDING 2, verified. A sort writing BOTH `requires A[T]` and the conversion
/// `provides A[T = T]` gets ONE slot (`a_sort_writing_both_clauses_gets_one_slot`), and
/// `direct_requires` keeps the `requires` one — whose `supply` is `Required`. So
/// `chain_has_conversion` finds no `SelfSupplied` entry, `is_conversion_edge_at` answers
/// `false`, and the spec is offered as a provider candidate again: WI-1110's headline
/// defect, reachable through the one shape its own comment sanctions.
#[test]
fn a_sort_writing_both_clauses_is_still_not_a_candidate() {
    let src = r#"
namespace wi1111.bothcand
  import anthill.prelude.{Int64}
  sort Low
    sort T = ?
    operation probe(a: T) -> Int64
  end
  sort High
    sort T = ?
    requires Low[T]
    provides Low[T = T]
  end
  enum Car
    entity car(v: Int64)
    provides Low[T = Car]
    operation probe(a: Car) -> Int64 = 7
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let cands = candidates(&mut kb, "wi1111.bothcand.Low", &[("T", "wi1111.bothcand.Car")]);
    assert_eq!(
        cands,
        vec!["wi1111.bothcand.Car".to_string()],
        "`High` forwards `Low`; it is not a `Low`. Writing `requires` beside the \
         conversion must not put it back in the search space",
    );
}

/// REVIEW FINDING 1, verified. `binding_key_named` keys a binding VALUE by its base
/// functor and throws the arguments away, so `Box[E = Int64]` and `Box[E = Bool]` key
/// alike. A hand-written row at one argument then reads as COVERING the derived row
/// needed at another, the derivation skips it — and `collect_provides_candidates` has
/// already excluded the conversion. The answer is DELETED, not relocated, which is the
/// one invariant this ticket rests on.
const ARGKEY_SRC: &str = r#"
namespace wi1111.argkey
  import anthill.prelude.{Int64, Bool}
  sort Low
    sort T = ?
    operation lo(a: T) -> Int64
  end
  sort Top
    sort T = ?
    provides Low[T = T]
  end
  enum Box
    sort E = ?
    entity box(v: E)
  end
  sort C
    provides Top[T = Box[E = Int64]]
    provides Low[T = Box[E = Bool]]
    operation lo(a: Box) -> Int64 = 3
  end
end
"#;

/// THE ASSERTION IS THE ROW'S EXISTENCE, not a candidate list, and the difference is the
/// point: both rows are at PARAMETERIZED arguments (`Box[E = Int64]` / `Box[E = Bool]`),
/// which a goal spelled at the bare base does not match either way. What the defect did
/// was stop the derived row being asserted at all — and, the conversion having been
/// excluded from the search already, `check_provider_requires` then refused the LOAD.
/// So a clean load carrying `C provides Low` is exactly the relocation invariant holding.
#[test]
fn a_sibling_row_at_other_arguments_does_not_suppress_the_derived_one_row() {
    let kb = crate::common::load_kb_with(ARGKEY_SRC);
    let rows: Vec<_> = crate::common::sort_provisions(&kb)
        .into_iter()
        .filter(|(c, s)| c == "wi1111.argkey.C" && s == "wi1111.argkey.Low")
        .collect();
    assert_eq!(
        rows.len(),
        2,
        "`C` must carry BOTH the written `Low[T = Box[E = Bool]]` and the derived \
         `Low[T = Box[E = Int64]]`; a base-only binding key made the first read as \
         covering the second, so only one exists and the load itself was refused. \
         got {rows:?}",
    );
}
