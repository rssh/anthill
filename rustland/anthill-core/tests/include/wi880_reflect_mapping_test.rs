//! WI-880 — the REFLECTION surface is host-mapped, so A RULE CAN READ A TERM.
//!
//! The last and largest of the hardcoded-registration families, and the one whose
//! consequence is not "a host op is awkward at one position": `eval/builtins.rs`
//! registered all 26 `anthill.reflect` operations by hardcoded qualified name, and
//! every load-time and resolver-time reader of "is this operation host-backed" counts
//! an `operation_map` entry and NOT a hardcoded registration (WI-884's split). Since
//! the whole accessor surface sat in that half, no rule could decompose a term at all.
//!
//! THE PRE-FIX MEASUREMENT, driven by BACKING THE CHANGE OUT — restoring the 26
//! `register_if_present` lines and moving the binding block aside, so the operations
//! are registered exactly as they were:
//!
//!   rule read(1)  :- term_as_int(7) = some(7)        0 solutions, total 0: DECIDED FALSE
//!   rule bad(1)   :- not(term_as_int(7) = some(7))   1 DEFINITE          : UNSOUND
//!
//! The second is the shape kernel-language.md §5.2 calls a soundness gap rather than an
//! incompleteness: a rule concluding a POSITIVE fact from a call that never ran, because
//! `is_unreduced_op_call` could not see the registration, so `eq` compared the
//! UN-REDUCED CALL to `some(7)` structurally and committed. After: 1 definite and 0.
//!
//! ONE ROW LOOKED LIKE A WITNESS AND IS NOT, recorded because it was nearly used as the
//! headline: `not(term_as_int(7) = some(8))` answers 1 DEFINITE BOTH WAYS — before,
//! because the call never ran and the structural comparison was false; after, because the
//! call ran and 7 is not 8. Same value, opposite reasons. The discriminating row is the
//! one whose inner comparison is TRUE, which is why `bad` above negates `some(7)`.
//!
//! TWENTY OF THE TWENTY-SIX HAVE NO CARRIER, which is what makes this family unlike
//! `Int64` or `String`, and it was driven rather than assumed. `extract`, `term_field`,
//! `as_term` & co. are declared at NAMESPACE level, so there is no `<carrier>.<op>` for
//! a mapping to key on. A binding block whose target is the NAMESPACE registers them
//! anyway — [`a_namespace_level_mapping_is_registered_and_reduces`] is the row that
//! says so, and it is the one to read first if this file ever goes red.
//!
//! §8.7's "a namespace-level operation is not BACKING" is a different rule and still
//! stands: that one is about discharging a `provides`, and none of these discharge
//! anything. `operation_map` says what REALIZES a declared operation.
//!
//! Reference: `rustland/anthill-stl/anthill/reflect.anthill` (the block and its
//! argument), `docs/proposals/library/008-term-view-and-operations.md` (the consumer
//! this unblocks), WI-884 (the split), WI-20260826-VPEWK (the rule-body host arm).

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// DEFINITE solutions only — `.len()` counts FLOUNDERED ones too, and for a rule body
/// a suspension is exactly the answer that must not read as success. Same counter, and
/// the same reason, as `wi_vpewk_host_op_operand_test`'s.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// Definite + floundered, so a "decided false" (0 total) is distinguishable from a
/// "suspended" (>0 total, 0 definite). `answers` alone cannot tell them apart, and the
/// difference is the whole soundness point.
fn total(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// THE ACCEPTANCE: a rule body reads a term through the reflection accessors.
///
/// Every argument is GROUND and no argument is itself a call — that boundary is
/// deliberate and is VPEWK's remaining limitation, pinned separately in
/// [`a_nested_host_call_reduces`] so this test cannot be read as claiming
/// more than it drives.
///
/// BACK THE MIGRATION OUT (restore the 26 `register_if_present` lines and drop the
/// binding block) and every row here returns to 0, while `bad` returns to 1.
#[test]
fn a_rule_can_read_a_term() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace wi880.refl
  import anthill.prelude.{Int64, String, Bool, Option}
  import anthill.prelude.Option.{some}
  import anthill.reflect.{term_as_int, term_functor_name}

  rule read(1)      :- term_as_int(7) = some(7)
  rule wrong(1)     :- term_as_int(7) = some(8)
  rule functor(1)   :- term_functor_name(some(7)) = some("some")
  rule bad(1)       :- not(term_as_int(7) = some(7))
  rule degenerate(1):- not(term_as_int(7) = some(8))
end
"#,
    );
    assert_eq!(
        answers(&mut kb, "wi880.refl.read(1)"),
        1,
        "an accessor REDUCES in a rule body. Backed out it answers 0 — and `total` is 0 \
         too, i.e. DECIDED FALSE rather than suspended, which is the whole defect"
    );
    assert_eq!(
        answers(&mut kb, "wi880.refl.functor(1)"),
        1,
        "...and so does a second accessor. One row is a coincidence, two is the family"
    );
    assert_eq!(
        answers(&mut kb, "wi880.refl.wrong(1)"),
        0,
        "THE CONTROL that `read` measures a READ and not a blanket success: the same \
         call against the WRONG value answers 0. An accessor returning `some(anything)` \
         would pass `read` and fail here"
    );
    assert_eq!(
        answers(&mut kb, "wi880.refl.bad(1)"),
        0,
        "THE SOUNDNESS ROW, and the reason this family was worth migrating. It answered \
         1 DEFINITE before — a positive conclusion drawn from a term the rule never \
         read. The call runs now, `some(7) = some(7)` holds, so the negation is false"
    );
    assert_eq!(
        answers(&mut kb, "wi880.refl.degenerate(1)"),
        1,
        "NAMED, NOT CREDITED: this answers 1 either way — before because the call never \
         ran and the structural comparison was false, after because 7 is not 8. It is \
         here so a reader does not mistake it for `bad`'s witness"
    );
}

/// THE OTHER BOUNDARY: `=` does not BIND, so an accessor's result cannot be captured
/// into a fresh variable — `term_as_int(7) = ?v` suspends even though the call reduces.
///
/// Pinned because it is the shape a reader will reach for first and it is NOT this
/// ticket's: `WI-20260822-F0HHB` (*what should `=` mean in a rule body*) owns it, and
/// proposal 008 names it as the neighbour. The migration is what makes the DECIDED
/// half work; binding is a separate question about the connective.
///
/// MEASURED across the back-out: this row is 0 definite before and after, which is what
/// distinguishes it from `read` above.
#[test]
fn an_unbound_right_hand_side_still_suspends() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace wi880.refl3
  import anthill.prelude.{Int64, Option}
  import anthill.reflect.{term_as_int}
  rule capture(?v) :- term_as_int(7) = ?v
end
"#,
    );
    assert_eq!(
        answers(&mut kb, "wi880.refl3.capture(?v)"),
        0,
        "`eq` never binds — the accessor reduces, and the result still cannot be captured"
    );
    assert!(
        total(&mut kb, "wi880.refl3.capture(?v)") > 0,
        "...and it SUSPENDS rather than being decided false: the residual is present"
    );
}

/// A NAMESPACE-LEVEL mapping is registered, and the operation reduces.
///
/// Twenty of this family's twenty-six are declared directly in `namespace
/// anthill.reflect` with no owning sort, so `operation_map`'s usual `<carrier>.<op>`
/// key does not exist for them. This is the row that says a namespace target works —
/// asserted on the PREDICATES the readers actually ask, not only on an answer, because
/// an answer would also appear if the registration had quietly stayed hardcoded.
#[test]
fn a_namespace_level_mapping_is_registered_and_reduces() {
    let kb = crate::common::load_kb_with("\nnamespace wi880.rmap\n  sort S\n  end\nend\n");
    let sym = |qn: &str| {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("no symbol {qn}"))
    };
    for qn in [
        "anthill.reflect.extract",
        "anthill.reflect.term_field",
        "anthill.reflect.as_term",
        "anthill.reflect.make_fn",
    ] {
        assert!(
            kb.is_host_mapped_op(sym(qn)),
            "{qn} is host-mapped — it has no carrier, so this is the namespace target working"
        );
        assert!(
            kb.is_interpreter_mapped_op(sym(qn)),
            "{qn} is INTERPRETER-mapped — the rust-only index, which is the one eval and \
             the rule-body gate read"
        );
    }
    // The carrier-owned six take the ordinary shape, from the same file.
    assert!(
        kb.is_host_mapped_op(sym("anthill.reflect.KB.facts_of")),
        "`KB` is a real carrier, so its five are the `Int64`/`String` shape"
    );
    assert!(
        kb.is_host_mapped_op(sym("anthill.reflect.Substitution.lookup")),
        "and so is `Substitution`'s one"
    );
    // THE CONTROL: an operation of this namespace that is NOT mapped stays unmapped, so
    // the assertions above are not passing off a predicate that answers true for
    // anything. `sort_as_term` is declared and implemented NOWHERE — the "worse case"
    // the WI-880 feedback separates from the split this ticket owns.
    assert!(
        !kb.is_host_mapped_op(sym("anthill.reflect.sort_as_term")),
        "the control: a declared-but-unimplemented reflect operation is not host-mapped"
    );
}

/// A NESTED HOST CALL REDUCES, and getting here took three wrong diagnoses — the trail
/// is kept because each one looked right.
///
/// The migration made the FLAT accessors reduce, and that alone was not enough: an
/// un-reduced call IS a term, so a `Term`-typed parameter passed the bridge's ground
/// check and the host function ran ON THE CALL, committing to a wrong value. MEASURED,
/// and only on the complementary polarity — `:- term_as_int(as_term(7)) = none()` went
/// from 0 to **1 DEFINITE** where the true value is `some(7)`. The `= some(7)` row is 0
/// on both sides of that back-out and cannot see it: the un-fired path and the
/// wrong-value path agree there by accident. /code-review probed the other polarity;
/// this file had asserted the blind one and called the result "pre-existing".
///
/// THE FIX is in `reduce_op_value`: a HOST callee's arguments are REDUCED, not merely
/// σ-walked, before the bridge. So the nested call answers correctly rather than either
/// committing or suspending, and VPEWK's documented "argument is never reduced"
/// remainder closes with it (`wi_vpewk_host_op_operand_test`'s `nest` row, 0 -> 1).
///
/// THE THREE WRONG DIAGNOSES, each refuted by the next probe: (1) "`as_term` is
/// broken" — no, two of MY OWN operations split the same way; (2) "it is GENERICITY" —
/// no, `squish(gid(7))` with a generic inner behaves like its non-generic twin; (3) "it
/// is the `Term` TYPE, and it is pre-existing" — the type part was right, the
/// pre-existing part was measured on the blind row.
///
/// WHAT STILL DOES NOT REDUCE is the binding case, and it is a different question —
/// [`an_unbound_right_hand_side_still_suspends`].
///
/// TWO GUARDS, both measured across the fix and both UNMOVED, because widening
/// reduction is exactly where a regression would hide: `:- Set.insert(Set.empty(), 1) =
/// Set.insert(Set.empty(), 1)` still answers 1 AS DATA (the wi616 five — those callees
/// are in no interpreter registry, so the recursion bails on them), and
/// `Colour.isRed(?c) = String.contains("abc", "b")` is unchanged.
#[test]
fn a_nested_host_call_reduces() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace wi880.refl2
  import anthill.prelude.{Int64, Option, Set, Bool, String}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Set.{insert, empty}
  import anthill.reflect.{as_term, term_as_int}
  rule nested(1)   :- term_as_int(as_term(7)) = some(7)
  -- THE ROW THAT SEES THE WRONG VALUE. `nested` alone is blind to it.
  rule wrongval(1) :- term_as_int(as_term(7)) = none()
  -- GUARD: symbolic algebra must stay DATA (the wi616 five).
  rule algebra(1)  :- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 1)
end
"#,
    );
    assert_eq!(
        answers(&mut kb, "wi880.refl2.nested(1)"),
        1,
        "a nested host call reduces — 0 before the argument-reduction fix"
    );
    assert_eq!(
        total(&mut kb, "wi880.refl2.nested(1)"),
        1,
        "...definitely, with no residual: reduced, not suspended"
    );
    assert_eq!(
        answers(&mut kb, "wi880.refl2.wrongval(1)"),
        0,
        "THE ROW THE FIRST DRAFT DID NOT WRITE. It answered 1 DEFINITE once the \
         accessors became host-mapped and before the arguments were reduced — the host \
         function ran on the un-reduced CALL, found no `Const::Int`, and committed to \
         `none()`. A wrong value asserted, not a missing answer"
    );
    assert_eq!(
        answers(&mut kb, "wi880.refl2.algebra(1)"),
        1,
        "THE GUARD: `Set.insert`/`Set.empty` are mapped in no interpreter registry, so \
         the argument recursion bails and leaves them as DATA. Widening reduction \
         without this row is how the wi616 five would break"
    );
}
