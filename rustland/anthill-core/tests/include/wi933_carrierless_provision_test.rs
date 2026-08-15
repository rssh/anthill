//! WI-933 — a namespace-level BRACKET-LESS `fact <Spec>` names no carrier, and is
//! refused rather than silently dropped.
//!
//! THE DEFECT. `fact Spec` written beside an entity read as a provision — that is
//! what `docs/rust-forward-mapping.md` §2.13 promised it meant, twice, as a feature
//! ("`fact QueryableStore` in the namespace where `SqlStore` is defined means
//! 'SqlStore is-a QueryableStore'") — and produced nothing at all. MEASURED while
//! delivering WI-931, by dumping every `anthill.reflect.SortProvidesInfo` fact of a
//! full stdlib + host-bindings load: two such lines shipped in the tree and NEITHER
//! produced a provision, while their BRACKETED neighbours on the very next line did.
//! So the load was clean, the doc was followed, and nothing was declared.
//!
//! WHY REFUSED AND NOT IMPLEMENTED. The doc's reading needs the carrier derived from
//! the enclosing namespace's entity declaration — a guess by proximity. It was
//! rejected on a measured case, not on taste: `anthill.persistence.filesystem`
//! declares TWO entities (`FileStore` and `IndexedFileStore`), so proximity would put
//! declaration ORDER in charge of which type a claim is about — exactly the
//! discriminator WI-978 removed from this same function.
//!
//! THE THREE POSITIONS, counted correctly — the count is stated because getting it
//! wrong is how the doc this ticket corrects went wrong. §6.3 enumerates FOUR
//! positions that carry a provision's obligation, but a `fact` is writable in only
//! three of them: the fourth, a `namespace X` block at a sort's address, is a
//! SECONDARY ENTRY, where `fact` is refused outright whatever its brackets and the
//! spelling is `provides Spec[…]` (measured; `secondary_entry_message`). Of the three,
//! only the sort-body one takes its carrier from the enclosing type. The other two —
//! beside the carrier in its namespace, and at a file's top level — must write it in
//! brackets, and are what this file is about. §2.13 was corrected in the same commit.
//!
//! WHAT EACH TEST HOLDS, AND WHICH FAIL WHEN THE CHANGE IS BACKED OUT.
//!
//! | test | on back-out |
//! |---|---|
//! | `a_namespace_level_bracketless_fact_is_refused` | FAILS — loads clean, no error |
//! | `the_refusal_names_the_spec_and_its_line` | FAILS — no error to render |
//! | `the_same_fact_at_a_files_top_level_is_refused_too` | FAILS — loads clean, no error |
//! | `a_secondary_entry_is_not_one_of_the_positions` | passes either way (BY DESIGN — pins the count above, which no other test measures) |
//! | `the_bracketed_repair_the_message_names_works` | passes either way (BY DESIGN — the repair route is untouched; it is here so the message cannot name a spelling that does not work) |
//! | `the_sort_body_repair_the_message_names_works` | passes either way (same) |
//! | `neither_repair_is_the_refused_position` | FAILS — its refusal leg is half of the pair it asserts together |
//! | `a_data_construction_over_a_parametric_sort_is_not_a_provision_claim` | passes either way (BY DESIGN — both legs are shapes the refusal must NOT reach, and each killed a discriminator that was written and reverted) |
//! | `an_op_only_bracketed_fact_is_refused_without_being_told_to_add_brackets` | passes either way for WI-933 (BY DESIGN — it is WI-1106's control, and fails when THAT is backed out) |
//!
//! The two "passes either way" repair tests are not filler: the acceptance is that
//! the diagnostic says WHAT TO WRITE INSTEAD, and a message naming a spelling nobody
//! drove is the failure mode this repo has hit before. They DRIVE each repair through
//! subtyping — `operation widen(c: Carrier) -> Spec = c` conforms only if the
//! provision reached `sort_provides` — and each carries its own control showing the
//! same program without the fact is refused, so neither can pass vacuously.

use crate::common::try_load_kb_with;

/// Load errors for `src` (stdlib + host bindings + `src`), empty when clean.
fn errors(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// The refused spelling: `fact Wi933Spec` at NAMESPACE level, beside a carrier it
/// does not name. `w933_describe` carries a default body so the carrier owes no
/// backing — otherwise a green run could be `check_provider_operations` complaining
/// about a provision that did get emitted, which is the opposite of the subject.
const BRACKETLESS: &str = r#"
namespace test.wi933.bracketless
  import anthill.prelude.{Int64}

  sort Wi933Spec
    operation w933_describe(s: Wi933Spec) -> Int64 = 0
  end

  sort Wi933Carrier
    entity w933_c
  end

  fact Wi933Spec
end
"#;

#[test]
fn a_namespace_level_bracketless_fact_is_refused() {
    let errs = errors(BRACKETLESS);
    assert!(
        errs.iter().any(|e| e.contains("names no carrier")),
        "a namespace-level bracket-less `fact Wi933Spec` declares nothing the loader \
         can file — it must be refused, not dropped; got {errs:?}"
    );
}

/// The acceptance's wording clause: the diagnostic NAMES THE SPEC and carries a
/// location. Both halves are asserted because either alone is satisfiable by an
/// unusable message — a located error about no particular spec, or a named spec with
/// nothing to point at in a file of a hundred facts.
#[test]
fn the_refusal_names_the_spec_and_its_line() {
    let errs = errors(BRACKETLESS);
    let msg = errs
        .iter()
        .find(|e| e.contains("names no carrier"))
        .unwrap_or_else(|| panic!("expected the carrier refusal; got {errs:?}"));
    assert!(
        msg.contains("Wi933Spec"),
        "the refusal must name the spec claimed: {msg}"
    );
    assert!(
        msg.contains("test.wi933.bracketless"),
        "and the scope it was written in, since that is what has no type to be about: \
         {msg}"
    );
    // `fact Wi933Spec` is on line 13 of BRACKETLESS. `Located`'s rendering resolves
    // the span against the source text, so a `line:col` prefix is what a reader gets;
    // a raw `at 271..283` byte range would be the unlocated rendering.
    assert!(
        msg.contains("13:") && !msg.contains(" at "),
        "the refusal must render as line:col, not a raw byte offset: {msg}"
    );
    // Both repairs, spelled out. Which one the author meant is not knowable here, and
    // "this fact named no carrier" is not a repair.
    assert!(
        msg.contains("[Carrier]") && msg.contains("`sort`/`enum` body"),
        "the message must say what to write instead — BOTH the bracketed spelling and \
         the sort-body one: {msg}"
    );
}

/// A FILE'S TOP LEVEL IS THE SAME ADDRESS, and gets the same refusal. §6.3 lists four
/// spellings that carry a provision's obligation and this is one of them — its scope
/// is the synthetic `_global` root, a symbol with no declared kind, so "names a type"
/// is as false for it as for a namespace. WI-978 found that population by making the
/// third case loud instead of letting it fall out of a `_ => return`; pinned here so
/// the refusal cannot quietly become namespace-only.
#[test]
fn the_same_fact_at_a_files_top_level_is_refused_too() {
    let errs = errors(
        r#"import anthill.prelude.{Int64}

sort Wi933TopSpec
  operation w933_top_describe(s: Wi933TopSpec) -> Int64 = 0
end

sort Wi933TopCarrier
  entity w933_tc
end

fact Wi933TopSpec
"#,
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("names no carrier") && e.contains("Wi933TopSpec")),
        "a bracket-less provision claim at a file's top level names no carrier either \
         and must be refused; got {errs:?}"
    );
}

/// THE FOURTH POSITION IS NOT ONE OF THIS FILE'S, and nothing else measures that.
/// §6.3 lists a `namespace X` block at a sort's address among the places a provision's
/// obligation is carried, but `fact` is refused there outright — bracketed or not —
/// because a fact is a rule and a secondary entry cannot tell a spec claim from an
/// ordinary fact over a parameterized data sort. So "write the brackets" is NOT the
/// repair there; `provides Spec[…]` is. Pinned so the module doc's count of three
/// stays a measured claim rather than a remembered one — miscounting these positions
/// is precisely how `rust-forward-mapping.md` §2.13 came to promise a spelling that
/// did nothing.
#[test]
fn a_secondary_entry_is_not_one_of_the_positions() {
    let errs = errors(
        r#"
namespace test.wi933.secondary
  import anthill.prelude.{Int64}

  sort Wi933SecSpec
    operation w933_sec_describe(s: Wi933SecSpec) -> Int64 = 0
  end

  sort Wi933SecCarrier
    entity w933_sc
  end

  namespace Wi933SecCarrier
    fact Wi933SecSpec[Wi933SecCarrier]
  end
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains("secondary entry")),
        "a `fact` in a secondary entry is refused as a secondary-entry violation, not \
         reached by the carrier rule — so this position is not one of the three; got \
         {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("names no carrier")),
        "and it is emphatically not the carrier refusal — this fact writes its \
         carrier: {errs:?}"
    );
}

/// REPAIR 1, DRIVEN: `fact Spec[Carrier]` at namespace level really does declare the
/// is-a, so the message names a spelling that works. Driven through return-type
/// conformance — `widen` type-checks only if `Wi933Carrier <: Wi933Spec`, which holds
/// only if the provision reached `sort_provides`.
#[test]
fn the_bracketed_repair_the_message_names_works() {
    let src = r#"
namespace test.wi933.bracketed
  import anthill.prelude.{Int64}

  sort Wi933Spec
    operation w933_describe(s: Wi933Spec) -> Int64 = 0
  end

  sort Wi933Carrier
    entity w933_c
  end

  fact Wi933Spec[Wi933Carrier]

  operation w933_widen(c: Wi933Carrier) -> Wi933Spec = c
end
"#;
    let errs = errors(src);
    assert!(
        errs.is_empty(),
        "`fact Wi933Spec[Wi933Carrier]` makes the carrier a Wi933Spec, so returning it \
         as one must conform; got {errs:?}"
    );

    // CONTROL — the same program with the fact deleted. Without it the widening is a
    // type error, so the test above is measuring the provision and not merely a
    // permissive return check.
    let control = src.replace("  fact Wi933Spec[Wi933Carrier]\n", "");
    assert!(
        control != src,
        "the control must actually remove the fact line"
    );
    let ctl_errs = errors(&control);
    assert!(
        !ctl_errs.is_empty(),
        "without the fact there is no is-a and `w933_widen` must be refused — a clean \
         control would mean the test above proves nothing"
    );
}

/// REPAIR 2, DRIVEN: the bare `fact Spec` INSIDE the carrier's own body — the other
/// spelling the message offers, and the one the store hierarchy is built from
/// (`sort QueryableStore { fact Store }`). Same drive, same control.
///
/// This is also the divergence pin the ticket asks for: the two positions read the
/// same three words differently ON PURPOSE, and this leg is what says the working one
/// still works after the other was closed.
#[test]
fn the_sort_body_repair_the_message_names_works() {
    let src = r#"
namespace test.wi933.sortbody
  import anthill.prelude.{Int64}

  sort Wi933Spec
    operation w933_describe(s: Wi933Spec) -> Int64 = 0
  end

  sort Wi933Carrier
    entity w933_c
    fact Wi933Spec
  end

  operation w933_widen(c: Wi933Carrier) -> Wi933Spec = c
end
"#;
    let errs = errors(src);
    assert!(
        errs.is_empty(),
        "a bare `fact Wi933Spec` inside the carrier's body takes the enclosing type as \
         its carrier and must keep working; got {errs:?}"
    );

    // CONTROL — delete the in-body fact and the widening must fail.
    let control = src.replace("    fact Wi933Spec\n", "");
    assert!(
        control != src,
        "the control must actually remove the fact line"
    );
    let ctl_errs = errors(&control);
    assert!(
        !ctl_errs.is_empty(),
        "without the in-body fact there is no is-a and `w933_widen` must be refused"
    );
}

/// THE THREE POSITIONS IN ONE TEST, so they cannot silently diverge again. The same
/// three words — `fact Wi933Spec` — mean a provision on the enclosing type inside a
/// sort body, and mean nothing filable at namespace level. Asserting each separately
/// leaves the pair free to drift into agreement by BOTH going silent; asserting them
/// together is what catches that.
#[test]
fn neither_repair_is_the_refused_position() {
    let refused = errors(BRACKETLESS);
    assert!(
        refused.iter().any(|e| e.contains("names no carrier")),
        "namespace level, no brackets: refused; got {refused:?}"
    );

    let in_body = errors(
        r#"
namespace test.wi933.diverge
  import anthill.prelude.{Int64}

  sort Wi933Spec
    operation w933_describe(s: Wi933Spec) -> Int64 = 0
  end

  sort Wi933Carrier
    entity w933_c
    fact Wi933Spec
  end
end
"#,
    );
    assert!(
        in_body.is_empty(),
        "the identical text inside the carrier's body is a provision and must load \
         clean; got {in_body:?}"
    );
}

/// THE SHAPE THE REFUSAL MUST NOT REACH — a DATA CONSTRUCTION — pinned from both
/// sides, because each side kills a different plausible discriminator and only the
/// conjunction of both survives.
///
/// An eponymous PARAMETRIC sort (`sort Box { sort T = ?; entity Box(…) }`, WI-926: one
/// symbol that is both a sort and its constructor) reaches the same carrier-derivation
/// branch a malformed provision does: the data-sort skip above it needs
/// `spec_params.is_empty()`, which a parametric sort is not.
///
/// `constructed_with_a_field` kills "refuse whenever no carrier could be RESOLVED" —
/// the literal `1` resolves to no type exactly as a bad carrier binding would. It was
/// measured as two of the four arrivals at that branch across the whole suite, and
/// that discriminator was written and reverted before this test existed.
///
/// `constructed_bare` kills "refuse whatever is written bare" — a NULLARY constructor
/// is written bare and is not a claim about anything. It loaded clean before WI-933
/// and a bare-shape-only refusal broke it (found in review, then measured).
///
/// So the refusal is bare-shape AND a constructor-less functor. Telling a construction
/// from a provision properly is a question about the written surface (parens vs
/// brackets, `mark_type_application`) and is WI-1106; until then this is where a
/// widening of the refusal would break first.
#[test]
fn a_data_construction_over_a_parametric_sort_is_not_a_provision_claim() {
    let constructed_with_a_field = errors(
        r#"
namespace test.wi933.construction
  import anthill.prelude.{Int64}

  sort Wi933Box
    sort T = ?
    entity Wi933Box(value: T)
  end

  fact Wi933Box(value: 1)
end
"#,
    );
    assert!(
        constructed_with_a_field.is_empty(),
        "`fact Wi933Box(value: 1)` constructs a value, it does not claim a provision — \
         the carrier refusal must not reach it; got {constructed_with_a_field:?}"
    );

    let constructed_bare = errors(
        r#"
namespace test.wi933.nullary
  import anthill.prelude.{Int64}

  sort Wi933Unit
    sort T = ?
    entity Wi933Unit
  end

  fact Wi933Unit
end
"#,
    );
    assert!(
        constructed_bare.is_empty(),
        "a NULLARY eponymous constructor is written bare and is still a construction, \
         not a carrier-less provision claim — the refusal must read the functor's \
         constructors, not only the shape; got {constructed_bare:?}"
    );
}

/// THE OTHER CARRIER-LESS SHAPE, WHICH WI-1106 CLOSED. `fact Spec[combine = f]` on a
/// spec with NO carrier type parameter writes brackets, binds only an operation, and
/// leaves the derivation nothing to read — WI-431 (E) declines it for want of a
/// parameter to name in its repair.
///
/// WI-933 left it SILENT, and this test asserted that silence. Not because silence was
/// right, but because the only message available then said "write the carrier in
/// brackets" at text that has them — and the arm was shared with `fact Box(value: 1)`,
/// so a second wording could not be aimed either. WI-1106's gate made the arm
/// construction-free, which let the refusal split its wording; so this is the control
/// that flips.
///
/// It asserts the refusal AND which of the two sentences it is, because a single
/// "some error about a carrier" check would pass if the two collapsed back into one —
/// and the collapsed one was the nonsense repair.
#[test]
fn an_op_only_bracketed_fact_is_refused_without_being_told_to_add_brackets() {
    let errs = errors(
        r#"
namespace test.wi933.oponly
  import anthill.prelude.{Int64}

  sort Wi933OpSpec
    operation w933_combine(x: Int64) -> Int64
  end

  operation w933_impl(x: Int64) -> Int64 = x

  fact Wi933OpSpec[w933_combine = w933_impl]
end
"#,
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("its bindings name no type")),
        "WI-1106: brackets that bind only an operation name no carrier, and are now \
         refused in the wording for bindings-that-name-no-type; got {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("Write the carrier in brackets")),
        "and NOT with the bracket-less repair — the brackets are already written, so \
         that sentence would prescribe the spelling the author used: {errs:?}"
    );
}
