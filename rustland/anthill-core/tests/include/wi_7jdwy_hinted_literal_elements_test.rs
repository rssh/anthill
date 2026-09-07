//! WI-20260826-7JDWY — A HINTED COLLECTION LITERAL CHECKS ITS ELEMENTS.
//!
//! ## The defect
//!
//! The element type of a `[…]` / `{…}` whose position DECLARES one was taken from that
//! declaration unconditionally, and the elements were walked only to merge effects. So the
//! declaration did not CHECK the literal, it OVERWROTE it:
//!
//! ```text
//! operation mk() -> List[T = Int64] = ["x"]      LOADED CLEAN
//! operation first() -> Int64 = List.head(mk())   …and answered Str("x")
//! ```
//!
//! Not a question about variants and not one about `Int64`: any element type behaved this
//! way in any position that declares one — a declared return, an annotated `let`, a
//! literal nested inside another literal.
//!
//! ## THE TICKET NAMED A SITE THAT IS NEARLY INERT
//!
//! It named `TypeBuildFrame::ListLit` and its `SetLit` twin, and quoted their code. Both
//! DO have the defect. Both are also almost never reached: instrumented over the whole
//! workspace suite, the two frames are entered **4** times, every one of them with NO
//! declared element type to overwrite. A source `[…]` in an operation body arrives on a
//! THIRD carrier the ticket did not name — `check_seq_literal_constructor`, the
//! un-lowered `constructor(ListLiteral, …)` the loader leaves behind because §4.6 lowers
//! to a `cons`/`nil` spine only in a rule / fact data slot — and that one is entered
//! **964** times, **605** of them with a declaration, covering **13693** elements. A
//! repair made only where the ticket pointed would have compiled, reviewed clean, and
//! changed nothing an author can write.
//!
//! The three now share ONE owner, `typing::seq_literal_element_type`, so the rule cannot
//! be fixed at one carrier and left standing at another again. A FOURTH — the value-level
//! `seq_literal_value_type` — was open-coding the same `List[T = …]` build behind the same
//! stringly-typed base name; `/code-review` read the "one owner" claim beside it and it now
//! goes through `seq_literal_type` too.
//!
//! ## FOUR AXES, FOUR BACK-OUTS — one mutation at a time, whole `wi_tests` binary, every
//! count below a run
//!
//! 1. **The element CHECK** — in `seq_literal_element_type`, make the `Some(hint)` arm a
//!    no-op (drop the `validate_arg_against_param` match). **11 fail, 4227 pass.** Eight of
//!    this file's rows — the six that assert a refusal on a declared literal, plus
//!    `the_restored_argument_hint_also_turns_an_acceptance_into_a_refusal` and
//!    `the_wrong_variant_in_an_argument_…`. Three more elsewhere, each a row that had
//!    WRITTEN DOWN that this is how it should end:
//!    `typer_capability_matrix_test::a_literal_is_checked_on_every_route_that_declares_-
//!    an_element_type`, `::the_row_remainders`, and
//!    `wi_q0093_type_value_occurrence_matrix_test::a_collection_literal_element_type_is_-
//!    checked_for_every_element_alike`.
//! 2. **The element HINT at the constructor carrier** — drop `seq_element_expected` from
//!    `pos_hints` in the `Expr::Constructor` visit. **4 fail, 4234 pass**, all here:
//!    `a_declared_variant_element_is_classified_at_its_constructor` (`expected red, got
//!    Colour` — the parent classification §8.2 gives an element with no expectation of its
//!    own), `a_variant_element_reaches_an_argument_slot`,
//!    `the_declaration_reaches_a_literal_nested_in_a_literal`, and
//!    `the_wrong_variant_in_an_argument_…`.
//! 3. **The argument-slot HINT** — drop the `arg_is_seq_literal` arm from
//!    `variant_slot_arg_hint`. **3 fail, 4235 pass**: the two argument rows and
//!    `the_restored_argument_hint_…`.
//! 4. **The `List`/`Set` HEAD test** in `declared_element_type` — read `T` off any
//!    expectation, as the first cut did. **1 fails, 4237 pass**:
//!    `a_declaration_that_is_not_a_collection_declares_no_element_type`, and nothing else in
//!    the binary, which is what says the head test moved a MESSAGE and no verdict.
//!
//! HOW THE FOUR SEPARATE. Axis 2 is separated from axis 3 by
//! `a_declared_variant_element_is_classified_at_its_constructor` and
//! `the_declaration_reaches_a_literal_nested_in_a_literal` (fail under 2, pass under 3 — a
//! declared RETURN supplies the expectation without the argument hint), and axis 3 from
//! axis 2 by `the_restored_argument_hint_…` (the reverse pairing). Axis 4 has a row of its
//! own. `the_wrong_variant_in_an_argument_…` fails under 1, 2 AND 3 — it is an ARM, not a
//! separator, and that is said here so it is not read as one.
//!
//! TWO OF THESE SETS WERE PREDICTED WRONG BEFORE THEY WERE RUN, in an earlier round, and
//! the corrections are worth keeping. I expected the NESTED-literal row to survive axis 2;
//! it does not — without the element hint the inner `["x"]` has no declaration of its own,
//! types `List[T = String]`, and the outer check then reports `expected List[T = Int64],
//! got List[T = String]`. Still a refusal, a different pair, and the row asserts the pair.
//! And I expected axis 3 to fail exactly one row.
//!
//! Axis 3 is WI-20260826-JSFHG's own repair, RESTORED. JSFHG built it, measured that
//! `takeReds([blue(v: 1)])` — the WRONG variant — then loaded clean, and reverted it,
//! filing this ticket: the hint was unsound because nothing checked it. Axis 1 is what
//! makes it sound, and `the_wrong_variant_in_an_argument_is_named_by_its_own_constructor`
//! is the row that would have caught the revert.
//!
//! ## WHAT `/code-review` CORRECTED, AND WHAT EACH CORRECTION COST
//!
//! Axis 4 and two of the rows here exist because of it. The head test (finding 2) is a
//! diagnostic repair — reading `T` off any expectation blamed an ELEMENT for a CONTAINER
//! mismatch. `the_restored_argument_hint_also_turns_an_acceptance_into_a_refusal` (finding
//! 3) retires an inherited claim that this arm "can only turn a refusal into an
//! acceptance": paired with the element check it does the reverse, measured. And the note
//! on the `WrapSome` arm was rewritten (finding 4): it had claimed the some-coercion could
//! not be inserted here for a structural reason that does not exist, when what actually
//! decides it is that inserting is a new capability with an empty population.
//!
//! ## CONTROLS — green under all FOUR back-outs, by design (measured, not assumed)
//!
//! `control_an_unhinted_literal_still_types_from_its_elements` (the reading an
//! argument-position literal has always had, and the one that was already checked),
//! `control_an_empty_hinted_literal_still_takes_its_declaration`, and
//! `control_a_literal_of_two_constructors_still_types_at_the_declared_parent` (the reason
//! the repair is not "prefer the elements": those two elements type at two different
//! constructors and only the declaration covers both).

use crate::common::{interp_for, try_load_kb_with};

fn errs_of(src: &str) -> Vec<String> {
    try_load_kb_with(src)
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e)
}

fn load_clean(src: &str, what: &str) {
    let errs = errs_of(src);
    assert!(errs.is_empty(), "{what} must load clean; got {errs:#?}");
}

fn drive(src: &str, qn: &str) -> String {
    let mut interp = interp_for(src);
    let got = interp
        .call(qn, &[])
        .unwrap_or_else(|e| panic!("{qn} must evaluate: {e:?}"));
    format!("{got:?}")
}

fn assert_reports(src: &str, needle: &str, what: &str) {
    let errs = errs_of(src);
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "{what}: no diagnostic containing {needle:?}; got {errs:#?}"
    );
}

/// THE TICKET'S OWN ROW — a declared `List[T = Int64]` returning a list of strings.
///
/// AXIS 1. BACKED OUT: loads clean, and `List.head(mk())` answers `Str("x")` out of a slot
/// the signature types `Int64` — which is why this is a wrong-VALUE defect and not only a
/// missing diagnostic.
#[test]
fn a_hinted_list_literal_is_checked_against_its_declared_element_type() {
    let src = r#"
namespace test.jdy.list
  import anthill.prelude.{Int64, String, List}
  operation mk() -> List[T = Int64] = ["x"]
end
"#;
    assert_reports(
        src,
        "expected Int64, got String",
        "a `List[T = Int64]` of strings",
    );
    assert_reports(
        src,
        "list.element 1 (collection-element)",
        "…named as the LITERAL'S first element, not as the whole return",
    );
}

/// THE SET SURFACE, which is the same rule on the other literal and the other prelude sort.
///
/// AXIS 1. Two elements, because a one-element `{x}` is not a set literal at the surface,
/// and because the SECOND element being the wrong one is what pins the index: the
/// diagnostic must say `element 2`, not report the literal as a whole.
///
/// BACKED OUT: loads clean.
#[test]
fn a_hinted_set_literal_is_checked_too_and_names_the_offending_element() {
    let src = r#"
namespace test.jdy.set
  import anthill.prelude.{Int64, String, Set}
  operation mk() -> Set[T = Int64] = {1, "x"}
end
"#;
    assert_reports(
        src,
        "set.element 2 (collection-element): expected Int64, got String",
        "a `Set[T = Int64]` whose SECOND element is a string",
    );
}

/// THE DECLARATION DESCENDS INTO A NESTED LITERAL, so the inner list is checked by the
/// element type the OUTER declaration names for it.
///
/// AXIS 1 (and axis 2, which is what carries the outer declaration into the inner literal).
/// BACKED OUT of axis 1: loads clean.
#[test]
fn the_declaration_reaches_a_literal_nested_in_a_literal() {
    let src = r#"
namespace test.jdy.nested
  import anthill.prelude.{Int64, String, List}
  operation mk() -> List[T = List[T = Int64]] = [["x"]]
end
"#;
    assert_reports(
        src,
        "list.element 1 (collection-element): expected Int64, got String",
        "the INNER literal, judged by the outer declaration's element type",
    );
}

/// AN ANNOTATED `let` DECLARES AN ELEMENT TYPE TOO — the same rule at a different position,
/// and the one that shows this is about the DECLARATION rather than about op-return.
///
/// AXIS 1. BACKED OUT: loads clean.
#[test]
fn an_annotated_let_declares_an_element_type_and_it_is_checked() {
    let src = r#"
namespace test.jdy.letann
  import anthill.prelude.{Int64, String, List}
  operation mk() -> Int64 =
    let xs: List[T = Int64] = ["x"]
    1
end
"#;
    assert_reports(
        src,
        "list.element 1 (collection-element): expected Int64, got String",
        "an annotated `let` binding a literal of the wrong element",
    );
}

/// A DECLARED VARIANT ELEMENT IS CLASSIFIED AT ITS CONSTRUCTOR — §8.2's checking direction,
/// reaching an element of a literal.
///
/// AXIS 2, and the row that separates it from axis 3: the expectation here comes from the
/// declared RETURN, so the argument-slot hint plays no part. BACKED OUT of axis 2:
/// `expected red, got Colour` — the element has no expectation of its own, so it is
/// classified at the parent sort and the check (correctly) refuses it.
///
/// DRIVEN through a `List[T = Colour.red]` PARAMETER, which is what makes the claim about
/// the element and not about the literal: a literal whose element typed at the parent would
/// be a `List[T = Colour]` and could not fill that slot. `mk()` is a CALL, not a literal, so
/// no argument-slot hint is involved — which is what leaves this row green under axis 3.
///
/// `List.head` is deliberately not used to read the element back: it raises
/// `Error[T = EmptyStream]`, so the fixture would carry an effect declaration that has
/// nothing to do with what is being measured.
#[test]
fn a_declared_variant_element_is_classified_at_its_constructor() {
    let src = r#"
namespace test.jdy.vret
  import anthill.prelude.{Int64, List}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation mk() -> List[T = Colour.red] = [red(v: 41)]
  operation takeReds(l: List[T = Colour.red]) -> Int64 = 41
  operation viaReturn() -> Int64 = takeReds(mk())
end
"#;
    load_clean(src, "a `List[T = Colour.red]` built from `[red(v: 41)]`");
    assert_eq!(
        drive(src, "test.jdy.vret.viaReturn"),
        "Int(41)",
        "the literal's type IS `List[T = Colour.red]`, so it fills that parameter"
    );
}

/// A VARIANT ELEMENT REACHES AN **ARGUMENT** SLOT — WI-20260826-JSFHG's reverted repair,
/// restored now that the hint it pushes is checked rather than trusted.
///
/// AXIS 3, and ONLY axis 3 fails it that the row above does not: back out
/// `arg_is_seq_literal` and this is `expected List[T = red], got List[T = Colour]` at the
/// argument while the declared-return row above still passes.
///
/// DRIVEN. `takeReds` returns a constant, so the value proves only that the call was
/// admitted; the element's own typing is what the row above drives.
#[test]
fn a_variant_element_reaches_an_argument_slot() {
    let src = r#"
namespace test.jdy.varg
  import anthill.prelude.{Int64, List}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeReds(l: List[T = Colour.red]) -> Int64 = 17
  operation viaArg() -> Int64 = takeReds([red(v: 1)])
end
"#;
    load_clean(src, "a list literal of the RIGHT variant at an argument");
    assert_eq!(
        drive(src, "test.jdy.varg.viaArg"),
        "Int(17)",
        "the call is admitted, not merely the declaration"
    );
}

/// THE WRONG VARIANT AT THAT SAME ARGUMENT IS REFUSED, AND NAMED — the row that would have
/// caught JSFHG's revert, and the reason axis 3 is only sound with axis 1 in place.
///
/// AXES 1, 2 AND 3 all fail it, each differently, and that is stated rather than hidden:
/// backing out the CHECK makes it LOAD CLEAN (the measured fail-open JSFHG reverted for);
/// backing out either hint keeps a refusal but reports `got Colour` — true, and about the
/// wrong thing, since what the author wrote is `blue`.
#[test]
fn the_wrong_variant_in_an_argument_is_named_by_its_own_constructor() {
    let src = r#"
namespace test.jdy.vargbad
  import anthill.prelude.{Int64, List}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeReds(l: List[T = Colour.red]) -> Int64 = 17
  operation viaArg() -> Int64 = takeReds([blue(v: 1)])
end
"#;
    assert_reports(
        src,
        "list.element 1 (collection-element): expected red, got blue",
        "the WRONG variant in a `List[T = Colour.red]` argument",
    );
}

/// THE INDEX IS THE ELEMENT'S OWN, and the span is the element's own — with three elements
/// the literal's span names the whole `[…]` and leaves the reader counting.
///
/// AXIS 1. BACKED OUT: loads clean.
#[test]
fn the_diagnostic_names_the_offending_element_by_position() {
    let src = r#"
namespace test.jdy.index
  import anthill.prelude.{Int64, String, List}
  operation mk() -> List[T = Int64] = [1, 2, "x"]
end
"#;
    assert_reports(
        src,
        "list.element 3 (collection-element): expected Int64, got String",
        "the THIRD element, counted from one",
    );
    let errs = errs_of(src);
    assert!(
        errs.iter().any(|e| e.starts_with("4:46:")),
        "the ELEMENT's own span — column 46 is where `\"x\"` starts; the literal itself \
         starts at column 39, which is what a whole-list report would name. Got {errs:#?}"
    );
}

/// A BARE `T` WHERE THE DECLARATION SAYS `Option[T]` IS REPORTED, NOT SILENTLY COERCED.
///
/// AXIS 1. Every other position takes the WI-408 some-coercion by rebuilding the argument
/// occurrence around a synthesized `some(…)`. A literal element COULD — `/code-review`
/// corrected an earlier claim here that it structurally could not — so this is a decision:
/// inserting the wrap is a new capability with an empty population (measured: zero elements
/// in the workspace corpus reach that arm), while refusing replaces a program that LOADED
/// and left the element bare at runtime. See `seq_literal_element_type`'s doc.
///
/// BACKED OUT: the first program loads clean. The second is the separator — an explicit
/// `some(…)` is admitted either way, so this is about the missing wrap and not about
/// `Option` elements being rejected.
#[test]
fn a_bare_element_where_an_option_is_declared_is_reported_not_coerced() {
    let bare = r#"
namespace test.jdy.optbare
  import anthill.prelude.{Int64, List, Option}
  operation mk() -> List[T = Option[T = Int64]] = [1]
end
"#;
    assert_reports(
        bare,
        "expected Option[T = Int64], got Int64",
        "a bare `1` in a declared `List[T = Option[T = Int64]]`",
    );

    let wrapped = r#"
namespace test.jdy.optwrapped
  import anthill.prelude.{Int64, List, Option}
  operation mk() -> List[T = Option[T = Int64]] = [Option.some(value: 1)]
  operation n() -> Int64 = List.length(mk())
end
"#;
    load_clean(wrapped, "the explicitly-wrapped element");
    assert_eq!(
        drive(wrapped, "test.jdy.optwrapped.n"),
        "Int(1)",
        "…and it is a list of one, so the wrap was not double-applied"
    );
}

/// THE DECLARATION IS READ OFF A `List`/`Set` HEAD, NOT OFF ANY `T` THAT HAPPENS TO BE
/// THERE — the correction `/code-review` found, and the row that pins it.
///
/// `Option[T = List[T = Int64]]` carries a `T`, and it is not an element type. Reading it
/// as one made the message blame an element and quote an "expected" lifted off `Option`'s
/// parameter: `list.element 1 … expected List[T = Int64], got Int64`, about a list the
/// program does not contain. The verdict was right either way — the container mismatch is
/// refused on both sides — so this row asserts the MESSAGE, which is the only thing that
/// moved.
///
/// BACKED OUT (drop the head test in `declared_element_type`): the element message returns.
#[test]
fn a_declaration_that_is_not_a_collection_declares_no_element_type() {
    let src = r#"
namespace test.jdy.head
  import anthill.prelude.{Int64, List, Option}
  operation mk() -> Option[T = List[T = Int64]] = [1]
end
"#;
    assert_reports(
        src,
        "mk.return (op-return): expected Option[T = List[T = Int64]], got List[T = Int64]",
        "the CONTAINERS are what disagree, so the containers are what the message names",
    );
    let errs = errs_of(src);
    assert!(
        !errs.iter().any(|e| e.contains("collection-element")),
        "nothing here is an element mismatch: `Option`'s `T` is not this literal's \
         element type. Got {errs:#?}"
    );
}

/// THE ARM DOES TURN AN ACCEPTANCE INTO A REFUSAL, and this is the row that says so.
///
/// WI-20260826-JSFHG's containment argument — "it can only turn a refusal into an
/// acceptance, never the reverse" — was inherited by the restored arm and is FALSE of it,
/// because this ticket adds the check the argument was written without. `[r, c]` in a
/// `List[T = Colour.red]` slot LOADED before: with no hint the literal's element type was
/// element ONE's (`red`), and element two was never looked at. It is refused now, correctly.
///
/// AXES 1 AND 3 both fail it. It is kept because a future widening of the
/// `type_mentions_an_entity` gate will look for this claim, and finding the retired version
/// would license a widening whose flip-set nobody has measured.
#[test]
fn the_restored_argument_hint_also_turns_an_acceptance_into_a_refusal() {
    let src = r#"
namespace test.jdy.flip
  import anthill.prelude.{Int64, List}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeReds(l: List[T = Colour.red]) -> Int64 = 17
  operation viaArg(r: Colour.red, c: Colour) -> Int64 = takeReds([r, c])
end
"#;
    assert_reports(
        src,
        "list.element 2 (collection-element): expected red, got Colour",
        "a parent-typed SECOND element, which the first element's type used to hide",
    );
}

/// CONTROL — an UNHINTED literal still types from its elements, and was already checked
/// there. Passes under every axis BY DESIGN, and it is what says the three axes above are
/// about the DECLARED direction only: the reading an argument-position literal has always
/// had is untouched, including the whole-list diagnostic it reports.
///
/// AND ITS RESIDUAL IS NAMED HERE rather than left to be rediscovered: this route reads the
/// FIRST element and never compares the rest, so `takeInts([1, "a"])` loads clean with a
/// `String` in an `Int64` slot (measured on this tree, asserted below). That is
/// WI-20260829-WBXGX — open, with its own census — and it is what the declared route above
/// no longer does.
#[test]
fn control_an_unhinted_literal_still_types_from_its_elements() {
    let wrong = r#"
namespace test.jdy.unhinted
  import anthill.prelude.{Int64, String, List}
  operation takeInts(l: List[T = Int64]) -> Int64 = 1
  operation wrong() -> Int64 = takeInts(["x"])
end
"#;
    assert_reports(
        wrong,
        "takeInts.l (op-arg): expected List[T = Int64], got List[T = String]",
        "an unhinted literal types from its elements and the ARGUMENT check refuses it",
    );

    let right = r#"
namespace test.jdy.unhinted2
  import anthill.prelude.{Int64, List}
  operation takeInts(l: List[T = Int64]) -> Int64 = List.length(l)
  operation n() -> Int64 = takeInts([1, 2, 3])
end
"#;
    load_clean(right, "a conforming unhinted literal");
    assert_eq!(drive(right, "test.jdy.unhinted2.n"), "Int(3)");

    // THE RESIDUAL, pinned so the asymmetry between the two routes is a measurement and not
    // a claim in a comment. WI-20260829-WBXGX; when it closes, this row fails and says so.
    let later_element = r#"
namespace test.jdy.unhinted3
  import anthill.prelude.{Int64, String, List}
  operation takeInts(l: List[T = Int64]) -> Int64 = 1
  operation wrong() -> Int64 = takeInts([1, "a"])
end
"#;
    load_clean(
        later_element,
        "the UNHINTED route reads element one and never the rest (WI-20260829-WBXGX) — if \
         this now refuses, that item has closed and this row becomes a positive",
    );
}

/// CONTROL — an EMPTY hinted literal has no element to check and keeps its declaration.
/// Passes under every axis by design; it is here because the check must not turn "no
/// elements" into "no declaration".
#[test]
fn control_an_empty_hinted_literal_still_takes_its_declaration() {
    let src = r#"
namespace test.jdy.empty
  import anthill.prelude.{Int64, List}
  operation mk() -> List[T = Int64] = []
  operation n() -> Int64 = List.length(mk())
end
"#;
    load_clean(src, "an empty literal at a declared element type");
    assert_eq!(drive(src, "test.jdy.empty.n"), "Int(0)");
}

/// CONTROL — a literal of TWO constructors still types at the declared parent, which is
/// why the repair is not "prefer the elements": those two elements type at two different
/// constructors, and only the declaration covers both. Passes under every axis by design.
#[test]
fn control_a_literal_of_two_constructors_still_types_at_the_declared_parent() {
    let src = r#"
namespace test.jdy.join
  import anthill.prelude.{Int64, List}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation mk() -> List[T = Colour] = [red(v: 1), blue(v: 2)]
  operation n() -> Int64 = List.length(mk())
end
"#;
    load_clean(src, "a mixed-constructor literal at a declared parent sort");
    assert_eq!(drive(src, "test.jdy.join.n"), "Int(2)");
}
