//! WI-20260826-JSFHG — A VARIANT TYPE IS INHABITED.
//!
//! ## The defect
//!
//! §8.2: *"Each constructor name is a sort in its own right"*, `C₁ <: S`, *"A term
//! classified as sort `C₁` is also of sort `S`"*. The type was DECLARABLE and correctly
//! RELATED — a `Colour.red` parameter passes where `Colour` is expected, and the reverse is
//! refused — but NOTHING COULD HAVE IT. Every route to a value typed at the PARENT:
//!
//!     takeRed(Colour.red(v: 1))                         expected red, got Colour
//!     takeRed(red(v: 1))                                expected red, got Colour
//!     operation mkRed() -> Colour.red = red(v: 1)       expected red, got Colour
//!     match c case red(x) -> takeRed(red(v: x))         expected red, got Colour
//!
//! So a signature written with a variant type was not merely awkward, it was
//! UNSATISFIABLE — and it LOADED CLEAN, which is the silent half.
//!
//! ## What settles it, and what it is NOT
//!
//! The CHECKING DIRECTION decides the classification. Where the expected type names an
//! entity, the application is classified at the constructor; everywhere else it keeps
//! typing at the parent exactly as before. One predicate — `type_head_names_an_entity` —
//! is asked at both ends of that decision (`check_constructor_iter`'s own `expected`, and
//! `variant_slot_arg_hint`'s `expected → argument` push), so the two cannot drift.
//!
//! THE ALTERNATIVE THE TICKET PRESCRIBED WAS MEASURED AND IS NOT THIS. It said
//! `constructor_value_type` should return the constructor's own sort ref unconditionally.
//! Implemented, that types every application at the variant — `cons[T = ?T]`,
//! `some[T = pair[…]]`, `mapped[…]` — and the STDLIB STOPS LOADING: 16 distinct errors in
//! FIVE roots, each a reader that would need its own entity→parent widening (same-family
//! conformance; provider admissibility through the entity, `mapped` vs `Stream`; a type
//! PROJECTION on an entity base, `FilteredStream.filtered has no member 'E'`; effect
//! LABELS compared structurally, `Error[T = empty_stream]` vs `Error[T = EmptyStream]`;
//! and the compounding one — entity types nested inside every binding). That is a
//! type-system-wide change, not this ticket's patch, and the residual row at the bottom of
//! this file is what it would additionally buy.
//!
//! ## The three back-outs these rows are stated against
//!
//! THREE AXES, measured SEPARATELY, because one mutation cannot separate three claims:
//!
//! 1. **The classification** — force `classify_sym` to `parent_sort.unwrap_or(ctor_sym)` in
//!    `check_constructor_iter`. **13 rows fail**; the 4 controls and the 2 known gaps pass.
//! 2. **The parent dot rung** — disable the `strict_parent_sort` arm before
//!    `if let Some(op_sym)`. Exactly **one** row fails,
//!    `a_parent_member_is_reachable_by_dot_through_a_variant_receiver` (which axis 1 also
//!    fails, since its program needs the classification to load at all).
//! 3. **The field-precedence guard** inside that rung — drop `names_own_field`. Exactly one
//!    row fails, and by its VALUE rather than by loading:
//!    `a_variants_own_field_still_beats_a_same_named_parent_operation` answers `Int(99)`,
//!    the parent's operation, where the entity's own field says `Int(5)`.
//!
//! THE FIRST STATEMENT OF THE CONTROLS WAS WRONG in a way worth keeping: it named four rows
//! as passing either way and three of them failed, because each had a control assertion
//! sharing a fixture with a DRIVEN one (a `relay(red(v: 4))` call beside the widening claim;
//! an annotated `let` beside the unannotated gap). Those are split, so a row is now either
//! an ARM or a CONTROL and never both.
//!
//! * **CONTROLS** — pass under every axis BY DESIGN, and together they say this is a
//!   classification REFINEMENT under an expectation and not a permissive accept:
//!   `control_the_lattice_is_unchanged_in_both_directions`,
//!   `control_a_sibling_variant_is_refused`,
//!   `control_an_unhinted_constructor_still_types_at_the_parent`,
//!   `control_an_unannotated_binding_still_widens_to_the_parent`.
//! * **KNOWN GAPS** — also pass either way, and that is their point: they measure what this
//!   ticket does NOT close. `known_gap_a_list_literal_of_variants_is_refused_at_an_argument`
//!   (whose own third assertion pins the fail-open that CAUSES it) and
//!   `known_gap_the_auto_some_coercion_is_withheld_at_a_variant_typed_field`.
//!
//! ## What /code-review found, and what it changed
//!
//! Four positions the first cut left uninhabitable, none of them variations on the others —
//! each reaches the classification down a different channel and each was refused for its own
//! reason. Three are closed here (a fieldless variant in its BARE spelling, which is §8.2's
//! own worked example; a named-tuple component; dot dispatch through a variant receiver) and
//! one is not.
//!
//! THE ONE THAT IS NOT is the correction worth recording. A list literal in a variant-typed
//! argument slot looked like the same fix, and the repair was built: it made
//! `takeReds([blue(v: 1)])` — the WRONG variant — LOAD CLEAN, because `TypeBuildFrame::ListLit`
//! takes `element_hint` as the element type UNCONDITIONALLY and never reads what the elements
//! typed as. The review was right about the asymmetry and the direction that "works" is the
//! broken one; the repair was REVERTED and the underlying hole filed as WI-20260826-7JDWY.

use crate::common::{interp_for, try_load_kb_with};

fn errs_of(src: &str) -> Vec<String> {
    try_load_kb_with(src)
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e)
}

fn drive(src: &str, qn: &str) -> String {
    let mut interp = interp_for(src);
    let got = interp
        .call(qn, &[])
        .unwrap_or_else(|e| panic!("{qn} must evaluate: {e:?}"));
    format!("{got:?}")
}

fn load_clean(src: &str, what: &str) {
    let errs = errs_of(src);
    assert!(errs.is_empty(), "{what} must load clean; got {errs:#?}");
}

/// A VALUE FLOWS THROUGH A VARIANT-TYPED PARAMETER, in both constructor spellings.
///
/// This is the claim, and it is driven rather than loaded: `takeRed` reads `r.v`, so if the
/// parameter's type were anything but `red` the argument would not check. The two
/// spellings carry DIFFERENT numbers so a failure names which one broke.
///
/// BACKED OUT: `type mismatch in takeRed.r (op-arg): expected red, got Colour`, twice —
/// the ticket's first two repro rows.
#[test]
fn a_variant_typed_parameter_takes_a_value_through_every_constructor_spelling() {
    let src = r#"
namespace test.jsfhg.param
  import anthill.prelude.{Int64}
  enum Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeRed(r: Colour.red) -> Int64 = r.v
  operation bare() -> Int64 = takeRed(red(v: 41))
  operation qualified() -> Int64 = takeRed(Colour.red(v: 7))
end
"#;
    load_clean(src, "a variant-typed parameter");
    assert_eq!(
        drive(src, "test.jsfhg.param.bare"),
        "Int(41)",
        "the BARE constructor `red(v: 41)` in a `Colour.red` slot"
    );
    assert_eq!(
        drive(src, "test.jsfhg.param.qualified"),
        "Int(7)",
        "the QUALIFIED constructor `Colour.red(v: 7)` in the same slot"
    );
}

/// A VARIANT-TYPED RETURN IS SATISFIABLE, and its value keeps the variant type onward.
///
/// Two claims in one program, and the second is why the row does not stop at loading:
/// `mkRed` declares `-> Colour.red`, and its result is then passed to a `Colour.red`
/// parameter. A body that still typed at `Colour` would be refused at the declaration; a
/// RESULT that widened would be refused at the call.
///
/// BACKED OUT: `type mismatch in mkRed.return (op-return): expected red, got Colour` — the
/// ticket's third repro row.
#[test]
fn a_variant_typed_return_is_satisfiable_and_its_value_stays_a_variant() {
    let src = r#"
namespace test.jsfhg.ret
  import anthill.prelude.{Int64}
  enum Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeRed(r: Colour.red) -> Int64 = r.v
  operation mkRed() -> Colour.red = red(v: 9)
  operation drive() -> Int64 = takeRed(mkRed())
end
"#;
    load_clean(src, "a variant-typed return");
    assert_eq!(
        drive(src, "test.jsfhg.ret.drive"),
        "Int(9)",
        "the declared `-> Colour.red` result must still BE a `Colour.red` at the next call"
    );
}

/// THE SHARPEST OF THE TICKET'S ROWS: a re-construction inside an arm that has ALREADY
/// discriminated on the variant.
///
/// `match c case red(x) -> takeRed(red(v: x))` — the program has proven it holds a `red`
/// and builds one, and the result was still classified `Colour`. The `blue` arm is present
/// so the match is exhaustive and the value genuinely flows through the `red` arm.
///
/// BACKED OUT: `type mismatch in takeRed.r (op-arg): expected red, got Colour`.
#[test]
fn a_reconstruction_inside_a_narrowed_arm_is_classified_at_the_variant() {
    let src = r#"
namespace test.jsfhg.narrow
  import anthill.prelude.{Int64}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeRed(r: Colour.red) -> Int64 = r.v
  operation reconstruct(c: Colour) -> Int64 =
    match c
      case red(x) -> takeRed(red(v: x))
      case blue(x) -> x
  operation driveRed() -> Int64 = reconstruct(red(v: 5))
  operation driveBlue() -> Int64 = reconstruct(blue(v: 6))
end
"#;
    load_clean(src, "a reconstruction inside a narrowed arm");
    assert_eq!(
        drive(src, "test.jsfhg.narrow.driveRed"),
        "Int(5)",
        "through the `red` arm, whose reconstruction is the row's subject"
    );
    assert_eq!(
        drive(src, "test.jsfhg.narrow.driveBlue"),
        "Int(6)",
        "the sibling arm still answers — the match was not narrowed to one variant"
    );
}

/// A VARIANT-TYPED ENTITY FIELD, which is the OTHER channel the hint is registered in.
///
/// A SEPARATE ROW from the op-arg one, and not redundant with it: an operation's parameter
/// types and a constructor's field types are looked up by different code and hinted at
/// different sites (`apply_arg_hints` vs the `Expr::Constructor` push arm). The field
/// channel additionally needed its own `has_ctor_field` gate — without it the declared
/// field type is never looked up at all and the hint is asked with `None`.
///
/// BACKED OUT: `type mismatch in holder.c (entity-field): expected red, got Colour`.
#[test]
fn a_variant_typed_entity_field_takes_a_constructor_value() {
    let src = r#"
namespace test.jsfhg.field
  import anthill.prelude.{Int64}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  sort Holder
    entity holder(c: Colour.red)
  end
  operation readIt(h: Holder) -> Int64 = h.c.v
  operation drive() -> Int64 = readIt(holder(c: red(v: 12)))
end
"#;
    load_clean(src, "a variant-typed entity field");
    assert_eq!(
        drive(src, "test.jsfhg.field.drive"),
        "Int(12)",
        "the field holds a `Colour.red` and `h.c.v` reads through it"
    );
}

/// A PLAIN `sort` BEHAVES EXACTLY AS AN `enum` — the ticket measured this and it is not
/// incidental: nothing here keys on the `enum` spelling, so a row that only covered `enum`
/// would leave the majority shape unmeasured.
///
/// The two programs are the same text but for the keyword, and both answer 3.
#[test]
fn a_plain_sort_behaves_exactly_as_an_enum() {
    let program = |keyword: &str| {
        format!(
            r#"
namespace test.jsfhg.kw
  import anthill.prelude.{{Int64}}
  {keyword} Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeRed(r: Colour.red) -> Int64 = r.v
  operation drive() -> Int64 = takeRed(red(v: 3))
end
"#
        )
    };
    for keyword in ["sort", "enum"] {
        let src = program(keyword);
        load_clean(&src, &format!("the `{keyword}` spelling"));
        assert_eq!(
            drive(&src, "test.jsfhg.kw.drive"),
            "Int(3)",
            "`{keyword} Colour` must inhabit `Colour.red` the same way"
        );
    }
}

/// A PARAMETRIC VARIANT TYPE — `Option.some[T = Int64]`, where the constructor carries the
/// PARENT's type parameter and not one of its own.
///
/// The bare `Colour.red` rows above cannot measure this: the built type is
/// `some[T = Int64]`, a parameterized type whose base is an ENTITY, and it must both
/// conform to the written `Option.some[T = Int64]` slot AND still widen to a plain
/// `Option[T = Int64]` one. Both are driven, with different numbers.
///
/// BACKED OUT: `expected some[T = Int64], got Option[T = Int64]`.
#[test]
fn a_parametric_variant_type_is_inhabited() {
    let src = r#"
namespace test.jsfhg.parametric
  import anthill.prelude.{Int64, Option, some}
  operation takeSome(o: Option.some[T = Int64]) -> Int64 = 21
  operation takeAny(o: Option[T = Int64]) -> Int64 = 22
  operation driveSome() -> Int64 = takeSome(some(1))
  operation driveAny() -> Int64 = takeAny(some(1))
end
"#;
    load_clean(src, "a parametric variant type");
    assert_eq!(
        drive(src, "test.jsfhg.parametric.driveSome"),
        "Int(21)",
        "`some(1)` in an `Option.some[T = Int64]` slot"
    );
    assert_eq!(
        drive(src, "test.jsfhg.parametric.driveAny"),
        "Int(22)",
        "…and the SAME expression still fills a plain `Option[T = Int64]` slot"
    );
}

/// CONTROL — THE LATTICE IS UNCHANGED IN BOTH DIRECTIONS. Passes with and without this
/// ticket BY DESIGN, and that is its job: it says the change refined a CLASSIFICATION and
/// left the subtyping relation underneath alone.
///
/// `relay` widens a `Colour.red` PARAMETER into a `Colour` slot — `red <: Colour`, accepted
/// — and `wrong` does the reverse, which is unsound and stays refused BY NAME. Nothing here
/// constructs anything, which is what keeps it a control: a constructor application is the
/// only thing this ticket reclassifies. Without the second half every arm in this file
/// would pass on a tree where a variant slot accepts anything.
#[test]
fn control_the_lattice_is_unchanged_in_both_directions() {
    let widen = r#"
namespace test.jsfhg.widen
  import anthill.prelude.{Int64}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeAny(c: Colour) -> Int64 = c.v
  operation relay(r: Colour.red) -> Int64 = takeAny(r)
end
"#;
    load_clean(widen, "`red <: Colour` where a parent slot is declared");

    let narrow = r#"
namespace test.jsfhg.narrowbad
  import anthill.prelude.{Int64}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeRed(r: Colour.red) -> Int64 = r.v
  operation wrong(c: Colour) -> Int64 = takeRed(c)
end
"#;
    let errs = errs_of(narrow);
    assert!(
        errs.iter()
            .any(|e| e.contains("expected red") && e.contains("got Colour")),
        "a PARENT-typed value in a variant slot is unsound and must stay refused; got \
         {errs:#?}"
    );
}

/// A WIDENED VARIANT VALUE STILL REACHES A PARENT SLOT — the ARM the control above cannot
/// carry, because driving it needs a constructor in a variant slot in the first place.
///
/// `relay(red(v: 4))` puts a construction through the `Colour.red` parameter and the body
/// hands it on to a `Colour` one, so both directions are exercised on one value.
///
/// BACKED OUT: `type mismatch in relay.r (op-arg): expected red, got Colour`.
#[test]
fn a_widened_variant_value_still_reaches_a_parent_slot() {
    let src = r#"
namespace test.jsfhg.widendrive
  import anthill.prelude.{Int64}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeAny(c: Colour) -> Int64 = c.v
  operation relay(r: Colour.red) -> Int64 = takeAny(r)
  operation drive() -> Int64 = relay(red(v: 4))
end
"#;
    load_clean(src, "a construction reaching a parent slot through a variant one");
    assert_eq!(drive(src, "test.jsfhg.widendrive.drive"), "Int(4)");
}

const SIBLING_SRC: &str = r#"
namespace test.jsfhg.sibling
  import anthill.prelude.{Int64}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeRed(r: Colour.red) -> Int64 = r.v
  operation wrong() -> Int64 = takeRed(blue(v: 1))
end
"#;

/// CONTROL — A SIBLING VARIANT IS REFUSED. Passes either way BY DESIGN.
///
/// This is what says the hint did not become a permissive accept: `takeRed(blue(v: 1))` is
/// hinted with `Colour.red`, and the application is classified at `blue` — its OWN
/// constructor, never the head the hint carried — so it is refused exactly as it was before
/// the ticket. The row asserts ONLY the refusal, so it cannot be satisfied by the message
/// improving; that is the arm below.
#[test]
fn control_a_sibling_variant_is_refused() {
    let errs = errs_of(SIBLING_SRC);
    assert!(
        errs.iter().any(|e| e.contains("expected red")),
        "a sibling constructor must be refused whether or not the classification is \
         refined; got {errs:#?}"
    );
}

/// THE REFUSAL NAMES THE VARIANT THE COMPILER BUILT — the arm the control above holds
/// fixed for.
///
/// Before the ticket the diagnostic said "got Colour": it named the PARENT of a value the
/// compiler knew exactly, because the classification had already discarded which
/// constructor it was. Now it names `blue`.
///
/// BACKED OUT: the same program is still refused, and the message reads "got Colour".
#[test]
fn the_refusal_names_the_variant_the_compiler_built() {
    let errs = errs_of(SIBLING_SRC);
    assert!(
        errs.iter()
            .any(|e| e.contains("expected red") && e.contains("got blue")),
        "the diagnostic must name the variant that was built, not its parent; got {errs:#?}"
    );
}

/// CONTROL — AN UNHINTED CONSTRUCTOR STILL TYPES AT THE PARENT. Passes either way BY
/// DESIGN, and it is the reason the stdlib is untouched by this ticket.
///
/// Every slot here is declared with the PARENT sort, so no expected type names an entity,
/// no hint fires, and the classification is the pre-ticket one. `join`'s two branches
/// return different variants and must still join at `Colour` — a per-branch variant type
/// would make the operation's return unwritable.
#[test]
fn control_an_unhinted_constructor_still_types_at_the_parent() {
    let src = r#"
namespace test.jsfhg.parent
  import anthill.prelude.{Int64, Bool}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeAny(c: Colour) -> Int64 = c.v
  operation join(b: Bool) -> Colour = if b then red(v: 1) else blue(v: 2)
  operation driveRed() -> Int64 = takeAny(join(true))
  operation driveBlue() -> Int64 = takeAny(join(false))
end
"#;
    load_clean(src, "an unhinted constructor in a parent-typed slot");
    assert_eq!(drive(src, "test.jsfhg.parent.driveRed"), "Int(1)");
    assert_eq!(drive(src, "test.jsfhg.parent.driveBlue"), "Int(2)");
}

fn let_program(binding: &str) -> String {
    format!(
        r#"
namespace test.jsfhg.letgap
  import anthill.prelude.{{Int64}}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeRed(r: Colour.red) -> Int64 = r.v
  operation drive() -> Int64 =
    let {binding} = red(v: 8)
    takeRed(r)
end
"#
    )
}

/// AN ANNOTATED BINDING OF A VARIANT TYPE IS SATISFIABLE — the arm.
///
/// `let r: Colour.red = red(v: 8)` is a checking position, so the annotation is what the
/// classification reads, and the value flows on into a `Colour.red` parameter.
///
/// BACKED OUT: `expected red, got Colour` at the binding.
#[test]
fn an_annotated_binding_of_a_variant_type_is_satisfiable() {
    let src = let_program("r: Colour.red");
    load_clean(&src, "an ANNOTATED binding of a variant type");
    assert_eq!(
        drive(&src, "test.jsfhg.letgap.drive"),
        "Int(8)",
        "the annotation is the checking direction, so this is the spelling that works"
    );
}

/// CONTROL / KNOWN GAP — AN UNANNOTATED BINDING STILL WIDENS TO THE PARENT. Passes either
/// way BY DESIGN, which is precisely the point: this is the residual the ticket leaves, and
/// the row exists so it is a MEASURED statement rather than a claim in a comment.
///
/// The classification is decided by the CHECKING DIRECTION, so an inference position with
/// no expected type keeps the parent: `let r = red(v: 8)` gives `r : Colour` and the later
/// `takeRed(r)` is refused. Its annotated twin above is the arm; keeping them in separate
/// rows is what lets this one measure the gap without also measuring the feature.
///
/// CLOSING IT is the ticket's own prescribed alternative — classify at the constructor
/// unconditionally — whose cost is measured in this file's module doc: 16 stdlib load
/// errors across five readers. If this row ever starts failing, the gap has closed and the
/// module doc must be updated.
#[test]
fn control_an_unannotated_binding_still_widens_to_the_parent() {
    let src = let_program("r");
    let errs = errs_of(&src);
    assert!(
        errs.iter()
            .any(|e| e.contains("expected red") && e.contains("got Colour")),
        "THE RESIDUAL: with no annotation there is no expected type at the binding, so the \
         application keeps typing at the parent; got {errs:#?}"
    );
}

// ---------------------------------------------------------------------------------------
// THE POSITIONS /code-review FOUND, each one a spelling the first cut left uninhabitable.
// They are not variations on the rows above: each reaches `check_constructor_iter` down a
// DIFFERENT channel, and each was refused for its own reason.
// ---------------------------------------------------------------------------------------

/// A FIELDLESS VARIANT, IN BOTH THE BARE AND THE APPLIED SPELLING — §8.2's OWN worked
/// example (`sort Color { entity red; entity green; entity blue }`), which the first cut
/// was the one shape unable to inhabit.
///
/// TWO SEPARATE CAUSES, both found by /code-review and neither guessable from the rows
/// above. (1) `check_bare_ref` passed a hard `None` where every other route threads
/// `expected`, so `takeRed(red)` took no checking direction at all while `takeRed(red())` —
/// the same value, one pair of parentheses apart — worked. (2) The hint gate read
/// `entity_field_types`, which a FIELDLESS entity has no entry in, so the gate answered
/// `false` for exactly this shape; it now reads `is_constructor_symbol`, the predicate
/// `check_bare_ref` itself routes on. The bare name also arrives as `Expr::VarRef`, not
/// `Ref`/`Ident` — measured, and the reason a first repair still refused it.
///
/// BACKED OUT: both spellings refused with "expected red, got Colour".
#[test]
fn a_fieldless_variant_is_inhabited_in_both_bare_and_applied_spellings() {
    let src = r#"
namespace test.jsfhg.fieldless
  import anthill.prelude.{Int64}
  enum Colour
    entity red
    entity blue
  end
  operation takeRed(r: Colour.red) -> Int64 = 31
  operation bare() -> Int64 = takeRed(red)
  operation applied() -> Int64 = takeRed(red())
end
"#;
    load_clean(src, "a fieldless variant in a variant-typed slot");
    assert_eq!(
        drive(src, "test.jsfhg.fieldless.bare"),
        "Int(31)",
        "the BARE reference — the spelling §8.2's own example is written in"
    );
    assert_eq!(
        drive(src, "test.jsfhg.fieldless.applied"),
        "Int(31)",
        "…and its applied twin, which must not differ by a pair of parentheses"
    );
}

/// KNOWN GAP — A LIST LITERAL OF VARIANTS IS STILL REFUSED AT AN ARGUMENT, AND THE REASON
/// IS A FAIL-OPEN ONE LEVEL DOWN. Passes either way BY DESIGN.
///
/// /code-review found the ASYMMETRY here and it is real: `-> List[T = Colour.red] =
/// [red(v: 1)]` loads while `takeReds([red(v: 1)])` is refused. The obvious repair — push
/// the slot type down as the literal's `expected`, exactly as the tuple row below does —
/// WAS BUILT AND REVERTED, because it does not check the literal, it OVERWRITES it:
/// [`TypeBuildFrame::ListLit`] takes `element_hint` as the element type unconditionally and
/// never consults what the elements typed as. Measured with the hint in place,
/// `takeReds([blue(v: 1)])` — the WRONG variant — LOADED CLEAN.
///
/// SO THE ASYMMETRY IS NOT THE DEFECT; the direction that "works" is the broken one. The
/// hole is general and predates this ticket, which is what the last row here shows: an
/// unhinted literal types from its elements and IS checked, while a hinted one is not, at
/// ANY element type. Filed as its own work item; until it is closed, a list of variants
/// stays refused at an argument rather than silently accepted.
#[test]
fn known_gap_a_list_literal_of_variants_is_refused_at_an_argument() {
    let src = r#"
namespace test.jsfhg.agg
  import anthill.prelude.{Int64, List}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeReds(l: List[T = Colour.red]) -> Int64 = 17
  operation viaArg() -> Int64 = takeReds([red(v: 1)])
end
"#;
    let errs = errs_of(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("expected List[T = red]") && e.contains("got List[T = Colour]")),
        "THE RESIDUAL: no hint is pushed into a list literal, deliberately — pushing one \
         would replace this refusal with a silent accept. If this row starts failing, check \
         FIRST that the wrong-variant program below is still refused; got {errs:#?}"
    );

    // THE SEPARATOR, and the reason the row above is a deliberate refusal rather than an
    // oversight: an UNHINTED list literal types from its elements and is checked.
    let unhinted = r#"
namespace test.jsfhg.agg2
  import anthill.prelude.{Int64, String, List}
  operation takeInts(l: List[T = Int64]) -> Int64 = 1
  operation wrong() -> Int64 = takeInts(["x"])
end
"#;
    assert!(
        !errs_of(unhinted).is_empty(),
        "an argument-position list literal takes no hint, so its elements decide its type \
         and a wrong one is caught — this is what a hint would have switched off"
    );

    // …and the HINTED direction, which is the actual defect: a declared return DOES hint,
    // and the elements are then never consulted at all. Nothing to do with variants.
    let hinted_return = r#"
namespace test.jsfhg.agg3
  import anthill.prelude.{Int64, String, List}
  operation mk() -> List[T = Int64] = ["x"]
end
"#;
    assert!(
        errs_of(hinted_return).is_empty(),
        "PINNING THE REAL DEFECT so closing it is loud here: a hinted list literal ignores \
         its elements, so a `List[T = Int64]` of strings loads. When this row starts \
         failing, the hole is closed and the argument-position hint can be restored"
    );
}

/// A NAMED-TUPLE COMPONENT CARRIES THE VARIANT — the third channel, and the one that was
/// refused in BOTH directions.
///
/// A tuple literal declares no fields of its own, so its components' declared types live in
/// the expected TUPLE and nowhere else; `field_types` is empty for `TupleLiteral` and every
/// existing hint reads it. Components are matched through the `_N` convention's owner
/// rather than by index, since the expected tuple's field list is positional-then-named and
/// an index would pair a positional component with a named field once both are present.
///
/// BACKED OUT: `expected (a: red, b: Int64), got (a: Colour, b: Int64)`.
#[test]
fn a_named_tuple_component_carries_the_variant() {
    let src = r#"
namespace test.jsfhg.tup
  import anthill.prelude.{Int64}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation mk() -> (a: Colour.red, b: Int64) = (a: red(v: 1), b: 2)
  operation takePair(p: (a: Colour.red, b: Int64)) -> Int64 = p.b
  operation viaArg() -> Int64 = takePair((a: red(v: 1), b: 23))
  operation viaReturn() -> Int64 = takePair(mk())
end
"#;
    load_clean(src, "a named tuple with a variant component");
    assert_eq!(drive(src, "test.jsfhg.tup.viaArg"), "Int(23)");
    assert_eq!(drive(src, "test.jsfhg.tup.viaReturn"), "Int(2)");
}

/// A MEMBER OF THE PARENT SORT IS REACHABLE BY DOT THROUGH A VARIANT RECEIVER.
///
/// THE POSITION-DEPENDENCE THIS CLOSES: a `Colour.red` value is a `Colour` (§8.2), and the
/// named spelling `Colour.shout(r)` resolved and the widening `takeAny(r)` was accepted —
/// but `r.shout()` reported *"no such member (dot dispatch)"*, because the three rungs
/// that search the receiver's sort search the CONSTRUCTOR, which declares no operations.
/// One value, two answers. Found by /code-review; the mechanism predates this ticket, but
/// making variant-typed values reachable is what put values in front of it.
///
/// DRIVEN THROUGH BOTH SPELLINGS with the same receiver, so a failure names which one
/// broke, and with the parent-typed receiver beside them as the shape that always worked.
///
/// BACKED OUT (the dot rung specifically — delete the `strict_parent_sort` arm before
/// `if let Some(op_sym)`): `viaDot` alone is refused, the other two still load.
#[test]
fn a_parent_member_is_reachable_by_dot_through_a_variant_receiver() {
    let src = r#"
namespace test.jsfhg.dot
  import anthill.prelude.{Int64}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
    operation shout(c: Colour) -> Int64 = c.v
  end
  operation viaDot(r: Colour.red) -> Int64 = r.shout()
  operation viaNamed(r: Colour.red) -> Int64 = Colour.shout(r)
  operation viaParent(c: Colour) -> Int64 = c.shout()
  operation driveDot() -> Int64 = viaDot(red(v: 3))
  operation driveNamed() -> Int64 = viaNamed(red(v: 4))
  operation driveParent() -> Int64 = viaParent(red(v: 5))
end
"#;
    load_clean(src, "a dot on a variant-typed receiver");
    assert_eq!(drive(src, "test.jsfhg.dot.driveDot"), "Int(3)");
    assert_eq!(drive(src, "test.jsfhg.dot.driveNamed"), "Int(4)");
    assert_eq!(drive(src, "test.jsfhg.dot.driveParent"), "Int(5)");
}

/// THE VARIANT'S OWN FIELD STILL BEATS A SAME-NAMED PARENT OPERATION.
///
/// The parent rung above is consulted only where every existing rung answered `None` — and
/// that is exactly where the frame would otherwise fall through to FIELD ACCESS. So without
/// a gate it would STEAL an entity's own field whenever the parent happens to declare an
/// operation of that name, silently changing what `r.v` means. The rung stands down when
/// the member names a field of the receiver entity.
///
/// THE VALUE IS THE ASSERTION, not loading: `5` is the field, `99` is the parent operation.
/// This row is an ARM for the ticket (the program needs the classification to load at all)
/// and its NUMBER is what measures the gate — back the gate out alone (drop the
/// `names_own_field` guard) and it answers 99 while still loading.
#[test]
fn a_variants_own_field_still_beats_a_same_named_parent_operation() {
    let src = r#"
namespace test.jsfhg.fieldwins
  import anthill.prelude.{Int64}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
    operation v(c: Colour) -> Int64 = 99
  end
  operation viaField(r: Colour.red) -> Int64 = r.v
  operation drive() -> Int64 = viaField(red(v: 5))
end
"#;
    load_clean(src, "a field shadowing a same-named parent operation");
    assert_eq!(
        drive(src, "test.jsfhg.fieldwins.drive"),
        "Int(5)",
        "the ENTITY's own field, not the parent's same-named operation (99) — the parent \
         dot rung must not steal a member the receiver itself has"
    );
}

/// KNOWN GAP — THE AUTO-`some` COERCION IS WITHHELD AT A VARIANT-TYPED FIELD. Passes either
/// way BY DESIGN; it records the one review finding this ticket does NOT close.
///
/// WI-408 wraps a bare value into `some(...)` for an `Option`-typed field, so
/// `holder(o: 5)` with `o: Option[T = Int64]` loads. With the field declared
/// `Option.some[T = Int64]` it is refused, even though the wrap would produce
/// `some[T = Int64]` — precisely the expected type. The coercion recognizer reads the
/// PARENT head, which is a fifth reader of the same question, and whether a slot that
/// demands `some` should silently manufacture one is a design question rather than an
/// oversight. Recorded here so it is measured rather than forgotten.
#[test]
fn known_gap_the_auto_some_coercion_is_withheld_at_a_variant_typed_field() {
    let src = r#"
namespace test.jsfhg.coerce
  import anthill.prelude.{Int64, Option, some}
  sort Holder
    entity holder(o: Option.some[T = Int64])
  end
  operation readIt(h: Holder) -> Int64 = 1
  operation drive() -> Int64 = readIt(holder(o: 5))
end
"#;
    let errs = errs_of(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("expected some[T = Int64]") && e.contains("got Int64")),
        "THE RESIDUAL: the WI-408 some-coercion reads the parent head, so it does not fire \
         where it would now be well-typed. If this row starts failing the gap has closed \
         and the module doc must be updated; got {errs:#?}"
    );
    // …and the parent-typed twin, which is what the coercion DOES serve — so the row says
    // "withheld here", not "the coercion is broken".
    let parent = src.replace("Option.some[T = Int64]", "Option[T = Int64]");
    load_clean(&parent, "the parent-typed field, where the coercion fires");
    assert_eq!(drive(&parent, "test.jsfhg.coerce.drive"), "Int(1)");
}

