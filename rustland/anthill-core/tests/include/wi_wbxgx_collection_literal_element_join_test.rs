//! WI-20260829-WBXGX — A COLLECTION LITERAL'S ELEMENT TYPE IS THE JOIN OF ITS ELEMENTS.
//!
//! ## The defect
//!
//! Where nothing declares an element type, the literal took ELEMENT ONE's and every later
//! element rode free:
//!
//! ```text
//! takes_list([1, "a"])          LOADED      ← a String in an Int64 slot
//! takes_list(["a", 1])          refused, `expected List[T = Int64], got List[T = String]`
//! ```
//!
//! The same two elements in the other order. That asymmetry is the tell: nothing was being
//! combined across the elements at all. The literal's own SHAPE was still checked
//! (`takes_set([1, 2])` is refused `expected Set[…], got List[…]`), which is why this read
//! as "loads clean" rather than "nothing is checked" and why it survived so long.
//!
//! WI-20260826-7JDWY is the other half and does NOT cover this: it fixed the route where a
//! position DECLARES an element type. This is the route that ticket's own table uses as its
//! control.
//!
//! ## THE TICKET PRESCRIBED THE WRONG REPAIR, AND ITS REASON WAS FALSE
//!
//! It asked for "unifying element `i`'s against the accumulated `T` and refusing at the
//! first that does not", and justified that with "Anthill has no join today, so refusing at
//! the first mismatch is the answer unless one is added". It has one: [`join_types`], which
//! `compute_branch_join_type` already gives `if` and `match` arms — the neighbouring
//! construct that asks this exact question of several expressions at once.
//!
//! AND THE PRESCRIBED REPAIR KEEPS AN ORDER-DEPENDENCE, only a different one. BUILT AND
//! MEASURED, not predicted: with the subtype-against-element-one version in place,
//!
//! ```text
//! takeColours([r, c])   r: Colour.red, c: Colour   REFUSED  `expected red, got Colour`
//! takeColours([c, r])                              LOADS
//! ```
//!
//! — the same two values, the same two verdicts by order, which is precisely the tell the
//! ticket used to identify the defect. Under the join both load, and
//! `the_element_type_is_a_join_so_it_does_not_depend_on_order` is the row that separates
//! the two repairs.
//!
//! ## THE WIDENING DIRECTION IS INERT ON THIS CORPUS, and that is stated rather than
//! claimed
//!
//! Instrumented over the whole workspace suite before the change: **4** literals reach the
//! element-vs-element comparison at all, and **every one CLASHES** — none widens. So the
//! join's ability to return a common supertype is exercised only by this file's own rows,
//! and the order-independence pair is the one witness that the join is doing something a
//! first-element rule would not. There is no corpus program whose TYPE this widens.
//!
//! ## THREE BACK-OUTS, because there are three claims — whole `wi_tests` binary, each a run
//!
//! **A. Is anything combined at all?** Replace the `join_types` call in
//! `seq_literal_element_type`'s `None` arm with `Some(acc)` — element one's type, nothing
//! checked, the pre-ticket reading. **7 fail, 4242 pass**: the four arms here, plus
//! `typer_capability_matrix_test::the_row_remainders` (whose two cells recorded this hole
//! as `SilentlyAccepted`), `wi_7jdwy_…::control_an_unhinted_literal_still_types_from_its_-
//! elements` (whose residual `load_clean` was PINNING this item and is the assertion that
//! failed the day it closed), and `wi_7jdwy_…::a_rival_collection_declares_no_element_type`,
//! whose mixed-element half reaches this arm because a `Set` declaration is not a `[…]`'s.
//!
//! **B. Is it a JOIN, or a subtype test against element one?** Replace the join with the
//! ticket's own prescription. **1 fails, 4248 pass** — exactly
//! `the_element_type_is_a_join_so_it_does_not_depend_on_order`, and nothing else in the
//! binary. That single row IS the difference between the two designs; every other row here
//! is satisfied by either, which is why it exists.
//!
//! **C. Does the VALUE carrier join too?** Restore `pos_child_types.first()` in
//! `seq_literal_value_type`. **1 fails, 4248 pass** —
//! `the_value_carrier_joins_its_elements_too`. It is its own axis because it is its own
//! function: `/code-review` found it still reading element one after the other three
//! carriers were fixed, and a back-out of A leaves it untouched.
//!
//! Note what A does NOT fail: the order-independence row passes under it, because element
//! one's type (`red`) is a subtype of the declared `Colour` and both orders loaded before
//! this ticket too. A row that separates B cannot also separate A, and this one says which
//! it is.
//!
//! ## CONTROLS — green either way, by design
//!
//! `control_a_homogeneous_literal_is_unchanged` (the overwhelming majority of literals, and
//! what says this is not "mixed literals are now hard"),
//! `control_the_literals_own_shape_is_still_checked` (a `[…]` in a `Set` slot is still a
//! shape mismatch, so a green row here is not "nothing is checked" ),
//! `control_a_declared_element_type_still_takes_the_other_route` (the two tags stay apart),
//! and `control_the_branch_join_answers_the_same_clash_the_same_way` (the borrowed relation
//! is the one `if` uses, which is why it is not a second opinion).

use anthill_core::eval::value::Value as EvalValue;
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term::Term;
use anthill_core::kb::typing::{sort_functor_of_view, value_type_term};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse::desugar_target as dt;

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

const LIST_HOST: &str = r#"
namespace test.wbxgx.list
  import anthill.prelude.{Int64, String, Bool, List}
  operation takes_list(l: List[T = Int64]) -> Int64 = List.length(l)
"#;

/// THE TICKET'S FIRST ROW — a later element that does not join is refused, AT ITS OWN SPAN.
///
/// BACKED OUT: loads clean, with a `String` sitting in a slot the signature types `Int64`.
#[test]
fn a_later_element_that_does_not_join_is_refused() {
    let src = format!("{LIST_HOST}  operation a() -> Int64 = takes_list([1, \"a\"])\nend\n");
    assert_reports(
        &src,
        "list.element 2 (collection-element-join): expected Int64, got String",
        "a `String` after an `Int64`",
    );
}

/// EVERY later element is reached, not just the second — the accumulator carries forward.
///
/// BACKED OUT: loads clean. The third element is the one that clashes, so a repair that
/// only compared element two against element one would pass this row while failing the one
/// above; both are here because neither implies the other.
#[test]
fn the_check_reaches_past_the_second_element() {
    let src = format!("{LIST_HOST}  operation a() -> Int64 = takes_list([1, 2, \"a\"])\nend\n");
    assert_reports(
        &src,
        "list.element 3 (collection-element-join): expected Int64, got String",
        "the THIRD element, after two that agree",
    );
}

/// THE SET SURFACE — the same rule on the other literal, which is what says this is the
/// literal's typing and not a `List` fact (the ticket's own reasoning).
///
/// BACKED OUT: loads clean.
#[test]
fn the_set_surface_is_checked_the_same_way() {
    let src = r#"
namespace test.wbxgx.set
  import anthill.prelude.{Int64, String, Set}
  operation takes_set(s: Set[T = Int64]) -> Int64 = 1
  operation a() -> Int64 = takes_set({1, "a"})
end
"#;
    assert_reports(
        src,
        "set.element 2 (collection-element-join): expected Int64, got String",
        "a `String` after an `Int64` in a set literal",
    );
}

/// THE REVERSED PAIR WAS ALREADY REFUSED, AND IS NOW REFUSED AT THE ELEMENT — the two
/// orders have stopped disagreeing, which is the whole claim.
///
/// This row is about the MESSAGE, because the verdict did not move: `["a", 1]` typed as
/// `List[T = String]` and the ARGUMENT check refused it, naming the whole list. The
/// asymmetry was that its mirror image loaded.
///
/// BACKED OUT: still refused, but as `takes_list.l (op-arg): expected List[T = Int64], got
/// List[T = String]` — so this row fails on the tag and the position, and the row above
/// fails on the verdict. Together they say the two orders now agree.
#[test]
fn the_reversed_pair_is_refused_at_the_element_too() {
    let src = format!("{LIST_HOST}  operation a() -> Int64 = takes_list([\"a\", 1])\nend\n");
    assert_reports(
        &src,
        "list.element 2 (collection-element-join): expected String, got Int64",
        "the mirror image of the row above, now refused in the same place",
    );
}

/// THE ELEMENT TYPE IS A JOIN, SO IT DOES NOT DEPEND ON ORDER — the row that separates this
/// repair from the one the ticket prescribed.
///
/// Both orders must LOAD and DRIVE. Under a subtype test against element one — the ticket's
/// prescription, BUILT AND RUN — `ab` is refused `list.element 2: expected red, got Colour`
/// while `ba` loads: the same two values, two verdicts by order, which is the defect this
/// item exists to remove rather than to re-spell.
///
/// It passes on the PRE-change tree too, and says so: element one's type (`red`) is a
/// subtype of the declared `Colour`, so `ab` loaded there as well. Its job is to fail the
/// WRONG repair, which is a thing only a control can do.
#[test]
fn the_element_type_is_a_join_so_it_does_not_depend_on_order() {
    let src = r#"
namespace test.wbxgx.order
  import anthill.prelude.{Int64, List}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation takeColours(l: List[T = Colour]) -> Int64 = List.length(l)
  operation viaAb(r: Colour.red, c: Colour) -> Int64 = takeColours([r, c])
  operation viaBa(r: Colour.red, c: Colour) -> Int64 = takeColours([c, r])
  operation ab() -> Int64 = viaAb(red(v: 1), blue(v: 2))
  operation ba() -> Int64 = viaBa(red(v: 1), blue(v: 2))
end
"#;
    load_clean(src, "a variant and its parent in a literal, in both orders");
    assert_eq!(
        drive(src, "test.wbxgx.order.ab"),
        "Int(2)",
        "VARIANT FIRST — the order the ticket's prescribed repair refuses",
    );
    assert_eq!(
        drive(src, "test.wbxgx.order.ba"),
        "Int(2)",
        "PARENT FIRST — which that repair accepts, and that difference is the defect",
    );
}

/// CONTROL — a homogeneous literal is untouched, and DRIVEN so the row is about a value and
/// not about a load. Green either way by design; it is what says this is not "mixed
/// literals became hard".
#[test]
fn control_a_homogeneous_literal_is_unchanged() {
    let src = format!("{LIST_HOST}  operation a() -> Int64 = takes_list([1, 2, 3])\nend\n");
    load_clean(&src, "a homogeneous literal");
    assert_eq!(drive(&src, "test.wbxgx.list.a"), "Int(3)");
}

/// CONTROL — the literal's own SHAPE is still checked, so a green row above cannot be read
/// as "the literal is unchecked". Green either way.
#[test]
fn control_the_literals_own_shape_is_still_checked() {
    let src = r#"
namespace test.wbxgx.shape
  import anthill.prelude.{Int64, List, Set}
  operation takes_set(s: Set[T = Int64]) -> Int64 = 1
  operation a() -> Int64 = takes_set([1, 2])
end
"#;
    assert_reports(
        src,
        "takes_set.s (op-arg): expected Set[T = Int64], got List[T = Int64]",
        "a LIST literal in a `Set` slot is a shape mismatch, and always was",
    );
}

/// CONTROL — a DECLARED element type still takes WI-20260826-7JDWY's route and says so in
/// its tag. Green either way; it is what keeps the two questions apart in the diagnostic,
/// since `expected Int64, got String` means something different depending on where the
/// `Int64` came from.
#[test]
fn control_a_declared_element_type_still_takes_the_other_route() {
    let src = r#"
namespace test.wbxgx.declared
  import anthill.prelude.{Int64, String, List}
  operation mk() -> List[T = Int64] = ["x"]
end
"#;
    let errs = errs_of(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("list.element 1 (collection-element):")),
        "a DECLARED element type reports `collection-element`, not `-join`; got {errs:#?}"
    );
}

/// CONTROL — the relation is BORROWED, not invented: the same clash under an `if` is
/// refused too, by `compute_branch_join_type`, which is where `join_types` already lived.
/// Green either way, and it is the row that says the literal did not acquire a second
/// opinion about when two types have no common supertype.
#[test]
fn control_the_branch_join_answers_the_same_clash_the_same_way() {
    let src = r#"
namespace test.wbxgx.branch
  import anthill.prelude.{Int64, String, Bool}
  operation j(b: Bool) -> Int64 = if b then 1 else "a"
end
"#;
    assert_reports(
        src,
        "if.rule (rule): expected Int64, got String",
        "the `if` arms of the same two types clash under the SAME join",
    );
}

/// THE VALUE CARRIER JOINS TOO — the fourth site, and the one `/code-review` found still
/// reading element ONE after the other three were fixed.
///
/// `value_type_term` types a RUNTIME value: a `ListLiteral(1, "a")` that SLD built, with no
/// program text behind it. It answered `List[T = Int64]` — a `String` inside a type that
/// says `Int64`, this ticket's defect in the one place a value can be inspected at runtime.
///
/// IT FLOUNDERS RATHER THAN ERRORING, which is the difference from the occurrence path: the
/// value exists, so there is no program to refuse, and "under-determined" is the honest
/// answer. That is the M6 / WI-067 convention the value typer already follows for a cyclic
/// or over-deep value. So the assertion is that the element type has stopped being a SORT,
/// not that it is some other sort.
///
/// BACKED OUT (restore `pos_child_types.first()`): the homogeneous half still passes and
/// the mixed half reports `Int64` again — which is what says this row measures the join and
/// not the literal's head.
#[test]
fn the_value_carrier_joins_its_elements_too() {
    let mut kb = crate::common::load_stdlib_kb();
    let subst = Substitution::new();

    let homogeneous = literal_value(&kb, vec![EvalValue::Int(1), EvalValue::Int(2)]);
    let ty = value_type_term(&mut kb, &subst, &homogeneous);
    assert_eq!(
        element_sort_name(&kb, &ty),
        Some("Int64".to_string()),
        "CONTROL — a homogeneous runtime value is unmoved",
    );

    let mixed = literal_value(&kb, vec![EvalValue::Int(1), EvalValue::Str("a".into())]);
    let ty = value_type_term(&mut kb, &subst, &mixed);
    assert_eq!(
        sort_functor_of_view(&kb, &ty).map(|s| kb.local_name_of(s).to_string()),
        Some("List".to_string()),
        "still a `List` — the literal's SHAPE was never in doubt",
    );
    assert_eq!(
        element_sort_name(&kb, &ty),
        None,
        "a heterogeneous runtime value has an UNDER-DETERMINED element type, not element \
         one's — a free variable names no sort",
    );
}

/// A `ListLiteral` runtime value, the shape `value_type_term` reads (WI-578's own fixture).
fn literal_value(kb: &KnowledgeBase, elems: Vec<EvalValue>) -> EvalValue {
    EvalValue::Entity {
        functor: kb.resolve_symbol(dt::qualified(dt::LIST_LITERAL)),
        pos: elems.into(),
        named: vec![].into(),
    }
}

/// The local name of the sort in the type's single binding, or `None` when the binding
/// names no sort (a type variable — the floundered answer).
fn element_sort_name(kb: &KnowledgeBase, ty: &EvalValue) -> Option<String> {
    let Term::Fn { named_args, .. } = kb.get_term(ty.expect_term()) else {
        return None;
    };
    named_args
        .iter()
        .find_map(|(_, p)| sort_functor_of_view(kb, &EvalValue::term(*p)))
        .map(|s| kb.local_name_of(s).to_string())
}
