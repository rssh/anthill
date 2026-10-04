//! WI-20261001-80ZV8, stage (c), part 6 — TWO WRITTEN RECEIVERS, AND A VALUE WHOSE TYPE IS BARE.
//!
//! `operation append(xs: Self, ys: Self) -> Self` could not be written. A list of lists whose
//! inner list is `nil` has the element type `List` — bare, the element unknown — and a call
//! handing `append` one such list and one of `List[T = Int64]`s was refused: `expected
//! consistent bindings for the sort's shared type parameter (first bound to List), got
//! Int64`. The first argument bound the callee's `T` to that bare `List`; comparing it with
//! the second's `List[T = Int64]` went through the unifier's bare-reference arm, which
//! writes the instance it meets into the sort's CANONICAL parameter variables — and in a
//! call to one of `List`'s own operations those are the callee's parameters. `T` was
//! written with the element of its own element.
//!
//! That arm serves a DECLARED bare reference (`reverse(xs: List)` reaches its argument's
//! element through it). A callee whose signature writes every reference to its own sort has
//! none, so for that call a bare reference to the callee's sort is a value's type, compatible
//! by width, and binds nothing (`Substitution::written_sort`, set by `check_apply_iter`,
//! read by `unify_parameterized_with_sort_ref`). The stdlib's `List.append` is written with
//! `Self` since this change — the last of its 135 references.
//!
//! The arm itself stays for everything else that rides it; it goes at proposal 070's stage
//! (e). The user agreed to move this much forward (2026-10-03).
//!
//! Every row RUNS and names its value.
//!
//! ── WHICH ROWS FAIL WHEN IT IS BACKED OUT ────────────────────────────────────
//!
//! MEASURED (2026-10-03), the call no longer marking its substitution (`check_apply_iter`
//! leaving `Substitution::written_sort` unset), over this file's 5 rows: 3 FAIL —
//! [`two_written_receivers_take_a_list_whose_element_type_is_bare`],
//! [`a_bare_typed_element_is_taken_beside_a_written_receiver`] and
//! [`the_stdlibs_append_takes_them`], each `expected consistent bindings for the sort's
//! shared type parameter` — and with them `wi374_expansion_test::member_tie_refinement_
//! accepted`, the stdlib's `append` on the same call.
//!
//! Two pass either way by design and say so at their sites:
//! [`two_written_receivers_are_still_one_instance`] and
//! [`a_receiver_still_declared_bare_keeps_its_reading`].

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// `MyList` with two-receiver `append` and an element test, all written with `Self`; `rest`
/// is what follows the sort.
fn list_program(ns: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool}}
  sort MyList
    sort T = ?
    entity mnil
    entity mcons(head: T, tail: Self)
    operation len(xs: Self) -> Int64 =
      match xs
        case mnil() -> 0
        case mcons(_, rest) -> 1 + len(rest)
    operation append(xs: Self, ys: Self) -> Self =
      match xs
        case mnil() -> ys
        case mcons(h, rest) -> mcons(head: h, tail: append(rest, ys))
    operation count(xs: Self, x: T) -> Int64 = len(xs)
  end
{rest}
end
"#
    )
}

/// A list holding one empty list, and a list holding one list of an `Int64`.
const OF_NIL: &str = "mcons(head: mnil, tail: mnil)";
const OF_INTS: &str = "mcons(head: mcons(head: 1, tail: mnil), tail: mnil)";

/// THE CALL THE STDLIB'S OWN TEST MAKES (`wi374 member_tie_refinement_accepted`), on a sort
/// of this file's: a list whose element is the bare `MyList` of `mnil`, appended to a list
/// of `MyList[T = Int64]`s. Runs, both ways round — the second order bound `T` to the
/// applied type first and met the bare one after, and was refused the same way.
#[test]
fn two_written_receivers_take_a_list_whose_element_type_is_bare() {
    for (ns, call) in [
        ("wi80zv8w.a1", format!("MyList.append({OF_NIL}, {OF_INTS})")),
        ("wi80zv8w.a2", format!("MyList.append({OF_INTS}, {OF_NIL})")),
    ] {
        let src = list_program(ns, &format!("  operation go() -> Int64 = MyList.len({call})"));
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(2), "{call}");
    }
}

/// …AND A RECEIVER BESIDE AN ELEMENT: `count(xs: Self, x: T)` over a list of
/// `MyList[T = Int64]`s, asked about `mnil`. The element argument's bare type met `T`'s
/// applied one through the same arm.
#[test]
fn a_bare_typed_element_is_taken_beside_a_written_receiver() {
    let src = list_program(
        "wi80zv8w.b1",
        &format!("  operation go() -> Int64 = MyList.count({OF_INTS}, mnil)"),
    );
    assert_eq!(run_src(&src, "wi80zv8w.b1.go"), Ok(1));
}

/// THE STDLIB'S `append`, written with `Self`: the same two calls on `List`.
#[test]
fn the_stdlibs_append_takes_them() {
    let src = r#"
namespace wi80zv8w.s1
  import anthill.prelude.{Int64, List}
  import anthill.prelude.List.{nil, cons}
  operation go() -> Int64 =
    List.length(List.append(cons(head: nil, tail: nil), cons(head: cons(head: 1, tail: nil), tail: nil))) * 10
      + List.length(List.append(cons(head: cons(head: 1, tail: nil), tail: nil), cons(head: nil, tail: nil)))
end
"#;
    assert_eq!(run_src(src, "wi80zv8w.s1.go"), Ok(22));
}

/// CONTROL — TWO RECEIVERS ARE STILL ONE INSTANCE. A list of `Int64`s appended to a list of
/// `String`s is refused at the second argument, by the written `Self` (proposal 070 §5).
/// Passes with or without the change by design: nothing here is bare.
#[test]
fn two_written_receivers_are_still_one_instance() {
    let src = list_program(
        "wi80zv8w.c1",
        "  operation go() -> Int64 =\n    MyList.len(MyList.append(mcons(head: 1, tail: mnil), mcons(head: \"s\", tail: mnil)))",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["append.ys (op-arg): expected MyList[T = Int64], got MyList[T = String]"],
        "a list of Int64 appended to a list of String",
    );
}

/// A RECEIVER DECLARED BARE — this file's control, when the bare name was this instance.
/// `keep(xs: Old) -> Old` kept the unifier's canonical channel, since the change is for a
/// signature that writes its sort, and the row passed with or without it by design. Since
/// the user's 2026-10-04 decision the bare name is the sort at `?` inside its own definition
/// (proposal 070 §1.3): `keep` takes ANY `Old` and returns one the operation picks, so its
/// result is no `Old[T = Int64]` to the annotation that asks for one — where `Self` is this
/// instance, and reads as the control did. (The loader writes the `?`, so no loaded member
/// reaches the channel with its own sort left out; it is deleted at stage (e).)
#[test]
fn a_receiver_declared_bare_is_any_instance_and_written_self_is_this_one() {
    let program = |ns: &str, own: &str, annotated: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Old
    sort T = ?
    entity onil
    entity ocons(head: T, tail: {own})
    operation keep(xs: {own}) -> {own} = xs
    operation olen(xs: {own}) -> Int64 =
      match xs
        case onil() -> 0
        case ocons(_, rest) -> 1 + olen(rest)
  end
  operation go() -> Int64 =
    let kept: Old[T = {annotated}] = Old.keep(ocons(head: 1, tail: onil))
    Old.olen(kept)
end
"#
        )
    };
    assert_refused_naming(
        &load_errors(&program("wi80zv8w.d0", "Old", "Int64")),
        &["kept.annotation (let-binding): expected Old[T = Int64], got Old[T = ?T]"],
        "the result of a member whose receiver and return name the sort bare",
    );
    assert_eq!(run_src(&program("wi80zv8w.d1", "Self", "Int64"), "wi80zv8w.d1.go"), Ok(1));
    assert_refused_naming(
        &load_errors(&program("wi80zv8w.d2", "Self", "String")),
        &["kept.annotation (let-binding): expected Old[T = String], got Old[T = Int64]"],
        "a kept list of Int64 read as a list of String",
    );
}
