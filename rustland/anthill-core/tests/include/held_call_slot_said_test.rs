//! A call that leaves a slot of its result open, where its callee owes a requirement at it, is
//! typed again where its value meets a type that says the slot: the parameter of the call it is
//! an argument of, or the other arm of a join (user, 2026-11-17: "fill after inference"). Its
//! dictionaries are then built at that type, as a written annotation would have built them.
//! Where nothing says the slot, an operation body's call is refused at load, naming the element:
//! a free type variable that owes a dictionary after typing.
//!
//! BACK-OUTS, each a temporary switch in one build, over this file, `map_keys_through_eq_test`,
//! `wi_jwcnn_tuple_equality_test` and `wi_2kv4y_unfixed_carrier_test` (86 rows):
//!   * the call held for its slot (`call_waits_for_its_slot`): 12 FAIL — every row here but
//!     the rewrite control and the coerced argument (the map rows die when run, `Map.empty`
//!     handed no `Eq`; the `TypeValue` row is refused, the element unconstrained; the
//!     said-type row loads, the arm answered at the one provider's `Int64`; the const row
//!     loads); `wi_2kv4y`'s `a_call_whose_slot_its_argument_position_says_runs_alike_in_both_spellings`
//!     (refused); and three of `map_keys_through_eq_test`'s, whose maps are made as an argument
//!     of `put` or nothing says their key (measured over 89 rows, after the review's rows);
//!   * the join saying an arm's slot: 3 FAIL — the two join rows and the refusal at the said
//!     type;
//!   * the parameter read through the call's other arguments alone: 1 FAILS,
//!     [`a_parameter_the_other_arguments_say`];
//!   * the refusal where nothing said the slot: 1 FAILS,
//!     `map_keys_through_eq_test::a_map_whose_key_type_nothing_says_is_refused` (loads).
//!
//! And over this file and `map_keys_through_eq_test` (15 rows), each part a review added:
//!   * a call in tail position read as the arm or argument alone (`tail_nodes`), a call that
//!     passes its argument on not saying it (the call typed again saying its own arguments, or
//!     reading them through the result it was said at): 1 FAILS each,
//!     [`a_call_in_tail_position_is_said_through_the_forms_around_it`];
//!   * a type not read down a construction's fields, or a construction's own fields not saying
//!     the calls written in them: 1 FAILS each,
//!     [`a_call_inside_a_construction_is_said_through_its_fields`];
//!   * a call built again by its second typing refused, where its stamps now reach the node its
//!     parent holds: 1 FAILS, [`a_call_with_a_coerced_argument_is_typed_again_in_place`];
//!   * the refusal judged in an operation's body alone: 1 FAILS,
//!     [`a_const_whose_map_nothing_keys_is_refused`] (loads, and dies when the const is read).
//!
//! [`a_call_a_rewrite_takes_out_is_not_judged`] passes either way by design: it bounds the
//! refusal.

use anthill_core::eval::Value;

use crate::common::{assert_refused_naming, interp_for, load_errors_of, show_value};

/// What each entry answers, printed; a load refusal fails the row.
fn answers(src: &str, entries: &[&str]) -> Vec<String> {
    let errs = load_errors_of(src);
    assert!(errs.is_empty(), "the program must load: {errs:#?}");
    let mut interp = interp_for(src);
    entries
        .iter()
        .map(|entry| match interp.call(entry, &[]) {
            Ok(v) => show_value(interp.kb(), &v),
            Err(e) => panic!("{entry}: {e:?}"),
        })
        .collect()
}

/// `Map.empty()` as the first argument of `put`: its `K` is the `String` the key argument gives
/// `put`'s, and the map is made under `String`'s `Eq`.
#[test]
fn a_map_made_as_an_argument_is_keyed_at_the_parameter() {
    let src = r#"
namespace test.held.arg
  import anthill.prelude.{Int64, Bool, Map}
  operation one() -> Int64 = Map.size(Map.put(Map.empty(), "a", 1))
  operation two() -> Int64 = Map.size(Map.put(Map.put(Map.empty(), "a", 1), "b", 2))
end
"#;
    assert_eq!(answers(src, &["test.held.arg.one", "test.held.arg.two"]), ["1", "2"]);
}

/// An arm whose `Map.empty()` fixes nothing, beside one that fixes `Map[String, Int64]`: the
/// join says the first arm's slots, and its map is made at them — in an `if` and in a `match`.
#[test]
fn a_map_an_arm_leaves_open_is_keyed_at_the_join() {
    let src = r#"
namespace test.held.join
  import anthill.prelude.{Int64, Bool, String, Map}
  operation fill(acc: Map[String, Int64]) -> Map[String, Int64] = Map.put(acc, "a", 1)
  operation viaIf(b: Bool) -> Int64 =
    let m = if b then Map.empty() else fill(Map.empty())
    Map.size(m)
  operation viaMatch(b: Bool) -> Bool =
    let m = match b
      case true -> Map.empty()
      case false -> fill(Map.empty())
    Map.contains(m, "a")
  operation ifOpen() -> Int64 = viaIf(true)
  operation ifFilled() -> Int64 = viaIf(false)
  operation matchOpen() -> Bool = viaMatch(true)
  operation matchFilled() -> Bool = viaMatch(false)
end
"#;
    assert_eq!(
        answers(
            src,
            &[
                "test.held.join.ifOpen",
                "test.held.join.ifFilled",
                "test.held.join.matchOpen",
                "test.held.join.matchFilled"
            ]
        ),
        ["0", "1", "false", "true"]
    );
}

/// `foldLeft(names, Map.empty(), add)`: the open map binds the fold's `Acc` first, so the call's
/// σ reads it back open; `add`'s type says `Map[String, Int64]`, and the map is made at it.
#[test]
fn a_parameter_the_other_arguments_say() {
    let src = r#"
namespace test.held.others
  import anthill.prelude.{Int64, String, List, Map}
  import anthill.prelude.List.{foldLeft}
  operation add(acc: Map[String, Int64], name: String) -> Map[String, Int64] = Map.put(acc, name, 1)
  operation count() -> Int64 = Map.size(foldLeft(["a", "b", "a"], Map.empty(), add))
end
"#;
    assert_eq!(answers(src, &["test.held.others.count"]), ["2"]);
}

/// The same at a `TypeValue` requirement: `Bx.mk()` in the first arm fixes nothing of `T`,
/// the second arm says `Int64`, and the first arm's value is a box at `Int64`. Refused before,
/// the element unconstrained at the call.
#[test]
fn a_type_value_an_arm_leaves_open_is_answered_at_the_join() {
    let src = r#"
namespace test.held.tv
  import anthill.prelude.{Int64, Bool, Type, List}
  import anthill.prelude.List.{nil}
  import anthill.reflect.{TypeValue}
  sort Bx
    sort T = ?
    entity bx(items: List[T = T], tag: Type)
    operation mk() -> Self requires TypeValue[T = T] = bx(items: nil(), tag: TypeValue.type_value[T = T]())
    operation tagOf(b: Self) -> Type = match b case bx(items, tag) -> tag
  end
  operation fill(b: Bx[T = Int64]) -> Bx[T = Int64] = b
  operation joined(c: Bool) -> Type =
    let b = if c then Bx.mk() else fill(Bx.mk())
    Bx.tagOf(b)
  operation first() -> Type = joined(true)
  operation second() -> Type = joined(false)
  operation viaArg() -> Type = Bx.tagOf(fill(Bx.mk()))
end
"#;
    assert_eq!(
        answers(src, &["test.held.tv.first", "test.held.tv.second", "test.held.tv.viaArg"]),
        ["Int64", "Int64", "Int64"]
    );
}

/// A call typed again where its slot is said owes its requirement at the said type: `Bx.mk()`
/// beside a `Bx[T = String]` owes `Tag[T = String]`, which nothing provides — refused at the
/// call. Before, the one provider completed the element and the arm ran with `Int64`'s `Tag`.
/// The `Int64` twin runs.
#[test]
fn a_call_typed_again_is_refused_where_the_said_type_has_no_instance() {
    let decls = r#"
  import anthill.prelude.{Int64, Bool, String, List}
  import anthill.prelude.List.{nil}
  sort Tag
    sort T = ?
    operation tag() -> Int64
  end
  sort IntTag
    provides Tag[T = Int64]
    operation tag() -> Int64 = 7
  end
  sort Bx
    sort T = ?
    entity bx(items: List[T = T], n: Int64)
    operation mk() -> Self requires Tag[T = T] = bx(items: nil(), n: Tag.tag[T = T]())
    operation num(b: Self) -> Int64 = match b case bx(items, n) -> n
  end
"#;
    let at_string = format!(
        "namespace test.held.said\n{decls}  operation givenS() -> Bx[T = String] = Bx.bx(items: nil(), n: 3)\n  \
         operation atString(c: Bool) -> Int64 =\n    let b = if c then Bx.mk() else givenS()\n    Bx.num(b)\nend\n"
    );
    assert_refused_naming(
        &load_errors_of(&at_string),
        &[
            "`test.held.said.Tag[T = anthill.prelude.String]`",
            "cannot be supplied for call to `test.held.said.Bx.mk`",
        ],
        "an arm said at a type its requirement has no instance at",
    );
    let at_int = format!(
        "namespace test.held.saidint\n{decls}  operation fillI(b: Bx[T = Int64]) -> Bx[T = Int64] = b\n  \
         operation atInt(c: Bool) -> Int64 =\n    let b = if c then Bx.mk() else fillI(Bx.mk())\n    Bx.num(b)\n  \
         operation open() -> Int64 = atInt(true)\nend\n"
    );
    assert_eq!(answers(&at_int, &["test.held.saidint.open"]), ["7"]);
}

/// CONTROL — a call a `@[simp]` rewrite takes out of the body is no call of the program, and is
/// not judged for what nothing said: `Map.size(Map.empty())` is `0`.
#[test]
fn a_call_a_rewrite_takes_out_is_not_judged() {
    let src = r#"
namespace test.held.folded
  import anthill.prelude.{Int64, Map}
  operation zero() -> Int64 = Map.size(Map.empty())
end
"#;
    let mut interp = interp_for(src);
    assert!(load_errors_of(src).is_empty());
    assert!(matches!(interp.call("test.held.folded.zero", &[]), Ok(Value::Int(0))));
}

/// What the value meets says a call in TAIL position of the arm or argument as well: the body
/// of a `let`, each branch of a nested `if`, and a call that passes its argument on (`idm`,
/// which owes nothing itself). Refused before, the element unconstrained.
#[test]
fn a_call_in_tail_position_is_said_through_the_forms_around_it() {
    let src = r#"
namespace test.held.tail
  import anthill.prelude.{Int64, Bool, String, Map}
  operation fill(acc: Map[String, Int64]) -> Map[String, Int64] = Map.put(acc, "a", 1)
  operation idm[A](x: A) -> A = x
  operation letArm(b: Bool) -> Int64 =
    let m = match b
      case true ->
        let a = 1
        Map.empty()
      case false -> fill(Map.empty())
    Map.size(m)
  operation nestedArm(b: Bool, c: Bool) -> Int64 =
    let m = if b then (if c then Map.empty() else Map.empty()) else fill(Map.empty())
    Map.size(m)
  operation passThrough() -> Int64 = Map.size(fill(idm(Map.empty())))
  operation r1() -> Int64 = letArm(true)
  operation r2() -> Int64 = nestedArm(true, false)
  operation r3() -> Int64 = passThrough()
end
"#;
    assert_eq!(
        answers(src, &["test.held.tail.r1", "test.held.tail.r2", "test.held.tail.r3"]),
        ["0", "0", "1"]
    );
}

/// A field of a construction says the call written there (`bx(m: Map.empty())`, at the sort's
/// own `T` under its `requires Hash[T = T]`), and a type a construction meets is read down to its
/// fields: `some(…)`, a list literal's elements, a tuple's components. A call that waits inside
/// a call that waits is said when the outer one is (`wrap(mk())`).
#[test]
fn a_call_inside_a_construction_is_said_through_its_fields() {
    let src = r#"
namespace test.held.ctor
  import anthill.prelude.{Int64, String, Map, Option, List, Hash}
  import anthill.prelude.Option.{some, none}
  sort Bx
    sort T = ?
    entity bx(m: Map[K = T, V = Int64])
    operation mk() -> Self requires Hash[T = T] = bx(m: Map.empty())
    operation wrap(b: Self) -> Self requires Hash[T = T] = b
    operation size(b: Self) -> Int64 = match b case bx(m) -> Map.size(m)
  end
  operation fillS(b: Bx[T = String]) -> Bx[T = String] = b
  operation nested() -> Int64 = Bx.size(fillS(Bx.wrap(Bx.mk())))
  operation takesOpt(o: Option[T = Map[String, Int64]]) -> Int64 =
    match o case some(m) -> Map.size(Map.put(m, "a", 1)) case none() -> 0
  operation takesList(xs: List[T = Map[String, Int64]]) -> Int64 = List.length(xs)
  operation takesPair(p: (a: Map[String, Int64], b: Int64)) -> Int64 = Map.size(Map.put(p.a, "x", 1))
  operation viaOpt() -> Int64 = takesOpt(some(Map.empty()))
  operation viaList() -> Int64 = takesList([Map.empty(), Map.empty()])
  operation viaPair() -> Int64 = takesPair((a: Map.empty(), b: 2))
end
"#;
    assert_eq!(
        answers(
            src,
            &[
                "test.held.ctor.nested",
                "test.held.ctor.viaOpt",
                "test.held.ctor.viaList",
                "test.held.ctor.viaPair"
            ]
        ),
        ["0", "1", "2", "1"]
    );
}

/// A call typed again whose argument the typing wraps in `some(…)` once more is the same call:
/// its typing reaches the node its parent holds. It was refused, "a call this typer rewrote".
#[test]
fn a_call_with_a_coerced_argument_is_typed_again_in_place() {
    let src = r#"
namespace test.held.coerce
  import anthill.prelude.{Int64, Bool, String, Option, Eq}
  sort Bx
    sort T = ?
    entity bx(n: Int64)
    operation mko(o: Option[T = Int64]) -> Self requires Eq[T = T] = bx(n: 1)
    operation num(b: Self) -> Int64 = match b case bx(n) -> n
  end
  operation fillS(b: Bx[T = String]) -> Bx[T = String] = b
  operation coerce(c: Bool) -> Int64 = Bx.num(if c then Bx.mko(5) else fillS(Bx.mko(5)))
  operation open() -> Int64 = coerce(true)
end
"#;
    assert_eq!(answers(src, &["test.held.coerce.open"]), ["1"]);
}

/// A const's value is a body the evaluator runs too: a map in it whose key type nothing says is
/// refused at load. It loaded, and died when the const was read.
#[test]
fn a_const_whose_map_nothing_keys_is_refused() {
    let src = r#"
namespace test.held.konst
  import anthill.prelude.{Int64, Map}
  const k: Int64 =
    let x = Map.empty()
    Map.size(x)
end
"#;
    assert_refused_naming(
        &load_errors_of(src),
        &[
            "`anthill.prelude.Hash[T = anthill.prelude.Map.K]`",
            "element `T = anthill.prelude.Map.K` is unconstrained at this call site",
        ],
        "a const's map no type is said for",
    );
}
