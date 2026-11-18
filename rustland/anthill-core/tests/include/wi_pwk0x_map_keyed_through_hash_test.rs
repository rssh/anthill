//! A `Map` keys through `Hash[T = K]` (library proposal 001-map, phase 2a): `Map requires
//! Hash[T = K]`, `Map.empty()` is handed the instance and the map keeps it. A key no `eq` of
//! its own reaches is keyed by its structure; one whose sort writes its own `eq` is hashed
//! through the instance and compared through `eq` with the stored keys of its bucket alone,
//! so a map never compares a key with every stored one (user, 2026-11-17: "Map with O(n) is
//! unacceptable"). `Hash` is derived where `Eq` is structural and written beside an own `eq`.
//!
//! BACK-OUTS, each a temporary switch in one build (`wi_brt4y`'s rule-body row run beside):
//!   * every key keyed by its structure: 6 FAIL — [`an_own_eq_with_its_hash_is_one_key`],
//!     [`a_composite_or_tuple_over_such_a_key_is_one_key`], [`the_laws_guard_agrees_with_an_own_eq`],
//!     [`a_sorted_set_built_in_two_orders_is_one_key`], [`a_rule_body_map_is_said_by_its_key`]
//!     and [`building_a_map_compares_a_key_with_its_bucket_alone`] (no comparison at all);
//!   * a key compared with every stored key, not its bucket's: 1 FAILS,
//!     [`building_a_map_compares_a_key_with_its_bucket_alone`] (4950 comparisons, not 0);
//!   * the written key type judged at `Eq` alone: 2 FAIL,
//!     [`an_own_eq_without_a_hash_is_no_key`] (the field `Map[K = Pn, V = Int64]` loads) and
//!     [`a_set_is_no_key`];
//!   * `Hash` derived for no composite: 3 FAIL — [`a_composite_or_tuple_over_such_a_key_is_one_key`],
//!     [`an_own_eq_without_a_hash_is_no_key`]'s control and
//!     [`a_host_value_that_names_no_key_type_is_refused_where_its_map_is_made`]'s, each refused
//!     at load — with most of the suite;
//!   * a `NoProvider` instance taken at `Map.empty`: 1 FAILS,
//!     [`a_host_value_that_names_no_key_type_is_refused_where_its_map_is_made`] (the map is
//!     made, and `put` dies on an internal error);
//!   * a rule-body `Map.empty()` refused at the call, as before this ticket: 2 FAIL,
//!     [`a_rule_body_map_is_said_by_its_key`] and `wi_brt4y`'s
//!     `a_migrated_pure_operation_reduces_in_a_rule_body`;
//!   * a rule-body child walk judging the calls it holds: the same 2 FAIL;
//!   * a rule-body call nothing said left unjudged: 1 FAILS,
//!     [`a_rule_body_map_nothing_says_is_refused`] (loads clean);
//!   * only the first unsaid rule-body call of a walk raised: the same row (one refusal of two);
//!   * a derived `Hash` for a sort that writes an operation `hash` of its own: 1 FAILS,
//!     [`an_own_eq_without_a_hash_is_no_key`] (`Tag` loads, its `hash` taken as the member);
//!   * a derived `hash` that does not mix in the constructor's position: 1 FAILS,
//!     [`a_derived_hash_tells_constructors_apart`] (one comparison, not none).
//!
//! `SortedSet`'s `provides Hash` is stdlib text, not switched: without it the sorted-set key
//! was refused naming `Hash[T = anthill.prelude.SortedSet[…]]` (measured before it was
//! written). [`a_removed_key_leaves_the_others_in_insertion_order`] passes either way by
//! design: it holds the order a removal keeps, which the O(log N) removal must not lose.

use crate::common::{
    assert_refused_naming, interp_for, load_errors_of, load_kb_with, pattern_answer_counts, show_value,
};
use anthill_core::eval::builtins::map_key_comparisons_by_this_thread;
use anthill_core::eval::Value;

/// `Pt`, whose `eq` and `hash` read `x` alone, and `Holder`, a composite over it.
const PT: &str = "  import anthill.prelude.{Int64, Bool, String, Map, Option, List, PartialEq, Eq, Hash}
  sort Pt
    entity pt(x: Int64, y: Int64)
    operation eq(a: Pt, b: Pt) -> Bool = PartialEq.eq(a.x, b.x)
    operation hash(p: Pt) -> Int64 = Hash.hash(p.x)
    provides PartialEq[T = Pt]
    provides Eq[T = Pt]
    provides Hash[T = Pt]
  end
  sort Holder
    entity holder(p: Pt, n: Int64)
  end
";

fn program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{PT}{body}end\n")
}

fn answers(src: &str, entries: &[&str]) -> Vec<String> {
    let errs = load_errors_of(src);
    assert!(errs.is_empty(), "the program must load: {errs:#?}");
    let mut interp = interp_for(src);
    entries
        .iter()
        .map(|entry| match interp.call(entry, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
            Ok(v) => show_value(interp.kb(), &v),
            Err(e) => panic!("{entry}: {e:?}"),
        })
        .collect()
}

/// `pt(1, 2)` and `pt(1, 9)` are one key by `Pt`'s `eq`: `get` finds it, `put` replaces it,
/// `remove` removes it; `pt(2, 2)` is another key.
#[test]
fn an_own_eq_with_its_hash_is_one_key() {
    let ns = "test.pwk0x.own";
    let src = program(
        ns,
        "  operation one() -> Map[K = Pt, V = Int64] = Map.put(Map.empty(), pt(1, 2), 7)
  operation found() -> Option[T = Int64] = Map.get(one(), pt(1, 9))
  operation other() -> Option[T = Int64] = Map.get(one(), pt(2, 2))
  operation replaced() -> Int64 = Map.size(Map.put(one(), pt(1, 9), 8))
  operation replacedValue() -> Option[T = Int64] = Map.get(Map.put(one(), pt(1, 9), 8), pt(1, 0))
  operation removed() -> Int64 = Map.size(Map.remove(one(), pt(1, 5)))
  operation two() -> Int64 = Map.size(Map.put(one(), pt(2, 2), 8))
",
    );
    let entries: Vec<String> = ["found", "other", "replaced", "replacedValue", "removed", "two"]
        .iter()
        .map(|e| format!("{ns}.{e}"))
        .collect();
    let entries: Vec<&str> = entries.iter().map(String::as_str).collect();
    assert_eq!(
        answers(&src, &entries),
        ["some(value: 7)", "none", "1", "some(value: 8)", "0", "2"]
    );
}

/// A composite over `Pt` derives a hash through `Pt`'s, and a tuple holding one hashes it
/// through `Pt`'s instance: `holder(pt(1, 2), 3)` and `holder(pt(1, 9), 3)` are one key, and
/// so are `(pt(1, 2), 3)` and `(pt(1, 9), 3)`.
#[test]
fn a_composite_or_tuple_over_such_a_key_is_one_key() {
    let ns = "test.pwk0x.over";
    let src = program(
        ns,
        "  operation held() -> Option[T = Int64] = Map.get(Map.put(Map.empty(), holder(pt(1, 2), 3), 7), holder(pt(1, 9), 3))
  operation heldApart() -> Option[T = Int64] = Map.get(Map.put(Map.empty(), holder(pt(1, 2), 3), 7), holder(pt(1, 2), 4))
  operation tupled() -> Option[T = Int64] = Map.get(Map.put(Map.empty(), (pt(1, 2), 3), 7), (pt(1, 9), 3))
",
    );
    assert_eq!(
        answers(&src, &[&format!("{ns}.held"), &format!("{ns}.heldApart"), &format!("{ns}.tupled")]),
        ["some(value: 7)", "none", "some(value: 7)"]
    );
}

/// Written inline, `contains`/`get` of a `put` are rewritten by `Map`'s laws at load, which
/// fire only where `neq(?k, ?k2)` at `K` holds: at `Pt` it does not for `pt(1, 2)` and `pt(1,
/// 9)`, the law declines, and the map answers as its `eq` says.
#[test]
fn the_laws_guard_agrees_with_an_own_eq() {
    let ns = "test.pwk0x.law";
    let src = program(
        ns,
        "  operation same() -> Bool = Map.contains(Map.put(Map.empty[K = Pt, V = Int64](), pt(1, 2), 7), pt(1, 9))
  operation got() -> Option[T = Int64] = Map.get(Map.put(Map.empty[K = Pt, V = Int64](), pt(1, 2), 7), pt(1, 9))
  operation apart() -> Bool = Map.contains(Map.put(Map.empty[K = Pt, V = Int64](), pt(1, 2), 7), pt(2, 2))
",
    );
    assert_eq!(
        answers(&src, &[&format!("{ns}.same"), &format!("{ns}.got"), &format!("{ns}.apart")]),
        ["true", "some(value: 7)", "false"]
    );
}

/// A `SortedSet`'s tree depends on the order its elements arrived in, and its `eq` compares
/// the elements in order: `{1, …, 5}` built in three orders is three trees (`===` says so) and
/// one key, and `{3}` is another.
#[test]
fn a_sorted_set_built_in_two_orders_is_one_key() {
    let ns = "test.pwk0x.sorted";
    let src = format!(
        "namespace {ns}
  import anthill.prelude.{{Int64, Bool, Map, SortedSet, Option, Ord}}
  sort Ascending
    import anthill.prelude.Numeric.{{sub}}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end
  operation e() -> SortedSet[T = Int64, O = Ascending] = SortedSet.empty[T = Int64, O = Ascending]()
  operation up() -> SortedSet[T = Int64, O = Ascending] =
    SortedSet.insert(SortedSet.insert(SortedSet.insert(SortedSet.insert(SortedSet.insert(e(), 1), 2), 3), 4), 5)
  operation down() -> SortedSet[T = Int64, O = Ascending] =
    SortedSet.insert(SortedSet.insert(SortedSet.insert(SortedSet.insert(SortedSet.insert(e(), 5), 4), 3), 2), 1)
  operation mid() -> SortedSet[T = Int64, O = Ascending] =
    SortedSet.insert(SortedSet.insert(SortedSet.insert(SortedSet.insert(SortedSet.insert(e(), 3), 1), 5), 2), 4)
  operation three() -> SortedSet[T = Int64, O = Ascending] = SortedSet.insert(e(), 3)
  operation shapes() -> Bool = if up() === down() then true else up() === mid()
  operation size() -> Int64 =
    Map.size(Map.put(Map.put(Map.put(Map.put(Map.empty(), up(), 1), down(), 2), mid(), 3), three(), 4))
  operation got() -> Option[T = Int64] = Map.get(Map.put(Map.empty(), up(), 1), mid())
end
"
    );
    assert_eq!(
        answers(&src, &[&format!("{ns}.shapes"), &format!("{ns}.size"), &format!("{ns}.got")]),
        ["false", "2", "some(value: 1)"]
    );
}

/// A sort that writes its own `eq` and no `hash` provides no `Hash`, so it is no key: refused
/// where `Map[K = …]` is written, where a map of it is made, and as the field of a composite,
/// which derives no `Hash` over it. A sort whose `eq` is structural and which writes an
/// operation `hash` of its own is given no derived `Hash` either: the row would take that
/// operation as its member unread. `Pt`, with its `hash`, is the control.
#[test]
fn an_own_eq_without_a_hash_is_no_key() {
    let pn = "  sort Pn
    entity pn(x: Int64, y: Int64)
    operation eq(a: Pn, b: Pn) -> Bool = PartialEq.eq(a.x, b.x)
    provides PartialEq[T = Pn]
    provides Eq[T = Pn]
  end
";
    for (label, body, key) in [
        (
            "a written key type",
            "  sort Store\n    entity store(m: Map[K = Pn, V = Int64])\n  end\n",
            "`K = test.pwk0x.nohash.Pn`",
        ),
        (
            "an inferred key",
            "  operation f() -> Int64 = Map.size(Map.put(Map.empty(), pn(1, 2), 1))\n",
            "`anthill.prelude.Hash[T = test.pwk0x.nohash.Pn]`",
        ),
        (
            "a composite over it",
            "  sort Wrap\n    entity wrap(p: Pn)\n  end\n  operation g() -> Int64 = Map.size(Map.put(Map.empty(), wrap(pn(1, 2)), 1))\n",
            "`anthill.prelude.Hash[T = test.pwk0x.nohash.Wrap]`",
        ),
        (
            "a structural `eq` beside a `hash` of its own",
            "  sort Tag\n    entity tag(n: Int64)\n    operation hash(t: Tag) -> String = \"tag\"\n    provides PartialEq[T = Tag]\n    provides Eq[T = Tag]\n  end\n  operation h() -> Int64 = Map.size(Map.put(Map.empty(), tag(1), 1))\n",
            "`anthill.prelude.Hash[T = test.pwk0x.nohash.Tag]`",
        ),
    ] {
        let src = program("test.pwk0x.nohash", &format!("{pn}{body}"));
        assert_refused_naming(&load_errors_of(&src), &["Hash", key], label);
    }
    let src = program(
        "test.pwk0x.hashed",
        "  sort Store\n    entity store(m: Map[K = Pt, V = Int64])\n  end\n  operation f() -> Int64 = Map.size(Map.put(Map.empty(), holder(pt(1, 2), 1), 1))\n",
    );
    assert_eq!(answers(&src, &["test.pwk0x.hashed.f"]), ["1"]);
}

/// `Set` writes its own `eq` and no `hash`, and nothing provides `Set`, so no set value reaches
/// a map: a set is no key, refused where `Map[K = Set[…]]` is written (user, 2026-11-18:
/// "Leave it refused").
#[test]
fn a_set_is_no_key() {
    let src = program(
        "test.pwk0x.set",
        "  import anthill.prelude.{Set}\n  sort Store\n    entity store(m: Map[K = Set[T = Int64], V = Int64])\n  end\n",
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            "'anthill.prelude.Map' requires `anthill.prelude.Hash` at its parameter `K`",
            "`K = anthill.prelude.Set[T = anthill.prelude.Int64]`",
            "does not provide `Hash`",
        ],
        "a set key",
    );
}

/// Building a map of `Pt`s with distinct hashes compares no key with another; putting each
/// key again compares it with its bucket's one stored key. `Coll`, whose hash is one for
/// every value, puts every key in one bucket: each is compared with all stored before it.
#[test]
fn building_a_map_compares_a_key_with_its_bucket_alone() {
    let ns = "test.pwk0x.cost";
    let src = program(
        ns,
        "  sort Coll
    entity coll(x: Int64)
    operation eq(a: Coll, b: Coll) -> Bool = PartialEq.eq(a.x, b.x)
    operation hash(c: Coll) -> Int64 = 7
    provides PartialEq[T = Coll]
    provides Eq[T = Coll]
    provides Hash[T = Coll]
  end
  operation fill(m: Map[K = Pt, V = Int64], n: Int64) -> Map[K = Pt, V = Int64] =
    if n > 0 then fill(Map.put(m, pt(n, 0), n), n - 1) else m
  operation fillColl(m: Map[K = Coll, V = Int64], n: Int64) -> Map[K = Coll, V = Int64] =
    if n > 0 then fillColl(Map.put(m, coll(n), n), n - 1) else m
  operation built() -> Int64 = Map.size(fill(Map.empty(), 100))
  operation rebuilt() -> Int64 = Map.size(fill(fill(Map.empty(), 100), 100))
  operation collided() -> Int64 = Map.size(fillColl(Map.empty(), 100))
",
    );
    let errs = load_errors_of(&src);
    assert!(errs.is_empty(), "the program must load: {errs:#?}");
    let mut interp = interp_for(&src);
    let mut measured = |entry: &str| {
        let before = map_key_comparisons_by_this_thread();
        let v = interp.call(&format!("{ns}.{entry}"), &anthill_core::eval::HostValue::all(&[])).map(|h| h.value).unwrap_or_else(|e| panic!("{entry}: {e:?}"));
        (show_value(interp.kb(), &v), map_key_comparisons_by_this_thread() - before)
    };
    assert_eq!(measured("built"), ("100".to_string(), 0));
    assert_eq!(measured("rebuilt"), ("100".to_string(), 100));
    assert_eq!(measured("collided"), ("100".to_string(), 4950));
}

/// A derived `hash` mixes in which constructor built the value: `left(pt(1, 2))` and
/// `right(pt(1, 2))` hold equal fields and hash apart, so finding one where the other is
/// stored compares nothing, and each is its own key.
#[test]
fn a_derived_hash_tells_constructors_apart() {
    let ns = "test.pwk0x.side";
    let src = program(
        ns,
        "  sort Side
    entity left(p: Pt)
    entity right(p: Pt)
  end
  operation lefts() -> Map[K = Side, V = Int64] = Map.put(Map.empty(), left(pt(1, 2)), 1)
  operation sameSide() -> Option[T = Int64] = Map.get(lefts(), left(pt(1, 9)))
  operation otherSide() -> Option[T = Int64] = Map.get(lefts(), right(pt(1, 2)))
",
    );
    let errs = load_errors_of(&src);
    assert!(errs.is_empty(), "the program must load: {errs:#?}");
    let mut interp = interp_for(&src);
    let mut measured = |entry: &str| {
        let before = map_key_comparisons_by_this_thread();
        let v = interp.call(&format!("{ns}.{entry}"), &anthill_core::eval::HostValue::all(&[])).map(|h| h.value).unwrap_or_else(|e| panic!("{entry}: {e:?}"));
        (show_value(interp.kb(), &v), map_key_comparisons_by_this_thread() - before)
    };
    assert_eq!(measured("sameSide"), ("some(value: 1)".to_string(), 1));
    assert_eq!(measured("otherSide"), ("none".to_string(), 0));
}

/// A removal keeps the other keys in the order they were first put, and a key put again
/// after its removal comes last.
#[test]
fn a_removed_key_leaves_the_others_in_insertion_order() {
    let ns = "test.pwk0x.order";
    let src = program(
        ns,
        "  operation abc() -> Map[K = String, V = Int64] = Map.put(Map.put(Map.put(Map.empty(), \"a\", 1), \"b\", 2), \"c\", 3)
  operation keys() -> List[T = String] = Map.keys(Map.put(Map.put(Map.remove(abc(), \"b\"), \"d\", 4), \"b\", 5))
  operation values() -> List[T = Int64] = Map.values(Map.put(Map.put(Map.remove(abc(), \"b\"), \"d\", 4), \"b\", 5))
",
    );
    assert_eq!(
        answers(&src, &[&format!("{ns}.keys"), &format!("{ns}.values")]),
        ["[\"a\", \"c\", \"d\", \"b\"]", "[1, 3, 4, 5]"]
    );
}

/// A host call hands `Map.empty` the `Hash` its argument's type names: `none` names no `T`,
/// so no provision answers `Hash[T = Option]`, and the call is refused where it is made, as
/// `emptyOf(none())` is in a body (proposal 074 §1.4). A nullary constructor of a sort with no
/// parameter is the control. FAILS, measured, with the requirement the typing parks not read
/// at the host call: the map is made.
#[test]
fn a_host_value_that_names_no_key_type_is_refused_where_its_map_is_made() {
    let ns = "test.pwk0x.host";
    let src = program(
        ns,
        "  sort Lamp\n    entity off\n  end\n  operation emptyOf[K](k: K) -> Map[K = K, V = Int64] requires Hash[T = K] = Map.empty()\n",
    );
    let mut interp = interp_for(&src);
    let none = interp.kb().try_resolve_symbol("anthill.prelude.Option.none").expect("none");
    let off = interp.kb().try_resolve_symbol(&format!("{ns}.Lamp.off")).expect("off");
    let refused = format!("{:?}", interp.call(&format!("{ns}.emptyOf"), &anthill_core::eval::HostValue::all(&[Value::SymbolRef(none)])).map(|h| h.value));
    assert!(
        refused.contains("HostCallRefused") && refused.contains("anthill.prelude.Hash[T = anthill.prelude.Option]"),
        "{refused}"
    );
    let twin = load_errors_of(&program(
        ns,
        "  sort Lamp\n    entity off\n  end\n  operation emptyOf[K](k: K) -> Map[K = K, V = Int64] requires Hash[T = K] = Map.empty()\n  operation twin() -> Map[K = Option, V = Int64] = emptyOf(Option.none())\n",
    ));
    assert!(
        twin.iter().any(|e| e.contains("anthill.prelude.Hash[T = anthill.prelude.Option]")),
        "the body twin is refused naming the requirement: {twin:#?}"
    );
    let m = interp.call(&format!("{ns}.emptyOf"), &anthill_core::eval::HostValue::all(&[Value::SymbolRef(off)])).map(|h| h.value).expect("emptyOf(off)");
    let m = interp
        .call("anthill.prelude.Map.put", &anthill_core::eval::HostValue::all(&[m, Value::SymbolRef(off), Value::Int(4)])).map(|h| h.value)
        .expect("put");
    let n = interp.call("anthill.prelude.Map.size", &anthill_core::eval::HostValue::all(&[m])).map(|h| h.value).expect("size");
    assert_eq!(show_value(interp.kb(), &n), "1");
}

/// A rule body's `Map.empty()` is typed alone before the call holding it is, and its `K` is
/// said by that call: the `String` `put`'s key gives, a `Pt` with its own `eq`.
#[test]
fn a_rule_body_map_is_said_by_its_key() {
    let ns = "test.pwk0x.rb";
    let src = program(
        ns,
        "  rule sz(1) :- Map.size(Map.put(Map.empty(), \"a\", 1)) = 1
  rule pts(1) :- Map.size(Map.put(Map.put(Map.empty(), pt(1, 2), 1), pt(1, 9), 2)) = 1
  rule nopts(1) :- Map.size(Map.put(Map.put(Map.empty(), pt(1, 2), 1), pt(1, 9), 2)) = 2
",
    );
    let mut kb = load_kb_with(&src);
    for (goal, counts) in [("sz(1)", (1, 1)), ("pts(1)", (1, 1)), ("nopts(1)", (0, 0))] {
        assert_eq!(pattern_answer_counts(&mut kb, &format!("{ns}.{goal}")), counts, "{goal}");
    }
}

/// A rule body's map whose `K` nothing says owes `Hash` at a type nothing fixed, and is
/// refused at load, as its operation-body twin is — each such map, two in one goal too.
#[test]
fn a_rule_body_map_nothing_says_is_refused() {
    let src = program("test.pwk0x.rbunsaid", "  rule r(?m) :- ?m = Map.empty()\n");
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            "`anthill.prelude.Hash[T = anthill.prelude.Map.K]`",
            "cannot be supplied for call to `anthill.prelude.Map.empty`",
        ],
        "a rule-body map no type is said for",
    );
    let src = program("test.pwk0x.rbunsaid2", "  rule r(?p) :- ?p = (Map.empty(), Map.empty())\n");
    let errs = load_errors_of(&src);
    let unsaid = errs
        .iter()
        .filter(|e| e.contains("`anthill.prelude.Hash[T = anthill.prelude.Map.K]` cannot be supplied"))
        .count();
    assert_eq!(unsaid, 2, "one refusal per map: {errs:#?}");
}
