//! A `Map` keeps the `Hash[T = K]` instance its construction is handed (`Map.empty() requires
//! Hash[T = K]`), and a tuple key is read through its `Eq` at the labels `K` names (user,
//! 2026-11-17: "By K's Eq", "The Map value"). The `@[simp]` laws that rewrite a `get` or
//! `contains` of a `put` guard on `neq(?k, ?k2)`, which is typed where the law fires, at the
//! map's `K` ("guard should be typed"), so the law and the map agree on which keys are equal.
//! A key whose sort writes an `eq` of its own is hashed through the instance:
//! `wi_pwk0x_map_keyed_through_hash_test`.
//!
//! BACK-OUTS, each a temporary switch in one build (the rows `held_call_slot_said_test` lists):
//!   * a tuple key read as its structure, not at `K`'s labels: 2 FAIL —
//!     [`a_tuple_key_wider_than_its_type_is_one_key`] and
//!     [`the_laws_guard_compares_at_the_maps_key_type`] (where the law declines, the map
//!     answers, and it answered by structure);
//!   * the law's guard typed at the redex: 1 FAILS, [`the_laws_guard_compares_at_the_maps_key_type`]
//!     (`false` for the wider, literal and dot keys, `none` for the `get`);
//!   * `neq` at a tuple read at `NamedTuple`'s instance: 2 FAIL, the same row (the guard's `neq`
//!     unclassified at the tuple) and `wi_jwcnn`'s `neq_at_a_tuple_type_runs_at_the_tuples_instance`;
//!   * the refusal of a held call nothing said: 1 FAILS,
//!     [`a_map_whose_key_type_nothing_says_is_refused`] (loads, and dies when run).
//!
//! And `Map.empty`'s `requires Hash[T = K]` removed from the standard library: every row of this
//! file fails, and the three map rows of `held_call_slot_said_test` (measured with its `Eq`
//! spelling).

use crate::common::{assert_refused_naming, interp_for, load_errors_of, show_value};

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

/// `K = (a: Int64)`: a key wider than its type is read at `a` (kernel-language §4.5), so `(a: 1,
/// b: 2)` and `(a: 1, b: 3)` are one key.
#[test]
fn a_tuple_key_wider_than_its_type_is_one_key() {
    let src = r#"
namespace test.mapeq.tup
  import anthill.prelude.{Int64, Map, Option}
  operation keyOf(n: Int64) -> (a: Int64) = (a: 1, b: n)
  operation one() -> Map[K = (a: Int64), V = Int64] = Map.put(Map.empty(), keyOf(2), 7)
  operation found() -> Option[T = Int64] = Map.get(one(), keyOf(3))
  operation replaced() -> Int64 = Map.size(Map.put(one(), keyOf(4), 8))
end
"#;
    assert_eq!(
        answers(src, &["test.mapeq.tup.found", "test.mapeq.tup.replaced"]),
        ["some(value: 7)", "1"]
    );
}

/// Written inline, `contains`/`get` of a `put` are rewritten by `Map`'s laws at load; the guard
/// `neq(?k, ?k2)` compares at the map's `K`, so the law fires only where `K`'s `Eq` says the
/// keys differ. A wider key, a literal one and the dot spelling agree with the map; keys that
/// differ at `a` do not; `Int64` keys are the control.
#[test]
fn the_laws_guard_compares_at_the_maps_key_type() {
    let src = r#"
namespace test.mapeq.law
  import anthill.prelude.{Int64, Bool, Map, Option}
  operation keyOf(n: Int64) -> (a: Int64) = (a: 1, b: n)
  operation wider() -> Bool = Map.contains(Map.put(Map.empty[K = (a: Int64), V = Int64](), keyOf(2), 7), keyOf(3))
  operation got() -> Option[T = Int64] = Map.get(Map.put(Map.empty[K = (a: Int64), V = Int64](), keyOf(2), 7), keyOf(3))
  operation literal() -> Bool = Map.contains(Map.put(Map.empty[K = (a: Int64), V = Int64](), (a: 1, b: 2), 7), (a: 1, b: 3))
  operation apart() -> Bool = Map.contains(Map.put(Map.empty[K = (a: Int64), V = Int64](), keyOf(2), 7), (a: 2, b: 2))
  operation dot() -> Bool = Map.put(Map.empty[K = (a: Int64), V = Int64](), keyOf(2), 7).contains(keyOf(3))
  operation intApart() -> Bool = Map.contains(Map.put(Map.empty[K = Int64, V = Int64](), 1, 7), 2)
  operation intSame() -> Bool = Map.contains(Map.put(Map.empty[K = Int64, V = Int64](), 1, 7), 1)
end
"#;
    assert_eq!(
        answers(
            src,
            &[
                "test.mapeq.law.wider",
                "test.mapeq.law.got",
                "test.mapeq.law.literal",
                "test.mapeq.law.apart",
                "test.mapeq.law.dot",
                "test.mapeq.law.intApart",
                "test.mapeq.law.intSame"
            ]
        ),
        ["true", "some(value: 7)", "true", "false", "true", "false", "true"]
    );
}

/// A map whose key type nothing says — not the call, not anything its value meets — owes `Hash`
/// at a type nothing fixed, and is refused at load where it is made. It loaded and died when
/// run, where its `TypeValue` twin was refused.
#[test]
fn a_map_whose_key_type_nothing_says_is_refused() {
    let src = r#"
namespace test.mapeq.unsaid
  import anthill.prelude.{Int64, Map}
  operation named() -> Int64 =
    let m = Map.empty()
    Map.size(m)
end
"#;
    assert_refused_naming(
        &load_errors_of(src),
        &[
            "`anthill.prelude.Hash[T = anthill.prelude.Map.K]`",
            "cannot be supplied for call to `anthill.prelude.Map.empty`",
            "element `T = anthill.prelude.Map.K` is unconstrained at this call site",
        ],
        "a map no type is said for",
    );
}

/// A key type that provides no `Hash` is refused where the map is made, written in the call's
/// bracket or inferred from a key: `Float`'s equality is partial. `Int64` is the control.
#[test]
fn a_key_type_without_eq_is_refused() {
    for (label, body) in [
        (
            "a bracket",
            "  operation f() -> Int64 =\n    let m = Map.empty[K = Float, V = Int64]()\n    Map.size(m)\n",
        ),
        ("an inferred key", "  operation g() -> Int64 = Map.size(Map.put(Map.empty(), 1.5, 1))\n"),
    ] {
        let src = format!(
            "namespace test.mapeq.float\n  import anthill.prelude.{{Int64, Float, Map}}\n{body}end\n"
        );
        assert_refused_naming(
            &load_errors_of(&src),
            &[
                "`anthill.prelude.Hash[T = anthill.prelude.Float]`",
                "cannot be supplied for call to `anthill.prelude.Map.empty`",
            ],
            label,
        );
    }
    let src = r#"
namespace test.mapeq.int
  import anthill.prelude.{Int64, Map}
  operation g() -> Int64 = Map.size(Map.put(Map.empty(), 15, 1))
end
"#;
    assert_eq!(answers(src, &["test.mapeq.int.g"]), ["1"]);
}
