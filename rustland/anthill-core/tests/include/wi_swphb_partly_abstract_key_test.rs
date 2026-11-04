//! WI-20261103-SWPHB — a key with an abstract part is judged at its concrete part.
//! `check_use_site_requires_eq` skipped a key `type_is_ground` answered false for, so an
//! unlawful part beside a type parameter loaded: `Set[T = (a: F, b: Float)]`, `Set[T =
//! Pair[A = F, B = Float]]` and the field `h(s: Set[T = (a: F, b: Float)])` of a sort with
//! `sort F = ?`. Since WI-20261102-7AB56 a projection that stays neutral was abstract the
//! same way, so `Set[T = (a: x.E, b: y.E)]` loaded with `x.E` read to `Float`.
//!
//! Now each abstract part — a type parameter, a type variable, a projection nothing fixes —
//! is a rigid with `Eq` assumed at it, the best case for the part, and the key is resolved
//! under that assumption with σ, so the assumption covers only its own
//! part (`KeyAtRigidParts`). What the declarations the key is written in require — the
//! frame of its operation, the declaration of each parameter in it — is assumed too, as
//! every other check of them assumes it. A tuple is read by its components, and the refusal
//! names the one that does not provide `Eq`.
//!
//! BACK-OUTS, MEASURED — each ONE part put back, over this file's 6 rows and
//! `wi_7ab56_projection_key_test`'s 9:
//!
//!  * A key with an abstract part skipped whole again — 6: every row here but the lawful
//!    twins, at its refused half, and `wi_7ab56…::a_projection_beside_a_type_parameter_is_read`
//!    (`(a: F, b: x.E)` over `x: Leaf[E = Float]` loads).
//!  * The assumptions without σ (the coarse cover) — 4: the keys whose unlawful part is an
//!    argument of an application load — the ticket's `Pair[A = F, B = Float]`, `P.Key`'s,
//!    the nested `Pair` and the `Box` with no `requires Ord[T = F]`. A tuple's components
//!    are judged one by one, so the tuple rows pass.
//!  * Each parameter's declaration not read for what it requires — 1:
//!    `the_declarations_own_requirements_are_assumed`, at the sort's `requires Ord[T = F]`
//!    beside `Box provides Eq :- Ord[T]`.
//!  * The frame of the operation the key is written in not assumed, only each parameter's
//!    declaration — 1: the same row, at the operation's `requires` over its sort's `F` and
//!    at the provision block's condition.
//!  * No component named — 3: the ticket's keys, the positions and the rigid projection.
//!  * A key printed as stored — 5: every row that prints a type parameter, here and the
//!    7AB56 one (`(a: ?F, b: Float)`, `Pair[A = ?, …]`, `Box[T = ?]`).
//!
//! PASS EITHER WAY BY DESIGN: `the_lawful_twins_load_and_run` (they loaded before) and the
//! loading halves of the other rows.

use crate::common::{load_errors_of, run_int64};

/// A program declaring `decl` beside `Leaf`, whose member `E` an instance may fix, `Pair`,
/// `Holder`, a spec whose carrier is `C`, and `Storage`, a spec with a carrier and a member
/// `Key`.
fn program(ns: &str, decl: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Float, Bool, Set, Map, Option, Ord, Eq, PartialEq}}
  import anthill.prelude.Option.{{none}}
  sort Leaf
    sort E = ?
    entity leaf(e: E)
  end
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(a: A, b: B)
  end
  sort Holder
    sort C = ?
    operation get(h: C) -> Int64
  end
  sort Storage
    sort C = ?
    sort Key = ?
  end
  {decl}
end
"#
    )
}

/// `Box`, whose `Eq` holds where its element's `Ord` does.
const BOX: &str = "sort Box
    sort T = ?
    entity box(v: T)
    provides PartialEq[T = Box] :- PartialEq[T = T]
    provides Eq[T = Box] :- Ord[T = T]
  end";

/// The refusals of `src` that judge a key.
fn key_refusals(src: &str) -> (Vec<String>, Vec<String>) {
    let errs = load_errors_of(src);
    let keys = errs
        .iter()
        .filter(|e| {
            e.contains("so it is not a lawful key") || e.contains("provides it is not known")
        })
        .cloned()
        .collect();
    (keys, errs)
}

/// `src` loads with no refusal.
#[track_caller]
fn assert_loads(src: &str, why: &str) {
    let errs = load_errors_of(src);
    assert!(errs.is_empty(), "{why} should load: {errs:#?}");
}

/// `src` refuses `count` keys, each `Set`'s `T` bound to `printed`, naming `component` as
/// the part that does not provide `Eq` — or no part, where the key is that part itself.
#[track_caller]
fn assert_unlawful(src: &str, count: usize, printed: &str, component: Option<&str>, why: &str) {
    let (keys, errs) = key_refusals(src);
    assert_eq!(keys.len(), count, "{why}: {count} key refusal(s): {errs:#?}");
    let part = component
        .map(|c| format!(": its component `{c}` does not"))
        .unwrap_or_default();
    let expected = format!(
        "'anthill.prelude.Set' requires `anthill.prelude.Eq` at its parameter `T`, but `T = {printed}` binds a type that does not provide `Eq`{part} (its equality"
    );
    for key in &keys {
        assert!(key.contains(&expected), "{why}: expected `{expected}`, got:\n{key}");
    }
}

/// The ticket's four keys are refused, each naming its unlawful part: the component of a
/// tuple, the whole application otherwise.
#[test]
fn the_tickets_keys_are_refused_naming_the_unlawful_part() {
    let ns = "wi_swphb.ticket.tuple";
    assert_unlawful(
        &program(ns, "operation k[F](s: Set[T = (a: F, b: Float)]) -> Int64 = 1"),
        1,
        "(a: F, b: Float)",
        Some("anthill.prelude.Float"),
        "a tuple beside an operation's type parameter",
    );
    let ns = "wi_swphb.ticket.app";
    assert_unlawful(
        &program(ns, "operation k[F](s: Set[T = Pair[A = F, B = Float]]) -> Int64 = 1"),
        1,
        &format!("{ns}.Pair[A = {ns}.k.F, B = anthill.prelude.Float]"),
        None,
        "an application beside an operation's type parameter",
    );
    let ns = "wi_swphb.ticket.field";
    assert_unlawful(
        &program(
            ns,
            "sort H\n    sort F = ?\n    entity h(s: Set[T = (a: F, b: Float)])\n  end",
        ),
        1,
        "(a: F, b: Float)",
        Some("anthill.prelude.Float"),
        "a field beside a sort's type parameter",
    );
    let ns = "wi_swphb.ticket.projection";
    assert_unlawful(
        &program(
            ns,
            "operation k(x: Leaf[E = Float], y: Leaf, s: Set[T = (a: x.E, b: y.E)]) -> Int64 = 1",
        ),
        1,
        "(a: Float, b: y.E)",
        Some("anthill.prelude.Float"),
        "a projection read to `Float` beside a neutral one",
    );
}

/// The lawful twins load, and each operation runs at an argument.
#[test]
fn the_lawful_twins_load_and_run() {
    let cases = [
        (
            "tuple",
            "operation k[F](s: Set[T = (a: F, b: Int64)]) -> Int64 = 7\n  operation main() -> Int64 = k[F = Bool]({(a: true, b: 2)})",
        ),
        (
            "app",
            "operation k[F](s: Set[T = Pair[A = F, B = Int64]]) -> Int64 = 7\n  operation main() -> Int64 = k[F = Bool]({pair(a: true, b: 2)})",
        ),
        (
            "projection",
            "operation k(x: Leaf, y: Leaf, s: Set[T = (a: x.E, b: y.E)]) -> Int64 = 7\n  operation main() -> Int64 = k(leaf(e: 1), leaf(e: true), {(a: 1, b: true)})",
        ),
    ];
    for (tag, decl) in cases {
        let ns = format!("wi_swphb.lawful.{tag}");
        assert_eq!(run_int64(&program(&ns, decl), &format!("{ns}.main")), Ok(7), "{tag}");
    }
}

/// The key `Set[T = <key>]`, `F` a type parameter of the operation or sort that holds it,
/// written at `position`.
fn at(position: &str, key: &str) -> String {
    let set = format!("Set[T = {key}]");
    match position {
        "parameter" => format!("operation k[F](s: {set}) -> Int64 = 1"),
        "return" => format!("operation k[F]() -> Option[T = {set}] = none"),
        "requires" => format!("operation k[F]() -> Int64 requires Holder[C = {set}] = 1"),
        "let" => format!(
            "operation k[F]() -> Bool =\n    let z: Option[T = {set}] = none\n    true"
        ),
        "lambda" => format!(
            "operation k[F]() -> Bool =\n    let h = lambda (s: {set}) -> true\n    true"
        ),
        "alias" => format!("sort G\n    sort F = ?\n    sort S = {set}\n  end"),
        "field" => format!("sort G\n    sort F = ?\n    entity g(s: {set})\n  end"),
        other => panic!("no position `{other}`"),
    }
}

const POSITIONS: [&str; 7] = [
    "parameter", "return", "requires", "let", "lambda", "alias", "field",
];

/// At every position a key is judged at, the unlawful component beside `F` is refused and
/// the lawful one loads; two sites are two refusals.
#[test]
fn a_partly_abstract_key_is_judged_at_every_position() {
    for position in POSITIONS {
        assert_unlawful(
            &program(
                &format!("wi_swphb.at.{position}.float"),
                &at(position, "(a: F, b: Float)"),
            ),
            1,
            "(a: F, b: Float)",
            Some("anthill.prelude.Float"),
            &format!("`(a: F, b: Float)` at the {position}"),
        );
        assert_loads(
            &program(
                &format!("wi_swphb.at.{position}.int"),
                &at(position, "(a: F, b: Int64)"),
            ),
            &format!("`(a: F, b: Int64)` at the {position}"),
        );
    }
    assert_unlawful(
        &program(
            "wi_swphb.at.twice",
            "operation k[F](a: Set[T = (a: F, b: Float)], b: Set[T = (a: F, b: Float)]) -> Int64 = 1",
        ),
        2,
        "(a: F, b: Float)",
        Some("anthill.prelude.Float"),
        "two sites",
    );
}

/// What the declarations the key is written in require are assumed with `Eq`: under
/// `requires Ord[T = F]` — at the operation, at the sort, at an operation over its sort's
/// `F`, or as the condition of the provision block the operation is written in — `Box[T =
/// F]` provides `Eq` and the key loads, and the operation runs. Without it nothing says
/// `Ord[T = F]`, and the key is refused.
#[test]
fn the_declarations_own_requirements_are_assumed() {
    let ns = "wi_swphb.declared.op";
    let src = program(
        ns,
        &format!(
            "{BOX}\n  operation k[F](s: Set[T = Box[T = F]]) -> Int64 requires Ord[T = F] = 7\n  operation main() -> Int64 = k({{box(v: 1)}})"
        ),
    );
    assert_eq!(run_int64(&src, &format!("{ns}.main")), Ok(7));
    assert_loads(
        &program(
            "wi_swphb.declared.sort",
            &format!(
                "{BOX}\n  sort Hb\n    sort F = ?\n    requires Ord[T = F]\n    entity hb(s: Set[T = Box[T = F]])\n  end"
            ),
        ),
        "the sort's `requires Ord[T = F]`",
    );
    assert_loads(
        &program(
            "wi_swphb.declared.member",
            &format!(
                "{BOX}\n  sort Hs\n    sort F = ?\n    entity hs(f: F)\n    operation m(s: Set[T = Box[T = F]]) -> Int64 requires Ord[T = F] = 1\n  end"
            ),
        ),
        "an operation's `requires Ord[T = F]` over its sort's `F`",
    );
    assert_loads(
        &program(
            "wi_swphb.declared.block",
            &format!(
                "{BOX}\n  sort Tag\n    sort C = ?\n    operation tag(c: C) -> Int64\n  end\n  sort Hq\n    sort F = ?\n    entity hq(f: F)\n    provides Tag[C = Self] :- Ord[T = F] where\n      operation tag(c: Self) -> Int64 =\n        let z: Option[T = Set[T = Box[T = F]]] = none\n        1\n    end\n  end"
            ),
        ),
        "the condition of the provision block the operation is written in",
    );
    let ns = "wi_swphb.declared.none";
    assert_unlawful(
        &program(
            ns,
            &format!("{BOX}\n  operation k[F](s: Set[T = Box[T = F]]) -> Int64 = 1"),
        ),
        1,
        &format!("{ns}.Box[T = {ns}.k.F]"),
        None,
        "no `requires Ord[T = F]`",
    );
}

/// A rigid projection its bound leaves open is an abstract part: an unlawful part beside it
/// is refused, a lawful one loads.
#[test]
fn a_neutral_rigid_projection_beside_an_unlawful_part_is_judged() {
    let op = |key: &str| {
        format!("operation k[P](s: Set[T = {key}]) -> Int64 requires Storage[C = P] = 1")
    };
    assert_unlawful(
        &program("wi_swphb.rigid.tuple", &op("(a: P.Key, b: Float)")),
        1,
        "(a: P.Key, b: Float)",
        Some("anthill.prelude.Float"),
        "a tuple beside `P.Key`",
    );
    let ns = "wi_swphb.rigid.app";
    assert_unlawful(
        &program(ns, &op("Pair[A = P.Key, B = Float]")),
        1,
        &format!("{ns}.Pair[A = P.Key, B = anthill.prelude.Float]"),
        None,
        "an application beside `P.Key`",
    );
    assert_loads(
        &program("wi_swphb.rigid.int", &op("Pair[A = P.Key, B = Int64]")),
        "`Pair[A = P.Key, B = Int64]`",
    );
}

/// A parameter written twice is one part, and two parameters are two: each loads, and an
/// unlawful part nested beside them is still refused.
#[test]
fn a_parameter_written_twice_is_one_part() {
    assert_loads(
        &program(
            "wi_swphb.twice.same",
            "operation k[F](s: Set[T = Pair[A = F, B = F]]) -> Int64 = 1",
        ),
        "`Pair[A = F, B = F]`",
    );
    assert_loads(
        &program(
            "wi_swphb.twice.two",
            "operation k[F, G](s: Set[T = Pair[A = F, B = G]]) -> Int64 = 1",
        ),
        "`Pair[A = F, B = G]`",
    );
    let ns = "wi_swphb.twice.nested";
    assert_unlawful(
        &program(
            ns,
            "operation k[F](s: Set[T = Pair[A = F, B = Pair[A = F, B = Float]]]) -> Int64 = 1",
        ),
        1,
        &format!("{ns}.Pair[A = {ns}.k.F, B = {ns}.Pair[A = {ns}.k.F, B = anthill.prelude.Float]]"),
        None,
        "an unlawful part nested beside the parameter",
    );
}
