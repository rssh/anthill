//! WI-20261102-7AB56 — a key that is a type projection is judged for a lawful `Eq` as the
//! type it stands for. `check_use_site_requires_eq` read `x.E` as a ground type of its own,
//! which provides nothing: `operation k(x: Leaf, s: Set[T = x.E])` was refused "`T = x.E`
//! binds a type that does not provide `Eq`" whatever `x` was — its `Leaf[E = Int64]` and
//! open-`E` spellings alike — and a rigid `P.Key` was read as abstract whatever its bound
//! fixed, so `requires Storage[C = P, Key = Float]` with `Set[T = P.Key]` loaded.
//!
//! Now the site records the operation it is written in (`ParameterizedSite::operation`),
//! and the check reads a projection key the way the body check reads the signature
//! (`read_projection_key`): an expression-carried one off the receiver PARAMETER's declared
//! type, a rigid one through the `requires` that bounds it. A member that reads to a type
//! is judged at that type; one that stays open (a neutral) is abstract, as a type parameter
//! is; one that does not read here — a receiver that is a binder of the body, a member no
//! one declares — is refused as not judged (`LoadError::KeyEqNotJudged`), never passed.
//!
//! Positions: a parameter, the return, the operation's own `requires`, a body `let`
//! annotation and a typed lambda binder. The lambda binder is driven at an OPEN member and at
//! `Float` only: at `x: Leaf[E = Int64]` the typer refuses the binder's annotation on its own
//! ("expected Set[T = x.E], got Set[T = Int64]" — `List[T = x.E]` too, no key involved;
//! WI-20261103-SG16K).
//!
//! NOT JUDGED, by the check's documented non-scope: an unlawful part beside an abstract one
//! (`Set[T = (a: x.E, b: y.E)]`, `x.E` read to `Float` and `y.E` open, loads, as the
//! type-parameter key `(a: F, b: Float)` does — WI-20261103-SWPHB), and a projection off a
//! binder of the body, refused as not judged here even where its key is lawful
//! (WI-20261103-BANCC).
//!
//! BACK-OUTS, MEASURED — each ONE part put back, over this file's 9 rows:
//!
//!  * The key read raw (no projection key read at all) — 9 of 9: every open and `Int64` row
//!    is refused "binds a type that does not provide `Eq`", every rigid `Float` row loads,
//!    and the not-judged rows print that refusal instead.
//!  * No operation recorded on a site (`operation: None` at the recorder) — 7: each key off a
//!    parameter is "not judged", its receiver "written outside an operation" — the open,
//!    declared-type and read-through rows, the receiver, beside and unsettled rows' reasons,
//!    and the member row's (it names the receiver, not the member). PASS:
//!    `a_rigid_projection_key_is_judged_through_its_bound` (a rigid projection names its
//!    declaration and needs no parameter table) and
//!    `a_key_not_judged_is_named_by_the_containers_parameter` (it asserts the name alone).
//!  * The operation recorded on its signature's sites alone, not its body's — 4: the `let`
//!    and lambda positions of `an_open_projection_key_loads_and_its_operation_runs` and
//!    `a_projection_key_is_judged_at_its_receivers_declared_type` are "not judged", and the
//!    receiver and beside rows' `let` reasons name no operation.
//!  * One reading instead of reading again while it changes — 1:
//!    `a_projection_key_reads_through_a_field_path_an_alias_and_a_sibling_parameter` (the
//!    chain `x: Leaf[E = y.E]` does not settle, and is refused open and at `Int64`).
//!  * No receiver check before the reading — 2:
//!    `a_key_whose_receiver_is_no_parameter_is_refused_as_not_judged` and the beside row's
//!    control (the reason says "not an argument-bound parameter of this call").
//!  * The not-judged refusal naming the `Eq` goal's key, not the container's parameter — 1:
//!    `a_key_not_judged_is_named_by_the_containers_parameter` (`Map`'s `T`).
//!  * No check for an abstract part beside the projections — 1:
//!    `a_key_abstract_beside_its_projection_is_not_judged_for_it` (refused as not judged).
//!  * A reading that does not settle passed as abstract — 1:
//!    `a_key_whose_projections_do_not_settle_is_refused` (no key refusal).
//!
//! NOT DRIVEN: an operation whose signature is not recorded is refused as not judged naming
//! that, not read as having no parameters; no program reaches it (every operation the loader
//! lowers records its `OperationInfo`), so no row can.
//!
//! PASS EITHER WAY BY DESIGN: the generic twin in the first row. The receiver row's control
//! (the key off the parameter itself) fails under the signature-only part alone, and the
//! beside row's control under the three that change its reason.

use crate::common::{load_errors_of, run_int64};

/// A program declaring `decl` beside `Leaf`, whose member `E` an instance may fix, `Holder`,
/// a spec whose carrier is `C`, and `Storage`, a spec with a carrier and a member `Key`.
fn program(ns: &str, decl: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Float, Bool, Set, Map, List, Option}}
  import anthill.prelude.Option.{{none}}
  sort Leaf
    sort E = ?
    entity leaf(e: E)
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

/// The key `Set[T = x.E]` written at `position` of an operation `k` whose parameter `x` is a
/// `recv`.
fn at(position: &str, recv: &str) -> String {
    let key = "Set[T = x.E]";
    match position {
        "parameter" => format!("operation k(x: {recv}, s: {key}) -> Int64 = 1"),
        "return" => format!("operation k(x: {recv}) -> Option[T = {key}] = none"),
        "requires" => format!("operation k(x: {recv}) -> Int64 requires Holder[C = {key}] = 1"),
        "let" => format!(
            "operation k(x: {recv}) -> Bool =\n    let z: Option[T = {key}] = none\n    true"
        ),
        "lambda" => format!(
            "operation k(x: {recv}) -> Bool =\n    let h = lambda (s: {key}) -> true\n    true"
        ),
        other => panic!("no position `{other}`"),
    }
}

const POSITIONS: [&str; 5] = ["parameter", "return", "requires", "let", "lambda"];

/// The refusals of `src` that judge a key: lawful or not, and not judged.
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

/// `src` refuses one key, `container`'s `param` bound to `printed`, which has no lawful `Eq`.
#[track_caller]
fn assert_unlawful(src: &str, container: &str, param: &str, printed: &str, why: &str) {
    let (keys, errs) = key_refusals(src);
    assert_eq!(keys.len(), 1, "{why}: one key refusal: {errs:#?}");
    let expected = format!(
        "'anthill.prelude.{container}' requires `anthill.prelude.Eq` at its parameter `{param}`, but `{param} = {printed}` binds a type that does not provide `Eq`"
    );
    assert!(
        keys[0].contains(&expected),
        "{why}: expected `{expected}`, got:\n{}",
        keys[0]
    );
}

/// `src` refuses one key as not judged, `binding` (`T = y.E`), saying `reason`.
#[track_caller]
fn assert_not_judged(src: &str, binding: &str, reason: &str, why: &str) {
    let (keys, errs) = key_refusals(src);
    assert_eq!(keys.len(), 1, "{why}: one key refusal: {errs:#?}");
    let expected = format!(
        "whether `{binding}` provides it is not known: the projection does not read here ({reason})"
    );
    assert!(
        keys[0].contains(&expected),
        "{why}: expected `{expected}`, got:\n{}",
        keys[0]
    );
}

/// The ticket's open key loads at every position, and the operation written with it runs at
/// an instance whose member is lawful. CONTROL — passes either way: the generic twin
/// `k[E](x: Leaf[E = E], s: Set[T = E])`, which loaded before.
#[test]
fn an_open_projection_key_loads_and_its_operation_runs() {
    for position in POSITIONS {
        let src = program(&format!("wi_7ab56.open.{position}"), &at(position, "Leaf"));
        assert_loads(
            &src,
            &format!("`Set[T = x.E]` over `x: Leaf` at the {position}"),
        );
    }
    let src = program(
        "wi_7ab56.open.run",
        "operation k(x: Leaf, s: Set[T = x.E]) -> Int64 = 7\n  operation main() -> Int64 = k(leaf(e: 1), {1, 2})",
    );
    assert_eq!(run_int64(&src, "wi_7ab56.open.run.main"), Ok(7));
    let twin = program(
        "wi_7ab56.open.twin",
        "operation k[E](x: Leaf[E = E], s: Set[T = E]) -> Int64 = 1",
    );
    assert_loads(&twin, "the generic twin");
}

/// The key is the member the receiver's declared type fixes: refused at `Float`, loaded at
/// `Int64`, at every position (the lambda binder at `Float` only, see the header).
#[test]
fn a_projection_key_is_judged_at_its_receivers_declared_type() {
    for position in POSITIONS {
        let src = program(
            &format!("wi_7ab56.float.{position}"),
            &at(position, "Leaf[E = Float]"),
        );
        let why = format!("`Set[T = x.E]` over `x: Leaf[E = Float]` at the {position}");
        assert_unlawful(&src, "Set", "T", "anthill.prelude.Float", &why);
        if position == "lambda" {
            continue;
        }
        let src = program(
            &format!("wi_7ab56.int.{position}"),
            &at(position, "Leaf[E = Int64]"),
        );
        assert_loads(
            &src,
            &format!("`Set[T = x.E]` over `x: Leaf[E = Int64]` at the {position}"),
        );
    }
}

/// A rigid projection is read through the `requires` that bounds it — an operation's, a
/// sort's — or a concrete sort's provision: open, it is abstract; fixed, it is judged.
#[test]
fn a_rigid_projection_key_is_judged_through_its_bound() {
    let op = |key: &str| {
        format!("operation k[P](s: Set[T = P.Key]) -> Int64 requires Storage[C = P{key}] = 1")
    };
    let sort = |key: &str| {
        format!("sort H\n    sort P = ?\n    requires Storage[C = P{key}]\n    entity h(p: P, s: Set[T = P.Key])\n  end")
    };
    let concrete = |key: &str| {
        format!(
            "sort MemStore\n    provides Storage[C = MemStore, Key = {key}]\n    entity memStore\n  end\n  operation k(s: Set[T = MemStore.Key]) -> Int64 = 1"
        )
    };
    for (tag, decl) in [("op", &op as &dyn Fn(&str) -> String), ("sort", &sort)] {
        assert_loads(
            &program(&format!("wi_7ab56.rigid.{tag}.open"), &decl("")),
            &format!("{tag}: `P.Key` open"),
        );
        assert_unlawful(
            &program(
                &format!("wi_7ab56.rigid.{tag}.float"),
                &decl(", Key = Float"),
            ),
            "Set",
            "T",
            "anthill.prelude.Float",
            &format!("{tag}: `P.Key` bound to `Float`"),
        );
        assert_loads(
            &program(&format!("wi_7ab56.rigid.{tag}.int"), &decl(", Key = Int64")),
            &format!("{tag}: `P.Key` bound to `Int64`"),
        );
    }
    assert_unlawful(
        &program("wi_7ab56.rigid.memstore.float", &concrete("Float")),
        "Set",
        "T",
        "anthill.prelude.Float",
        "`MemStore.Key` provided as `Float`",
    );
    assert_loads(
        &program("wi_7ab56.rigid.memstore.int", &concrete("Int64")),
        "`MemStore.Key` provided as `Int64`",
    );
}

/// A receiver's type is read as the body check reads it: through a field path, a type
/// alias, and a sibling parameter's own projection, declared before or after it; and a
/// projection nested in the key is read where it stands.
#[test]
fn a_projection_key_reads_through_a_field_path_an_alias_and_a_sibling_parameter() {
    let cases: [(&str, fn(&str) -> String, &str, &str); 6] = [
        (
            "path",
            |e| {
                format!("sort W\n    entity w(cell: Leaf{e})\n  end\n  operation k(x: W, s: Set[T = x.cell.E]) -> Int64 = 1")
            },
            "Set",
            "anthill.prelude.Float",
        ),
        (
            "alias",
            |e| format!("sort LF = Leaf{e}\n  operation k(x: LF, s: Set[T = x.E]) -> Int64 = 1"),
            "Set",
            "anthill.prelude.Float",
        ),
        (
            "chain",
            |e| format!("operation k(y: Leaf{e}, x: Leaf[E = y.E], s: Set[T = x.E]) -> Int64 = 1"),
            "Set",
            "anthill.prelude.Float",
        ),
        (
            "chain_after",
            |e| format!("operation k(s: Set[T = x.E], x: Leaf[E = y.E], y: Leaf{e}) -> Int64 = 1"),
            "Set",
            "anthill.prelude.Float",
        ),
        (
            "nested",
            |e| format!("operation k(x: Leaf{e}, s: Set[T = List[T = x.E]]) -> Int64 = 1"),
            "Set",
            "anthill.prelude.List[T = anthill.prelude.Float]",
        ),
        (
            "map",
            |e| format!("operation k(x: Leaf{e}, m: Map[K = x.E, V = Int64]) -> Int64 = 1"),
            "Map",
            "anthill.prelude.Float",
        ),
    ];
    for (tag, decl, container, printed) in cases {
        let param = if container == "Map" { "K" } else { "T" };
        // The chains fix their member at `y`; open there, `x.E` is open too.
        assert_loads(
            &program(&format!("wi_7ab56.read.{tag}.open"), &decl("")),
            &format!("{tag}, open"),
        );
        assert_unlawful(
            &program(&format!("wi_7ab56.read.{tag}.float"), &decl("[E = Float]")),
            container,
            param,
            printed,
            &format!("{tag} at `Float`"),
        );
        assert_loads(
            &program(&format!("wi_7ab56.read.{tag}.int"), &decl("[E = Int64]")),
            &format!("{tag} at `Int64`"),
        );
    }
}

/// A receiver that is a binder of the body has no declared type the check can read, and a
/// `let` that shadows a parameter is its own binder: both are refused as not judged, naming
/// the receiver. CONTROL: the key off the parameter itself loads — under every back-out but
/// the signature-only one, where a body's `let` names no operation.
#[test]
fn a_key_whose_receiver_is_no_parameter_is_refused_as_not_judged() {
    let alias = "operation k(x: Leaf) -> Bool =\n    let y = x\n    let z: Option[T = Set[T = y.E]] = none\n    true";
    assert_not_judged(
        &program("wi_7ab56.local.alias", alias),
        "T = y.E",
        "its receiver `y` is no parameter of `wi_7ab56.local.alias.k`",
        "a key off a `let` alias",
    );
    let shadow =
        "operation k(x: Leaf[E = Int64]) -> Bool =\n    let x = leaf(e: 1.5)\n    let z: Option[T = Set[T = x.E]] = none\n    true";
    assert_not_judged(
        &program("wi_7ab56.local.shadow", shadow),
        "T = x.E",
        "its receiver `x` is no parameter of `wi_7ab56.local.shadow.k`",
        "a key off a `let` that shadows the parameter",
    );
    assert_loads(
        &program("wi_7ab56.local.control", &at("let", "Leaf")),
        "the key off the parameter",
    );
}

/// A member no one declares does not read, and the key is refused as not judged — in a
/// spec's body-less operation, the one refusal the program gets.
#[test]
fn a_key_whose_member_does_not_read_is_refused_as_not_judged() {
    let src = program(
        "wi_7ab56.nomember",
        "sort Sp\n    operation k(x: Leaf, s: Set[T = x.Nope]) -> Int64\n  end",
    );
    let errs = load_errors_of(&src);
    assert_eq!(errs.len(), 1, "one refusal: {errs:#?}");
    assert_not_judged(
        &src,
        "T = x.Nope",
        "type 'wi_7ab56.nomember.Leaf' has no member 'Nope'",
        "a key whose member does not read",
    );
}

/// A refusal names the CONTAINER's parameter the key is bound to — `Map`'s `K`, not the
/// `T` of the `Eq` its clause requires, which the two refusals once disagreed about.
#[test]
fn a_key_not_judged_is_named_by_the_containers_parameter() {
    let src = program(
        "wi_7ab56.mapparam",
        "operation k(x: Leaf) -> Bool =\n    let y = x\n    let z: Option[T = Map[K = y.E, V = Int64]] = none\n    true",
    );
    let (keys, errs) = key_refusals(&src);
    assert_eq!(keys.len(), 1, "one key refusal: {errs:#?}");
    assert!(
        keys[0].contains(
            "'anthill.prelude.Map' requires `anthill.prelude.Eq` at its parameter `K`, and whether `K = y.E`"
        ),
        "the refusal names `K`, got:\n{}",
        keys[0]
    );
}

/// A key abstract BESIDE its projection — a type parameter written next to it — is abstract
/// whatever the projection reads to, so one that does not read is not refused for it: no
/// reading of `y.E` makes `(a: F, b: y.E)` ground. CONTROL: the same key without `F` is
/// refused as not judged — its reason changes under three back-outs (see the header).
#[test]
fn a_key_abstract_beside_its_projection_is_not_judged_for_it() {
    let body = |key: &str| {
        format!(
            "operation k[F](x: Leaf) -> Bool =\n    let y = x\n    let z: Option[T = Set[T = {key}]] = none\n    true"
        )
    };
    assert_loads(
        &program("wi_7ab56.beside", &body("(a: F, b: y.E)")),
        "a key abstract beside its projection",
    );
    assert_not_judged(
        &program("wi_7ab56.beside.control", &body("(a: Int64, b: y.E)")),
        "T = (a: Int64, b: y.E)",
        "its receiver `y` is no parameter of `wi_7ab56.beside.control.k`",
        "the same key without the type parameter",
    );
}

/// A key whose projections read through one another without end is refused as not judged,
/// never passed: here `x.E` reads to `List[T = x.E]`, and on. (The declaration is refused
/// for the cycle as well.)
#[test]
fn a_key_whose_projections_do_not_settle_is_refused() {
    let src = program(
        "wi_7ab56.settle",
        "operation k(x: Leaf[E = List[T = x.E]], s: Set[T = x.E]) -> Int64 = 1",
    );
    let (keys, errs) = key_refusals(&src);
    assert_eq!(keys.len(), 1, "one key refusal: {errs:#?}");
    assert!(
        keys[0].contains("whether `T = x.E` provides it is not known")
            && keys[0].contains("its projections read through one another"),
        "the key is refused as unsettled, got:\n{}",
        keys[0]
    );
}
