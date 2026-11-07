//! WI-20260929-TJ3G4 — a key is judged for a lawful `Eq` at each position measured here: a
//! key whose type HOLDS A VALUE as its ground twin is, and a key written in an operation's
//! own `requires` as the same key in its signature is.
//!
//! THE VALUE. The use-site check (`typing::check_use_site_requires_eq`) once kept only the
//! bindings of a written type that were hash-consed terms, on the reading that the others
//! were values in a type position. A type that holds one somewhere inside is no term either,
//! so `Map[K = Buf[T = Float, N = 3], V = Int64]` loaded where `Map[K = Buf[T = Float, N =
//! Bool], V = Int64]` was refused — in an operation's parameter, in a sort's `requires` and in
//! a `provides` clause alike, and so did a key whose OWN argument holds the value (`P[A =
//! Float, B = Buf[T = Int64, N = 3]]`). WI-20260829-2NMXA narrowed the filter to a binding
//! that IS a value at its root and pinned the parameter position
//! (`wi_2nmxa…::a_key_whose_type_holds_a_value_is_checked_for_a_lawful_equality`); the rows
//! here pin the others, and the key that holds its value one argument down.
//!
//! THE OPERATION'S `requires`. That clause is lowered as a term (`convert_term`), not by a
//! type lowering, and recorded no use site: `operation k() -> Int64 requires Holder[C =
//! Map[K = Float, V = Int64]]` loaded, its ground key included, where a sort's `requires` of
//! the same was refused. Found while measuring this ticket. A bracket written there as a TYPE
//! ARGUMENT of a bracket is recorded now where `convert_term` builds it, at its own span, its
//! bindings read through the type aliases they name as the finished goal reads them; the
//! goal's own application, a requirement, is no use of its spec, as a sort's clause's is not,
//! and neither is a goal under `not(…)`. A bracket whose arguments the clause refused is not
//! judged again. A literal there is refused before any of this ("unresolved name '3'",
//! WI-20261012-6SAAP), so its value-holding key is written with a value's NAME (`N = size`),
//! the spelling the clause reads as the value in the type. The written-row check reads that
//! clause whole through a source of its own, so it is handed the type lowerings' sites alone
//! (`kb::WrittenTypeSites`), and a row nested there is judged once.
//!
//! A PROJECTION KEY (`Set[T = x.E]`) was refused at both positions, as in a signature: the
//! check read `x.E` as ground. WI-20261102-7AB56 reads it at the receiver's declared type, at
//! both positions alike (`wi_7ab56_projection_key_test`).
//! NOT JUDGED, and not measured here: a key in an `ensures` clause, or in a `fact`'s bracket
//! (`check_use_site_requires_eq`'s non-scope (4)).
//!
//! BACK-OUTS, MEASURED — each ONE part put back wrong, over this file, the `wi_2nmxa` row,
//! `wi835_*`, `wi644_*`, `v25n3` and `rsrp5`; the cases of a row that stops at its first
//! failure also through the CLI, one load each:
//!
//!  * A binding kept only where it is a `Value::Term` (the filter before 2NMXA) — 6:
//!    `a_key_that_holds_a_value_is_refused_where_its_twin_is` (all eight pairs load with no
//!    refusal), `a_key_in_an_operations_requires_is_refused_as_in_its_signature` (the valued
//!    key's signature twin, an occurrence, loads), `a_lawful_or_open_key_in_an_operations_requires_loads`
//!    (`K = size`, a `denoted` TERM, kept and refused), the `wi_2nmxa` row, and
//!    `wi835…::a_function_is_no_key` / `a_set_of_functions_is_refused` (a `Function` key
//!    rides no term).
//!  * No root-value filter — 2: `a_value_at_the_root_is_no_key` ("`K = 3` binds a type that
//!    does not provide `Eq`") and `a_lawful_or_open_key_in_an_operations_requires_loads`
//!    (`K = size`).
//!  * The bracket's site not recorded — 3:
//!    `a_key_in_an_operations_requires_is_refused_as_in_its_signature` (each of its seven keys
//!    loads with no refusal at the `requires`), `two_keys_in_one_goal…` and
//!    `key_refusals_keep_their_source_order` (one refusal).
//!  * Its bindings recorded as converted, aliases unread — 2:
//!    `a_lawful_or_open_key_in_an_operations_requires_loads` (`Set[T = LI]` and `Map[K = TI]`
//!    refused for `LI`, `TI`) and `a_key_in_an_operations_requires_is_refused_as_in_its_signature`
//!    (`Set[T = FA]` refused naming `FA`, where the signature names `Float`).
//!  * A bracket recorded at any depth of the clause, not as a type argument of a bracket — 1:
//!    `a_bracket_that_is_a_goal_is_no_key_under_a_connective_either`.
//!  * A bracket recorded though its arguments were refused — 1:
//!    `a_bracket_whose_argument_was_refused_is_not_judged_again` (a second refusal, "`T =
//!    Self` binds a type that does not provide `Eq`").
//!  * The row check handed every site — 1: `a_row_in_an_operations_requires_is_judged_once`
//!    (two refusals of one label).
//!  * The sites handed out type lowerings first — 1: `key_refusals_keep_their_source_order`.
//!  * The sites taken off the FINISHED goal instead, each at the goal's span (this change's
//!    second cut) — 4: `two_keys_in_one_goal…` (one refusal for two keys),
//!    `a_spec_aliass_key_is_refused_once…` (the alias's fixed key refused again at the
//!    bracketed goal), `a_key_in_an_operations_requires_is_refused_as_in_its_signature` (at
//!    the goal, not the bracket) and `a_bracket_whose_argument_was_refused…`.
//!
//! PASS EITHER WAY BY DESIGN: `a_lawful_key_that_holds_a_value_loads` and the ground twins in
//! the first row — the change admits nothing new there and refuses nothing it did not.

use crate::common::load_errors_of;

/// A program declaring `decl` beside `Buf` and `P`, plain composites, `Holder`, a spec whose
/// carrier is `C`, `Holder2`, one of two parameters, and `size`, a value a type can hold by
/// name.
fn program(ns: &str, decl: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Float, Bool, Map, Set, List}}
  sort Buf
    sort T = ?
    sort N = ?
    entity buf(items: List[T])
  end
  sort P
    sort A = ?
    sort B = ?
    entity p(a: A, b: B)
  end
  sort Holder
    sort C = ?
    operation get(h: C) -> Int64
  end
  sort Holder2
    sort C = ?
    sort D = ?
    operation get(h: C, g: D) -> Int64
  end
  operation size() -> Int64 = 3
  {decl}
end
"#
    )
}

/// `key` written as `Map`'s key at `position`.
fn at(position: &str, key: &str) -> String {
    let map = format!("Map[K = {key}, V = Int64]");
    match position {
        "parameter" => format!("operation k(s: {map}) -> Int64 = 1"),
        "field" => format!("sort H\n    entity h(m: {map})\n  end"),
        "requires" => format!("sort S\n    requires Holder[C = {map}]\n  end"),
        "provides" => format!(
            "sort S\n    provides Holder[C = {map}]\n    operation get(h: {map}) -> Int64 = 1\n  end"
        ),
        other => panic!("no position `{other}`"),
    }
}

/// The positions, each with the number of keys it writes: a `provides` clause's carrier is
/// written again in the member that fits it, and each is a site of its own.
const POSITIONS: [(&str, usize); 4] = [("parameter", 1), ("field", 1), ("requires", 1), ("provides", 2)];

/// The key refusals of `src`: one per written site whose key has no lawful `Eq`.
fn key_refusals(src: &str) -> (Vec<String>, Vec<String>) {
    let errs = load_errors_of(src);
    let keys = errs.iter().filter(|e| e.contains("so it is not a lawful key")).cloned().collect();
    (keys, errs)
}

/// The `line:col` a refusal of the bracket written at byte `at` of `src` begins with.
fn line_col(src: &str, at: usize) -> String {
    let before = &src[..at];
    let line = before.matches('\n').count() + 1;
    let col = at - before.rfind('\n').map_or(0, |nl| nl + 1) + 1;
    format!("{line}:{col}:")
}

/// The `line:col` of each occurrence of `bracket` in `src` after its first `after`.
fn brackets_after(src: &str, after: &str, bracket: &str) -> Vec<String> {
    let from = src.find(after).expect("the fixture writes it");
    src[from..].match_indices(bracket).map(|(i, _)| line_col(src, from + i)).collect()
}

/// `src` refuses exactly `sites` keys, each at `container`'s `param`, naming `printed`.
#[track_caller]
fn assert_key_refusals(src: &str, sites: usize, container: &str, param: &str, printed: &str, why: &str) {
    let (keys, errs) = key_refusals(src);
    assert_eq!(keys.len(), sites, "{why}: {errs:#?}");
    let at_param = format!("'anthill.prelude.{container}' requires `anthill.prelude.Eq` at its parameter `{param}`");
    for k in &keys {
        assert!(
            k.contains(&at_param) && k.contains(printed),
            "{why}: the refusal should name `{param}` and `{printed}`, got:\n{k}"
        );
    }
}

/// The ticket's two keys, beside the twin whose `N` is a type. Each is refused, at each
/// position, once per site, naming the WHOLE key — the value it holds included.
#[test]
fn a_key_that_holds_a_value_is_refused_where_its_twin_is() {
    // The key as the refusal prints it, qualified in the program's namespace.
    let pairs: [(&str, &str, fn(&str) -> String, &str); 2] = [
        (
            "buf",
            "Buf[T = Float, N = 3]",
            |ns| format!("{ns}.Buf[T = anthill.prelude.Float, N = 3]"),
            "Buf[T = Float, N = Bool]",
        ),
        (
            "sibling",
            "P[A = Float, B = Buf[T = Int64, N = 3]]",
            |ns| format!("{ns}.P[A = anthill.prelude.Float, B = {ns}.Buf[T = anthill.prelude.Int64, N = 3]]"),
            "P[A = Float, B = Buf[T = Int64, N = Bool]]",
        ),
    ];
    for (tag, valued, printed, twin) in pairs {
        for (position, sites) in POSITIONS {
            let ns = format!("wi_tj3g4.{tag}.{position}");
            let why = format!("`{valued}` at the {position}");
            assert_key_refusals(&program(&ns, &at(position, valued)), sites, "Map", "K", &printed(&ns), &why);
            // CONTROL — passes either way: the ground twin, refused as it always was.
            let ns = format!("wi_tj3g4.{tag}twin.{position}");
            let (keys, errs) = key_refusals(&program(&ns, &at(position, twin)));
            assert_eq!(keys.len(), sites, "`{twin}` at the {position}: {errs:#?}");
        }
    }
}

/// CONTROL — PASSES EITHER WAY BY DESIGN: a key that holds a value and whose equality is
/// lawful loads at every position, so the refusals above are about `Float`.
#[test]
fn a_lawful_key_that_holds_a_value_loads() {
    for (tag, key) in [
        ("buf", "Buf[T = Int64, N = 3]"),
        ("sibling", "P[A = Int64, B = Buf[T = Int64, N = 3]]"),
    ] {
        for (position, _) in POSITIONS {
            let errs = load_errors_of(&program(&format!("wi_tj3g4.lawful{tag}.{position}"), &at(position, key)));
            assert!(errs.is_empty(), "`{key}` at the {position}: {errs:#?}");
        }
    }
}

/// A value at the root of the key position is no type whose `Eq` could be asked, and the
/// check says nothing of it. Fails with the root-value filter taken out.
#[test]
fn a_value_at_the_root_is_no_key() {
    let errs = load_errors_of(&program("wi_tj3g4.root", &at("parameter", "3")));
    assert!(errs.is_empty(), "{errs:#?}");
}

/// A key written in an operation's own `requires` is refused as the same key in its
/// signature is, once, at the bracket that writes it: a plain key, its positional spelling, one
/// nested a container down, one whose own argument is a type, one that holds a value, one
/// written through a type alias (named by the type the alias stands for) and one under a named
/// binder. The CONTROL is loaded beside each: the same type as a parameter, refused by WI-835
/// naming the same key, so the two positions are held to one verdict and not to two.
#[test]
fn a_key_in_an_operations_requires_is_refused_as_in_its_signature() {
    let float = "anthill.prelude.Float";
    for (tag, aliases, binder, written, container, param, printed) in [
        ("plain", "", "", "Map[K = Float, V = Int64]", "Map", "K", float.to_owned()),
        ("positional", "", "", "Map[Float, Int64]", "Map", "K", float.to_owned()),
        ("nested", "", "", "List[T = Set[T = Float]]", "Set", "T", float.to_owned()),
        (
            "typed",
            "",
            "",
            "Map[K = Buf[T = Float, N = Bool], V = Int64]",
            "Map",
            "K",
            "Buf[T = anthill.prelude.Float, N = anthill.prelude.Bool]".to_owned(),
        ),
        (
            "valued",
            "",
            "",
            "Map[K = Buf[T = Float, N = size], V = Int64]",
            "Map",
            "K",
            "Buf[T = anthill.prelude.Float, N = size]".to_owned(),
        ),
        ("aliased", "sort FA = Float", "", "Set[T = FA]", "Set", "T", format!("`T = {float}`")),
        ("binder", "", "h: ", "Map[K = Float, V = Int64]", "Map", "K", float.to_owned()),
    ] {
        let ns = format!("wi_tj3g4.contract.{tag}");
        let bound = format!("{binder}Holder[C = {written}]");
        let src = program(&ns, &format!("{aliases}\n  operation k() -> Int64 requires {bound} = 1"));
        let why = format!("`requires {bound}`");
        assert_key_refusals(&src, 1, container, param, &printed, &why);
        // At the bracket that writes the key, as a signature's refusal is at its own.
        let at = brackets_after(&src, "requires", &format!("{container}["));
        let (keys, _) = key_refusals(&src);
        assert!(keys[0].starts_with(&at[0]), "{why}: the refusal should be at {}, got:\n{}", at[0], keys[0]);
        // CONTROL — the signature twin.
        let twin = program(&format!("{ns}sig"), &format!("{aliases}\n  operation k(s: {written}) -> Int64 = 1"));
        assert_key_refusals(&twin, 1, container, param, &printed, &format!("`k(s: {written})`"));
    }
}

/// A requirement is no use of its spec, wherever the goal stands: `requires not(Set[T =
/// Float])` writes the bracket as a goal of the clause, under a connective, not as a type
/// argument of one, and loads as `requires Set[T = Float]` does.
#[test]
fn a_bracket_that_is_a_goal_is_no_key_under_a_connective_either() {
    let decl = "operation f() -> Int64 requires not(Set[T = Float]) = 1\n  \
                operation g() -> Int64 requires Set[T = Float] = 1";
    let errs = load_errors_of(&program("wi_tj3g4.connective", decl));
    assert!(errs.is_empty(), "{errs:#?}");
}

/// A bracket whose argument the clause refused is not judged again as a key: `Self` in an
/// operation's `requires` is refused where it is written, and a `Set[T = Self]` there adds no
/// second refusal telling the author `Self` has no `Eq`. (Its signature twin, `f2`, reads
/// `Self` as `Bag`, whose equality is lawful, and loads.)
#[test]
fn a_bracket_whose_argument_was_refused_is_not_judged_again() {
    let decl = "sort Bag\n    entity bag(x: Int64)\n    \
                operation f() -> Int64 requires Holder[C = Set[T = Self]] = 1\n    \
                operation f2(s: Set[T = Self]) -> Int64 = 1\n  end";
    let errs = load_errors_of(&program("wi_tj3g4.refusedarg", decl));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains("`Self`"), "{errs:#?}");
}

/// Key refusals keep the order their sites were written in, whichever walk recorded them: an
/// operation's `requires` one line above a signature is reported first.
#[test]
fn key_refusals_keep_their_source_order() {
    let decl = "operation a() -> Int64 requires Holder[C = Map[K = Float, V = Int64]] = 1\n  \
                operation b(s: Set[T = Float]) -> Int64 = 1";
    let (keys, errs) = key_refusals(&program("wi_tj3g4.order", decl));
    assert_eq!(keys.len(), 2, "{errs:#?}");
    assert!(keys[0].contains("'anthill.prelude.Map'") && keys[1].contains("'anthill.prelude.Set'"), "{keys:#?}");
}

/// Two keys in one goal are two refusals, each at its own bracket, as the same two in a
/// signature are: what is recorded is each bracket a goal holds, not the goal.
#[test]
fn two_keys_in_one_goal_are_refused_each_at_its_bracket() {
    let decl = "operation k() -> Int64 requires Holder2[C = Map[K = Float, V = Int64], D = Map[K = Float, V = Int64]] = 1";
    let src = program("wi_tj3g4.two", decl);
    let (keys, errs) = key_refusals(&src);
    let at = brackets_after(&src, "requires", "Map[");
    assert_eq!((keys.len(), at.len()), (2, 2), "{errs:#?}");
    for place in &at {
        assert!(keys.iter().any(|k| k.starts_with(place)), "no refusal at {place}: {keys:#?}");
    }
}

/// A spec alias's key is judged where the alias writes it, once: a goal naming the alias,
/// bracketed or bare, writes no bracket of that key and adds no refusal of it.
#[test]
fn a_spec_aliass_key_is_refused_once_where_the_alias_writes_it() {
    let decl = "sort FH = Holder2[C = Set[T = Float]]\n  \
                operation f() -> Int64 requires FH[D = Int64] = 1\n  \
                operation g() -> Int64 requires FH = 1";
    let src = program("wi_tj3g4.specalias", decl);
    let (keys, errs) = key_refusals(&src);
    assert_eq!(keys.len(), 1, "{errs:#?}");
    let at = brackets_after(&src, "sort FH", "Set[");
    assert!(keys[0].starts_with(&at[0]), "the refusal should be at {}, got:\n{}", at[0], keys[0]);
}

/// In an operation's `requires`, a lawful key, one that holds a value with a lawful element,
/// one bound to the operation's own type parameter (the requirement of the code that binds
/// it), a value at the root, and a lawful key written through a type alias — of a sort and of
/// a tuple — all load. The two aliased ones fail with the bindings recorded as converted, their
/// aliases unread, and the value at the root without the root-value filter (the header's table).
#[test]
fn a_lawful_or_open_key_in_an_operations_requires_loads() {
    for (tag, aliases, op) in [
        ("lawful", "", "k() -> Int64 requires Holder[C = Map[K = Int64, V = Float]]"),
        ("valued", "", "k() -> Int64 requires Holder[C = Map[K = Buf[T = Int64, N = size], V = Int64]]"),
        ("open", "", "k[X]() -> Int64 requires Holder[C = Map[K = X, V = Int64]]"),
        ("root", "", "k() -> Int64 requires Holder[C = Map[K = size, V = Int64]]"),
        ("aliased", "sort LI = List[T = Int64]", "k() -> Int64 requires Holder[C = Set[T = LI]]"),
        ("tuple", "sort TI = (Int64, Bool)", "k() -> Int64 requires Holder[C = Map[K = TI, V = Float]]"),
    ] {
        let src = program(&format!("wi_tj3g4.contractok.{tag}"), &format!("{aliases}\n  operation {op} = 1"));
        let errs = load_errors_of(&src);
        assert!(errs.is_empty(), "`{op}`: {errs:#?}");
    }
}

/// A row written in a type nested in an operation's `requires` is judged ONCE: the written-row
/// check reads the clause whole (its source 3) and skips the sites the `Eq`-key check reads
/// there. Read through both, one unregistered label was two refusals.
#[test]
fn a_row_in_an_operations_requires_is_judged_once() {
    let decl = "sort Spec\n    effects E = ?\n    operation run() -> Int64\n  end\n  sort Beep end\n  \
                operation k() -> Int64 requires Holder[C = Spec[E = {Beep}]] = 1";
    let errs = load_errors_of(&program("wi_tj3g4.row", decl));
    let rows: Vec<&String> = errs.iter().filter(|e| e.contains("is not a REGISTERED effect kind")).collect();
    assert_eq!(rows.len(), 1, "{errs:#?}");
    assert!(rows[0].contains("`wi_tj3g4.row.k`'s `requires Holder[C = Spec[E = {Beep}]]`"), "{rows:#?}");
}
