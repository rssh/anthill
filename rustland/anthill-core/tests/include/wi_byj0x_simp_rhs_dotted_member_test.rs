//! WI-20261106-BYJ0X — A PAREN-LESS DOTTED MEMBER IN A `@[simp]` RIGHT-HAND SIDE DIED IN THE
//! TYPER WHERE THE REWRITE FIRED.
//!
//! Over `sort K { const seven: Int64 = 7; operation one() -> Int64 = 1; … }`, the
//! replacement of `f(?a) <=> K.seven @[simp]` (and `K.one`, `K.mk.v`, a nested sort's
//! `K.In`) was refused at every body it was spliced into:
//!
//! ```text
//!   type mismatch in p.K.reference: expected a type value recorded where the sort is
//!     written (proposal 055 §1), got a plain reference to the sort — a defect in the walk
//!     that built this occurrence, not an error in the program
//!   type mismatch in seven.name: expected resolved name, got unresolved
//! ```
//!
//! while `seven`, `K.one()` and `K.mk().v` ran. The replacement is built by the rule-body
//! walk with the const fold off, so the walk's DATA-slot readers of a dotted name declined and
//! the chain stood, its root a plain reference to the sort. It is now built by the walk that
//! reads the same text in an operation body (`Loader::replacement_dotted_name_occurrence`).
//!
//! ## WHICH ROWS MOVE
//!
//! With `replacement_dotted_name_occurrence` returning `None` at once (the change backed out),
//! measured over this file:
//!
//! - fail: `a_dotted_member_in_a_replacement_runs_where_it_fires`,
//!   `a_dotted_member_nested_in_a_replacement_runs_where_it_fires`,
//!   `a_dotted_sort_in_a_replacement_is_its_type_value`,
//!   `a_dotted_const_in_a_replacement_loads_where_a_rule_fires_it` — each refused as above.
//! - pass, by design: `a_nullary_operation_fired_in_a_rule_body_is_unmoved` (the resolver
//!   reduced the chain there already), `a_name_with_no_reading_keeps_its_refusal` (the
//!   delegation leaves such a name to the head-name check), and
//!   `a_quoted_field_in_a_replacement_is_never_a_silent_miss` — which fails instead with the
//!   change's `in_quoted_term` gate taken out: the fired field then holds `seven`, and the
//!   fact holding the chain is not found, with nothing refused.

use crate::common::{load_errors_of, print_type, query_unary, run_int64, scalar_display, try_load_kb_with};

/// The sort whose members the rows name, and the one-segment names the twins read.
const K: &str = "\
  import byja.K.{seven, one, mk, In}
  import byja.K.In.{eight}
  sort K
    const seven: Int64 = 7
    operation one() -> Int64 = 1
    entity box(v: Int64)
    operation mk() -> box = box(v: 3)
    sort In
      entity inn
      const eight: Int64 = 8
    end
  end
";

/// `f`, its rewrite to `rhs`, and `consumer`, in namespace `byja`.
fn program(f_result: &str, rhs: &str, consumer: &str) -> String {
    format!(
        "namespace byja\n  import anthill.prelude.{{Int64, Type}}\n{K}  \
         operation f(a: Int64) -> {f_result}\n  \
         rule r: f(?a) <=> {rhs} @[simp]\n{consumer}end\n"
    )
}

/// What `byja.g()` runs to, with `f(1)` in its body rewritten to `rhs`.
fn run_spliced(rhs: &str) -> Result<i64, String> {
    run_int64(
        &program("Int64", rhs, "  operation g() -> Int64 = f(1)\n"),
        "byja.g",
    )
}

/// The answers of `byja.<rel>(?r)`, rendered, over `src` loaded clean.
fn answers(src: &str, rel: &str) -> Vec<String> {
    let mut kb = try_load_kb_with(src)
        .unwrap_or_else(|errs| panic!("refused:\n{}", errs.join("\n")));
    query_unary(&mut kb, &format!("byja.{rel}"))
        .iter()
        .map(|(v, _)| scalar_display(&kb, v).unwrap_or_else(|| print_type(&kb, v)))
        .collect()
}

/// **THE HEADLINE.** Spliced into an operation body, each dotted member runs to what its
/// twin — the one-segment name, or the applied spelling — runs to: a const its value, a
/// nullary operation its call, a field read on that call the field.
///
/// RED under the back-out, each dotted row refused as the module doc shows. The twins are
/// green either way: they are what the dotted rows are read against.
#[test]
fn a_dotted_member_in_a_replacement_runs_where_it_fires() {
    for (what, dotted, twin, value) in [
        ("a const", "K.seven", "seven", 7),
        ("a const by its whole path", "byja.K.seven", "seven", 7),
        ("a const of a nested sort", "K.In.eight", "eight", 8),
        ("a nullary operation", "K.one", "K.one()", 1),
        ("a field read on a nullary operation", "K.mk.v", "K.mk().v", 3),
    ] {
        assert_eq!(run_spliced(twin), Ok(value), "{what}: the twin `{twin}` is the yardstick");
        assert_eq!(run_spliced(dotted), Ok(value), "{what}: `{dotted}` runs as `{twin}` does");
    }
}

/// …and so does one written INSIDE the replacement: a call's argument, a constructor's field
/// the lowering wraps in `some(…)` (the field is an `Option`, and the walk builds the written
/// child under the wrap), and one wrapped as written.
///
/// RED under the back-out, each row refused as the module doc shows.
#[test]
fn a_dotted_member_nested_in_a_replacement_runs_where_it_fires() {
    for (what, rhs, value) in [
        ("a call's argument", "id(K.seven)", 7),
        ("a field the lowering wraps", "ob(v: K.seven)", 7),
        ("a field wrapped as written", "ob(v: some(K.one))", 1),
    ] {
        // `f` returns what the replacement builds; the body reads an `ob`'s field back out.
        let (result, call) = if rhs.starts_with("ob(") {
            ("ob", "match f(1).v\n    case some(x) -> x\n    case _ -> 0")
        } else {
            ("Int64", "f(1)")
        };
        let src = format!(
            "namespace byjn\n  import anthill.prelude.{{Int64, Option}}\n  \
             import anthill.prelude.Option.{{some}}\n  \
             sort K\n    const seven: Int64 = 7\n    operation one() -> Int64 = 1\n  end\n  \
             entity ob(v: Option[T = Int64])\n  operation id(x: Int64) -> Int64 = x\n  \
             operation f(a: Int64) -> {result}\n  \
             rule r: f(?a) <=> {rhs} @[simp]\n  \
             operation g() -> Int64 = {call}\nend\n"
        );
        assert_eq!(run_int64(&src, "byjn.g"), Ok(value), "{what}: `{rhs}`");
    }
}

/// A dotted path to a sort is the sort's type value, as its one-segment name is.
///
/// RED under the back-out: refused as the module doc shows.
#[test]
fn a_dotted_sort_in_a_replacement_is_its_type_value() {
    let consumer = "  operation g(x: Int64) -> Type = f(x)\n  rule t(?v) :- ?v <=> g(1)\n";
    let twin = answers(&program("Type", "In", consumer), "t");
    assert_eq!(twin.len(), 1, "the twin `In` answers once: {twin:?}");
    for dotted in ["K.In", "byja.K.In"] {
        assert_eq!(
            answers(&program("Type", dotted, consumer), "t"),
            twin,
            "`{dotted}` is the type value `In` is"
        );
    }
}

/// Fired by the resolver in a RULE body, the dotted const answers what the one-segment name
/// answers there. WHAT that is — the const's name, not its value, in this position — is the
/// one-segment spelling's reading, and not this ticket's: the row holds the two to one answer.
///
/// RED under the back-out: refused as the module doc shows, with no operation body in the
/// file to fire in.
#[test]
fn a_dotted_const_in_a_replacement_loads_where_a_rule_fires_it() {
    let consumer = "  rule d(?v) :- ?v <=> f(1)\n";
    let twin = answers(&program("Int64", "seven", consumer), "d");
    assert_eq!(twin.len(), 1, "the twin answers once: {twin:?}");
    assert_eq!(answers(&program("Int64", "K.seven", consumer), "d"), twin);
}

/// A CONTROL: fired in a rule body, the resolver already reduced a dotted nullary operation
/// to its call, and the node the replacement is built as now — that call — answers the same.
///
/// GREEN under the back-out, by design.
#[test]
fn a_nullary_operation_fired_in_a_rule_body_is_unmoved() {
    let consumer = "  rule d(?v) :- ?v <=> f(1)\n";
    for rhs in ["K.one", "K.one()", "K.mk.v"] {
        let expected = if rhs == "K.mk.v" { "3" } else { "1" };
        assert_eq!(answers(&program("Int64", rhs, consumer), "d"), [expected], "`{rhs}`");
    }
}

/// A CONTROL: a dotted name with no reading keeps the refusals it had, and gains none — the
/// name that names nothing, the member hidden by `internal`, the namespace. The delegation
/// leaves each to the checks that judge it; handed to the operation-body walk, they would be
/// reported there a second time. The counts are the ones measured before the change: the
/// hidden member was refused twice already, by the head-name check and where it fires.
///
/// GREEN under the back-out, by design.
#[test]
fn a_name_with_no_reading_keeps_its_refusal() {
    const LIB: &str = "\
namespace byjb.lib
  import anthill.prelude.{Int64}
  sort Vault
    internal operation secret() -> Int64 = 1
  end
end
";
    for (rhs, says, count) in [
        ("K.zz", "`K.zz` names nothing", 1),
        ("K.zz.deep", "`K.zz` names nothing", 1),
        ("Vault.secret", "is internal to 'byjb.lib.Vault'", 2),
        ("byjb.lib", "is a namespace", 1),
    ] {
        let src = format!(
            "{LIB}{}",
            program("Int64", rhs, "  operation g() -> Int64 = f(1)\n")
                .replacen("  import anthill.prelude", "  import byjb.lib.{Vault}\n  import anthill.prelude", 1)
        );
        let errs = load_errors_of(&src);
        assert!(
            errs.len() == count && errs.iter().all(|e| e.contains(says)),
            "`{rhs}`: refused {count} time(s), each saying {says:?}: {errs:#?}"
        );
    }
}

/// A CONTROL FOR THE QUOTED-FIELD GATE: a dotted name in a `Term` field of a replacement is
/// the term its author wrote, which the fact it is matched with holds. Fired, it is refused
/// where it fires (the chain is typed there — a question of its own, open), or it finds that
/// fact — and it never loads clean and finds nothing.
///
/// GREEN under the back-out (refused, as before). RED with only the `in_quoted_term` gate
/// taken out: the fired field holds `seven`, the load is clean, and `hit` has no answer.
///
/// A refusal counts only where the replacement is written (line 9), and the same program
/// with the one-segment `seven` there loads clean — so a fixture broken for another reason
/// does not pass this row.
#[test]
fn a_quoted_field_in_a_replacement_is_never_a_silent_miss() {
    let rewrite = "  rule r: f(?a) <=> Q(pattern: K.seven) @[simp]\n";
    let src = "\
namespace byja
  import anthill.prelude.{Int64}
  import anthill.reflect.{Term}
  sort K
    const seven: Int64 = 7
  end
  entity Q(pattern: Term)
  operation f(a: Int64) -> Q
  rule r: f(?a) <=> Q(pattern: K.seven) @[simp]
  fact held(q: Q(pattern: K.seven))
  rule hit(1) :- ?q <=> f(1), held(q: ?q)
end
";
    let term_import = "  import anthill.reflect.{Term}\n";
    assert!(src.contains(rewrite) && src.contains(term_import), "the fixture is the one described");
    let twin = src
        .replace(rewrite, &rewrite.replace("K.seven", "seven"))
        .replace(term_import, &format!("{term_import}  import byja.K.{{seven}}\n"));
    assert_eq!(load_errors_of(&twin), Vec::<String>::new(), "the fixture is sound with `seven`");
    match try_load_kb_with(src) {
        Err(errs) => assert!(
            errs.iter().all(|e| e.starts_with("9:")),
            "refused where the replacement is written: {errs:#?}"
        ),
        Ok(mut kb) => {
            let found = query_unary(&mut kb, "byja.hit");
            assert_eq!(found.len(), 1, "loaded clean, so the fired field must find its fact");
        }
    }
}
