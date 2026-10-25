//! WI-20261023-GJVVW — A NAME AN OPERATION'S SIGNATURE DECLARES IS IN SCOPE IN THAT
//! OPERATION ONLY: no import reaches it, and from outside the operation neither does a
//! path or a scope an import or a `requires` opens.
//!
//! A parameter, a type parameter, the operation's `result` and a callback's place are
//! symbols the loader registers under the operation's qualified name (`lib.useIt.c`). An
//! import `import lib.{c}` that found no `lib.c` yet — a fact's head is minted after the
//! imports are read — took the nested-scope rung, which is there for an entity declared
//! in a sort of `lib`, and bound the parameter one scope below; the goal `c(?x)` then
//! answered nothing, silently, and answered 1 with the parameter renamed. The same
//! symbols were reached by an import naming one (`import lib.useIt.c`,
//! `import lib.useIt.{c}`) and by a goal spelling one's path, each loading clean. A sort
//! that shares its name with an operation is one symbol, so its scope holds the
//! operation's parameters beside the sort's members, and a wildcard import or a
//! `requires` of that sort reached them.
//!
//! What is checked is `SymbolTable::is_operation_place`: the import sites (plain, the
//! selective rungs, the nested-scope rung) ask it of what they land on; the resolver's
//! visibility filter and the dotted ladder ask `operation_place_visible_from`, which
//! admits the name from the operation's own scope and the scopes it encloses. A
//! reference position that reads such a path reports it as an unresolved name
//! (`Loader::resolve_dotted_reported`), and hands back the place rather than a bare
//! intern of its qualified name — a second symbol of that name, which a stored rule head
//! tripped WI-581's assert on (`fact lib.useIt.c(2)`). A refused `internal` name now
//! hands back its own symbol for the same reason: `fact lib.secret(2)` over an
//! `internal` operation aborted the load on that assert before this change.
//!
//! Not this file's: a sort that shares its name with an operation still gives the
//! operation's parameters and type parameters the sort's scope, so a rule in the sort's
//! body reads the operation's parameter, an import reaches its type parameter, and the
//! sort accepts the operation's type parameter in a bracket.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ─────────────────────────────
//!
//! | part backed out | rows that fail |
//! |---|---|
//! | the import sites | `a_selective_import_reaches_the_relation_not_the_parameter`, `a_sort_named_like_an_operation_keeps_the_relation_importable`, `an_import_naming_an_operations_own_name_is_refused` |
//! | the resolver's visibility filter | `a_wildcard_or_a_requires_of_a_sort_named_like_an_operation_reaches_no_parameter` |
//! | the dotted ladder | `a_path_to_a_parameter_from_outside_its_operation_is_refused`, `a_type_naming_another_operations_type_parameter_is_refused`, `a_rule_head_at_a_parameters_path_is_refused`, `a_host_name_reaches_no_parameter` |
//! | the report of a place's path (`resolve_dotted_reported`) | `a_path_to_a_parameter_from_outside_its_operation_is_refused`, `a_type_naming_another_operations_type_parameter_is_refused`, `a_rule_head_at_a_parameters_path_is_refused` |
//! | `push_forbidden_internal` returning a fresh intern, as before | `a_rule_head_at_an_internal_name_is_refused_as_internal` (WI-581's assert) |
//!
//! The controls pass either way by design: the plain import and the qualified goal name
//! `lib.c` exactly, which the parameter's symbol never was; two parameters of one name
//! are two matches, and the nested rung binds none; the sort's own entity is a member of
//! its scope and not the operation's; an operation reads its own parameter beside a
//! relation of that name.

use anthill_core::eval::Value;
use anthill_core::intern::ResolveResult;

use crate::common::{
    assert_refused_naming, definite_unary, load_errors_of_files, run_int64, try_load_kb_with_files,
};

const LIB: &str = "namespace test.gjvvw.lib
  import anthill.prelude.{Int64}
  operation useIt(c: Int64) -> Int64 = c
  operation idt[T](x: T) -> T = x
  operation hof(f: (Int64) -> Int64, a: Int64) -> Int64 = f(a)
  fact c(1)
end
";

/// `LIB` with no relation `c`: an import of `c` names nothing importable there.
const LIB_NO_RELATION: &str = "namespace test.gjvvw.bare
  import anthill.prelude.{Int64}
  operation useIt(c: Int64) -> Int64 = c
end
";

/// A sort and an operation of one name, with a relation named like the operation's
/// parameter and a fact over the sort's entity.
const PAIR: &str = "namespace test.gjvvw.pair
  import anthill.prelude.{Int64}
  sort Pos
    entity pk(v: Int64)
  end
  operation Pos(c: Int64) -> Int64 = c
  fact c(1)
  fact holds(pk(v: 2))
end
";

/// The definite answers of `relation(?x)` over `files` loaded in one call, each an `Int64`.
fn answers(files: &[&str], relation: &str) -> Vec<i64> {
    let mut kb = try_load_kb_with_files(files).unwrap_or_else(|errs| panic!("{}", errs.join("\n")));
    definite_unary(&mut kb, relation)
        .into_iter()
        .map(|v| match v {
            Value::Int(n) => n,
            other => panic!("`{relation}` answered a non-Int64 {other:?}"),
        })
        .collect()
}

#[test]
fn a_selective_import_reaches_the_relation_not_the_parameter() {
    let user = "namespace test.gjvvw.use
  import test.gjvvw.lib.{c}
  rule r(?x) :- c(?x)
end
";
    assert_eq!(answers(&[LIB, user], "test.gjvvw.use.r"), vec![1]);
}

#[test]
fn the_plain_import_and_the_qualified_goal_reach_the_relation() {
    let plain = "namespace test.gjvvw.plain
  import test.gjvvw.lib.c
  rule r(?x) :- c(?x)
end
";
    let qualified = "namespace test.gjvvw.qual
  rule r(?x) :- test.gjvvw.lib.c(?x)
end
";
    assert_eq!(answers(&[LIB, plain], "test.gjvvw.plain.r"), vec![1]);
    assert_eq!(answers(&[LIB, qualified], "test.gjvvw.qual.r"), vec![1]);
}

#[test]
fn two_parameters_of_one_name_bind_no_import() {
    let lib = "namespace test.gjvvw.two
  import anthill.prelude.{Int64}
  operation u1(c: Int64) -> Int64 = c
  operation u2(c: Int64) -> Int64 = c
  fact c(1)
end
";
    let user = "namespace test.gjvvw.twouse
  import test.gjvvw.two.{c}
  rule r(?x) :- c(?x)
end
";
    assert_eq!(answers(&[lib, user], "test.gjvvw.twouse.r"), vec![1]);
}

#[test]
fn a_sort_named_like_an_operation_keeps_the_relation_importable() {
    let user = "namespace test.gjvvw.pairuse
  import test.gjvvw.pair.{c}
  rule r(?x) :- c(?x)
end
";
    assert_eq!(answers(&[PAIR, user], "test.gjvvw.pairuse.r"), vec![1]);
}

#[test]
fn a_sort_named_like_an_operation_keeps_its_entity_importable() {
    let user = "namespace test.gjvvw.pairent
  import test.gjvvw.pair.{pk, holds}
  rule s(?x) :- holds(pk(v: ?x))
end
";
    assert_eq!(answers(&[PAIR, user], "test.gjvvw.pairent.s"), vec![2]);
}

#[test]
fn an_import_naming_an_operations_own_name_is_refused() {
    for (lib, import, path) in [
        (LIB, "test.gjvvw.lib.useIt.{c}", "test.gjvvw.lib.useIt.c"),
        (LIB, "test.gjvvw.lib.useIt.c", "test.gjvvw.lib.useIt.c"),
        (LIB_NO_RELATION, "test.gjvvw.bare.{c}", "test.gjvvw.bare.c"),
        (LIB, "test.gjvvw.lib.{T}", "test.gjvvw.lib.T"),
        (LIB, "test.gjvvw.lib.{result}", "test.gjvvw.lib.result"),
        (LIB, "test.gjvvw.lib.useIt.{result}", "test.gjvvw.lib.useIt.result"),
        (LIB, "test.gjvvw.lib.hof.{f}", "test.gjvvw.lib.hof.f"),
        (LIB, "test.gjvvw.lib.hof.f.result", "test.gjvvw.lib.hof.f.result"),
        (PAIR, "test.gjvvw.pair.Pos.{c}", "test.gjvvw.pair.Pos.c"),
    ] {
        let user = format!("namespace test.gjvvw.imp\n  import {import}\nend\n");
        let errs = load_errors_of_files(&[lib, &user]);
        assert_refused_naming(
            &errs,
            &[&format!("unresolved import '{path}'")],
            &format!("`import {import}`"),
        );
    }
}

#[test]
fn a_wildcard_or_a_requires_of_a_sort_named_like_an_operation_reaches_no_parameter() {
    for clause in ["import test.gjvvw.pair.Pos.*", "requires test.gjvvw.pair.Pos"] {
        let user = format!("namespace test.gjvvw.open\n  {clause}\n  rule r(?x) :- c(?x)\nend\n");
        let errs = load_errors_of_files(&[PAIR, &user]);
        assert_refused_naming(&errs, &["rule-body goal `c` names nothing"], clause);
    }
}

#[test]
fn a_path_to_a_parameter_from_outside_its_operation_is_refused() {
    let user = "namespace test.gjvvw.path
  rule r(?x) :- test.gjvvw.lib.useIt.c(?x)
end
";
    let errs = load_errors_of_files(&[LIB, user]);
    assert_refused_naming(
        &errs,
        &["unresolved name 'test.gjvvw.lib.useIt.c'"],
        "a goal spelling a parameter's path",
    );
}

#[test]
fn a_type_naming_another_operations_type_parameter_is_refused() {
    let user = "namespace test.gjvvw.ty
  import anthill.prelude.{Int64}
  operation f(x: test.gjvvw.lib.idt.T) -> Int64 = 1
end
";
    let errs = load_errors_of_files(&[LIB, user]);
    assert_refused_naming(
        &errs,
        &["unresolved name 'test.gjvvw.lib.idt.T'"],
        "a parameter's type naming `idt`'s type parameter",
    );
}

#[test]
fn a_rule_head_at_a_parameters_path_is_refused() {
    for head in [
        "fact useIt.c(1)",
        "rule useIt.c(?x) :- c(?x)",
        "fact useIt.result",
        "fact test.gjvvw.lib.useIt.c(2)",
    ] {
        let user = format!("namespace test.gjvvw.lib\n  {head}\nend\n");
        let errs = load_errors_of_files(&[LIB, &user]);
        let path = head.split(['(', ' ']).nth(1).expect("a head");
        assert_refused_naming(&errs, &[&format!("unresolved name '{path}'")], head);
    }
}

#[test]
fn a_rule_head_at_an_internal_name_is_refused_as_internal() {
    let lib = "namespace test.gjvvw.hidden
  import anthill.prelude.{Int64}
  internal operation secret(x: Int64) -> Int64 = x
end
";
    let user = "namespace test.gjvvw.other
  fact test.gjvvw.hidden.secret(2)
end
";
    let errs = load_errors_of_files(&[lib, user]);
    assert_refused_naming(
        &errs,
        &["'test.gjvvw.hidden.secret' is internal to 'test.gjvvw.hidden'"],
        "a fact head spelling an internal operation's path",
    );
}

#[test]
fn a_host_name_reaches_no_parameter() {
    let kb = try_load_kb_with_files(&[LIB]).unwrap_or_else(|errs| panic!("{}", errs.join("\n")));
    assert!(
        matches!(kb.resolve_name_in_global("test.gjvvw.lib.useIt.c"), ResolveResult::NotFound),
        "a host name reads at `<global>`, inside no operation"
    );
    assert!(
        matches!(kb.resolve_name_in_global("test.gjvvw.lib.c"), ResolveResult::Found(_)),
        "control: the relation is reached"
    );
}

#[test]
fn an_operation_reads_its_own_parameter_beside_a_relation_of_its_name() {
    let src = "namespace test.gjvvw.own
  import anthill.prelude.{Int64}
  operation useIt(c: Int64) -> Int64 = c
  operation hof(f: (Int64) -> Int64, a: Int64) -> Int64 = f(a)
  operation main() -> Int64 = hof(lambda (n) -> useIt(n), 5)
  fact c(1)
end
";
    assert_eq!(run_int64(src, "test.gjvvw.own.main"), Ok(5));
}
