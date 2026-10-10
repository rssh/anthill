//! WI-20261009-AN6CQ — the standard library is its own load, SEALED, and a program is
//! a later one: driven through the built `anthill` binary, because the rule is about
//! how the PRODUCT hands files to the loader.
//!
//! What a program is held to by that order (`docs/kernel-language.md` §8.3), each
//! proved in `anthill-core` over a KB the test recipes built and each driven here over
//! the KB the CLI builds:
//!
//! * it may not supply the equality of a composite the library defines
//!   (WI-20261006-SZKV7). Until this ticket such a file loaded clean from the command
//!   line — the library and the program went to the loader in one call — and was
//!   refused everywhere a program is loaded after the library;
//! * it may not declare a library operation or type again (WI-20261009-4ZRTG). One
//!   call refuses that too; a library loaded first and NOT sealed does not, and the
//!   program's body then replaced the library's in silence;
//! * it may not reach into a library body with a `@[simp]` rule (WI-20261010-9BKZ4),
//!   which one call lets it do.
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file):
//!
//! * `load::load_program` made not to seal the library's load: `load_refuses_a_
//!   library_operation_declared_again`, `load_refuses_a_library_type_declared_again`,
//!   `load_refuses_a_simp_rule_that_rewrites_a_library_body` and `the_library_on_disk_
//!   is_not_a_program_over_the_embedded_one` FAIL — each file loads. The two `…_an_eq_
//!   for_the_librarys_list` rows pass: that rule is the order's, not the seal's.
//! * `anthill-cli/src/main.rs` made to hand `load_program` everything as the program
//!   (one call): `load_refuses_an_eq_for_the_librarys_list` and `load_refuses_a_simp_
//!   rule_that_rewrites_a_library_body` FAIL — the files load. The two `…_declared_
//!   again` rows pass, one call refusing those as well.
//! * `anthill-cli/src/run.rs` the same: `run_refuses_an_eq_for_the_librarys_list`
//!   FAILS, and the `load` rows pass — the two commands build their KB at two sites.
//! * `a_sort_of_the_programs_own_says_its_equality` and `an_operation_added_to_a_
//!   library_scope_loads` pass either way BY DESIGN: they are the controls that the
//!   refusals are about the LIBRARY's names and not about writing an `eq` or an
//!   operation at all. `with_no_stdlib_the_paths_are_one_load` passes either way too:
//!   it says what the flag means.
//! * `check_lists_no_record_for_a_provision_the_librarys_load_derived` is WI-20261009-
//!   4ZRTG's, run here because the product is where a second load is now made: it
//!   FAILS with that ticket's skip in `register_specialization_witnesses` backed out
//!   (142 records where there are 127), and passes with `main.rs` back at one call.

use std::path::PathBuf;

use crate::common::{anthill, write_temp, Output};

/// A witness that supplies `eq` for the standard library's `List`.
const OVER_THE_LIBRARYS_LIST: &str = r#"
namespace test.an6cq.over
  import anthill.prelude.{Eq, PartialEq, List, Bool}
  sort EqList
    sort A = ?
    requires Eq[T = A]
    provides PartialEq[T = List[T = A]]
    provides Eq[T = List[T = A]]
    operation eq(x: List[T = A], y: List[T = A]) -> Bool = true
  end
end
"#;

/// The repair: a sort of the program's own that HOLDS a list, and a witness for that.
const OVER_ITS_OWN_SORT: &str = r#"
namespace test.an6cq.own
  import anthill.prelude.{Eq, PartialEq, List, Bool, Int64}
  sort Bag
    entity bag(items: List[T = Int64])
  end
  sort EqBag
    provides PartialEq[T = Bag]
    provides Eq[T = Bag]
    operation eq(x: Bag, y: Bag) -> Bool = true
  end
end
"#;

/// A second declaration of an operation the library declares, with another body.
const A_LIBRARY_OPERATION_AGAIN: &str =
    "namespace anthill.prelude.Option\n  operation isEmpty(o: Self) -> Bool = true\nend\n";

/// NOT a second declaration: a new operation written into a library sort's scope.
const AN_OPERATION_ADDED: &str =
    "namespace anthill.prelude.Option\n  operation brandNewAn6cq(o: Self) -> Bool = true\nend\n";

/// A second declaration of a library enum, with a variant of its own.
const A_LIBRARY_TYPE_AGAIN: &str =
    "namespace anthill.prelude.Meta\n  enum Trust {\n    entity wild_guess\n  }\nend\n";

/// A `@[simp]` rule over `Option.isEmpty`, which the library's own `Option.nonEmpty`
/// calls: `nonEmpty(o) = not(isEmpty(o))`.
const A_RULE_OVER_A_LIBRARY_CALL: &str = r#"
namespace test.an6cq.simp
  import anthill.prelude.{Option, Bool}
  import anthill.prelude.Option.{isEmpty}
  rule isEmpty(?o) <=> true @[simp]
end
"#;

/// A program with nothing to refuse.
const A_SMALL_PROGRAM: &str = r#"
namespace test.an6cq.small
  import anthill.prelude.{Int64}
  sort Fine
    entity fine(n: Int64)
  end
  fact fine(n: 1)
end
"#;

fn load(name: &str, source: &str) -> Output {
    let path = write_temp(name, source);
    anthill(&["load", path.to_str().unwrap()])
}

fn refused_with(out: &Output, needle: &str) -> bool {
    out.code != 0 && out.has_diagnostic("error:", needle)
}

/// The standard library and the Rust host bindings as they are ON DISK — what
/// `--no-stdlib` is given in place of the embedded copy.
fn the_library_on_disk() -> [String; 2] {
    let rustland = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    [
        rustland.join("../stdlib/anthill"),
        rustland.join("anthill-stl/anthill"),
    ]
    .map(|dir| dir.to_str().expect("a UTF-8 path").to_owned())
}

#[test]
fn load_refuses_an_eq_for_the_librarys_list() {
    let out = load("an6cq_over_load.anthill", OVER_THE_LIBRARYS_LIST);
    assert!(
        refused_with(&out, "the equality of 'anthill.prelude.List' is closed"),
        "a program is a later load than the standard library, and may not supply the \
         equality of its `List`; exit {}, stderr:\n{}",
        out.code,
        out.stderr
    );
}

#[test]
fn run_refuses_an_eq_for_the_librarys_list() {
    let path = write_temp("an6cq_over_run.anthill", OVER_THE_LIBRARYS_LIST);
    let out = anthill(&["run", path.to_str().unwrap()]);
    assert!(
        refused_with(&out, "the equality of 'anthill.prelude.List' is closed"),
        "`anthill run` builds its KB at a site of its own, and loads the same way; \
         exit {}, stderr:\n{}",
        out.code,
        out.stderr
    );
}

#[test]
fn a_sort_of_the_programs_own_says_its_equality() {
    let out = load("an6cq_own.anthill", OVER_ITS_OWN_SORT);
    assert_eq!(
        out.code, 0,
        "a program supplies the equality of its OWN sorts as any load does; stderr:\n{}",
        out.stderr
    );
}

#[test]
fn load_refuses_a_library_operation_declared_again() {
    let out = load("an6cq_op_again.anthill", A_LIBRARY_OPERATION_AGAIN);
    assert!(
        refused_with(
            &out,
            "operation 'anthill.prelude.Option.isEmpty' is declared more than once"
        ) && out.has_diagnostic("error:", "2 declarations"),
        "the library's load is sealed, so the program's declaration is the SECOND one \
         and is counted with the library's; exit {}, stderr:\n{}",
        out.code,
        out.stderr
    );
}

#[test]
fn an_operation_added_to_a_library_scope_loads() {
    let out = load("an6cq_op_added.anthill", AN_OPERATION_ADDED);
    assert_eq!(
        out.code, 0,
        "a NEW name in a library sort's scope is not a second declaration; stderr:\n{}",
        out.stderr
    );
}

#[test]
fn load_refuses_a_library_type_declared_again() {
    let out = load("an6cq_type_again.anthill", A_LIBRARY_TYPE_AGAIN);
    assert!(
        refused_with(&out, "type 'Trust' is declared more than once"),
        "a program may not reopen a library type; exit {}, stderr:\n{}",
        out.code,
        out.stderr
    );
}

#[test]
fn load_refuses_a_simp_rule_that_rewrites_a_library_body() {
    let out = load("an6cq_simp.anthill", A_RULE_OVER_A_LIBRARY_CALL);
    assert!(
        refused_with(
            &out,
            "rewrites the body of 'anthill.prelude.Option.nonEmpty'"
        ),
        "the library's bodies were typed by its own load, and a rule loaded after it \
         cannot be applied to one; exit {}, stderr:\n{}",
        out.code,
        out.stderr
    );
}

/// The library's files named on the command line BESIDE the embedded copy are a
/// program that declares every library name again. (They were refused before this
/// ticket as well, by the one call that held both copies.)
#[test]
fn the_library_on_disk_is_not_a_program_over_the_embedded_one() {
    let [stdlib, _] = the_library_on_disk();
    let out = anthill(&["load", &stdlib]);
    assert!(
        refused_with(&out, "is declared more than once"),
        "behind a seal there is no presenting again; exit {}, stderr (its head):\n{}",
        out.code,
        out.stderr.lines().take(3).collect::<Vec<_>>().join("\n")
    );
}

/// `--no-stdlib` is the way to load a library's OWN files, and it means what it says:
/// there is no library, and the paths are ONE load — so a file named beside a library
/// on disk is part of that library's load and is judged as part of it. The same file
/// is refused two rows up, where it is a program over the embedded library.
#[test]
fn with_no_stdlib_the_paths_are_one_load() {
    let [stdlib, bindings] = the_library_on_disk();
    let path = write_temp("an6cq_over_one_load.anthill", OVER_THE_LIBRARYS_LIST);
    let out = anthill(&[
        "load",
        "--no-stdlib",
        &stdlib,
        &bindings,
        path.to_str().unwrap(),
    ]);
    assert_eq!(
        out.code, 0,
        "one load over a library and a file that supplies its `List`'s equality is the \
         library's own load; stderr:\n{}",
        out.stderr
    );
}

/// The proof records `check` walks are registered at load — and the program's load
/// must not register, as records of its own, the provisions the LIBRARY's load derived
/// (WI-20261009-4ZRTG: the pass sweeps the whole KB, and a later load found the rows an
/// earlier one derived; measured there as fifteen more records). One load of both
/// registers none of them, the pass running before the derivations.
///
/// ONE spec, one requirement, two origins, so that the absent names are spelled by a
/// present one: `Float provides NonEq` is WRITTEN in the library and has its record,
/// `Option` and `List` get their `NonEq` DERIVED and have none. A record named any
/// other way fails the first assertion rather than passing the second in silence.
#[test]
fn check_lists_no_record_for_a_provision_the_librarys_load_derived() {
    let path = write_temp("an6cq_small.anthill", A_SMALL_PROGRAM);
    let out = anthill(&["check", path.to_str().unwrap()]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    let listed = |sort: &str| {
        let record = format!("anthill.prelude.{sort}.provides.NonEq.PartialEq_T");
        out.stdout.lines().any(|l| l.ends_with(&record))
    };
    assert!(
        listed("Float"),
        "the fixture: the record of a `NonEq` provision the library WRITES is listed, \
         under this name; stdout:\n{}",
        out.stdout
    );
    for derived in ["Option", "List"] {
        assert!(
            !listed(derived),
            "`{derived}`'s `NonEq` is a provision the library's load DERIVED, and is no \
             proof record of the program's load; stdout:\n{}",
            out.stdout
        );
    }
}
