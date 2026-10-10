//! WI-20261009-AN6CQ — `load::load_program`, the entry point the product loads
//! through: the library in a load of its own, SEALED, and the program in a later one.
//!
//! Driven over a small library of the test's own, with no standard library in it: the
//! subject is what `load_program` does with its two slices, and the rows that put the
//! real library under it run the built binaries (`anthill-cli` and `anthill-todo`,
//! `wi_an6cq_stdlib_first_test` in each).
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file):
//!
//! * `load_program` made not to seal the library's load: `the_library_is_sealed_
//!   between_the_two_loads` FAILS — the program's second declaration of `libOp` loads —
//!   and `an_empty_program_is_no_second_load` FAILS on its census.
//! * `load_program` made not to bootstrap for itself: `nothing_at_all_is_still_a_
//!   bootstrapped_kb` FAILS, by the panic a bare KB answers `unify_functor` with.
//! * `LoadWarning::is_raised_again_by_a_later_load` made to answer `false` for the
//!   requires-shadow lint: `an_advisory_about_the_library_is_given_once` FAILS — the
//!   library's advisory is listed twice, three warnings where there are two.
//! * the same made to answer `true` for everything is NOT measured here: no pass
//!   raises a per-file warning today (`LoadWarning::span`), so there is none to lose.
//! * `the_same_files_in_one_load_are_judged_as_one` and `an_empty_library_is_one_load_
//!   and_seals_nothing` pass either way BY DESIGN: they are the one-load reading the
//!   other rows are measured against, and what `--no-stdlib` gives the CLI.

use anthill_core::kb::load::{self, LoadError, NullResolver, ProgramLoad};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

/// A library: a spec, a carrier, a sort that shadows the spec's operation under a
/// `requires` (the WI-346 advisory, raised by a lint over the whole KB), and one free
/// operation for a program to declare again.
const LIBRARY: &str = r#"
namespace an6cq.lib
  sort Sp
    sort T = ?
    operation s_op(x: T) -> T
  end
  sort Carrier
    entity c
  end
  sort Req
    requires Sp[T = Carrier]
    operation s_op(x: Carrier) -> Carrier = x
  end
  operation libOp(x: Carrier) -> Carrier = x
end
"#;

/// A program over it, with a shadow of its own.
const PROGRAM: &str = r#"
namespace an6cq.prog
  import an6cq.lib.{Sp, Carrier}
  sort Req2
    requires Sp[T = Carrier]
    operation s_op(x: Carrier) -> Carrier = x
  end
end
"#;

/// A program that declares a library operation again, with another body.
const A_LIBRARY_OPERATION_AGAIN: &str = r#"
namespace an6cq.lib
  operation libOp(x: Carrier) -> Carrier = c()
end
"#;

fn parsed(sources: &[&str]) -> Vec<ParsedFile> {
    sources
        .iter()
        .map(|s| parse::parse(s).expect("parse fixture"))
        .collect()
}

/// `load_program` over `library` and `program`, into a fresh KB that is handed back
/// with the verdict.
fn program_load(
    library: &[&str],
    program: &[&str],
) -> (KnowledgeBase, Result<ProgramLoad, Vec<LoadError>>) {
    let (library, program) = (parsed(library), parsed(program));
    let library: Vec<&ParsedFile> = library.iter().collect();
    let program: Vec<&ParsedFile> = program.iter().collect();
    let mut kb = KnowledgeBase::new();
    let verdict = load::load_program(&mut kb, &library, &program, &NullResolver);
    (kb, verdict)
}

fn rendered(errors: Vec<LoadError>) -> Vec<String> {
    crate::common::rendered_load_errors(errors)
}

fn loaded(verdict: Result<ProgramLoad, Vec<LoadError>>, how: &str) -> ProgramLoad {
    verdict.unwrap_or_else(|errors| panic!("{how} must load; got {:?}", rendered(errors)))
}

#[test]
fn the_library_is_sealed_between_the_two_loads() {
    let (_, verdict) = program_load(&[LIBRARY], &[A_LIBRARY_OPERATION_AGAIN]);
    let errors = rendered(verdict.expect_err(
        "a program is a later load than its library and may not declare one of its \
         operations again",
    ));
    assert!(
        errors
            .iter()
            .any(|e| e.contains("operation 'an6cq.lib.libOp' is declared more than once")
                && e.contains("2 declarations")),
        "the one-load refusal, counting the library's declaration and the program's; \
         got {errors:?}"
    );
}

/// The reading the row above is measured against: the same two files as ONE load are
/// refused for the same declaration — the seal carries that rule across, it does not
/// add one.
#[test]
fn the_same_files_in_one_load_are_judged_as_one() {
    let (_, verdict) = program_load(&[], &[LIBRARY, A_LIBRARY_OPERATION_AGAIN]);
    let errors = rendered(verdict.expect_err("one load refuses the second declaration"));
    assert!(
        errors
            .iter()
            .any(|e| e.contains("operation 'an6cq.lib.libOp' is declared more than once")),
        "got {errors:?}"
    );
}

#[test]
fn an_empty_library_is_one_load_and_seals_nothing() {
    let (kb, verdict) = program_load(&[], &[LIBRARY, PROGRAM]);
    let load = loaded(verdict, "a KB built with no library");
    assert!(load.library.is_none(), "no library was handed in, so none was loaded");
    assert_eq!(
        load.program.as_ref().map(|program| program.per_file.len()),
        Some(2),
        "one load was made for the program, and its per-file results are parallel to \
         the program's files"
    );
    assert_eq!(
        kb.sealed_census(),
        (0, 0, 0),
        "with no library there is no first load to seal"
    );
}

#[test]
fn an_empty_program_is_no_second_load() {
    let (kb, verdict) = program_load(&[LIBRARY], &[]);
    let load = loaded(verdict, "a library with no program");
    assert!(load.library.is_some());
    assert!(
        load.program.is_none(),
        "no program was handed in: no load was made for one, and none is reported"
    );
    assert!(
        loaded(program_load(&[LIBRARY], &[]).1, "the same")
            .into_program_per_file()
            .is_empty(),
        "file by file it is parallel to the files handed in, of which there were none"
    );
    let (operations, sorts, sources) = kb.sealed_census();
    assert!(
        operations >= 3 && sorts >= 3 && sources == 1,
        "the library's load is sealed whether or not a program follows; the seal holds \
         {operations} operations, {sorts} sorts, {sources} sources"
    );
}

#[test]
fn nothing_at_all_is_still_a_bootstrapped_kb() {
    let (mut kb, verdict) = program_load(&[], &[]);
    let load = loaded(verdict, "no files at all");
    assert!(load.library.is_none() && load.program.is_none());
    // A bare KB PANICS here (`register_prelude`'s doc): asking it for kernel
    // vocabulary is an error, and every load entry point leaves a KB that has it.
    let _ = kb.unify_functor();
}

#[test]
fn an_advisory_about_the_library_is_given_once() {
    let shadows = |load: &ProgramLoad, sort: &str| {
        load.warnings()
            .filter(|w| {
                let w = w.to_string();
                w.contains(sort) && w.contains("s_op")
            })
            .count()
    };

    let (_, verdict) = program_load(&[LIBRARY], &[PROGRAM]);
    let load = loaded(verdict, "the library and then the program");
    // What makes this a test: the lint reads the whole KB, so BOTH loads raise the
    // library's advisory.
    let raised_by = |result: Option<&load::LoadResult>| {
        result
            .expect("the load was made")
            .warnings
            .iter()
            .filter(|w| w.to_string().contains("`an6cq.lib.Req`"))
            .count()
    };
    assert_eq!(
        (
            raised_by(load.library.as_ref()),
            raised_by(load.program.as_ref().map(|program| &program.merged)),
        ),
        (1, 1),
        "the fixture: the library's load and the program's each raise the library's \
         advisory"
    );
    assert_eq!(shadows(&load, "`an6cq.lib.Req`"), 1, "and it is given once");
    assert_eq!(shadows(&load, "`an6cq.prog.Req2`"), 1, "beside the program's own");
    assert_eq!(load.warnings().count(), 2);

    // With no program there is no later load to raise it again, and it is not dropped.
    let (_, verdict) = program_load(&[LIBRARY], &[]);
    let load = loaded(verdict, "the library alone");
    assert_eq!(shadows(&load, "`an6cq.lib.Req`"), 1);
    assert_eq!(load.warnings().count(), 1);
}
