//! AN ANNOTATION NAMING A SORT THE LOADER COULD NOT RESOLVE IS REPORTED ONCE — where it is
//! written — and the binder is read as unannotated (`node_occurrence::pattern_annotation_value`,
//! the one reader of a binder's annotation).
//!
//! THE DEFECT (found 2026-10-21 while designing WI-20261013-GGXCX): the typer compared the
//! annotation anyway and refused it a second time, under a missing import as `expected
//! Relation[T = (x: Int64), E = {Error}], got Relation[T = (x: Int64), E = {Error}] (these render
//! alike … please report it)` — the unresolved name and the sort it was meant to name print the
//! same — and at every other annotation site as a mismatch against the unresolved name (a lambda
//! binder's, a type argument's, a match binder's).
//!
//! BACK-OUT, measured: with `pattern_annotation_value` returning the annotation whatever it names,
//! every row here fails except `a_resolved_annotation_is_still_checked`, which passes either way
//! by design.

fn errors_of(body: &str) -> Vec<String> {
    crate::common::load_errors_of(&format!(
        "namespace unres\n  import anthill.prelude.{{Int64, String, List}}\n  \
         rule r(?x) :- ?x <=> 1\n  \
         operation app(f: (Int64) -> Int64, x: Int64) -> Int64 = f(x)\n{body}end\n"
    ))
}

/// The errors are the unresolved names, one per site, and nothing else.
#[track_caller]
fn only_unresolved(errs: &[String], name: &str, sites: usize) {
    let unresolved = errs
        .iter()
        .filter(|e| e.contains(&format!("unresolved name '{name}'")))
        .count();
    assert!(
        unresolved == sites && errs.len() == sites,
        "{sites} unresolved `{name}` and nothing else, got {errs:#?}"
    );
}

#[test]
fn a_missing_import_in_a_let_annotation_is_reported_once() {
    let errs = errors_of(
        "  operation a() -> Int64 effects {Error} =\n    \
           let s: Relation[T = (x: Int64), E = {Error}] = r\n    \
           s.takeN(5).length()\n",
    );
    only_unresolved(&errs, "Relation", 1);
}

#[test]
fn an_unresolved_name_at_every_annotation_site_is_reported_once() {
    for body in [
        "  operation o1() -> Int64 = app(lambda (x: Nope) -> 1, 2)\n",
        "  operation o2() -> Int64 =\n    let xs: List[T = Nope] = [1]\n    3\n",
        "  operation o4() -> Int64 = match (1, 2)\n    case (a: Nope, b) -> b\n",
        "  operation o6() -> Int64 =\n    let x: Nope = 3\n    4\n",
    ] {
        only_unresolved(&errors_of(body), "Nope", 1);
    }
}

/// CONTROL, PASSES EITHER WAY: an annotation that names a sort is compared as before.
#[test]
fn a_resolved_annotation_is_still_checked() {
    let errs = errors_of("  operation o3() -> Int64 =\n    let x: String = 3\n    4\n");
    assert!(
        errs.len() == 1 && errs[0].contains("expected String, got Int64"),
        "the mismatch, got {errs:#?}"
    );
}
