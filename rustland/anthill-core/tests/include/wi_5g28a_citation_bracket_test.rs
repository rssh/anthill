//! WI-20260911-5G28A S1 — THE TYPER READS A RULE CITATION'S SORT PARAMETERS
//! (`docs/design/060-implementation.md` §7.3, S1).
//!
//! A relation declared in `sort Wrap[T]` types its column `?x: Wrap[T = T]` at the SORT's
//! canonical `T` — one variable shared by every clause and every citation, which is neither
//! a wildcard nor something a citation may bind. So a citation that said which instance it
//! meant was refused against it: `Wrap[T = Colour].dom.head.x` returned as
//! `Wrap[T = Colour]` reported `got Wrap[T = ?T]`, and an argument meant for the column
//! reported "incompatible type". Each citation now OPENS the parameter as a variable of its
//! own (`typing/relation.rs`, `open_citation_params`) and pins it the way an operation call
//! pins its own parameters: from the receiver bracket (read by `receiver_bracket_entries`,
//! the reader an operation's receiver uses), an applied argument, the expected type passed
//! down, or — inside a member of the same sort — the enclosing instance. A parameter none of
//! them fixes is REFUSED at the citation (`TypeError::UnconstrainedCitationParam`), which is
//! WI-270's rule for an operation's parameter. A value written in the bracket or the expected
//! type is read in the body's own terms, so a rigid `X` there is that rigid.
//!
//! TYPER ONLY, said so a green file is not read as more. What a citation EVALUATES to is
//! unchanged: the pinned instance does not travel into the clause yet (§7.3 S2), and the
//! clause's bound still carries the sort's shared parameter (§7.3 S3(d)), so the citations
//! below still flounder at run time — `the_citation_still_flounders_at_run_time` pins that.
//!
//! BACK-OUT, measured one axis at a time (each run, not predicted; the fixture cites `dom`
//! only where a row does, so an axis reddens the rows that read it and no others):
//!  * [O] `open_citation_params` answering `None` — the whole step. 6 red:
//!    `the_bracket_types_the_column_at_its_instance`, `an_argument_pins_the_parameter`,
//!    `a_rigid_in_the_bracket_is_that_rigid` and `a_member_of_the_sort_cites_its_own_instance`
//!    (the old `got Wrap[T = ?T]` / "incompatible type" refusals), `nothing_at_the_citation_
//!    names_the_parameter` (loads clean), and `the_citation_still_flounders_at_run_time`,
//!    whose program is one of the false refusals S1 closes and so does not load at all.
//!  * [B] the bracket arm of `seed_citation_params`. 4 red: the bracket, rigid and member rows
//!    (refused as undetermined), and `an_argument_pins_the_parameter`'s second half — without
//!    the bracket, `Wrap[T = Colour].dom(wrap(1))` lets the argument pin `T` and loads.
//!  * [E] the enclosing-instance arm. 1 red: `a_member_of_the_sort_cites_its_own_instance`
//!    (a member's own bare `dom` refused as undetermined).
//!  * [X] the expected-type arm of `settle_citation_type`. 1 red:
//!    `the_expected_type_pins_the_parameter`, refused as undetermined.
//!  * [R] `body_rigids` (the bracket value and the expected type read raw). 1 red:
//!    `a_rigid_in_the_bracket_is_that_rigid` — its two WRONG programs load, `X`'s variable
//!    unifying with whatever the return check offers it.
//!  * [V] the refusal in `settle_citation_type`. 1 red:
//!    `nothing_at_the_citation_names_the_parameter` (loads clean).
//!
//! PASS EITHER WAY, BY DESIGN: `a_rule_body_citation_keeps_the_relations_variables` under
//! every axis (a rule body builds no `CitationSite`, so none of this runs there). And
//! `the_expected_type_pins_the_parameter` passes under [O]: with the sort's canonical `T`
//! left in the column, the expected type is accepted by the variable rather than pinning it
//! — the row is [X]'s, not S1's as a whole.

/// `Colour` and `Wrap[T]`, whose relation `dom` is typed at `Wrap`'s own `T`, followed by
/// `extra`. Nothing here cites `dom`, so each row's own citation is the only one the typer
/// sees — which is what lets one back-out axis redden one row.
fn program(extra: &str) -> String {
    program_with_members("", extra)
}

/// [`program`] with `members` written inside `sort Wrap[T]`.
fn program_with_members(members: &str, extra: &str) -> String {
    format!(
        "namespace zz5g28as1\n\
         \x20 import anthill.prelude.{{Int64, Error, EmptyStream, Relation}}\n\
         \x20 sort Colour\n\
         \x20   entity red\n\
         \x20   entity green\n\
         \x20   entity blue\n\
         \x20 end\n\
         \x20 sort Wrap[T]\n\
         \x20   entity wrap(v: T)\n\
         \x20   rule dom(?x: Wrap[T = T]) :- true\n\
         {members}\
         \x20 end\n\
         {extra}\
         end\n"
    )
}

fn loads(extra: &str, why: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(&program(extra)) {
        panic!("{why}; got load errors: {errs:?}");
    }
}

fn refused(extra: &str, expected: &[&str]) {
    crate::common::expect_load_errors(crate::common::try_load_kb_with(&program(extra)), expected);
}

#[test]
fn the_bracket_types_the_column_at_its_instance() {
    loads(
        "  operation a() -> Wrap[T = Colour] effects {Error, Error[EmptyStream]} =\n\
         \x20   Wrap[T = Colour].dom.head.x\n",
        "the bracket types `dom`'s column at `Wrap[T = Colour]`, the declared return",
    );
    // The CONTROL for the row above, and the proof that the column is typed at the
    // BRACKET's instance rather than accepted as anything: both types in the message.
    refused(
        "  operation a() -> Wrap[T = Int64] effects {Error, Error[EmptyStream]} =\n\
         \x20   Wrap[T = Colour].dom.head.x\n",
        &["expected Wrap[T = Int64], got Wrap[T = Colour]"],
    );
}

#[test]
fn an_argument_pins_the_parameter() {
    loads(
        "  operation a() -> Int64 effects {Error} = Wrap.dom(wrap(red())).takeN(5).length()\n",
        "an argument binding the column pins `T` from its own type",
    );
    // The bracket and the argument must AGREE: the bracket pins first, so the argument is
    // CHECKED against `Wrap[T = Colour]` rather than pinning anything.
    refused(
        "  operation a() -> Int64 effects {Error} = Wrap[T = Colour].dom(wrap(1)).takeN(5).length()\n",
        &["argument binding column `x` has an incompatible type"],
    );
}

#[test]
fn the_expected_type_pins_the_parameter() {
    loads(
        "  operation a() -> Relation[T = (x: Wrap[T = Colour]), E = {Error}] = Wrap.dom\n",
        "the type the consumer passes down pins what nothing at the citation wrote",
    );
}

#[test]
fn a_rigid_in_the_bracket_is_that_rigid() {
    loads(
        "  operation a[X]() -> Wrap[T = X] effects {Error, Error[EmptyStream]} =\n\
         \x20   Wrap[T = X].dom.head.x\n",
        "the operation's own `X` in the bracket is the `X` of the declared return",
    );
    // The two wrong programs are the CONTROL: `X` is this body's rigid, equal to itself
    // alone — neither a concrete type nor another parameter.
    refused(
        "  operation a[X]() -> Wrap[T = Colour] effects {Error, Error[EmptyStream]} =\n\
         \x20   Wrap[T = X].dom.head.x\n",
        &["expected Wrap[T = Colour], got Wrap[T = ?X]"],
    );
    refused(
        "  operation a[X, Y]() -> Wrap[T = Y] effects {Error, Error[EmptyStream]} =\n\
         \x20   Wrap[T = X].dom.head.x\n",
        &["expected Wrap[T = ?Y], got Wrap[T = ?X]"],
    );
}

#[test]
fn nothing_at_the_citation_names_the_parameter() {
    // Before S1 this loaded clean and floundered at run time: nothing in the program says
    // which `Wrap` is meant, so no instance can ever reach the clause.
    refused(
        "  operation a() -> Int64 effects {Error} = Wrap.dom.takeN(5).length()\n",
        &["type parameter 'T' of `zz5g28as1.Wrap` is not determined at this citation of \
           `zz5g28as1.Wrap.dom` — no bracket, argument or expected type fixes it; write it: \
           `Wrap[T = …].dom`"],
    );
}

#[test]
fn a_member_of_the_sort_cites_its_own_instance() {
    // A bare `dom` in a member of `Wrap` is pinned by the ENCLOSING instance, WI-424's
    // sibling rule; and a WRITTEN bracket beats the enclosing instance, as it does for an
    // operation call inside the sort.
    let src = program_with_members(
        "    operation inside() -> Int64 effects {Error} = dom.takeN(5).length()\n\
         \x20   operation other() -> Wrap[T = Colour] effects {Error, Error[EmptyStream]} =\n\
         \x20     Wrap[T = Colour].dom.head.x\n",
        "",
    );
    if let Err(errs) = crate::common::try_load_kb_with(&src) {
        panic!(
            "a member's own citation takes the enclosing instance, a bracketed one the \
             written instance; got {errs:?}"
        );
    }
}

#[test]
fn a_rule_body_citation_keeps_the_relations_variables() {
    // CONTROL — passes either way, BY DESIGN: a rule body unifies types at run time, so
    // its citations build no `CitationSite` and nothing in S1 runs there.
    loads(
        "  rule outside(?x) :- Wrap.dom(?x)\n",
        "a rule-body citation is typed as before",
    );
}

#[test]
fn the_citation_still_flounders_at_run_time() {
    // PINNED — S1 is the typer, and this row is its limit. S1 is what makes the program
    // LOAD (without it this citation is one of the false refusals), and eval is untouched:
    // even with the value bound, the clause's bound carries `Wrap`'s SHARED `T`, which the
    // resolver refuses to pin from one value (`bindable_type_var`), so the conformance goal
    // suspends and the drain raises. §7.3 S3(d) — the parameter per activation — flips this
    // row to `1`.
    let mut interp = crate::common::interp_for(&program(
        "  operation a() -> Int64 effects {Error} = Wrap.dom(wrap(red())).takeN(5).length()\n",
    ));
    let err = interp
        .call("zz5g28as1.a", &[])
        .expect_err("PINNED: the citation still flounders; if it now answers, S3(d) has landed");
    assert!(
        matches!(err, anthill_core::eval::EvalError::Raised { .. }),
        "the flounder raises on the Error channel, got {err:?}"
    );
}
