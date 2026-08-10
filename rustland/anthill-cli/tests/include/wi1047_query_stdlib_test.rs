//! WI-1047 — `anthill query` answers from the embedded stdlib, like every other
//! command, instead of from the user's paths alone.
//!
//! `run_query` reached the KB through a `load_kb` wrapper that hard-coded
//! `include_stdlib = false`, and `QueryArgs` carried no flag either way — while `check`
//! passed `!args.no_stdlib` and HAD the flag. So every stdlib clause was invisible to
//! `query`, and invisible SILENTLY: a rule whose body calls one still loads, is listed
//! by `--match`, and simply answers nothing.
//!
//! ## The smallest case, and why it was confusing
//!
//! `a | b` lowers to `anthill.kernel.or`, whose ONLY clause is
//! `rule or(?a, ?b) :- push_choice(?a, ?b)` in `kernel/kernel.anthill`. MEASURED on one
//! file with `fact l(1)`, `fact r(2)`:
//!
//! | | in-process | `anthill query` (before) |
//! |---|---|---|
//! | `rule either(?x) :- l(?x) \| r(?x)` | 2 | **no solutions** |
//! | `rule both(?x) :- l(?x), r(?y)` | 1 | 1 |
//! | `rule viaPush(?x) :- push_choice(l(?x), r(?x))` | 2 | 2 |
//!
//! The third row is what made it look like a disjunction bug rather than a missing
//! stdlib: `push_choice` is a BUILTIN registered by `register_prelude`, not a clause,
//! so it kept working with no stdlib at all. Three more measurements narrowed it —
//! `--match "demo.either(?x)"` LISTED the rule (so the file loaded), `--match
//! "anthill.kernel.or(?a, ?b)"` found 0 clauses (so the kernel one did not), and
//! loading the SAME embedded set in-process answered 2 (so neither the file set nor the
//! KB was at fault).
//!
//! ## Why this needed a CLI test specifically
//!
//! Nothing in-process can see it: the defect is in which files the `query` COMMAND
//! assembles, and every in-process suite builds its own KB. The whole CLI suite (156
//! tests) passed both before and after the fix — so this file is the only thing that
//! holds it.
//!
//! ## A BREAKING CHANGE for `query`, and why it is the right one — MEASURED
//!
//! A user file whose predicate shares a short name with a stdlib constructor now fails
//! to load through `query` where it used to answer:
//!
//! ```text
//! namespace probe.f4
//!   fact flag(1)
//!   rule any(?x) :- flag(?x)
//! end
//! ```
//! `anthill query …` → `error: constructor 'flag' given 1 positional argument(s) but has
//! 0 unfilled field(s)`; with `--no-stdlib` it answers 1 solution.
//!
//! That is a CONSISTENCY fix, not a regression, and the measurement is what settles it:
//! `anthill check` and `anthill run` ALREADY reject that exact file with the IDENTICAL
//! error, and always did. So the file was never valid by the toolchain's own standard —
//! `query` was the outlier, answering from a KB no other command would assemble, which
//! is worse than a load error because the answers looked authoritative. `--no-stdlib`
//! keeps the old reading for anyone who wants it.
//!
//! ## One side effect, deliberately accepted
//!
//! `query` now also prints the stdlib's own advisory load warnings, as `check` always
//! did. There are exactly two (the WI-346 requires-shadow lint on
//! `FiniteCollection.map`/`.filter`), they go to STDERR so a piped stdout is unaffected,
//! and they are unactionable — driven, the stdlib is right (`xs.map(f)` on a `List`
//! dispatches to the more specific `FiniteCollection.map`, which is the design) and the
//! lint's "rename to silence" advice is what is wrong. **WI-1048** owns that. Suppressing
//! them here instead would have hidden a USER's own advisories along with the stdlib's.
//!
//! ## What fails if this is backed out
//!
//! `a_query_resolves_through_a_stdlib_clause` FAILS (it is the row above).
//! `the_no_stdlib_flag_answers_from_the_paths_alone` passes either way BY DESIGN — it
//! asserts the OPT-OUT, which is what the old behaviour was, so it is the one test here
//! that the defect satisfied. It is worth keeping for exactly that reason: it pins that
//! the old behaviour is still reachable deliberately, and it is the control proving the
//! fixture's emptiness comes from the missing stdlib and not from the fixture.

use super::common::{anthill, write_temp};

/// One file whose rule body needs a stdlib clause (`|` → `anthill.kernel.or`), beside a
/// comma-bodied twin that needs none.
const SRC: &str = "namespace wi1047.q\n\
                   \x20 fact l1047(1)\n\
                   \x20 fact r1047(2)\n\
                   \x20 rule either1047(?x) :- l1047(?x) | r1047(?x)\n\
                   \x20 rule both1047(?x) :- l1047(?x), r1047(?y)\n\
                   end\n";

/// THE HEADLINE, driven through the built binary: a disjunctive rule answers.
///
/// The comma-bodied row is asserted beside it as the CONTROL — it needs no stdlib
/// clause, so it answered correctly through the defect. A test on the disjunction alone
/// could not tell "the stdlib is missing" from "this file does not load".
#[test]
fn a_query_resolves_through_a_stdlib_clause() {
    let path = write_temp("wi1047-query.anthill", SRC);
    let p = path.to_str().unwrap();

    let control = anthill(&["query", "--path", p, "wi1047.q.both1047(?x)"]);
    assert_eq!(control.code, 0, "control stderr:\n{}", control.stderr);
    assert!(
        control.stdout.contains("1 solution"),
        "the comma-bodied control must answer (it needs no stdlib clause); stdout:\n{}",
        control.stdout,
    );

    let out = anthill(&["query", "--path", p, "wi1047.q.either1047(?x)"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(
        out.stdout.contains("2 solution"),
        "`|` lowers to `anthill.kernel.or`, whose clause is in the stdlib — `query` must \
         load it; stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr,
    );
}

/// …AND THE OPT-OUT, the same spelling `check` uses. `--no-stdlib` answers from the
/// given paths alone, which is exactly what `query` used to do unconditionally.
///
/// Passes either way by design (see the header). Its job is to show the two modes
/// DIFFER on this fixture — which is also what proves the headline above is measuring
/// the stdlib and not something about the file.
#[test]
fn the_no_stdlib_flag_answers_from_the_paths_alone() {
    let path = write_temp("wi1047-nostdlib.anthill", SRC);
    let p = path.to_str().unwrap();
    let out = anthill(&[
        "query",
        "--path",
        p,
        "--no-stdlib",
        "wi1047.q.either1047(?x)",
    ]);
    assert!(
        out.stdout.contains("no solutions"),
        "without the stdlib there is no `or` clause to resolve through; stdout:\n{}",
        out.stdout,
    );
}
