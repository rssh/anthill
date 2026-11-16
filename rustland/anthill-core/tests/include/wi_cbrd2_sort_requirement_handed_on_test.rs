//! A REQUIREMENT A SORT STATES IS HANDED ON TO ITS CLAUSE'S GOAL (WI-20261105-CBRD2). A rule
//! of a sort declares no requirement its sort states (060.1 §8.2). Where a goal of such a rule
//! cites a rule that guards the requirement at the sort's parameter — `rule viaH(?x: T, ?t) :-
//! keep(?x, ?t)` in `sort Holder` with `requires Marker[T = T]`, under `rule keep[A](?x: A, ?t)
//! :- Marker[A], Marker.tag(?x, ?t)` — the goal passed nothing: the guard found no dictionary
//! when it ran, and `Holder[T = Int64].viaH(1, ?t)` answered conditionally, with a warning that
//! the goal was built at run time. The clause now reads the requirement as it reads a guard of
//! its own (`install_sort_requirement_reads`), the goal passes that read, and a citation that
//! fixes the sort's parameter fills it. A guard the sort states at another instance is refused
//! at load, as one at a type the clause declares nothing at is, and one it states under two
//! names is refused as two requirements of the clause are.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * The whole change (no read given to the clause, and a guard of a spec the sort supplies
//!   passing nothing, as before): every row but the control fails — the citations answering
//!   conditionally, the two refusal rows loading clean.
//! * The read alone (a guard the sort states refused where the clause has no read of it): the
//!   same rows fail, refused at load, and so does
//!   [`a_goal_built_at_run_time_is_passed_nothing`], whose program is refused too.
//! * An element left out (a guard naming a variable beside its carrier gets no read):
//!   [`elements_the_sort_states_are_handed_on_with_the_carrier`] and
//!   [`an_element_the_goal_fixes_matches_the_sort_as_written`] fail, refused at load.
//! * A spec's own parameter left out:
//!   [`a_specs_own_rule_and_a_requirement_reached_through_another_spec`] fails at
//!   `Tagged[T = Int64].own`.
//! * A clause whose citation markers went stale left out:
//!   [`a_later_load_that_guards_a_callee_again_is_handed_on`] fails, the later load refused.
//! * The refusal of a requirement the sort states at another instance, passing nothing there:
//!   [`a_guard_the_sort_states_at_another_instance_is_refused`] fails.
//! * Two names read as one: [`a_requirement_the_sort_states_under_two_names_is_refused_at_the_goal`]
//!   fails, refused with the plain text.
//!
//! [`a_goal_built_at_run_time_is_passed_nothing`] passes with the whole change backed out, by
//! design: the run-time path the change leaves as it was.

use anthill_core::kb::load::LoadOptions;
use anthill_core::kb::resolve::ResolveConfig;

use crate::common::{expect_loaded, load_errors_of, load_in_a_later_call, load_kb_with, pattern_last_ints, run_time_goal};

const MARKER: &str = r#"
  import anthill.prelude.{Int64, Bool}
  sort Marker
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort IntMarker
    provides Marker[T = Int64]
    operation tag(x: Int64) -> Int64 = 1
  end
  sort BoolMarker
    provides Marker[T = Bool]
    operation tag(x: Bool) -> Int64 = 2
  end
  rule keep[A](?x: A, ?t) :- Marker[A], Marker.tag(?x, ?t)
"#;

fn src(ns: &str, decls: &str) -> String {
    format!("namespace {ns}\n{MARKER}\n{decls}\nend\n")
}

/// The definite integers `<ns>.<pattern>` answers at its last argument.
fn answers(src: &str, ns: &str, pattern: &str) -> Vec<i64> {
    let mut kb = load_kb_with(src);
    pattern_last_ints(&mut kb, &format!("{ns}.{pattern}"))
}

const HOLDER: &str = r#"
  sort Holder
    sort T = ?
    requires Marker[T = T]
    rule viaH(?x: T, ?t) :- keep(?x, ?t)
    rule chain(?x: T, ?t) :- viaH(?x, ?t)
    rule alt(?x: T, ?t) :- keep(?x, ?t) | ?t <=> 0
    rule negd(?x: T, ?t) :- not(keep(?x, 5)), ?t <=> 9
    rule rec(?x: T, ?n: Int64, ?t) :- (?n = 0, keep(?x, ?t)) | (?n > 0, rec(?x, ?n - 1, ?t))
  end
  rule atInt(?t) :- Holder[T = Int64].viaH(1, ?t)
  rule atBool(?t) :- Holder[T = Bool].viaH(true, ?t)
  rule chained(?t) :- Holder[T = Bool].chain(true, ?t)
  rule branched(?t) :- Holder[T = Bool].alt(true, ?t)
  rule negated(?t) :- Holder[T = Int64].negd(1, ?t)
  rule recursed(?t) :- Holder[T = Int64].rec(1, 2, ?t)
"#;

/// `Holder[T = Int64].viaH(1, ?t)` is `Int64`'s `tag`, `[T = Bool]` `Bool`'s; so through a goal
/// of another clause of the sort, in a branch of `|`, under `not`, down a recursion, and from a
/// query, whose types fix `T`.
#[test]
fn a_goal_passes_the_requirement_its_sort_states() {
    let ns = "test.cbrd2.hand.h";
    let program = src(ns, HOLDER);
    for (pattern, want) in [
        ("atInt(?t)", vec![1]),
        ("atBool(?t)", vec![2]),
        ("chained(?t)", vec![2]),
        ("branched(?t)", vec![0, 2]),
        ("negated(?t)", vec![9]),
        ("recursed(?t)", vec![1]),
        ("Holder.viaH(1, ?t)", vec![1]),
        ("Holder.viaH(true, ?t)", vec![2]),
    ] {
        assert_eq!(answers(&program, ns, pattern), want, "`{pattern}`");
    }
}

/// A guard naming an element beside its carrier, `Conv[A = X, B = Y]`, takes the sort's
/// `Conv[A = T, B = U]` with each at the parameter the goal puts it at, whichever order the
/// clause's columns are in; one the sort fixes, `B = Int64`, matches as written.
#[test]
fn elements_the_sort_states_are_handed_on_with_the_carrier() {
    let ns = "test.cbrd2.hand.e";
    let program = src(
        ns,
        r#"
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(x: A) -> B
  end
  sort IntConv
    provides Conv[A = Int64, B = Int64]
    operation conv(x: Int64) -> Int64 = x + 10
  end
  sort BoolConv
    provides Conv[A = Bool, B = Int64]
    operation conv(x: Bool) -> Int64 = 20
  end
  rule ck2[X, Y](?x: X, ?y: Y, ?r) :- Conv[A = X, B = Y], Conv.conv(?x, ?r)
  rule ck[X](?x: X, ?r) :- Conv[A = X, B = Int64], Conv.conv(?x, ?r)
  sort Two
    sort T = ?
    sort U = ?
    requires Conv[A = T, B = U]
    rule v(?x: T, ?y: U, ?r) :- ck2(?x, ?y, ?r)
    rule w(?y: U, ?x: T, ?r) :- ck2(?x, ?y, ?r)
  end
  sort Fixed
    sort T = ?
    requires Conv[A = T, B = Int64]
    rule v(?x: T, ?r) :- ck(?x, ?r)
  end
  rule two(?r) :- Two[T = Int64, U = Int64].v(1, 5, ?r)
  rule swapped(?r) :- Two[T = Bool, U = Int64].w(7, true, ?r)
  rule fixed(?r) :- Fixed[T = Int64].v(1, ?r)
"#,
    );
    for (pattern, want) in [("two(?r)", 11), ("swapped(?r)", 20), ("fixed(?r)", 11)] {
        assert_eq!(answers(&program, ns, pattern), vec![want], "`{pattern}`");
    }
}

/// A guard whose element the goal fixes at a concrete type, `ck2(?x, 5, ?r)` at `Conv[A = X, B =
/// Y]`, takes the sort's `Conv[A = T, B = Int64]`.
#[test]
fn an_element_the_goal_fixes_matches_the_sort_as_written() {
    let ns = "test.cbrd2.hand.k";
    let program = src(
        ns,
        r#"
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(x: A) -> B
  end
  sort IntConv
    provides Conv[A = Int64, B = Int64]
    operation conv(x: Int64) -> Int64 = x + 10
  end
  rule ck2[X, Y](?x: X, ?y: Y, ?r) :- Conv[A = X, B = Y], Conv.conv(?x, ?r)
  sort Fixed
    sort T = ?
    requires Conv[A = T, B = Int64]
    rule v(?x: T, ?r) :- ck2(?x, 5, ?r)
  end
  rule fixed(?r) :- Fixed[T = Int64].v(1, ?r)
"#,
    );
    assert_eq!(answers(&program, ns, "fixed(?r)"), vec![11]);
}

/// A sort stating the requirement under two names, `requires Plus: Mon[T = T]` and `requires
/// Times: Mon[T = T]`, holds two dictionaries, and the goal of `keepMon` says neither: refused at
/// the goal, naming both, as a clause holding two named requirements is.
#[test]
fn a_requirement_the_sort_states_under_two_names_is_refused_at_the_goal() {
    let program = src(
        "test.cbrd2.hand.t",
        r#"
  sort Mon
    sort T = ?
    operation op(x: T) -> Int64
  end
  sort Sum
    provides Mon[T = Int64]
    operation op(x: Int64) -> Int64 = 1
  end
  rule keepMon[A](?x: A, ?r) :- Mon[A], Mon.op(?x, ?r)
  sort Semi
    sort T = ?
    requires Plus: Mon[T = T]
    requires Times: Mon[T = T]
    rule s(?x: T, ?r) :- keepMon(?x, ?r)
  end
"#,
    );
    let errs = load_errors_of(&program);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("two of the clause's hold, `Plus` and `Times`"), "{errs:?}");
}

/// A rule of the spec itself reads the spec at its own parameter (060.1 §3), and a sort whose
/// requirement requires `Marker` hands on `Marker` too.
#[test]
fn a_specs_own_rule_and_a_requirement_reached_through_another_spec() {
    let ns = "test.cbrd2.hand.s";
    let program = src(
        ns,
        r#"
  sort Tagged
    sort T = ?
    operation tagged(x: T) -> Int64
    rule own(?x: T, ?t) :- keepTagged(?x, ?t)
  end
  sort IntTagged
    provides Tagged[T = Int64]
    operation tagged(x: Int64) -> Int64 = 1
  end
  rule keepTagged[A](?x: A, ?t) :- Tagged[A], Tagged.tagged(?x, ?t)
  sort Fancy
    sort T = ?
    requires Marker[T = T]
    operation fancy(x: T) -> Int64
  end
  sort IntFancy
    provides Fancy[T = Int64]
    operation fancy(x: Int64) -> Int64 = 5
  end
  sort ViaFancy
    sort T = ?
    requires Fancy[T = T]
    rule v(?x: T, ?t) :- keep(?x, ?t)
  end
  rule owned(?t) :- Tagged[T = Int64].own(1, ?t)
  rule reached(?t) :- ViaFancy[T = Int64].v(1, ?t)
"#,
    );
    for pattern in ["owned(?t)", "reached(?t)"] {
        assert_eq!(answers(&program, ns, pattern), vec![1], "`{pattern}`");
    }
}

/// A later load gives `keep` a clause guarding `Other[A]`, which `Holder` states beside
/// `Marker`: `viaH`, routed by the first load, is routed again and reads `Other` as well, and
/// its citation answers through both clauses.
#[test]
fn a_later_load_that_guards_a_callee_again_is_handed_on() {
    let ns = "test.cbrd2.hand.l";
    let first = src(
        ns,
        r#"
  sort Other
    sort T = ?
    operation other(x: T) -> Int64
  end
  sort IntOther
    provides Other[T = Int64]
    operation other(x: Int64) -> Int64 = 5
  end
  sort Holder
    sort T = ?
    requires Marker[T = T]
    requires Other[T = T]
    rule viaH(?x: T, ?t) :- keep(?x, ?t)
  end
  rule atInt(?t) :- Holder[T = Int64].viaH(1, ?t)
"#,
    );
    let mut kb = load_kb_with(&first);
    assert_eq!(pattern_last_ints(&mut kb, &format!("{ns}.atInt(?t)")), vec![1]);
    let later = format!(
        "namespace {ns}\n  rule keep[A](?x: A, ?t) :- Other[A], Other.other(?x, ?t)\nend\n"
    );
    expect_loaded(load_in_a_later_call(&mut kb, &later, LoadOptions::default()));
    assert_eq!(pattern_last_ints(&mut kb, &format!("{ns}.atInt(?t)")), vec![1, 5]);
}

/// `sort Other requires Conv[A = T, B = Bool]` states no `Conv[A = T, B = Int64]`, which `ck`
/// guards: the goal is refused at load, naming the instance the sort states.
#[test]
fn a_guard_the_sort_states_at_another_instance_is_refused() {
    let program = src(
        "test.cbrd2.hand.r",
        r#"
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(x: A) -> B
  end
  sort IntConv
    provides Conv[A = Int64, B = Int64]
    operation conv(x: Int64) -> Int64 = x + 10
  end
  rule ck[X](?x: X, ?r) :- Conv[A = X, B = Int64], Conv.conv(?x, ?r)
  sort Other
    sort T = ?
    requires Conv[A = T, B = Bool]
    rule v(?x: T, ?r) :- ck(?x, ?r)
  end
"#,
    );
    let errs = load_errors_of(&program);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        errs[0].contains("the clause's sort `Other` states `Conv` at another instance"),
        "{errs:?}"
    );
}

/// The control: a goal of `viaH` built at run time, which no load typed, is passed nothing, and
/// its guard says so when it runs.
#[test]
fn a_goal_built_at_run_time_is_passed_nothing() {
    let ns = "test.cbrd2.hand.c";
    let mut kb = load_kb_with(&src(ns, HOLDER));
    let goal = run_time_goal(&mut kb, &format!("{ns}.Holder.viaH(1, ?t)"));
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    let faults: Vec<&str> = stats.errors.iter().map(|e| e.message.as_str()).collect();
    assert!(sols.iter().all(|s| !s.is_definite()), "{faults:?}");
    assert!(faults.iter().any(|m| m.contains("was passed by no caller")), "{faults:?}");
}
