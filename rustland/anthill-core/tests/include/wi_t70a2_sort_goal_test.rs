//! WI-20260822-T70A2 / proposal 062 — a sort's goal over its type parameters.
//!
//! `requires is_entity_of(Trust, TrustLevel)` in `Text` is a goal every instance of `Text`
//! must satisfy: at an instance, each parameter the goal names is replaced by the type the
//! instance binds it to, and the goal is resolved (kernel-language §5.2, "a goal over the
//! sort's parameters"). One judge, `typing::sort_goal_failures`, asked where an instance
//! is made — a written type, a call that binds an operation's type parameter, a
//! construction in a body or in a clause — and once at the declaration for a goal that
//! names no parameter.
//!
//! BACK-OUTS, measured in one build with a temporary switch each (since removed); the
//! control, no switch, passes all 14:
//!   the written-site check out — FAIL: the_acceptance_program,
//!     every_written_position_is_held, a_default_is_the_argument_an_instance_leaves_out,
//!     a_goal_over_two_parameters_is_resolved_once_both_are_concrete,
//!     a_goal_with_a_variable_of_its_own_is_proved_by_one_answer,
//!     an_undecided_goal_is_refused_as_undecided, the_parameter_is_substituted_by_its_type,
//!     a_construction_is_held_at_what_its_fields_fix (its `const` row);
//!   the call check out — FAIL: a_call_is_held_at_what_it_binds;
//!   the operation-body construction check out — FAIL:
//!     a_construction_is_held_at_what_its_fields_fix (its body rows);
//!   the clause construction check out — FAIL: the same row (its fact and rule rows);
//!   the declaration check out — FAIL:
//!     a_goal_naming_no_parameter_is_decided_where_it_is_declared,
//!     a_goal_that_names_nothing_is_refused_where_it_is_written;
//!   the argument-name walk out — FAIL: a_goal_that_names_nothing_is_refused_where_it_is_written;
//!   the skip of a goal its declaration refuses out — FAIL: the same row (two reports);
//!   an undecided search read as holding — FAIL: an_undecided_goal_is_refused_as_undecided;
//!   the readiness gate out (a goal resolved at an argument that is not concrete) — FAIL:
//!     all 13 rows that load a sort with a goal: the sort's own application, recorded where
//!     it is declared, is `Text[Trust = ?]`, its goal flounders there, and the sort is
//!     refused as undecided. The gate is what lets such a sort load at all.
//!   Measured after /code-review, each against its fix backed out: a goal naming no
//!     parameter decided again at each instance — FAIL:
//!     a_goal_naming_no_parameter_is_decided_where_it_is_declared (three reports, by the CLI
//!     probe before the fix); a goal over an enclosing sort's parameter read as a constant
//!     claim — FAIL: a_goal_that_names_nothing_is_refused_where_it_is_written (its `Outer`
//!     row); two goal refusals at a fact's one place kept as one — FAIL:
//!     a_construction_is_held_at_what_its_fields_fix (its two-construction row); the
//!     negation's groundness gate asserting on a type occurrence (node_occurrence.rs at its
//!     parent) — FAIL: the_parameter_is_substituted_by_its_type (a panic at its
//!     value-holding row).
//!   PASS UNDER EACH but the last, by design: a_goal_is_a_sorts (the converter's refusals),
//!     a_goal_is_recorded_and_is_no_requirement (the relation's rows),
//!     a_sort_without_a_goal_admits_every_argument (the opt-in control).

use anthill_core::kb::load::LoadError;

use crate::common::{load_errors_of, load_kb_with, query_unary, run_int64, unrendered_load_errors_of};

/// `test.<ns>` with `TrustLevel` and `Text` as proposal 062 writes them, and `body` after.
fn source(ns: &str, body: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{String, Int64, Unit, List, Option, todo}}\n  \
         import anthill.reflect.typing.{{is_entity_of}}\n  \
         enum TrustLevel\n    entity Public\n    entity Untrusted\n  end\n  \
         enum Text\n    sort Trust = ?\n    requires is_entity_of(Trust, TrustLevel)\n    \
         entity text(raw: String)\n  end\n{body}\nend\n"
    )
}

/// One refusal of an instance by a goal of its sort: the sort's last segment, the
/// bindings as the refusal prints them, and what the goal does there.
#[derive(Debug, PartialEq)]
struct Unmet {
    sort: String,
    bindings: String,
    reason: String,
}

/// The `SortGoalUnmet` refusals of `src`, and the count of every other error.
fn unmet(src: &str) -> (Vec<Unmet>, Vec<String>) {
    let mut goals = Vec::new();
    let mut others = Vec::new();
    for e in unrendered_load_errors_of(src) {
        match e.peel() {
            LoadError::SortGoalUnmet {
                sort,
                bindings,
                reason,
                ..
            } => goals.push(Unmet {
                sort: sort.rsplit('.').next().unwrap_or_default().to_string(),
                bindings: bindings.clone(),
                reason: reason.clone(),
            }),
            other => others.push(other.to_string()),
        }
    }
    (goals, others)
}

/// `src` is refused by exactly one goal of `sort`, at `bindings`, and by nothing else.
fn refused_once(src: &str, sort: &str, bindings: &str, why: &str) -> Unmet {
    let (mut goals, others) = unmet(src);
    assert!(others.is_empty(), "{why}: other errors {others:#?}");
    assert_eq!(goals.len(), 1, "{why}: {goals:#?}");
    let got = goals.remove(0);
    assert_eq!((got.sort.as_str(), got.bindings.as_str()), (sort, bindings), "{why}");
    got
}

/// The rendered refusals of `src` name `line` of the source (1-based, as rendered).
fn refused_at_line(src: &str, line: usize, why: &str) {
    let errs = load_errors_of(src);
    let at = format!("{line}:");
    assert!(
        errs.iter().any(|e| e.starts_with(&at) || e.contains(&format!(":{at}"))),
        "{why}: expected a refusal at line {line}: {errs:#?}"
    );
}

/// The program loads, and `entry` runs to `want`.
fn runs(src: &str, entry: &str, want: i64, why: &str) {
    assert_eq!(run_int64(src, entry), Ok(want), "{why}");
}

/// THE TICKET'S ACCEPTANCE. `Text[Int64]` against a parameter declared to range over the
/// level sorts is a load error naming the parameter, the offending argument and what was
/// admissible; `Text[Public]` and `Text[Untrusted]` load, and a program over them runs. A
/// bare `Text` is the sort at `?` (proposal 070): it binds `Trust` to nothing concrete, so
/// the goal is not decided there.
#[test]
fn the_acceptance_program() {
    let src = source("t70acc", "  operation nonsense(t: Text[Int64]) -> Unit = todo()");
    let got = refused_once(&src, "Text", "Trust = Int64", "Text[Int64]");
    assert!(got.reason.starts_with("does not hold"), "{got:?}");
    assert!(got.reason.contains("`Public`, `Untrusted`"), "{got:?}");
    let errs = load_errors_of(&src);
    assert!(
        errs[0].contains("requires `is_entity_of(Trust, TrustLevel)`"),
        "the refusal quotes the goal as written: {errs:#?}"
    );
    refused_at_line(&src, 13, "at the instance's own line");
    let ok = source(
        "t70accok",
        "  operation pub(t: Text[Public]) -> Int64 = 1\n  \
         operation unt(t: Text[Untrusted]) -> Int64 = 2\n  \
         operation bare(t: Text) -> Int64 = 3\n  \
         operation main() -> Int64 = pub(Text.text(raw: \"a\")) + unt(Text.text(raw: \"b\")) \
         + bare(Text.text(raw: \"c\"))",
    );
    runs(&ok, "test.t70accok.main", 6, "Text[Public], Text[Untrusted] and Text");
}

/// Every place a type is written holds its instance to the goal, at the instance's span —
/// the positions the written-site record covers, the named and the positional spelling,
/// and an instance nested in another type.
#[test]
fn every_written_position_is_held() {
    for (ns, body) in [
        ("t70wparam", "  operation f(t: Text[Int64]) -> Unit = todo()"),
        ("t70wnamed", "  operation f(t: Text[Trust = Int64]) -> Unit = todo()"),
        ("t70wret", "  operation f() -> Text[Int64] = todo()"),
        ("t70wfield", "  entity box(t: Text[Int64])"),
        ("t70wconst", "  const c: Option[T = Text[Int64]] = Option.none()"),
        ("t70walias", "  sort Bad = Text[Int64]"),
        ("t70wlet", "  operation f() -> Unit = { let x: Text[Int64] = todo()  () }"),
        (
            "t70wlambda",
            "  operation f() -> Unit = { let g = lambda (t: Text[Int64]) -> 1  () }",
        ),
        ("t70wnested", "  operation f(t: List[T = Text[Int64]]) -> Unit = todo()"),
    ] {
        let src = source(ns, body);
        refused_once(&src, "Text", "Trust = Int64", ns);
        refused_at_line(&src, 13, ns);
        let ok = source(&format!("{ns}ok"), &body.replace("Int64]", "Public]"));
        let errs = load_errors_of(&ok);
        assert!(errs.is_empty(), "{ns} at `Public`: {errs:#?}");
    }
}

/// A call that binds an operation's type parameter makes the instance its signature
/// writes at that parameter, and is held to the goal there: by an argument (`mk(5)`), by
/// a bracket, by a callee whose own signature carries the instance, in a rule body's
/// value slot and in a const. An instance at a rigid of the body is not decided —
/// `join[L]` loads, and its callers are held at what they bind `L` to.
#[test]
fn a_call_is_held_at_what_it_binds() {
    let mk = "  operation mk[X](x: X) -> Text[X] = todo()\n  operation mk0[X]() -> Text[X] = todo()\n";
    for (ns, body) in [
        ("t70carg", "  operation f() -> Unit = { let t = mk(5)  () }"),
        ("t70cbr", "  operation f() -> Unit = { let t = mk0[X = Int64]()  () }"),
        (
            "t70csig",
            "  operation k[Y](y: Y) -> Text[Y] = mk(y)\n  operation f() -> Unit = { let t = k(5)  () }",
        ),
        ("t70crule", "  rule r(?t) :- ?t <=> mk(5)"),
        ("t70cconst", "  const c: Text[Public] = mk(5)"),
    ] {
        let src = source(ns, &format!("{mk}{body}"));
        let (goals, others) = unmet(&src);
        assert!(!goals.is_empty(), "{ns}: refused by the goal: {others:#?}");
        assert!(
            goals.iter().all(|g| g.bindings == "Trust = Int64"),
            "{ns}: {goals:#?}"
        );
    }
    let ok = source(
        "t70cok",
        &format!(
            "{mk}  operation join[L](a: Text[L], b: Text[L]) -> Text[L] = a\n  \
             operation f() -> Int64 = {{ let t = mk0[X = Public]()  let u: Text[Untrusted] = mk0()  \
             let j = join(t, t)  7 }}"
        ),
    );
    let errs = load_errors_of(&ok);
    assert!(errs.is_empty(), "a rigid, a bracket and an expectation at a level: {errs:#?}");
    let joined = source(
        "t70cjoin",
        "  operation join[L](a: L, b: Text[L]) -> Text[L] = b\n  \
         operation f() -> Unit = { let j = join(5, todo())  () }",
    );
    let (goals, _) = unmet(&joined);
    assert_eq!(goals.len(), 1, "join(5, …) binds `L` to Int64: {goals:#?}");
}

/// `Box`, a sort whose field is typed by the parameter the goal constrains.
const BOX: &str = "  sort Box\n    sort V = ?\n    requires is_entity_of(V, TrustLevel)\n    \
                   entity box(v: V)\n  end\n  entity holds(b: Box)\n";

/// `W`, a sort with no goal whose field's declared type is an instance of `Text` at `W`'s
/// own parameter.
const WRAP: &str = "  sort W\n    sort V = ?\n    entity wrap(t: Text[V], v: V)\n  end\n  \
                    entity holdsW(w: W)\n";

/// A construction makes the instance its fields fix, and is held to the goal there — in an
/// operation body, in a fact, in a rule body, and where the field's argument is typed later
/// in the clause. `box(v: 5)` makes a `Box[V = Int64]`; `wrap(…, v: 5)` makes its field's
/// `Text[V]` a `Text[Int64]`. A type handed to a construction is not its to judge: the
/// `Text[Int64]` a `const`'s type writes is refused once, at the type, and not again at the
/// `Option.none()` that meets it.
#[test]
fn a_construction_is_held_at_what_its_fields_fix() {
    for (ns, body) in [
        ("t70kbody", "  operation f() -> Unit = { let b = Box.box(v: 5)  () }"),
        ("t70kfact", "  fact holds(b: Box.box(v: 5))"),
        ("t70krule", "  rule r(?b) :- ?b <=> Box.box(v: 5)"),
        ("t70klate", "  rule r(?b) :- ?b <=> Box.box(v: ?x), ?x <=> 5"),
    ] {
        let src = source(ns, &format!("{BOX}{body}"));
        refused_once(&src, "Box", "V = Int64", ns);
    }
    for (ns, body) in [
        (
            "t70kwbody",
            "  operation f() -> Unit = { let w = W.wrap(t: Text.text(raw: \"a\"), v: 5)  () }",
        ),
        ("t70kwfact", "  fact holdsW(w: W.wrap(t: Text.text(raw: \"a\"), v: 5))"),
    ] {
        let src = source(ns, &format!("{WRAP}{body}"));
        refused_once(&src, "Text", "Trust = Int64", ns);
    }
    // Two constructions of one fact, refused by the goals of two sorts: two refusals, though
    // a fact's constructions share the fact's place.
    let two = source(
        "t70ktwo",
        &format!(
            "{BOX}{WRAP}  entity holds2(b: Box, w: W)\n  \
             fact holds2(b: Box.box(v: 5), w: W.wrap(t: Text.text(raw: \"a\"), v: 6))"
        ),
    );
    let (goals, others) = unmet(&two);
    assert!(others.is_empty(), "{others:#?}");
    let mut sorts: Vec<&str> = goals.iter().map(|g| g.sort.as_str()).collect();
    sorts.sort();
    assert_eq!(sorts, ["Box", "Text"], "{goals:#?}");
    let handed = source(
        "t70khanded",
        "  const c: Option[T = Text[Int64]] = Option.none()",
    );
    refused_once(&handed, "Text", "Trust = Int64", "a const's type, once");
    // A value of an entity of `TrustLevel` is of the sort `TrustLevel`, which
    // `is_entity_of` holds of itself.
    let ok = source(
        "t70kok",
        &format!("{BOX}  fact holds(b: Box.box(v: Public))\n  rule r(?b) :- holds(b: ?b)"),
    );
    let mut kb = load_kb_with(&ok);
    let got = query_unary(&mut kb, "test.t70kok.r");
    assert_eq!(got.len(), 1, "{got:?}");
}

/// A goal over two parameters is resolved once both are bound to concrete types, the
/// facts it reads written over types (§4.4): one that leaves `To` open is not decided.
#[test]
fn a_goal_over_two_parameters_is_resolved_once_both_are_concrete() {
    let transfer = "  fact flows_to(Public[], Public[])\n  fact flows_to(Untrusted[], Untrusted[])\n  \
                    fact flows_to(Untrusted[], Public[])\n  sort Transfer\n    sort From = ?\n    \
                    sort To = ?\n    requires flows_to(From, To)\n  end\n";
    let src = source(
        "t70two",
        &format!(
            "{transfer}  operation ok(t: Transfer[From = Untrusted, To = Public]) -> Unit = todo()\n  \
             operation half(t: Transfer[From = Untrusted]) -> Unit = todo()\n  \
             operation bad(t: Transfer[From = Public, To = Untrusted]) -> Unit = todo()"
        ),
    );
    refused_once(&src, "Transfer", "From = Public[], To = Untrusted[]", "Public to Untrusted");
    // The instances, not their types: the goal at two types does not read them.
    let instances = source(
        "t70twoinst",
        "  fact flows_to(Untrusted, Public)\n  sort Transfer\n    sort From = ?\n    \
         sort To = ?\n    requires flows_to(From, To)\n  end\n  \
         operation ok(t: Transfer[From = Untrusted, To = Public]) -> Unit = todo()",
    );
    refused_once(&instances, "Transfer", "From = Untrusted[], To = Public[]", "instance facts");
}

/// The goal's own variables are existential: one answer proves it.
#[test]
fn a_goal_with_a_variable_of_its_own_is_proved_by_one_answer() {
    let src = source(
        "t70local",
        "  fact level_rank(Public[], 1)\n  fact level_rank(Public[], 2)\n  sort S\n    sort T = ?\n    \
         requires level_rank(T, ?n)\n  end\n  \
         operation ok(s: S[Public]) -> Unit = todo()\n  \
         operation bad(s: S[Untrusted]) -> Unit = todo()",
    );
    refused_once(&src, "S", "T = Untrusted[]", "no rank for Untrusted");
}

/// A goal that names none of the sort's parameters holds of every instance or of none, so
/// it is decided once, where it is declared.
#[test]
fn a_goal_naming_no_parameter_is_decided_where_it_is_declared() {
    let holds = source(
        "t70zt",
        "  sort S\n    requires is_entity_of(Public, TrustLevel)\n  end",
    );
    let errs = load_errors_of(&holds);
    assert!(errs.is_empty(), "{errs:#?}");
    let fails = source(
        "t70zf",
        "  sort S\n    requires is_entity_of(Int64, TrustLevel)\n  end",
    );
    let got = refused_once(&fails, "S", "", "a constant goal that fails");
    assert!(got.reason.starts_with("does not hold"), "{got:?}");
    refused_at_line(&fails, 14, "at the declaration");
    // Once, there, and not again at each instance of the sort.
    let with_instances = source(
        "t70zfi",
        "  sort S\n    sort T = ?\n    requires is_entity_of(Int64, TrustLevel)\n  end\n  \
         operation f(s: S[Public]) -> Unit = todo()\n  \
         operation g(s: S[Untrusted]) -> Unit = todo()",
    );
    refused_once(&with_instances, "S", "", "a constant goal, with two instances");
}

/// A search that is cut short decides nothing: the instance is refused as undecided, not
/// as refuted and not as holding.
#[test]
fn an_undecided_goal_is_refused_as_undecided() {
    let src = source(
        "t70loop",
        "  rule lp(?x) :- lp(?x)\n  sort S\n    sort T = ?\n    requires lp(T)\n  end\n  \
         operation f(s: S[Public]) -> Unit = todo()",
    );
    let got = refused_once(&src, "S", "T = Public[]", "a looping goal");
    assert!(got.reason.starts_with("cannot be decided"), "{got:?}");
}

/// A goal naming a relation, an argument or a namespace nothing declares is refused where
/// it is written, once — no instance of the sort is also refused for it.
#[test]
fn a_goal_that_names_nothing_is_refused_where_it_is_written() {
    for (ns, goal, name) in [
        ("t70nfun", "is_entity_og(T, TrustLevel)", "is_entity_og"),
        ("t70narg", "is_entity_of(T, TrustLevl)", "TrustLevl"),
    ] {
        let src = source(
            ns,
            &format!(
                "  sort S\n    sort T = ?\n    requires {goal}\n  end\n  \
                 operation f(s: S[Public]) -> Unit = todo()"
            ),
        );
        let errs = unrendered_load_errors_of(&src);
        assert_eq!(errs.len(), 1, "{ns}: {errs:#?}");
        match errs[0].peel() {
            LoadError::UndefinedSortGoal { functor, .. } => {
                assert!(functor.ends_with(name), "{ns}: {functor}")
            }
            other => panic!("{ns}: expected UndefinedSortGoal, got {other:?}"),
        }
    }
    // A parameter of an enclosing sort is not the sort's own: an instance of `Inner` binds
    // nothing to it, so the goal is neither a constant claim nor a goal over `Inner`'s
    // parameters.
    let outer = source(
        "t70nouter",
        "  sort Outer\n    sort P = ?\n    sort Inner\n      \
         requires is_entity_of(P, TrustLevel)\n    end\n  end",
    );
    let errs = unrendered_load_errors_of(&outer);
    assert_eq!(errs.len(), 1, "{errs:#?}");
    match errs[0].peel() {
        LoadError::SortGoalNamesAnotherParameter { param, .. } => {
            assert!(param.ends_with("Outer.P"), "{param}")
        }
        other => panic!("expected SortGoalNamesAnotherParameter, got {other:?}"),
    }
    let ns_goal = source(
        "t70nns",
        "  sort S\n    sort T = ?\n    requires anthill.prelude(T)\n  end",
    );
    let errs = unrendered_load_errors_of(&ns_goal);
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(
        matches!(errs[0].peel(), LoadError::NamespaceAsGoal { .. }),
        "{errs:#?}"
    );
}

/// Only a sort declares a goal, in its own body: a namespace has no parameters for it to be
/// over, and a secondary entry of the sort is a namespace's body.
#[test]
fn a_goal_is_a_sorts() {
    let in_namespace = source("t70gns", "  requires is_entity_of(Public, TrustLevel)");
    let errs = anthill_core::parse::parse(&in_namespace).expect_err("refused by the converter");
    assert!(
        errs.iter().any(|e| e.message.contains("a goal after `requires` is a sort's")),
        "{errs:#?}"
    );
    let in_entry = source(
        "t70gentry",
        "  namespace Text\n    requires is_entity_of(Trust, TrustLevel)\n  end",
    );
    let errs = anthill_core::parse::parse(&in_entry).expect_err("refused by the converter");
    assert!(
        errs.iter().any(|e| e.message.contains("a secondary entry of the sort included")),
        "{errs:#?}"
    );
}

/// The goal is a reflect relation, one row per clause, and never a requirement: a sort
/// that declares only goals has no `SortRequiresInfo` row.
#[test]
fn a_goal_is_recorded_and_is_no_requirement() {
    let src = source(
        "t70rec",
        "  fact level_rank(Public[], 1)\n  sort S\n    sort T = ?\n    \
         requires is_entity_of(T, TrustLevel)\n    requires level_rank(T, ?n)\n  end\n  \
         rule goals(?g) :- anthill.reflect.SortGoalInfo(sort_ref: S, goal: ?g)\n  \
         rule reqs(?r) :- anthill.reflect.SortRequiresInfo(sort_ref: S, spec: ?r)",
    );
    let mut kb = load_kb_with(&src);
    assert_eq!(query_unary(&mut kb, "test.t70rec.goals").len(), 2);
    assert!(query_unary(&mut kb, "test.t70rec.reqs").is_empty());
}

/// The goal is resolved with the parameter replaced by the instance's argument — the row
/// `wi_53w12_type_value_in_clause_test::a_sort_parameter_in_a_rule_body_is_the_parameter`
/// left for this ticket, where in a rule body the parameter is its own name. A negation
/// shows the substitution both ways: it holds at `Int64` and fails at `Public`.
#[test]
fn the_parameter_is_substituted_by_its_type() {
    let negated = "  sort Outside\n    sort T = ?\n    requires not(is_entity_of(T, TrustLevel))\n  end\n";
    let ok = source(
        "t70subok",
        &format!("{negated}  operation f(s: Outside[Int64]) -> Int64 = 1"),
    );
    let errs = load_errors_of(&ok);
    assert!(errs.is_empty(), "{errs:#?}");
    let bad = source(
        "t70subbad",
        &format!("{negated}  operation f(s: Outside[Public]) -> Unit = todo()"),
    );
    refused_once(&bad, "Outside", "T = Public[]", "not(is_entity_of(Public, TrustLevel))");
    // A type that holds a value rides an occurrence, and the negation's groundness gate
    // reads it there as it reads a term.
    let held = source(
        "t70subnode",
        &format!(
            "{negated}  sort Buf\n    sort E = ?\n    sort N = ?\n  end\n  \
             operation f(s: Outside[Buf[E = Int64, N = 3]]) -> Int64 = 1"
        ),
    );
    let errs = load_errors_of(&held);
    assert!(errs.is_empty(), "{errs:#?}");
}

/// A parameter an instance leaves out takes its declared default, and the goal is held
/// there.
#[test]
fn a_default_is_the_argument_an_instance_leaves_out() {
    for (ns, default, refused) in [("t70dint", "Int64", true), ("t70dpub", "Public", false)] {
        let src = source(
            ns,
            &format!(
                "  sort S\n    sort T = ? default {default}\n    \
                 requires is_entity_of(T, TrustLevel)\n  end\n  \
                 operation f(s: S) -> Unit = todo()"
            ),
        );
        let (goals, others) = unmet(&src);
        assert!(others.is_empty(), "{ns}: {others:#?}");
        assert_eq!(goals.len(), usize::from(refused), "{ns}: {goals:#?}");
    }
}

/// The goal is opt-in: a sort that declares none admits every argument.
#[test]
fn a_sort_without_a_goal_admits_every_argument() {
    let src = source(
        "t70open",
        "  enum Open\n    sort Trust = ?\n    entity open(raw: String)\n  end\n  \
         operation f(o: Open[Int64], l: List[T = Int64]) -> Int64 = 4
  \
         operation main() -> Int64 = f(Open.open(raw: \"x\"), [1])",
    );
    runs(&src, "test.t70open.main", 4, "no goal");
}
