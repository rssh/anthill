//! WI-20261023-X5SB4, WI-20260930-AMYV4 — A GUARDED EFFECT IS DROPPED ONLY WHERE ITS GUARD IS
//! REFUTED (kernel-language §5.5), AND TWO THINGS REFUTED A GUARD THAT WAS NOT.
//!
//! A GUARD GOAL THAT NAMES NOTHING — `eq` written without importing it, a misspelt predicate —
//! has no clause, so negation as failure proved its negation wherever its arguments were
//! ground and the effect vanished at that call: `operation u0() -> Int64 = safe(0)` over
//! `safe(n: Int64) -> Int64 effects { Error[Boom] :- eq(n, 0) }` loaded with an empty row and
//! raised at run time, while `safe(n)` was refused. Such a goal is now refused where it is
//! written, in every row a guard can be written in (§5.3, "Naming one from elsewhere").
//!
//! A RULE VARIABLE reached the guard as its raw De Bruijn index, which the resolver compares
//! as a constant distinct from every literal: `neq(?#0, true)` was proved, so `?s <=>
//! stampIf(?b)` loaded with `Clock` dropped — through the call's own σ and through the
//! override's (`?c.stamp(?b)`) — and, the other way round, a rule body's call of an operation
//! that `requires eq(b, 0)` was refused, quoting `eq(?#1, 0)`. Such an argument is not
//! substituted now, so the guard is undecided, as it is at an operation's own parameter.
//!
//! ## Back-out
//!
//! Each piece made a no-op in place under a switch of its own, one build, this file run under
//! each (measured 2026-10-28):
//!
//! | backed out | fails |
//! |---|---|
//! | the guard name check (`check_undefined_effect_guard_goals`) | `a_guard_goal_that_names_nothing_is_refused_where_it_is_written` |
//! | every branch read as under `not` (`undefined_negated_goal_functors`) | `a_guard_goal_that_names_nothing_is_refused_where_it_is_written`, at `nosuch(d) \| eq(d, 0)` |
//! | the dot's own message (`dots_on_values`) | `a_dot_in_a_guard_is_refused_naming_the_application` |
//! | its report once per goal (`seen`) | none: the phase's dedup collapses the alias's copy too |
//! | a rule variable left out of the call's σ (`build_call_guard_sigma`) | `a_rule_variable_leaves_the_guard_undecided`: `stampIf(?b)`, `?c.stamp(?b)`, `onlyZero(?x)` |
//! | a rule variable left out of the override's σ (`dispatched_impl_effects_of`) | `a_rule_variable_leaves_an_overrides_guard_undecided` |
//! | both | also `Stamper.stamp(?c, ?b)` over a guarded spec row: either σ alone keeps `Clock` |
//!
//! CONTROLS, green under every back-out: `a_guard_naming_a_declared_predicate_decides_the_call`,
//! `a_guard_over_a_literal_decides_the_call`.

use crate::common::{
    assert_refused_naming, interp_for_files, load_errors_of, load_errors_of_files, run_int64,
    unrendered_load_errors_of,
};
use anthill_core::eval;
use anthill_core::kb::load::LoadError;

/// `line:col:` of the first `needle` in `src`, as a rendered load error of a file with no path
/// begins.
fn at(src: &str, needle: &str) -> String {
    let i = src.find(needle).unwrap_or_else(|| panic!("`{needle}` is not in the program"));
    let line = src[..i].matches('\n').count() + 1;
    let col = i - src[..i].rfind('\n').map_or(0, |p| p + 1) + 1;
    format!("{line}:{col}:")
}

/// Each program writes a guard goal that names nothing, at the place the second item names;
/// the third is the functor the refusal names.
const NAMELESS: [(&str, &str, &str); 12] = [
    // The ticket's program: `eq` not imported.
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, String, Error}
  sort Boom
    entity boom(why: String)
  end
  operation safe(n: Int64) -> Int64 effects { Error[Boom] :- eq(n, 0) } =
    if n === 0 then Error.raise(boom("z")) else n
  operation u0() -> Int64 = safe(0)
end
"#,
        "eq(n, 0)",
        "eq",
    ),
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{String, Bool}
  import anthill.prelude.Time.{now, Clock}
  operation stampIf(b: Bool) -> String effects { Clock :- eq(b, true) } =
    if b then now() else "none"
  operation userT() -> String = stampIf(true)
end
"#,
        "eq(b, true)",
        "eq",
    ),
    // An operation's own row.
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, Error, DivisionByZero}
  operation dz(d: Int64) -> Int64 effects {Error[DivisionByZero] :- nosuchpred(d, 0)} = 1
  operation pure0() -> Int64 = dz(0)
end
"#,
        "nosuchpred(d, 0)",
        "nosuchpred",
    ),
    // A function type's row, at a parameter and at a field.
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, Error, DivisionByZero}
  operation app(f: (d: Int64) -> Int64 @ {Error[DivisionByZero] :- nosuchpred(d, 0)}) -> Int64
    effects {Error[DivisionByZero]} = f(0)
end
"#,
        "nosuchpred(d, 0)",
        "nosuchpred",
    ),
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, Error, DivisionByZero}
  sort Holder
    entity holder(f: (d: Int64) -> Int64 @ {Error[DivisionByZero] :- nosuchpred(d, 0)})
  end
end
"#,
        "nosuchpred(d, 0)",
        "nosuchpred",
    ),
    // A type alias's, whose body is lowered twice.
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, Error, DivisionByZero}
  sort F = (d: Int64) -> Int64 @ {Error[DivisionByZero] :- nosuchpred(d, 0)}
  operation useF(f: F) -> Int64 effects {Error[DivisionByZero]} = f(1)
end
"#,
        "nosuchpred(d, 0)",
        "nosuchpred",
    ),
    // A provision's binding of a row parameter.
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, Error, DivisionByZero}
  sort Sp
    sort T = ?
    effects E = ?
    operation run(x: T) -> Int64 effects E
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Car, E = {Error[DivisionByZero] :- nosuchpred(1, 0)}]
    operation run(x: Car) -> Int64 = 1
  end
end
"#,
        "nosuchpred(1, 0)",
        "nosuchpred",
    ),
    // One conjunct of a conjunctive guard, a goal under `not`, a nullary goal.
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, Error, DivisionByZero}
  import anthill.prelude.PartialEq.{eq}
  operation dz(d: Int64) -> Int64 effects {(Error[DivisionByZero] :- eq(d, 0), nosuch(d))} = 1
end
"#,
        "nosuch(d)",
        "nosuch",
    ),
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, Error, DivisionByZero}
  operation dz(d: Int64) -> Int64 effects {Error[DivisionByZero] :- not(nosuch(d))} = 1
end
"#,
        "not(nosuch(d))",
        "nosuch",
    ),
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, Error, DivisionByZero}
  operation dz(d: Int64) -> Int64 effects {Error[DivisionByZero] :- nosuchflag} = 1
end
"#,
        "nosuchflag",
        "nosuchflag",
    ),
    // A branch of a disjunction: the guard is read negated, so every branch counts.
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, Error, DivisionByZero}
  import anthill.prelude.PartialEq.{eq}
  operation dz(d: Int64) -> Int64 effects {(Error[DivisionByZero] :- nosuch(d) | eq(d, 0))} = 1
end
"#,
        "nosuch(d) |",
        "nosuch",
    ),
    // A qualified name that names nothing: `isEmpty` is `Iterable`'s, not `List`'s.
    (
        r#"
namespace test.x5sb4.a
  import anthill.prelude.{Int64, List, Error, DivisionByZero}
  operation dz(xs: List[T = Int64]) -> Int64 effects {Error[DivisionByZero] :- List.isEmpty(xs)} = 1
end
"#,
        "List.isEmpty(xs)",
        "List.isEmpty",
    ),
];

/// A dot on a value is not dispatched in a guard, so it names nothing too; the refusal says
/// so and names the application to write, at the head and under a `not`. Before, `dz([])`
/// loaded with no row though `[]` is empty.
#[test]
fn a_dot_in_a_guard_is_refused_naming_the_application() {
    for guard in ["xs.isEmpty()", "not(xs.isEmpty())"] {
        let src = format!(
            r#"
namespace test.x5sb4.g
  import anthill.prelude.{{Int64, List, Error, DivisionByZero}}
  operation dz(xs: List[T = Int64]) -> Int64 effects {{Error[DivisionByZero] :- {guard}}} = 1
  operation go() -> Int64 = dz([])
end
"#
        );
        let want = format!(
            "{} effect guard goal `xs.isEmpty` is a dot on the value `xs`, and a guard does not \
             dispatch a dot",
            at(&src, guard)
        );
        let errs = load_errors_of(&src);
        assert!(
            errs.iter().any(|e| e.starts_with(&want) && e.contains("`isEmpty(xs)`")),
            "{guard}: expected `{want}` naming `isEmpty(xs)`, got {errs:#?}"
        );
    }
    let applied = r#"
namespace test.x5sb4.g
  import anthill.prelude.{Int64, List, Error, DivisionByZero}
  import anthill.prelude.Iterable.{isEmpty}
  operation dz(xs: List[T = Int64]) -> Int64 effects {Error[DivisionByZero] :- isEmpty(xs)} = 1
  operation go() -> Int64 = dz([])
end
"#;
    assert_refused_naming(
        &load_errors_of(applied),
        &["go.effects", "Error[T = DivisionByZero]"],
        "the advised application decides the call",
    );
}

/// Every goal above is refused where it is written, once, naming its functor. Before, each
/// loaded clean, and the ticket's `u0` and `userT` dropped the effect they perform.
#[test]
fn a_guard_goal_that_names_nothing_is_refused_where_it_is_written() {
    for (src, written, functor) in NAMELESS {
        let errs = load_errors_of(src);
        let want = format!(
            "{} effect guard goal `{functor}` names nothing",
            at(src, written)
        );
        assert_eq!(
            errs.iter().filter(|e| e.starts_with(&want)).count(),
            1,
            "expected `{want}` once, got {errs:#?}\nin {src}"
        );
        let raised = unrendered_load_errors_of(src)
            .into_iter()
            .filter(|e| matches!(e.peel(), LoadError::UndefinedEffectGuardGoal { .. }))
            .count();
        assert_eq!(raised, 1, "raised once: {src}");
    }
}

/// A guard over a declared predicate, at a literal its guard refutes, loads and runs; at one
/// it does not, the call is refused the effect. The predicate is declared later in the file,
/// by facts alone, by its qualified name, and in another file of the load.
#[test]
fn a_guard_naming_a_declared_predicate_decides_the_call() {
    for (decl, guard) in [
        ("import anthill.prelude.PartialEq.{eq}", "eq(d, 0)"),
        ("import anthill.prelude.PartialEq.{eq}", "(eq(d, 0) | eq(d, 5))"),
        ("", "anthill.prelude.PartialEq.eq(d, 0)"),
        ("import anthill.prelude.PartialEq.{eq}\n  rule small(?x) :- eq(?x, 0)", "small(d)"),
        ("fact zeroish(0)", "zeroish(d)"),
    ] {
        let program = |arg: i64| {
            format!(
                r#"
namespace test.x5sb4.b
  import anthill.prelude.{{Int64, Error, DivisionByZero}}
  operation dz(d: Int64) -> Int64 effects {{Error[DivisionByZero] :- {guard}}} = 1
  operation go() -> Int64 = dz({arg})
  {decl}
end
"#
            )
        };
        assert_eq!(run_int64(&program(1), "test.x5sb4.b.go"), Ok(1), "`{guard}` at 1");
        assert_refused_naming(
            &load_errors_of(&program(0)),
            &["go.effects", "Error[T = DivisionByZero]"],
            &format!("`{guard}` at 0"),
        );
    }
    let caller = |arg: i64| {
        format!(
            r#"
namespace test.x5sb4.c
  import anthill.prelude.{{Int64, Error, DivisionByZero}}
  import test.x5sb4.d.{{tiny}}
  operation dz(d: Int64) -> Int64 effects {{Error[DivisionByZero] :- tiny(d)}} = 1
  operation go() -> Int64 = dz({arg})
end
"#
        )
    };
    let defining = r#"
namespace test.x5sb4.d
  import anthill.prelude.{Int64}
  import anthill.prelude.PartialEq.{eq}
  rule tiny(?x) :- eq(?x, 0)
end
"#;
    let mut interp = interp_for_files(&[&caller(1), defining]);
    assert!(
        matches!(interp.call("test.x5sb4.c.go", &[]), Ok(eval::Value::Int(1))),
        "a predicate of another file refutes the guard at 1"
    );
    assert_refused_naming(
        &load_errors_of_files(&[&caller(0), defining]),
        &["go.effects", "Error[T = DivisionByZero]"],
        "a predicate of another file holds at 0",
    );
}

const SAFE: &str = r#"
namespace test.x5sb4.e
  import anthill.prelude.{Int64, String, Bool, Error}
  import anthill.prelude.Time.{now, Clock}
  import anthill.prelude.PartialEq.{eq}
  sort Boom
    entity boom(why: String)
  end
  operation safe(n: Int64) -> Int64 effects { Error[Boom] :- eq(n, 0) } =
    if n === 0 then Error.raise(boom("z")) else n
  operation stampIf(b: Bool) -> String effects { Clock :- eq(b, true) } =
    if b then now() else "none"
  operation stampIfN(n: Int64) -> String effects { Clock :- eq(n, 1) } =
    if n === 1 then now() else "none"
"#;

fn with_safe(item: &str) -> String {
    format!("{SAFE}  {item}\nend\n")
}

/// The ticket's acceptance, its programs with `eq` imported: a literal that satisfies the
/// guard keeps the effect, one that refutes it drops it, and a parameter keeps it.
#[test]
fn a_guard_over_a_literal_decides_the_call() {
    for (item, tokens) in [
        ("operation u0() -> Int64 = safe(0)", &["u0.effects", "Error[T = Boom]"][..]),
        ("operation uv(n: Int64) -> Int64 = safe(n)", &["uv.effects", "Error[T = Boom]"]),
        ("operation d0() -> Int64 = Int64.div(7, 0)", &["d0.effects", "Error[T = DivisionByZero]"]),
        ("operation userT() -> String = stampIf(true)", &["userT.effects", "Clock"]),
        ("operation userN() -> String = stampIfN(1)", &["userN.effects", "Clock"]),
        ("rule rt(?s) :- ?s <=> stampIf(true)", &["a rule body performs no effect", "Clock"]),
    ] {
        assert_refused_naming(&load_errors_of(&with_safe(item)), tokens, item);
    }
    assert_eq!(
        run_int64(&with_safe("operation u1() -> Int64 = safe(1)"), "test.x5sb4.e.u1"),
        Ok(1)
    );
    for item in [
        "operation userF() -> String = stampIf(false)",
        "operation userN2() -> String = stampIfN(2)",
        "rule rf(?s) :- ?s <=> stampIf(false)",
    ] {
        let errs = load_errors_of(&with_safe(item));
        assert!(errs.is_empty(), "{item}: {errs:#?}");
    }
}

const STAMPER: &str = r#"
  sort Stamper
    sort C = ?
    operation stamp(c: C, b: Bool) -> String effects { Clock :- eq(b, true) }
  end
  sort Pad
    entity pad(n: Int64)
    provides Stamper[C = Pad]
    operation stamp(c: Pad, b: Bool) -> String effects { Clock :- eq(b, true) } =
      if b then now() else "none"
  end
  operation onlyZero(b: Int64) -> Int64 requires eq(b, 0) = b
"#;

/// A rule variable is not known until the rule runs, so a guard over it is undecided and the
/// effect kept — at a call, at a spec operation's call and at a dot the provider answers — and
/// a precondition over it is not refuted, so a rule body's call is not refused. A literal still
/// decides each.
#[test]
fn a_rule_variable_leaves_the_guard_undecided() {
    let program = |item: &str| with_safe(&format!("{STAMPER}  {item}"));
    for item in [
        "rule r(?s, ?b) :- ?s <=> stampIf(?b)",
        "rule r(?c, ?b, ?s) :- ?c <=> pad(1), ?s <=> Stamper.stamp(?c, ?b)",
        "rule r(?c, ?b, ?s) :- ?c <=> pad(1), ?s <=> ?c.stamp(?b)",
        "rule r(?c, ?s) :- ?c <=> pad(1), ?s <=> ?c.stamp(true)",
    ] {
        assert_refused_naming(
            &load_errors_of(&program(item)),
            &["a rule body performs no effect", "Clock"],
            item,
        );
    }
    for item in [
        "rule r(?c, ?s) :- ?c <=> pad(1), ?s <=> Stamper.stamp(?c, false)",
        "rule r(?c, ?s) :- ?c <=> pad(1), ?s <=> ?c.stamp(false)",
        "rule r(?x, ?y) :- ?y <=> onlyZero(?x)",
        "rule r(?y) :- ?y <=> onlyZero(0)",
    ] {
        let errs = load_errors_of(&program(item));
        assert!(errs.is_empty(), "{item}: {errs:#?}");
    }
    assert_refused_naming(
        &load_errors_of(&program("rule r(?y) :- ?y <=> onlyZero(1)")),
        &["onlyZero.requires", "eq(1, 0)"],
        "a literal refutes the precondition in a rule body",
    );
}

/// The override's own guard, where the spec operation's row is a parameter it fills: the
/// override renames its parameter, so only the σ built over the spec operation's parameters and
/// paired to the override's can ground `eq(y, true)`. Before, `Stamper.stamp(?c, ?b)` loaded.
#[test]
fn a_rule_variable_leaves_an_overrides_guard_undecided() {
    let program = |call: &str| {
        format!(
            r#"
namespace test.x5sb4.f
  import anthill.prelude.{{Int64, String, Bool}}
  import anthill.prelude.Time.{{now, Clock}}
  import anthill.prelude.PartialEq.{{eq}}
  sort Stamper
    sort C = ?
    effects E = ?
    operation stamp(c: C, b: Bool) -> String effects E
  end
  sort Pad
    entity pad(n: Int64)
    operation stamp(p: Pad, y: Bool) -> String effects {{ Clock :- eq(y, true) }} =
      if y then now() else "none"
  end
  namespace Pad
    provides Stamper[C = Pad]
  end
  rule r(?c, ?b, ?s) :- ?c <=> pad(1), ?s <=> {call}
end
"#
        )
    };
    for call in ["Stamper.stamp(?c, ?b)", "Stamper.stamp(?c, true)"] {
        assert_refused_naming(
            &load_errors_of(&program(call)),
            &["a rule body performs no effect", "Clock"],
            call,
        );
    }
    let errs = load_errors_of(&program("Stamper.stamp(?c, false)"));
    assert!(errs.is_empty(), "a literal refutes the override's guard: {errs:#?}");
}
