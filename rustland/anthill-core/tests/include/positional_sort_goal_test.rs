//! A SORT APPLICATION AT A GOAL BINDS BY POSITION AS BY NAME. `Marker[Car]` is `Marker[T =
//! Car]`, and `Conv[Car, B = Int64]` is `Conv[A = Car, B = Int64]`, at a rule body's goal, a
//! negand, a branch of `|` and a query, as in every other place a sort application is written
//! (positional and named are one spelling). The loader named the positions of a bracket only
//! where it is a type value, so at a goal the positional one stayed positional and matched no
//! provision: `Marker[Car]` answered nothing where `Marker[T = Car]` holds, `not(Marker[Car])`
//! held, and `Conv[Car, B = Int64]` answered conditionally. A sort alias at a goal is the sort it
//! stands for, as in a type; it was read as no alias, so `IntConv[A = Bool]` held. A positional
//! beyond the parameters a sort with parameters leaves unnamed is refused, as in a `requires`
//! line, and so is a parameter bound twice; both answered nothing or a reading of one binding.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch per walk (`goal_positional_keys`' two callers answering
//! nothing), then removed:
//!
//! * the rule-body walk (`build_body_atom_occurrence_inner`):
//!   [`a_positional_goal_is_its_named_spelling`], [`an_alias_at_a_goal_is_the_sort_it_stands_for`]
//!   and the rule-body half of [`a_positional_beyond_the_parameters_is_refused`];
//! * the query walk (`convert_query_term_expecting`):
//!   [`a_positional_query_is_its_named_spelling`], the query half of
//!   [`an_alias_at_a_goal_is_the_sort_it_stands_for`] and of
//!   [`a_positional_beyond_the_parameters_is_refused`];
//! * the alias read at a goal (`applied_value_alias` in the rule-body walk, the alias expansion
//!   in the query walk), each alone: [`an_alias_at_a_goal_is_the_sort_it_stands_for`].
//!
//! [`the_named_spellings_answer`] passes either way, by design: it is what the positional
//! spellings are measured against.


/// `Marker` with one parameter and `Conv` with two, both provided by `Car` (`Conv` at `B =
/// Int64`), and `IntConv` the alias of `Conv` at `B = Int64`; `rules` are written at the end of
/// the namespace.
fn program(rules: &str) -> String {
    format!(
        r#"namespace p.g
  import anthill.prelude.{{Int64, Bool}}
  sort Marker
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(a: A, b: B) -> Int64
  end
  sort IntConv = Conv[B = Int64]
  sort Car
    entity car(n: Int64)
    provides Marker[T = Car]
    operation tag(x: Car) -> Int64 = 3
    provides Conv[A = Car, B = Int64]
    operation conv(a: Car, b: Int64) -> Int64 = 4
  end
{rules}end
"#
    )
}

use crate::common::pattern_answer_counts as answers;

/// Each goal, as `rule gN() :- <goal>`, and whether it holds.
const GOALS: &[(&str, bool)] = &[
    ("Marker[Car]", true),
    ("Marker[Bool]", false),
    ("not(Marker[Car])", false),
    ("not(Marker[Bool])", true),
    ("Conv[Car, Int64]", true),
    ("Conv[Car, Bool]", false),
    ("Conv[Car, B = Int64]", true),
    ("Conv[B = Int64, Car]", true),
    ("Conv[Car]", true),
    ("(Marker[Bool] | Marker[Car])", true),
];

/// The named spelling of each of [`GOALS`], in its order.
const NAMED: &[&str] = &[
    "Marker[T = Car]",
    "Marker[T = Bool]",
    "not(Marker[T = Car])",
    "not(Marker[T = Bool])",
    "Conv[A = Car, B = Int64]",
    "Conv[A = Car, B = Bool]",
    "Conv[A = Car, B = Int64]",
    "Conv[B = Int64, A = Car]",
    "Conv[A = Car]",
    "(Marker[T = Bool] | Marker[T = Car])",
];

fn rules_of(goals: &[&str]) -> String {
    goals
        .iter()
        .enumerate()
        .map(|(i, g)| format!("  rule g{i}() :- {g}\n"))
        .collect()
}

/// A positional binding at a rule body's goal is the named one: each goal holds where its named
/// spelling does. `Marker[Car]`, `Conv[Car, Int64]`, `Conv[Car]` and the `|` branch answered
/// nothing, `not(Marker[Car])` held, and the mixed spellings answered conditionally.
#[test]
fn a_positional_goal_is_its_named_spelling() {
    let goals: Vec<&str> = GOALS.iter().map(|(g, _)| *g).collect();
    let mut kb = crate::common::load_kb_with(&program(&rules_of(&goals)));
    for (i, (goal, holds)) in GOALS.iter().enumerate() {
        let want = if *holds { (1, 1) } else { (0, 0) };
        assert_eq!(answers(&mut kb, &format!("p.g.g{i}()")), want, "{goal}");
    }
}

/// A query is read so too: `Marker[Car]`, `Conv[Car, Int64]`, `Conv[Car, B = Int64]` and
/// `Conv[Car]` hold, `Conv[Car, Bool]` and `not(Marker[Car])` do not. The positional ones
/// answered nothing, and `not(Marker[Car])` held.
#[test]
fn a_positional_query_is_its_named_spelling() {
    let mut kb = crate::common::load_kb_with(&program(""));
    for (query, holds) in [
        ("p.g.Marker[p.g.Car]", true),
        ("p.g.Conv[p.g.Car, anthill.prelude.Int64]", true),
        ("p.g.Conv[p.g.Car, B = anthill.prelude.Int64]", true),
        ("p.g.Conv[p.g.Car]", true),
        ("p.g.Conv[p.g.Car, anthill.prelude.Bool]", false),
        ("not(p.g.Marker[p.g.Car])", false),
    ] {
        let want = if holds { (1, 1) } else { (0, 0) };
        assert_eq!(answers(&mut kb, query), want, "{query}");
    }
}

/// A sort alias at a goal is the sort it stands for, with what it fixes, as in a type: over
/// `IntConv = Conv[B = Int64]`, `IntConv[Car]` and `IntConv[A = Car]` hold and `IntConv[Bool]` and
/// `IntConv[A = Bool]` do not, at a rule body's goal and as a query. The goal read no alias:
/// `IntConv[Car]` answered nothing, and `IntConv[A = Bool]` held although nothing provides `Conv`
/// at `A = Bool`.
#[test]
fn an_alias_at_a_goal_is_the_sort_it_stands_for() {
    const ALIASED: &[(&str, bool)] = &[
        ("IntConv[Car]", true),
        ("IntConv[A = Car]", true),
        ("IntConv[Bool]", false),
        ("IntConv[A = Bool]", false),
    ];
    let goals: Vec<&str> = ALIASED.iter().map(|(g, _)| *g).collect();
    let mut kb = crate::common::load_kb_with(&program(&rules_of(&goals)));
    for (i, (goal, holds)) in ALIASED.iter().enumerate() {
        let want = if *holds { (1, 1) } else { (0, 0) };
        assert_eq!(answers(&mut kb, &format!("p.g.g{i}()")), want, "{goal}");
        let query = goal
            .replace("IntConv", "p.g.IntConv")
            .replace("Car", "p.g.Car")
            .replace("Bool", "anthill.prelude.Bool");
        assert_eq!(answers(&mut kb, &query), want, "the query {query}");
    }
}

/// A positional beyond the parameters a sort with parameters leaves unnamed is refused, in a
/// rule body at load and in a query where it is read, naming the sort, and so is a parameter
/// bound twice by name. Each answered nothing, or by whichever binding was read.
#[test]
fn a_positional_beyond_the_parameters_is_refused() {
    for (goal, said) in [
        ("Marker[Car, Car]", "over-applied"),
        ("Conv[Car, Int64, Bool]", "over-applied"),
        ("Conv[Car, Int64, A = Car]", "over-applied"),
        ("Conv[A = Car, A = Bool]", "more than once"),
    ] {
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&program(&format!("  rule over() :- {goal}\n"))),
            &["invalid type argument", said],
            goal,
        );
    }
    let mut kb = crate::common::load_kb_with(&program(""));
    for (query, said) in [
        ("p.g.Marker[p.g.Car, p.g.Car]", "`p.g.Marker` is over-applied"),
        ("p.g.Conv[A = p.g.Car, A = anthill.prelude.Bool]", "more than once"),
    ] {
        crate::common::assert_refused_naming(
            &crate::common::query_pattern_refusals(&mut kb, query),
            &["invalid type argument", said],
            query,
        );
    }
}

/// CONTROL, passing either way by design: the named spellings of [`GOALS`] hold as they say.
#[test]
fn the_named_spellings_answer() {
    let mut kb = crate::common::load_kb_with(&program(&rules_of(NAMED)));
    for (i, (named, (_, holds))) in NAMED.iter().zip(GOALS).enumerate() {
        let want = if *holds { (1, 1) } else { (0, 0) };
        assert_eq!(answers(&mut kb, &format!("p.g.g{i}()")), want, "{named}");
    }
}
