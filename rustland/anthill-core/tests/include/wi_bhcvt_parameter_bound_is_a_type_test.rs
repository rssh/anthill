//! WI-20261005-BHCVT — a rule head's sigil-free parameter bound (`x: T`, kernel-language.md
//! §5.3, "The parameter form") is a TYPE as a whole, its own top-level bracket included: the
//! arguments bind the parameters they take, one that takes none is refused where it is written
//! and not built, the application is the one term its type is (a positional keyed, a declared
//! default filled), and a type alias applied anywhere in it is the sort it stands for. The
//! `?x: T` spelling lowers its annotation as a type, and §5.3 says the two are one form.
//!
//! Before, the bound's top level was converted at the depth of a clause's instance claim, which
//! nothing fits (`Loader::bracket_reads_as_type`), and a bracket nested in it skipped the alias
//! reading and the normalization a nested bracket elsewhere gets. MEASURED on 3bf56e41: `rule
//! p(x: Buf[W = Int64]) :- q(x)` loaded clean and answered nothing where `?x: Buf[W = Int64]`
//! is refused; `x: Buf[Int64]` answered nothing where `?x: Buf[Int64]` answers `buf(v: 1)`;
//! `x: IntBuf[N = Bool]` answered every row of `q` with a residual `domain(…, IntBuf[N =
//! Bool])`; `x: List[T = IntBuf[N = Bool]]` was refused, "`IntBuf` … declares no type
//! parameters".
//!
//! WHICH ROWS FAIL WITH THE CHANGE BACKED OUT — measured with each part switched off alone in
//! one build, over this file:
//!
//!   * the bound's own top level read as a clause's top-level term is (`bracket_reads_as_type`
//!     answering `term_depth > 1` alone) → [`the_tickets_heads_are_refused_where_written_once`]
//!     (its top-level heads load clean), [`a_positional_argument_binds_the_parameter_it_takes`],
//!     [`a_declared_default_is_filled`], [`an_applied_alias_is_the_sort_it_stands_for`] and the
//!     positional `List[A]` half of [`a_head_type_variable_inside_the_bound_still_resolves`];
//!   * the bound's arguments fitted as a data slot's are, reported and kept (the
//!     `in_rule_head_bound` branch of the fit taken out) →
//!     [`a_misfit_is_refused_once_and_not_built`], and nothing else: a data slot's fit normalizes
//!     an application that fits as the bound's does;
//!   * an applied alias in the bound read as its own name (the alias reading gated off the bound
//!     again) → [`an_applied_alias_is_the_sort_it_stands_for`], and nothing else.
//!   * a constructor not taken for a type (`parse_arg_is_constructor_type` answering `false`)
//!     → [`a_constructor_is_its_type`] but its call half, and nothing else: the
//!     `Buf.buf[W = Int64]` head is refused with the same message as a named argument's value;
//!     only a bracket taken for one → that row's `Buf.buf` and `Option.none` entries.
//!
//!   PASSES EITHER WAY, by design: [`a_well_formed_bound_filters`], the control the refusals and
//!   the answers are read against; and so does the named `List[T = A]` half of
//!   [`a_head_type_variable_inside_the_bound_still_resolves`] (WI-20260908-PW9A0's row, which
//!   the fit now runs over).

use anthill_core::eval::Value;
use anthill_core::kb::node_occurrence::value_to_term;
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{load_errors_of, load_kb_with, query_unary};

/// The sorts and the table the rows filter. `q` holds a value of each instance a bound below
/// tells apart.
const DECLS: &str = "  sort Buf\n    sort T = ?\n    sort N = ?\n    entity buf(v: T)\n  end\n  \
                     sort IntBuf = Buf[T = Int64]\n  sort D[A, B = Int64]\n    entity dd(a: A, b: \
                     B)\n  end\n  rule q(?x)\n  fact q(buf(v: 1))\n  fact q(buf(v: \"s\"))\n  fact \
                     q([buf(v: 1)])\n  fact q([buf(v: \"s\")])\n  fact q(Option.some(1))\n  fact \
                     q(Option.some(\"s\"))\n  fact q(dd(a: \"s\", b: 1))\n  fact q(dd(a: \"s\", b: \
                     true))\n  fact q([dd(a: \"s\", b: 1)])\n  fact q([dd(a: \"s\", b: true)])\n";

/// A program in `test.<ns>` with the rows' declarations and `rule`.
fn program(ns: &str, rule: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64, String, Bool, List, Option, Eq}}\n\
         {DECLS}  {rule}\nend\n"
    )
}

/// `rule p(x: <bound>) :- q(x)` and its sigil twin, `rule p(?x: <bound>) :- q(?x)`.
fn both_spellings(bound: &str) -> [(&'static str, String); 2] {
    [
        ("sigil-free", format!("rule p(x: {bound}) :- q(x)")),
        ("sigil", format!("rule p(?x: {bound}) :- q(?x)")),
    ]
}

/// Every answer of `test.<ns>.p(?z)`, rendered, sorted; one the search leaves conditional is
/// marked so.
fn answers(ns: &str, rule: &str) -> Vec<String> {
    let mut kb = load_kb_with(&program(ns, rule));
    let found = query_unary(&mut kb, &format!("test.{ns}.p"));
    let mut rendered: Vec<String> = found
        .into_iter()
        .map(|(v, definite)| {
            let text = render(&mut kb, &v);
            if definite { text } else { format!("{text} (conditional)") }
        })
        .collect();
    rendered.sort();
    rendered
}

fn render(kb: &mut KnowledgeBase, v: &Value) -> String {
    let t = value_to_term(kb, v).expect("an answer of `p` has a term");
    TermPrinter::new(kb).print_term(t)
}

/// THE TICKET'S HEADS: a name the sort does not declare, an over-application, a parameter
/// bound twice, and the same name one bracket down. Each is refused once, in both spellings,
/// with one message.
#[test]
fn the_tickets_heads_are_refused_where_written_once() {
    for (tag, bound, says) in [
        ("undeclared", "Buf[W = Int64]", "has no type parameter named 'W' — it declares type parameter(s) T, N"),
        (
            "over",
            "Buf[Int64, 3, Bool]",
            "is over-applied: 3 positional type argument(s) but only 2 declared type parameter(s) left to bind",
        ),
        ("twice", "Buf[T = Int64, T = Int64]", "binds the type parameter 'T' more than once"),
        ("nested", "List[T = Buf[W = Int64]]", "has no type parameter named 'W'"),
        (
            "ctor",
            "Buf.buf[W = Int64]",
            "`test.bhcvtctor.Buf.buf` has no type parameter named 'W' — its sort `test.bhcvtctor.Buf` declares",
        ),
    ] {
        for (spelling, rule) in both_spellings(bound) {
            let errs = load_errors_of(&program(&format!("bhcvt{tag}"), &rule));
            assert_eq!(errs.len(), 1, "{spelling} `{bound}`: one report: {errs:#?}");
            assert!(
                errs[0].contains("invalid type argument: `test.bhcvt") && errs[0].contains(says),
                "{spelling} `{bound}`: the type position's message: {errs:#?}"
            );
        }
    }
}

/// A MISFIT IS NOT BUILT: refused where it is written, naming the constructor it is written on
/// as the type position does, and left out of the type, so no later report carries it. `q`
/// holds only a `Buf`, so the `List` bound is refused again by the typer, which prints the
/// bound as built.
#[test]
fn a_misfit_is_refused_once_and_not_built() {
    for (bound, says) in [
        (
            "List[T = Option.some[Zork = Int64]]",
            "`anthill.prelude.Option.some` has no type parameter named 'Zork' — its sort \
             `anthill.prelude.Option` declares type parameter(s) T",
        ),
        ("List[T = Buf[Zork = Int64]]", "`test.bhcvtmisfit.Buf` has no type parameter named 'Zork'"),
    ] {
        for (spelling, rule) in both_spellings(bound) {
            let errs = load_errors_of(&format!(
                "namespace test.bhcvtmisfit\n  import anthill.prelude.{{Int64, List, Option}}\n  sort \
                 Buf\n    sort T = ?\n    entity buf(v: T)\n  end\n  rule q(?x)\n  fact q(buf(v: \
                 1))\n  {rule}\nend\n"
            ));
            let naming: Vec<&String> = errs.iter().filter(|e| e.contains("Zork")).collect();
            assert_eq!(naming.len(), 1, "{spelling} `{bound}`: one report names the misfit: {errs:#?}");
            assert!(naming[0].contains(says), "{spelling} `{bound}`: {errs:#?}");
            assert!(
                errs.iter().any(|e| e.contains("type mismatch")),
                "{spelling} `{bound}`: the typer prints the bound as built: {errs:#?}"
            );
        }
    }
}

/// A CONSTRUCTOR after the `:` — its name, or a bracket applying it — is that constructor's
/// type (§5.3, §8.2), so `x` is a parameter bounded by it, as `?x` is: over `:- true` the
/// clause has one column, and `p(?z)` one answer, left waiting on the bound in both
/// spellings. Before, the sigil-free `x` was a constant and `p(?z)` answered nothing. Whether
/// the bound keeps `buf(v: 1)` is the constructor's own domain, which neither spelling decides
/// yet (WI-20260925-SHED7's `SortDomain` per entity).
///
/// A CALL builds a value, so `x: Option.some(1)` stays a named argument, and `p(?z)` has no
/// column to answer. That half passes either way, by design: it is the fence.
#[test]
fn a_constructor_is_its_type() {
    for bound in [
        "Buf.buf[T = Int64]",
        "Buf.buf[Int64]",
        "Option.some[T = Int64]",
        "Buf.buf",
        "Option.none",
    ] {
        for (spelling, rule) in both_spellings(bound) {
            let rule = rule.replace(":- q(x)", ":- true").replace(":- q(?x)", ":- true");
            let mut kb = load_kb_with(&program("bhcvtctorty", &rule));
            let found = query_unary(&mut kb, "test.bhcvtctorty.p");
            assert_eq!(found.len(), 1, "{spelling} `{bound}`: one answer: {found:?}");
            assert!(!found[0].1, "{spelling} `{bound}`: left waiting on the bound");
        }
    }
    let mut kb = load_kb_with(&program("bhcvtctorcall", "rule p(x: Option.some(1)) :- true"));
    assert_eq!(query_unary(&mut kb, "test.bhcvtctorcall.p").len(), 0, "a call is a datum");
}

/// THE CONTROL: a bound that fits answers the rows of its instance and no other, in both
/// spellings.
#[test]
fn a_well_formed_bound_filters() {
    for (bound, rows) in [
        ("Buf[T = Int64]", vec!["buf(v: 1)"]),
        ("Buf[T = String]", vec!["buf(v: \"s\")"]),
        ("List[T = Buf[T = Int64]]", vec!["[buf(v: 1)]"]),
    ] {
        for (spelling, rule) in both_spellings(bound) {
            assert_eq!(answers("bhcvtwell", &rule), rows, "{spelling} `{bound}`");
        }
    }
}

/// A POSITIONAL ARGUMENT binds the next parameter no name took, at the bound's top level and
/// one bracket down; a `?` there leaves its slot open. Before, the sigil-free spelling kept the
/// positional, which no value's type has, and answered nothing.
#[test]
fn a_positional_argument_binds_the_parameter_it_takes() {
    for (bound, rows) in [
        ("Buf[Int64]", vec!["buf(v: 1)"]),
        ("Buf[Int64, Bool]", vec!["buf(v: 1)"]),
        ("Buf[String, N = Bool]", vec!["buf(v: \"s\")"]),
        ("Buf[?]", vec!["buf(v: \"s\")", "buf(v: 1)"]),
        ("Option[Int64]", vec!["some(value: 1)"]),
        ("List[Buf[T = Int64]]", vec!["[buf(v: 1)]"]),
        ("List[T = Buf[Int64]]", vec!["[buf(v: 1)]"]),
    ] {
        for (spelling, rule) in both_spellings(bound) {
            assert_eq!(answers("bhcvtpos", &rule), rows, "{spelling} `{bound}`");
        }
    }
}

/// A PARAMETER THE BOUND LEAVES OUT takes its declared default, as in a type position: `D[A =
/// String]` is `D[A = String, B = Int64]`, and keeps the `dd` whose `b` is an `Int64`. Before,
/// the sigil-free spelling left `B` open and kept both.
#[test]
fn a_declared_default_is_filled() {
    for (bound, rows) in [
        ("D[A = String]", vec!["dd(a: \"s\", b: 1)"]),
        ("D[String]", vec!["dd(a: \"s\", b: 1)"]),
        ("List[T = D[String]]", vec!["[dd(a: \"s\", b: 1)]"]),
    ] {
        for (spelling, rule) in both_spellings(bound) {
            assert_eq!(answers("bhcvtdflt", &rule), rows, "{spelling} `{bound}`");
        }
    }
}

/// AN APPLIED ALIAS is the sort it stands for, with what it fixes, at the bound's top level and
/// one bracket down; a positional binds the parameter it leaves open, and binding again what it
/// fixes is refused once.
#[test]
fn an_applied_alias_is_the_sort_it_stands_for() {
    for (bound, rows) in [
        ("IntBuf[N = Bool]", vec!["buf(v: 1)"]),
        ("IntBuf[Bool]", vec!["buf(v: 1)"]),
        ("List[T = IntBuf[N = Bool]]", vec!["[buf(v: 1)]"]),
    ] {
        for (spelling, rule) in both_spellings(bound) {
            assert_eq!(answers("bhcvtalias", &rule), rows, "{spelling} `{bound}`");
        }
    }
    for bound in ["IntBuf[T = String]", "List[T = IntBuf[T = String]]"] {
        for (spelling, rule) in both_spellings(bound) {
            let errs = load_errors_of(&program("bhcvtrebind", &rule));
            assert_eq!(errs.len(), 1, "{spelling} `{bound}`: one report: {errs:#?}");
            assert!(
                errs[0].contains("'test.bhcvtrebind.IntBuf' is a type alias that already binds `T` to `Int64`"),
                "{spelling} `{bound}`: {errs:#?}"
            );
        }
    }
}

/// A HEAD-INTRODUCED TYPE VARIABLE inside an applied bound still denotes its guard's bound
/// (WI-20260908-PW9A0), named and positional: the list whose element type provides `Summable`
/// is kept, the other filtered. The named half passes either way, by design: it is PW9A0's
/// row, which the fit now runs over; the positional half answered nothing before.
#[test]
fn a_head_type_variable_inside_the_bound_still_resolves() {
    for bound in ["List[T = A]", "List[A]"] {
        for (spelling, param) in [("sigil-free", "a"), ("sigil", "?a")] {
            let src = format!(
                "namespace test.bhcvttvar\n  import anthill.prelude.{{Int64, Bool, Eq, List}}\n  sort \
                 Summable\n    sort T = ?\n    requires Eq[T]\n  end\n  rule src(?a)\n  fact \
                 src([1, 2])\n  fact src([true])\n  rule p[A]({param}: {bound}) :- src({param}), \
                 Summable[A]\nend\nnamespace anthill.prelude.Int64\n  import \
                 test.bhcvttvar.Summable\n  provides Summable[T = Int64]\nend\n"
            );
            let mut kb = load_kb_with(&src);
            let found = query_unary(&mut kb, "test.bhcvttvar.p");
            let rendered: Vec<String> = found
                .into_iter()
                .map(|(v, definite)| {
                    assert!(definite, "{spelling} `{bound}`: a definite answer");
                    render(&mut kb, &v)
                })
                .collect();
            assert_eq!(rendered, vec!["[1, 2]"], "{spelling} `{bound}`");
        }
    }
}
