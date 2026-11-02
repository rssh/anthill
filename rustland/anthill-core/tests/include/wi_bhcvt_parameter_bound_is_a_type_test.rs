//! WI-20261005-BHCVT — a rule head's sigil-free parameter bound (`x: T`, kernel-language.md
//! §5.3, "The parameter form") is lowered as the type it writes, by the door that lowers the
//! `?x: T` spelling's annotation, so the two are one form: an argument binds the parameter it
//! takes and one that takes none is refused where it is written and not built, a positional is
//! keyed, a declared default filled, a value written by name kept (`N = 3`), a type alias read
//! through at any depth; and a constructor after the `:` — its name, or a bracket applying it —
//! is its type (§8.2). A call builds a value and stays a named argument.
//!
//! Before, the bound was converted as a TERM, at the depth of a clause's instance claim, which
//! nothing fits, with the term walk's own readings of what a type door reads. MEASURED on
//! 3bf56e41: `rule p(x: Buf[W = Int64]) :- q(x)` loaded clean and answered nothing where `?x:
//! Buf[W = Int64]` is refused; `x: Buf[Int64]` answered nothing where `?x: Buf[Int64]` answers
//! `buf(v: 1)`; `x: IntBuf[N = Bool]` answered every row of `q` with a residual `domain(…,
//! IntBuf[N = Bool])`; `x: List[T = IntBuf[N = Bool]]` was refused, "`IntBuf` … declares no
//! type parameters"; `x: Buf[Int64, N = 3]` was refused, "unresolved name '3'"; `x:
//! Buf.buf[T = Int64]` and `x: Colour.red` were named arguments over a constant `x`; `x:
//! Buf[T = Int64].T` was refused as a companion receiver.
//!
//! WHICH ROWS FAIL WITH THE CHANGE BACKED OUT — measured with each part switched off alone in
//! one build, over this file:
//!
//!   * the applied bound converted as a term again (`convert_term`, then its aliases read) →
//!     every row but [`a_well_formed_bound_filters`] and [`a_constructor_is_its_type`];
//!   * a call taken for a type (the call exclusion in `parse_arg_names_a_sort` taken out) →
//!     [`a_constructor_is_its_type`]: its `x: Option.some(1)` is lowered as a bound, and the
//!     load panics on a bracket that writes no type;
//!   * a constructor not taken for a type (`parse_arg_is_constructor_type` answering `false`)
//!     → [`a_constructor_is_its_type`], and nothing else.
//!   * a member read off a bracket given no type reading (`convert_paren_less_citation`
//!     recording none) → [`a_member_read_off_a_bracket_is_its_type`], refused as a companion
//!     receiver, and [`an_open_member_is_refused_not_a_crash`]'s sigil-free entry;
//!   * a member asked of the sort an alias stands for no more (`parse_arg_is_bracket_member_type`
//!     answering `false`) → [`a_member_read_off_a_bracket_is_its_type`], at `IntBuf[N =
//!     Bool].T`: a member of the sort itself is a type parameter by its dotted name;
//!   * a structural type form completed as a sort (`expand_unwritten_type_params` without its
//!     `TypeExtractor` arm) → [`an_open_member_is_refused_not_a_crash`], which panics.
//!
//!   PASSES EITHER WAY, by design: [`a_well_formed_bound_filters`], the control the refusals and
//!   the answers are read against.

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
    // A call whose head names a SORT (`Leaf` is its own entity) builds a value too.
    let mut kb = load_kb_with(
        "namespace test.bhcvtleaf\n  import anthill.prelude.String\n  sort Leaf\n    entity \
         Leaf(name: String)\n  end\n  rule p(c: Leaf(name: \"tip\")) :- true\nend\n",
    );
    assert_eq!(query_unary(&mut kb, "test.bhcvtleaf.p").len(), 0, "a sort-headed call is a datum");
    let held = crate::common::query_pattern_term(&mut kb, "test.bhcvtleaf.p(c: ?v)");
    assert_eq!(
        kb.resolve(&[held], &anthill_core::kb::resolve::ResolveConfig::default()).len(),
        1,
        "the call is the named argument `c`'s value"
    );
}

/// A MEMBER READ OFF A BRACKET is the type it names at the bracket's arguments (§5.4), as a
/// type position reads it: `List[T = Buf[T = Int64]].T` is `Buf[T = Int64]`, through an alias
/// too. Before, the sigil-free spelling was refused, "a companion receiver's type bracket is not
/// read here".
#[test]
fn a_member_read_off_a_bracket_is_its_type() {
    for bound in ["List[T = Buf[T = Int64]].T", "List[T = IntBuf[N = Bool]].T"] {
        for (spelling, rule) in both_spellings(bound) {
            assert_eq!(answers("bhcvtmember", &rule), vec!["buf(v: 1)"], "{spelling} `{bound}`");
        }
    }
    // At the bound's top level, through an alias: `IntBuf[N = Bool].T` is `Int64`.
    for (spelling, rule) in both_spellings("IntBuf[N = Bool].T") {
        let mut kb = load_kb_with(&format!(
            "namespace test.bhcvtmemberalias\n  import anthill.prelude.{{Int64, String, Bool}}\n  \
             sort Buf\n    sort T = ?\n    sort N = ?\n    entity buf(v: T)\n  end\n  sort IntBuf \
             = Buf[T = Int64]\n  rule q(?x)\n  fact q(5)\n  fact q(\"s\")\n  {rule}\nend\n"
        ));
        let found = query_unary(&mut kb, "test.bhcvtmemberalias.p");
        let rendered: Vec<String> = found.iter().map(|(v, _)| render(&mut kb, v)).collect();
        assert_eq!(rendered, vec!["5"], "{spelling}: the `Int64` row");
        assert!(found.iter().all(|(_, definite)| *definite), "{spelling}: definite");
    }
}

/// A MEMBER THE BRACKET LEAVES OPEN, and a sort's member named without its arguments, is
/// refused as a type the clause cannot check a value at, in both spellings. Before, `?x:
/// Buf.N` and `?x: Buf[T = Int64].N` crashed the loader (`make_parameterized_type` handed the
/// rigid projection `Buf.N` as a sort to complete).
#[test]
fn an_open_member_is_refused_not_a_crash() {
    for (bound, spellings) in [
        ("Buf[T = Int64].N", both_spellings("Buf[T = Int64].N").to_vec()),
        ("Buf.N", vec![("sigil", "rule p(?x: Buf.N) :- q(?x)".to_owned())]),
    ] {
        for (spelling, rule) in spellings {
            let errs = load_errors_of(&program("bhcvtopen", &rule));
            assert!(
                errs.iter().any(|e| e.contains("expected a well-formed type projection")),
                "{spelling} `{bound}`: {errs:#?}"
            );
        }
    }
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
        ("Buf[Int64, N = 3]", vec!["buf(v: 1)"]),
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
        ("IntBuf[N = 3]", vec!["buf(v: 1)"]),
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
/// is kept, the other filtered. The named half is PW9A0's row, now lowered by the type door;
/// the positional half answered nothing before.
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
