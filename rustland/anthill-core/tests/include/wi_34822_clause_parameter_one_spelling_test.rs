//! WI-20261013-34822 — a sort's parameter written inside a tuple or an arrow of a clause
//! binding is the parameter's NAME, as it is at a name and in an applied sort.
//!
//! `sort P { sort A = ?  requires Mark[T = (A, Int64)]  provides Apply[F = (A, Int64)] … }`
//! called at `(String, Int64)` beside `MarkS provides Mark[T = (String, Int64)]` was refused,
//! "no impl matches — unresolved: `Mark[T = (_1: ?_, _2: Int64)]`". The loader lowered a
//! binding that is a name or an applied sort with its parameters as references
//! (`sort_binding_to_value`), and handed a tuple or an arrow to the type-position lowering,
//! where a parameter is the variable its declaration published. The readers that put a
//! provider's parameters into its `requires` and its conditions substitute by NAME
//! (`sigma_subst_type`), so the variable was passed by and the requirement asked at `?_`.
//! The provision lookup read the variable as the parameter since da39cc3d (`impl_param_ref`),
//! a reading at that one reader; it is gone, and the loader writes one spelling.
//!
//! AN EFFECT ROW STAYS AS A TYPE POSITION HOLDS IT, in this lowering and in the alias reading
//! that shares its canon (`type_in_clause_canon`): a row's tail is a variable, and the member
//! rule reads a row slot naming its own row by it. The alias reading turned that tail into
//! the parameter's name, and a provision binding written through an alias was refused where
//! the same binding written out answers — found while this change was measured.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: the call runs and the provider answers its number, or the
//! refusal names the type the call binds the parameter to.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! MEASURED 2026-10-14, one back-out at a time, each switched in one build:
//!
//! 1. A TUPLE OR AN ARROW BINDING LOWERED AS A TYPE POSITION, its parameter the variable
//!    (`sort_binding_to_value`'s tuple-and-arrow arm not taken): 5 of this file's 6 fail,
//!    all but [`an_alias_binding_whose_row_names_its_own_row_meets_the_instance`].
//!    [`the_controls_answer_as_they_did`] is among them: the lookup reads a parameter by its
//!    name only, so a provision at `(A, Int64)` binds nothing. All five rows of
//!    `provision_own_parameter_in_structural_type_test` fail with them, and
//!    `wi_f8pyz_spec_clause_alias_test::an_alias_binding_a_tuple_reads_as_the_tuple_written_
//!    directly`. In a build with debug assertions each fails at `impl_param_ref`'s
//!    assertion, which names the parameter whose variable the binding holds; without it,
//!    10 of the 11 fail by their verdicts.
//! 2. THE CANON REACHING INTO AN EFFECT ROW (`type_in_clause_canon` and the occurrence
//!    rewriter without their row stop):
//!    [`an_alias_binding_whose_row_names_its_own_row_meets_the_instance`] alone; its direct
//!    spelling passes, by design.
//!
//! PASS ON THE TREE BEFORE THIS CHANGE, by design: [`the_controls_answer_as_they_did`], and
//! the direct spelling in [`an_alias_binding_whose_row_names_its_own_row_meets_the_instance`]
//! (each run with the binary of the parent commit).

use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::Value;

/// `Apply`, whose one parameter is the type its operation receives; `Mark`, the spec a
/// provider requires; `Box`, `Buf[T, N]` (`N` the value-in-type argument) and `Strm[T, E]`
/// (`E` a row). `body` follows.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List}}

  sort Box
    sort T = ?
    entity box(v: T)
  end

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
  end

  sort Apply
    sort F = ?
    operation run(f: F) -> Int64
  end

  sort Mark
    sort T = ?
    operation mark(x: T) -> Int64
  end
{body}
end
"#
    )
}

/// `MarkS`, providing `Mark` at `at`; its `mark` answers 1.
fn mark_at(at: &str) -> String {
    format!(
        "\n  sort MarkS\n    provides Mark[T = {at}]\n    \
         operation mark(x: {at}) -> Int64 = 1\n  end\n"
    )
}

/// `P`, over `A` and the row `R`, with `clauses`, and a `run` taking `at` that answers 30.
fn provider(clauses: &str, at: &str) -> String {
    format!(
        "\n  sort P\n    sort A = ?\n    effects R = ?\n{clauses}\n    \
         operation run(f: {at}) -> Int64 = 30\n  end\n"
    )
}

/// `operation via(f: {at}) -> Int64 = Apply.run(f)`, and `go` calling it with `arg`.
fn via(at: &str, arg: &str) -> String {
    format!(
        "\n  operation via(f: {at}) -> Int64 = Apply.run(f)\n  \
         operation go() -> Int64 = via({arg})\n"
    )
}

fn answers(ns: &str, body: &str) -> i64 {
    let src = program(ns, body);
    let mut interp = interp_for(&src);
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` must run to an Int64: {other:?}\n{src}"),
    }
}

/// One program of the requirement table: `Mark` provided at `marked`, `P` with `clauses`
/// and a member at `provided`, the call at `called` with `arg`.
struct Row {
    marked: &'static str,
    clauses: &'static str,
    provided: &'static str,
    called: &'static str,
    arg: &'static str,
}

impl Row {
    fn body(&self) -> String {
        format!(
            "{}{}{}{}",
            mark_at(self.marked),
            provider(self.clauses, self.provided),
            via(self.called, self.arg),
            "\n  operation mk() -> Buf[T = String, N = 3] = buf(v: \"s\")\n  \
             operation mkb() -> Buf[T = Bool, N = 3] = buf(v: true)\n"
        )
    }
}

/// THE PROVIDER'S REQUIREMENT, OR ITS PROVISION'S CONDITION, WRITTEN AT A TUPLE OR AN ARROW
/// OF ITS PARAMETER, IS READ AT THE TYPE THE CALL BINDS THE PARAMETER TO, and `MarkS`
/// supplies it. Each row was refused naming `Mark` with the parameter left `?_`. The
/// ticket's (1) to (4), a type holding a value inside the tuple, and an arrow whose row is
/// `P`'s own row parameter — inside the row only, and beside the same parameter outside it.
#[test]
fn a_requirement_at_a_tuple_or_an_arrow_of_the_parameter_is_supplied() {
    let rows = [
        (
            "requires_tuple",
            Row {
                marked: "(String, Int64)",
                clauses: "    requires Mark[T = (A, Int64)]\n    provides Apply[F = (A, Int64)]",
                provided: "(A, Int64)",
                called: "(String, Int64)",
                arg: "(\"s\", 1)",
            },
        ),
        (
            "condition_tuple",
            Row {
                marked: "(String, Int64)",
                clauses: "    provides Apply[F = (A, Int64)] :- Mark[T = (A, Int64)]",
                provided: "(A, Int64)",
                called: "(String, Int64)",
                arg: "(\"s\", 1)",
            },
        ),
        (
            "requires_arrow",
            Row {
                marked: "(String) -> Int64",
                clauses: "    requires Mark[T = (A) -> Int64]\n    provides Apply[F = (A, Int64)]",
                provided: "(A, Int64)",
                called: "(String, Int64)",
                arg: "(\"s\", 1)",
            },
        ),
        (
            "applied_provision",
            Row {
                marked: "(String, Int64)",
                clauses: "    requires Mark[T = (A, Int64)]\n    provides Apply[F = Box[T = A]]",
                provided: "Box[T = A]",
                called: "Box[T = String]",
                arg: "box(v: \"s\")",
            },
        ),
        (
            "held_value",
            Row {
                marked: "(Buf[T = String, N = 3], Int64)",
                clauses: "    requires Mark[T = (Buf[T = A, N = 3], Int64)]\n    \
                          provides Apply[F = (Buf[T = A, N = 3], Int64)]",
                provided: "(Buf[T = A, N = 3], Int64)",
                called: "(Buf[T = String, N = 3], Int64)",
                arg: "(mk(), 1)",
            },
        ),
        (
            "row_parameter",
            Row {
                marked: "(Int64) -> Int64",
                clauses:
                    "    requires Mark[T = (A) -> A @ {R}]\n    provides Apply[F = (A) -> A @ {R}]",
                provided: "(A) -> A @ {R}",
                called: "(Int64) -> Int64",
                arg: "lambda (x: Int64) -> x",
            },
        ),
        (
            "row_parameter_twice",
            Row {
                marked: "(Strm[T = Int64, E = {}]) -> Int64",
                clauses: "    requires Mark[T = (Strm[T = A, E = R]) -> A @ {R}]\n    \
                          provides Apply[F = (Strm[T = A, E = R]) -> A @ {R}]",
                provided: "(Strm[T = A, E = R]) -> A @ {R}",
                called: "(Strm[T = Int64, E = {}]) -> Int64",
                arg: "lambda (s: Strm[T = Int64, E = {}]) -> 5",
            },
        ),
    ];
    for (name, row) in rows {
        assert_eq!(
            answers(&format!("w34822.{name}"), &row.body()),
            30,
            "`{name}`"
        );
    }
}

/// `Self` inside the tuple: `P[A = A]`, its parameter a reference as the rest of the clause.
#[test]
fn self_inside_a_tuple_is_read_at_the_calls_type() {
    let body = format!(
        "{}\n  sort P\n    sort A = ?\n    entity p(v: A)\n    \
         requires Mark[T = (Self, Int64)]\n    provides Apply[F = (Self, Int64)]\n    \
         operation run(f: (Self, Int64)) -> Int64 = 30\n  end\n{}",
        mark_at("(P[A = String], Int64)"),
        via("(P[A = String], Int64)", "(p(v: \"s\"), 1)")
    );
    assert_eq!(answers("w34822.self_tuple", &body), 30);
}

/// … AND A CALL AT A TYPE `MarkS` DOES NOT SUPPLY IS REFUSED NAMING THAT TYPE, where it named
/// the tuple with the parameter left `?_` (the ticket's (5)).
#[test]
fn a_requirement_nothing_supplies_is_refused_naming_the_calls_type() {
    let rows = [
        (
            "bool_tuple",
            Row {
                marked: "(String, Int64)",
                clauses: "    requires Mark[T = (A, Int64)]\n    provides Apply[F = (A, Int64)]",
                provided: "(A, Int64)",
                called: "(Bool, Int64)",
                arg: "(true, 1)",
            },
            "Mark[T = (_1: Bool, _2: Int64)]",
        ),
        (
            "bool_held_value",
            Row {
                marked: "(Buf[T = String, N = 3], Int64)",
                clauses: "    requires Mark[T = (Buf[T = A, N = 3], Int64)]\n    \
                          provides Apply[F = (Buf[T = A, N = 3], Int64)]",
                provided: "(Buf[T = A, N = 3], Int64)",
                called: "(Buf[T = Bool, N = 3], Int64)",
                arg: "(mkb(), 1)",
            },
            "Mark[T = (_1: Buf[T = Bool, N = 3], _2: Int64)]",
        ),
    ];
    for (name, row, named) in rows {
        let errs = load_errors_of(&program(&format!("w34822.{name}"), &row.body()));
        assert_refused_naming(&errs, &["no impl matches", named], name);
    }
}

/// TWO DEFAULT MARKS AT A TUPLE OF EACH ONE'S OWN PARAMETER OVERLAP, as two at an applied
/// sort of it do: the refusal names both carriers. With the parameter a variable the two
/// read as one carrier, `(_1: ?_, _2: Int64)`, and the refusal was another one's.
#[test]
fn two_default_marks_at_a_tuple_of_the_parameter_overlap_as_at_an_applied_sort() {
    let marks = |a: &str, b: &str, called: &str, arg: &str| {
        format!(
            "\n  sort P1\n    sort A = ?\n    default provides Apply[F = {a}]\n    \
             operation run(f: {a}) -> Int64 = 10\n  end\n  \
             sort P2\n    sort B = ?\n    default provides Apply[F = {b}]\n    \
             operation run(f: {b}) -> Int64 = 20\n  end\n{}",
            via(called, arg)
        )
    };
    let rows = [
        (
            "tuple",
            marks("(A, Int64)", "(B, Int64)", "(String, Int64)", "(\"s\", 1)"),
            "(_1: A, _2: Int64)",
            "(_1: B, _2: Int64)",
        ),
        (
            "applied",
            marks(
                "Box[T = A]",
                "Box[T = B]",
                "Box[T = String]",
                "box(v: \"s\")",
            ),
            "Box[T = A]",
            "Box[T = B]",
        ),
    ];
    for (name, body, first, second) in rows {
        let errs = load_errors_of(&program(&format!("w34822.defaults_{name}"), &body));
        assert_refused_naming(&errs, &["overlapping defaults", first, second], name);
    }
}

/// A PROVISION BINDING WRITTEN THROUGH AN ALIAS WHOSE ROW NAMES ITS OWN ROW meets the
/// instance, as the binding written out does
/// (`wi_0rp29_member_rule_test::a_receiver_binding_naming_its_own_row_meets_the_instance`).
/// Through the alias it was refused, "writes one of `Car`'s own parameters inside its own
/// slot": the alias reading turned the row's tail into the parameter's name.
#[test]
fn an_alias_binding_whose_row_names_its_own_row_meets_the_instance() {
    for (name, decl, bound) in [
        (
            "alias",
            "    sort CR = Car[EC = {EC, Error[Foo]}, V = V]\n",
            "CR",
        ),
        ("direct", "", "Car[EC = {EC, Error[Foo]}, V = V]"),
    ] {
        let src = format!(
            r#"
namespace w34822.ownrow_{name}
  import anthill.prelude.{{Int64, String, List, Error}}
  sort Foo
    entity foo
  end
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
{decl}    provides Holder[C = {bound}]
    operation peek(c: {bound}) -> Int64 = 30
  end
  operation go() -> Int64 =
    let b: Car[V = Int64, EC = {{Error[Foo]}}] = car(v: 5)
    Holder.peek(b)
end
"#
        );
        let mut interp = interp_for(&src);
        let entry = format!("w34822.ownrow_{name}.go");
        assert!(
            matches!(interp.call(&entry, &[]), Ok(Value::Int(30))),
            "`{name}`: the provision at `{bound}` answers"
        );
    }
}

/// CONTROLS, which pass either way by design: the requirement and the condition at an APPLIED
/// SORT of the parameter, whose `A` was a reference already — supplied at `(String, Int64)`
/// and refused naming `Box[T = Bool]` at `(Bool, Int64)`; and a requirement and a provision
/// written through an alias of the tuple, which the alias reading put in the clause canon
/// already.
#[test]
fn the_controls_answer_as_they_did() {
    let applied = |clauses: &'static str| Row {
        marked: "Box[T = String]",
        clauses,
        provided: "(A, Int64)",
        called: "(String, Int64)",
        arg: "(\"s\", 1)",
    };
    let requires = "    requires Mark[T = Box[T = A]]\n    provides Apply[F = (A, Int64)]";
    let condition = "    provides Apply[F = (A, Int64)] :- Mark[T = Box[T = A]]";
    assert_eq!(
        answers("w34822.ctl_requires", &applied(requires).body()),
        30
    );
    assert_eq!(
        answers("w34822.ctl_condition", &applied(condition).body()),
        30
    );
    let at_bool = Row {
        called: "(Bool, Int64)",
        arg: "(true, 1)",
        ..applied(requires)
    };
    assert_refused_naming(
        &load_errors_of(&program("w34822.ctl_bool", &at_bool.body())),
        &[
            "no impl matches",
            "Mark[T = w34822.ctl_bool.Box[T = anthill.prelude.Bool]]",
        ],
        "the requirement at `Box[T = A]` at `(Bool, Int64)`",
    );
    let alias = Row {
        marked: "(String, Int64)",
        clauses: "    sort TA = (A, Int64)\n    requires Mark[T = TA]\n    provides Apply[F = TA]",
        provided: "TA",
        called: "(String, Int64)",
        arg: "(\"s\", 1)",
    };
    assert_eq!(answers("w34822.ctl_alias", &alias.body()), 30);
}
