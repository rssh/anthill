//! WI-20261022-DRGCP — a query answer is printed by the one printer, through the view.
//!
//! An answer the resolver rebuilds over its bindings is a transient entity, not a
//! hash-consed term (WI-20260905-N20EZ), and `anthill query` printed it with a renderer of
//! its own that wrote every entity as an application, `Box(V: Untrusted)` — a spelling the
//! loader refuses for a type — where its term twin prints `Box[V = Untrusted]`.
//!
//! An answer that holds an EXPRESSION is written as the source it was written as: the view
//! reads an `if` as its reflect-term twin, and the printer hands an expression occurrence to
//! the occurrence writer instead (`PrintView::own_spelling`).
//!
//! BACKED OUT — the table in the header of
//! `anthill-core/tests/include/wi_drgcp_precondition_goal_spelling_test.rs`.

use crate::common::{anthill, write_temp};

#[test]
fn an_answer_rebuilt_over_a_type_is_written_as_the_type() {
    let path = write_temp(
        "drgcp_answer.anthill",
        "namespace t\n  enum Level\n    entity Untrusted\n  end\n  sort Box\n    sort V = ?\n  end\n  \
         fact held(Untrusted[])\n  rule boxed(Box[V = ?x]) :- held(?x)\nend\n",
    );
    let out = anthill(&["query", "--path", path.to_str().unwrap(), "t.boxed(?b)"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(
        out.has_stdout_line("?b = Box[V = Untrusted]"),
        "the answer is the type the rule builds; stdout:\n{}",
        out.stdout
    );
}

/// The `if` is its reflect constructor, written as a call: data, which the rule binds. The
/// syntax `(if … then … else …)` would be evaluated (WI-20261011-2S5FP).
#[test]
fn an_answer_holding_an_expression_is_written_as_its_source() {
    let path = write_temp(
        "drgcp_expr_answer.anthill",
        "namespace t\n  import anthill.prelude.{Int64, String}\n  sort Box\n    sort V = ?\n  end\n  \
         rule pick(?t) :- ?t <=> anthill.reflect.Expr.if_expr(cond: true, \
         then_branch: Box[V = Int64], else_branch: Box[V = String])\nend\n",
    );
    let out = anthill(&["query", "--path", path.to_str().unwrap(), "t.pick(?t)"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(
        out.has_stdout_line("?t = if true then Box[V = Int64] else Box[V = String]"),
        "the answer is the expression as written; stdout:\n{}",
        out.stdout
    );
}

/// One type, two carriers, one answer: written in the rule as an expression (a type value
/// whose binding is a type value) and read off a fact as a term.
#[test]
fn a_type_value_answers_as_its_fact_twin() {
    let path = write_temp(
        "drgcp_type_value_answer.anthill",
        "namespace t\n  enum Level\n    entity Untrusted\n  end\n  sort Box\n    sort V = ?\n  end\n  \
         fact pt(Box[V = Untrusted])\n  rule pq(?t) :- pt(?t)\n  \
         rule ty(?t) :- ?t <=> Box[V = Untrusted[]]\nend\n",
    );
    for pattern in ["t.ty(?t)", "t.pq(?t)"] {
        let out = anthill(&["query", "--path", path.to_str().unwrap(), pattern]);
        assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
        assert!(
            out.has_stdout_line("?t = Box[V = Untrusted]"),
            "{pattern}: stdout:\n{}",
            out.stdout
        );
    }
}
