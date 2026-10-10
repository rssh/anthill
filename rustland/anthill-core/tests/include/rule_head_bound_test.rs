//! A rule head's bound is a type on whichever carrier it rides, in both spellings.
//!
//! THE RULE. `rule p(?x: T)` and `rule p(x: T)` give the head variable the same bound: the
//! type `T` is, a type alias written in it read as the type it stands for and kept by name
//! for a message. The rule's record holds the bound as a value, and everything that reads
//! it — the check a typed equation makes when it is applied, the goal the typer adds to a
//! relational rule, the relation's column type — reads it through the view.
//!
//! BEFORE.
//!
//!   * The parameter spelling stored a bare alias AS THE TYPE. Over `rule boxes(x:
//!     IntBox)`, `Box.peek(boxes.head.x)` was refused, "no impl matches … Box[V =
//!     Int64]", where the `?x: IntBox` spelling typed; and the column printed `(x:
//!     IntBox)` where the other spelling printed `(x: Box[V = Int64])`.
//!   * The record held a term, so the name a bound was written by had nowhere to ride:
//!     `rule colours(?x: Shade)` gave a column `(x: Colour)`.
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   the parameter spelling's bound kept as written (`rule_bound_read_through_aliases`
//!   not called) — FAIL:
//!     a_bound_is_the_type_its_alias_stands_for_in_both_spellings
//!     a_bound_keeps_the_alias_it_was_written_by_in_both_spellings, the `x:` rows
//!   the `?x:` spelling's bound lowered without the alias node (`type_expr_to_value`),
//!   or a bound stored as the term of its type (`rule_bound_as_written` answering the
//!   term) — FAIL:
//!     a_bound_keeps_the_alias_it_was_written_by_in_both_spellings
//!   the check of a typed equation reading a term alone (`typed_pattern_bounds_hold`
//!   refusing a bound that is no term) — FAIL:
//!     a_typed_equation_fires_at_a_bound_written_through_an_alias
//!   a bound on an occurrence left open when the rule is stored
//!   (`install_rule_type_bounds` closing a term alone), or left closed when the rule is
//!   read as a relation (`relation_clause_columns` opening a term alone) — FAIL:
//!     a_tie_between_two_bounds_is_pinned_through_one_written_by_an_alias
//!
//!   PASS EITHER WAY, by design:
//!     both_spellings_keep_the_values_of_the_type — the fence: what a bound filters is
//!       the same before and after, and in both spellings.

use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

use crate::common::{load_errors_of, load_kb_with, query_unary};

fn source(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace test.{ns}
  import anthill.prelude.{{Int64, String, Bool, List, EmptyStream}}
  sort Colour
    entity red
    entity green
  end
  sort Shade = Colour
  sort Money = Int64
  sort Box
    sort V = ?
    entity mk(v: V)
    operation peek(b: Self) -> V = b.v
  end
  sort IntBox = Box[V = Int64]
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(a: A, b: B)
  end
  fact item(red())
  fact item(green())
  fact item(5)
  fact held(mk(v: 1))
  fact many([red()])
{body}
end
"#
    )
}

/// The one refusal of a source that must not load.
fn refusal(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, body));
    assert_eq!(errs.len(), 1, "{ns}: one refusal: {errs:#?}");
    errs.into_iter().next().unwrap()
}

/// The two spellings of a head whose one variable is bound at `ty`.
fn spellings(name: &str, ty: &str, body_of: &str) -> [(&'static str, String); 2] {
    [
        ("sigil", format!("  rule {name}(?x: {ty}) :- {body_of}(?x)")),
        ("param", format!("  rule {name}(x: {ty}) :- {body_of}(x)")),
    ]
}

/// An operation that reads relation `rel` whole and declares its rows as `row`.
fn rows_of(rel: &str, row: &str) -> String {
    format!("  operation all() -> List[({row})] effects Error =\n    let r = {rel}\n    r.takeN(5)")
}

// ── the type a bound is ─────────────────────────────────────────────────────

/// A bound written through an alias is the type the alias stands for, in both spellings:
/// the sort's own operation takes the column's value.
#[test]
fn a_bound_is_the_type_its_alias_stands_for_in_both_spellings() {
    for (spelling, rule) in spellings("boxes", "IntBox", "held") {
        let call = "  operation go() -> RESULT effects {Error, Error[EmptyStream]} =\n    \
                    Box.peek(boxes.head.x)";
        let errs = load_errors_of(&source(
            &format!("rhbis{spelling}"),
            &format!("{rule}\n{}", call.replace("RESULT", "Int64")),
        ));
        assert!(errs.is_empty(), "{spelling}: {errs:#?}");
        // …and it is typed, not waved through: at another result it is refused by type.
        let refused = refusal(
            &format!("rhbisbad{spelling}"),
            &format!("{rule}\n{}", call.replace("RESULT", "String")),
        );
        assert!(
            refused.contains("go.return (op-return): expected String, got Int64"),
            "{spelling}: {refused}"
        );
    }
}

/// A bound keeps what it filters, in both spellings and through an alias: the values of
/// the type, and no other.
#[test]
fn both_spellings_keep_the_values_of_the_type() {
    let mut rules = String::from("  rule every(?x) :- item(?x)\n");
    for (ty, tag) in [("Shade", "alias"), ("Colour", "plain")] {
        for (spelling, rule) in spellings(&format!("{tag}_NAME"), ty, "item") {
            rules.push_str(&rule.replace("NAME", spelling));
            rules.push('\n');
        }
    }
    let mut kb = load_kb_with(&source("rhbkeep", &rules));
    let count = |kb: &mut KnowledgeBase, rule: &str| {
        query_unary(kb, &format!("test.rhbkeep.{rule}")).len()
    };
    assert_eq!(count(&mut kb, "every"), 3, "the facts hold a number too");
    for rule in ["alias_sigil", "alias_param", "plain_sigil", "plain_param"] {
        assert_eq!(count(&mut kb, rule), 2, "{rule} answers the two colours");
    }
}

// ── the name it was written by ──────────────────────────────────────────────

/// The column of a rule read as a relation shows its bound as written, in both spellings.
#[test]
fn a_bound_keeps_the_alias_it_was_written_by_in_both_spellings() {
    for (ty, facts, shown) in [
        ("Shade", "item", "got List[T = (x: Shade)] (List[T = (x: Colour)])"),
        (
            "List[T = Shade]",
            "many",
            "got List[T = (x: List[T = Shade])] (List[T = (x: List[T = Colour])])",
        ),
    ] {
        for (spelling, rule) in spellings("colours", ty, facts) {
            let ns = format!("rhbname{spelling}{}", facts);
            let refused = refusal(&ns, &format!("{rule}\n{}", rows_of("colours", "x: Int64")));
            assert!(refused.contains(shown), "{spelling} {ty}: {refused}");
        }
    }
}

// ── the readers ─────────────────────────────────────────────────────────────

/// A typed `@[simp]` equation whose bound is written through an alias is applied to a
/// value of the type, and to no other.
#[test]
fn a_typed_equation_fires_at_a_bound_written_through_an_alias() {
    let mut kb = load_kb_with(
        "namespace test.rhbeq\n  import anthill.prelude.{Int64, Bool}\n  \
         import test.rhbeq.Lib.{keep}\n  sort Money = Int64\n  \
         sort Lib\n    sort A = ?\n    operation {\n      keep(x: A, y: A) -> A\n    }\n    \
         rule {\n      keep_id: keep(?x: Money, ?y) <=> ?x @[simp]\n    }\n  end\nend\n",
    );
    let keep = kb.resolve_symbol("test.rhbeq.Lib.keep");
    let call = |kb: &mut KnowledgeBase, a: Literal, b: Literal| {
        let a = kb.alloc(Term::Const(a));
        let b = kb.alloc(Term::Const(b));
        let call = kb.alloc(Term::Fn {
            functor: keep,
            pos_args: SmallVec::from_slice(&[a, b]),
            named_args: SmallVec::new(),
        });
        (call, kb.simplify(call))
    };
    let (_, at_int) = call(&mut kb, Literal::Int(5), Literal::Int(7));
    assert_eq!(kb.get_term(at_int), &Term::Const(Literal::Int(5)));
    let (written, at_bool) = call(&mut kb, Literal::Bool(true), Literal::Bool(false));
    assert_eq!(at_bool, written, "a `Bool` is no `Money`: the call stays");
}

/// Two bounds tied by one variable, one of them written through an alias: the argument
/// pins the variable, and the other column comes back at it.
#[test]
fn a_tie_between_two_bounds_is_pinned_through_one_written_by_an_alias() {
    let program = |result: &str| {
        format!(
            "  rule same(?x: Pair[A = Money, B = ?t], ?y: List[T = ?t]) :- ?y <=> [?x.b]\n  \
             operation o(x: Pair[A = Int64, B = String]) -> {result}\n    \
             effects {{Error, Error[EmptyStream]}}\n    = same(x).head.y"
        )
    };
    let errs = load_errors_of(&source("rhbtie", &program("List[T = String]")));
    assert!(errs.is_empty(), "{errs:#?}");
    let refused = refusal("rhbtiebad", &program("List[T = Int64]"));
    assert!(
        refused.contains("expected List[T = Int64], got List[T = String]"),
        "{refused}"
    );
}
