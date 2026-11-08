//! WI-20260909-SM910 — a rule-body comparison reaches the carrier's own member, and the
//! resolver's built-in comparison runs only a member a primitive realizes.
//!
//! Measured on 7379c5fd over a `Point` that provides `PartialOrd` and writes `operation
//! gt(a: Point, b: Point) -> Bool = false`: the operation body answered `false`; the
//! rule-body goal, a typed head, a clause declaring `PartialOrd[T = A]` and the query were
//! each UNDECIDED, because a goal took `BuiltinTag::Gt` off its spelled functor
//! `PartialOrd.gt` and `builtin_cmp` has no order for two entities.
//!
//! Now (1) `PartialOrd.gt`/`gte`/`lt`/`lte` are no builtins: their tag is the primitive a
//! carrier's member runs (`Int64.gt`), derived for the carriers as before
//! (`KnowledgeBase::spec_op_primitive_of`); (2) a goal reads the typer's pin
//! (`KnowledgeBase::goal_builtin_tag`), and one nothing typed is read at the type its
//! arguments carry; (3) the `requires` of a body written in the spec over the spec's own
//! parameters is owed by each provision that takes the body, and a call through a
//! dictionary of the spec its caller holds owes it nothing (decided with the user
//! 2026-11-08; kernel-language §8.7); (4) `eq`'s handler reads the pin before its value
//! index, and both families read their result column at three arguments.
//!
//! ## Back-out
//!
//! - `PartialOrd.gt` registered as a builtin again (`register_builtin_tag_as` for
//!   `register_spec_op_primitive` in `KnowledgeBase::register_builtin_tags`):
//!   `the_carriers_own_member_answers_every_spelling`,
//!   `a_carrier_writing_compare_alone_takes_the_spec_body` and
//!   `a_caller_holding_the_spec_owes_the_body_nothing` fail, and so do wi1036's two rows,
//!   wi879's own-`gt` and `Bool` rows, wi1102's and wi642's comparison refusals and
//!   ckd4j's nothing-in-scope row;
//! - the provision's spec-body requirements out (`spec_body_requirements_of_row`
//!   answering nothing): `a_provision_taking_the_body_owes_its_requires` loads clean, and
//!   so does wi_d5wfq's `PBox` written without its condition;
//! - the caller's park kept (`call_park_site` answering `OpSlotParkSite::for_call`):
//!   `a_caller_holding_the_spec_owes_the_body_nothing` is refused naming
//!   `WeakOrd[T = A]`, and wi_d5wfq's `NoUnit` / `viaNo` naming `Unit`;
//! - the result column out of `sem_eq_core` (`pos_arity < 3` read as a test):
//!   `equality_reads_its_result_column` answers with `?r` free;
//! - `no_typed_caller` off in `check_apply_call`:
//!   `an_untyped_comparison_runs_at_the_type_its_values_carry` is refused.
//!
//! Measured 2026-11-08, one switch each, over the rows of this file, wi_d5wfq, wi1036,
//! wi879, wi1102, wi642 and wi_ckd4j.
//!
//! PASS EITHER WAY, BY DESIGN: `equality_at_a_known_type_answers_the_carriers_own_eq`
//! — the pin `sem_eq_core` reads names the member the value index names, on every program
//! measured; the row holds the answer to the pin's reader.

use anthill_core::eval::Value;

/// `Point` provides the ordering tower; `own_gt` decides whether it writes its own `gt`
/// (`false` for every pair, so the answer says which implementation ran: the member
/// `false`, the spec's body derived from `compare` `true` for `pt(2, 1)` over `pt(1, 9)`).
fn point_program(ns: &str, own_gt: bool, tail: &str) -> String {
    let gt = if own_gt {
        "    operation gt(a: Point, b: Point) -> Bool = false\n"
    } else {
        ""
    };
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}}
  import anthill.kernel.{{unify}}

  sort Point
    import anthill.prelude.{{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}}
    entity pt(x: Int64, y: Int64)
    provides PartialEq[Point]
    provides Eq[Point]
    provides PartialOrd[Point]
    provides Ord[Point]
    operation eq(a: Point, b: Point) -> Bool =
      match a
        case pt(ax, ay) ->
          match b
            case pt(bx, by) ->
              if PartialEq.eq(ax, bx) then PartialEq.eq(ay, by) else false
    operation compare(a: Point, b: Point) -> Int64 =
      match a
        case pt(ax, ay) ->
          match b
            case pt(bx, by) ->
              let c = WeakOrd.compare(ax, bx)
              if PartialEq.eq(c, 0) then WeakOrd.compare(ay, by) else c
{gt}  end

  operation viaOp() -> Bool = PartialOrd.gt(pt(2, 1), pt(1, 9))
  operation viaInfix() -> Bool = pt(2, 1) > pt(1, 9)
  rule op(?r) :- unify(?r, viaOp())
  rule infixOp(?r) :- unify(?r, viaInfix())
  rule goal(?r) :- PartialOrd.gt(pt(2, 1), pt(1, 9), ?r)
  rule typed(?r: Bool) :- PartialOrd.gt(pt(2, 1), pt(1, 9), ?r)
  rule cmpG[A](?a: A, ?b: A, ?r) :- PartialOrd[T = A], PartialOrd.gt(?a, ?b, ?r)
  rule guarded(?r) :- cmpG(pt(2, 1), pt(1, 9), ?r)
  rule operand(?r) :- unify(?r, PartialOrd.gt(pt(2, 1), pt(1, 9)))
  rule infix(?r) :- unify(?r, pt(2, 1) > pt(1, 9))
{tail}end
"#
    )
}

const SPELLINGS: [&str; 8] = [
    "op", "infixOp", "goal", "typed", "guarded", "operand", "infix", "query",
];

/// The answer of one spelling, rendered: a definite `Bool`, or `UNDECIDED`. The query is the
/// two-place test the CLI converts, read by its solutions: none is `false`, one definite
/// `true`.
fn answer(kb: &mut anthill_core::kb::KnowledgeBase, ns: &str, spelling: &str) -> String {
    if spelling == "query" {
        let goal = crate::common::query_pattern_term(
            kb,
            &format!("anthill.prelude.PartialOrd.gt({ns}.Point.pt(2, 1), {ns}.Point.pt(1, 9))"),
        );
        let got = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
        return match got.as_slice() {
            [] => "false".to_string(),
            [one] if one.is_definite() => "true".to_string(),
            _ => format!("UNDECIDED ({} rows)", got.len()),
        };
    }
    let rows = crate::common::query_unary(kb, &format!("{ns}.{spelling}"));
    rows.iter()
        .map(|(v, definite)| match v {
            Value::Bool(b) if *definite => b.to_string(),
            _ if !*definite => "UNDECIDED".to_string(),
            other => format!("{other:?}"),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn answers(ns: &str, own_gt: bool) -> Vec<(&'static str, String)> {
    let mut kb = crate::common::load_kb_with(&point_program(ns, own_gt, ""));
    SPELLINGS.iter().map(|s| (*s, answer(&mut kb, ns, s))).collect()
}

/// The carrier's own `gt` answers every spelling of the call: an operation body, `>` in one,
/// the rule-body goal, a typed head, a clause declaring `PartialOrd[T = A]` (its dictionary
/// chooses the member), an operand, `>` in a rule body, and the query. Fails with
/// `PartialOrd.gt` a builtin again: the goal, typed, guarded and query rows are UNDECIDED.
#[test]
fn the_carriers_own_member_answers_every_spelling() {
    let got = answers("sm910.own", true);
    let wrong: Vec<_> = got.iter().filter(|(_, a)| a != "false").collect();
    assert!(wrong.is_empty(), "every spelling answers `Point.gt`'s `false`; got {got:?}");
}

/// A carrier writing `compare` alone takes `PartialOrd.gt`'s body, which derives the answer
/// from it: `true` for `pt(2, 1)` over `pt(1, 9)`, in every spelling. Fails with
/// `PartialOrd.gt` a builtin again, as the row above does.
#[test]
fn a_carrier_writing_compare_alone_takes_the_spec_body() {
    let got = answers("sm910.cmp", false);
    let wrong: Vec<_> = got.iter().filter(|(_, a)| a != "true").collect();
    assert!(wrong.is_empty(), "every spelling answers `compare`'s `true`; got {got:?}");
}

/// The body written in `PartialOrd` requires `WeakOrd[T]`; a provision taking it owes that at
/// its own type, and is refused where it does not hold, with no call anywhere. The advised
/// repairs answer: providing `WeakOrd` (with its `compare`), or writing `gt`, `gte`, `lt`
/// and `lte`. Fails with `spec_body_requirements_of_row` answering nothing: it loads clean.
#[test]
fn a_provision_taking_the_body_owes_its_requires() {
    let program = |members: &str| {
        format!(
            r#"namespace sm910.order
  import anthill.prelude.{{Int64, Bool, WeakOrd, PartialOrd, PartialEq, Eq}}
  import anthill.kernel.{{unify}}
  sort Blob
    import anthill.prelude.{{Int64, Bool, WeakOrd, PartialOrd, PartialEq, Eq}}
    entity blob(v: Int64)
    provides PartialEq[Blob]
    provides Eq[Blob]
    provides PartialOrd[Blob]
{members}  end
  operation probe() -> Bool = PartialOrd.gt(blob(2), blob(1))
  rule answer(?r) :- unify(?r, probe())
end
"#
        )
    };
    let errors = crate::common::load_errors_of(&program(""));
    for op in ["gt", "gte", "lt", "lte"] {
        crate::common::assert_refused_naming(
            &errors,
            &[
                &format!("'sm910.order.Blob' provides 'anthill.prelude.PartialOrd' and writes no `{op}` of its own"),
                "'sm910.order.Blob' does not provide 'anthill.prelude.WeakOrd'",
            ],
            "`Blob` taking the ordering bodies without `WeakOrd`",
        );
    }
    let compare = "    provides WeakOrd[Blob]
    \
                   operation compare(a: Blob, b: Blob) -> Int64 = match a\n      \
                   case blob(x) -> match b\n        case blob(y) -> WeakOrd.compare(x, y)\n";
    let own = "    operation gt(a: Blob, b: Blob) -> Bool = true\n    \
               operation gte(a: Blob, b: Blob) -> Bool = true\n    \
               operation lt(a: Blob, b: Blob) -> Bool = false\n    \
               operation lte(a: Blob, b: Blob) -> Bool = false\n";
    for (repair, members) in [("WeakOrd", compare), ("its own members", own)] {
        let mut kb = crate::common::load_kb_with(&program(members));
        let rows = crate::common::query_unary(&mut kb, "sm910.order.answer");
        assert!(
            matches!(rows.as_slice(), [(Value::Bool(true), true)]),
            "the repair by {repair} answers `true`; got {rows:?}"
        );
    }
}

/// A generic caller holding `PartialOrd[T = A]` calls `PartialOrd.gt` through that
/// dictionary and owes the body's `WeakOrd[T = A]` nothing: it loads, and answers at each
/// carrier its own way — `Int64`'s primitive, `Float`'s IEEE order, a carrier's own `gt`,
/// a carrier's `compare` through the body. A caller holding nothing of the spec owes the
/// body's requirement as the call of any operation does. Fails with the caller's park kept
/// (`call_park_site` answering `for_call`): refused naming `WeakOrd[T = A]`.
#[test]
fn a_caller_holding_the_spec_owes_the_body_nothing() {
    let tail = "  operation bigger[A](a: A, b: A) -> Bool requires PartialOrd[T = A] = PartialOrd.gt(a, b)\n  \
                operation i() -> Bool = bigger(3, 1)\n  \
                operation f() -> Bool = bigger(1.5, 2.5)\n  \
                operation p() -> Bool = bigger(pt(2, 1), pt(1, 9))\n";
    for (ns, own_gt, want_p) in [("sm910.gen.own", true, false), ("sm910.gen.cmp", false, true)] {
        let mut interp = crate::common::interp_for(&point_program(ns, own_gt, tail));
        for (entry, want) in [("i", true), ("f", false), ("p", want_p)] {
            let got = interp.call(&format!("{ns}.{entry}"), &[]);
            assert!(
                matches!(got, Ok(Value::Bool(b)) if b == want),
                "{ns}.{entry} answers {want}; got {got:?}"
            );
        }
    }
    let unheld = point_program(
        "sm910.gen.none",
        false,
        "  operation bare[A](a: A, b: A) -> Bool = PartialOrd.gt(a, b)\n",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&unheld),
        &["anthill.prelude.WeakOrd[T = A]"],
        "a caller holding nothing of `PartialOrd`",
    );
}

/// `Pt`'s own `eq` (equal when `x` agrees) answers every spelling of an equality at `Pt`: the
/// rule-body goal, `=` in a rule body, a clause declaring `PartialEq[T = A]`, and the query.
/// Passes either way by design (the module header).
#[test]
fn equality_at_a_known_type_answers_the_carriers_own_eq() {
    let src = r#"namespace sm910.eq
  import anthill.prelude.{Int64, Bool, PartialEq, Eq}
  sort Pt
    import anthill.prelude.{Int64, Bool, PartialEq, Eq}
    entity pt(x: Int64, y: Int64)
    provides PartialEq[Pt]
    provides Eq[Pt]
    operation eq(a: Pt, b: Pt) -> Bool =
      match a
        case pt(ax, ay) ->
          match b
            case pt(bx, by) -> PartialEq.eq(ax, bx)
  end
  rule goal() :- PartialEq.eq(pt(1, 2), pt(1, 9))
  rule infix() :- pt(1, 2) = pt(1, 9)
  rule eqG[A](?a: A, ?b: A) :- PartialEq[T = A], ?a = ?b
  rule guarded() :- eqG(pt(1, 2), pt(1, 9))
  rule apart() :- pt(1, 2) = pt(2, 2)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let holds = |kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str| {
        let goal = crate::common::query_pattern_term(kb, pattern);
        let got = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
        match got.as_slice() {
            [] => Some(false),
            [one] if one.is_definite() => Some(true),
            _ => None,
        }
    };
    for (pattern, want) in [
        ("sm910.eq.goal()", true),
        ("sm910.eq.infix()", true),
        ("sm910.eq.guarded()", true),
        ("sm910.eq.apart()", false),
        ("anthill.prelude.PartialEq.eq(sm910.eq.Pt.pt(1, 2), sm910.eq.Pt.pt(1, 9))", true),
    ] {
        assert_eq!(holds(&mut kb, pattern), Some(want), "`{pattern}`");
    }
}

/// `eq(a, b, ?r)` and `neq(a, b, ?r)` bind `?r` to the verdict, as `gt(a, b, ?r)` does; they
/// answered with `?r` free (`eq(3, 4, ?r)` too). Fails with the column out of `sem_eq_core`.
#[test]
fn equality_reads_its_result_column() {
    let src = r#"namespace sm910.col
  import anthill.prelude.{Int64, Bool, PartialEq}
  rule same(?r) :- PartialEq.eq(3, 4, ?r)
  rule self(?r) :- PartialEq.eq(3, 3, ?r)
  rule apart(?r) :- PartialEq.neq(3, 4, ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    for (relation, want) in [("same", false), ("self", true), ("apart", true)] {
        let rows = crate::common::query_unary(&mut kb, &format!("sm910.col.{relation}"));
        assert!(
            matches!(rows.as_slice(), [(Value::Bool(b), true)] if *b == want),
            "`{relation}` binds `?r` to {want}; got {rows:?}"
        );
    }
}

/// A comparison at a type the clause leaves open, with no dictionary of `PartialOrd` declared,
/// has no typed caller: it loads, owing the clause nothing, and its goal is read at the type
/// its values carry when it runs (decided with the user 2026-11-08) — `Float`, `Int64` and
/// `String` here, a delay while unbound — as the resolver's built-in comparison was. So does
/// one at the `T` of a sort that requires nothing. Fails with `no_typed_caller` off in
/// `check_apply_call`: `related` and `Scope.p` are refused "a rule takes no dictionary it
/// does not declare".
#[test]
fn an_untyped_comparison_runs_at_the_type_its_values_carry() {
    let src = r#"namespace sm910.untyped
  import anthill.prelude.PartialOrd.{gte, gt}
  import anthill.prelude.PartialEq.{eq}
  rule related(?a, ?b) :- gte(?a, ?b)
  rule chain(?x, ?y, ?z) :- eq(?x, ?y), gt(?y, ?z)
  sort Scope
    sort T = ?
    rule p(?a: T) :- gte(?a, ?a)
  end
  rule floats() :- related(5.0, 1.0)
  rule ints() :- related(1, 5)
  rule strings() :- related("b", "a")
  rule linked() :- chain(2, 2, 1)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    for (pattern, want) in [
        ("sm910.untyped.floats()", Some(true)),
        ("sm910.untyped.ints()", Some(false)),
        ("sm910.untyped.strings()", Some(true)),
        ("sm910.untyped.linked()", Some(true)),
        ("sm910.untyped.related(?x, 3)", None),
    ] {
        let goal = crate::common::query_pattern_term(&mut kb, pattern);
        let got = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
        let verdict = match got.as_slice() {
            [] => Some(false),
            [one] if one.is_definite() => Some(true),
            [_] => None,
            _ => panic!("`{pattern}`: {} rows", got.len()),
        };
        assert_eq!(verdict, want, "`{pattern}`");
    }
}
