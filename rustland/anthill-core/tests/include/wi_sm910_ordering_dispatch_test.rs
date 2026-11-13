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
//! index, and both families read their result column at three arguments; (5) an `eq` a
//! binding supplies is the call's member as an own member is (`resolve_at_goal`, decided
//! with the user 2026-11-08), so a recursive binding compares at any depth; (6) the `eq` of
//! a carrier that provides `Eq` is not entered on identical operands
//! (`dispatch_resolved_operation`), as §8.3 says, so a pinned call answers what the
//! resolver's semantic equality answers.
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
//!   `an_untyped_comparison_runs_at_the_type_its_values_carry` is refused;
//! - semantic equality answered from the provider's table again in `resolve_at_goal`:
//!   `a_binding_eq_is_the_calls_member` is undecided at the bridge's re-entry cap, and
//!   wi_tsys6's `a_circular_binding_runs_to_the_step_budget` is undecided instead;
//! - the law out of `dispatch_resolved_operation`:
//!   `identical_operands_of_a_lawful_carrier_are_equal` answers 0 for `own` and `bound`,
//!   and wi_7k84m's `identical_operands_of_a_lawful_binding_are_equal` and wi_tsys6's
//!   `a_type_providing_eq_keeps_reflexivity` fail.
//!
//! Measured 2026-11-08, one switch each, over the rows of this file, wi_d5wfq, wi1036,
//! wi879, wi1102, wi642, wi_ckd4j, wi_tsys6, wi_7k84m, wi625 and wi1092.
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
/// instance the call is at, as a call of a body-less spec operation does (proposal 073
/// §6.2): refused naming `PartialOrd[T = …]`. It named the body's `WeakOrd[T = A]` while a
/// call of a default at a type parameter was the default's own call; a caller holding that
/// one loads too, and answers as through `PartialOrd`. Fails with the caller's park kept
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
        &["missing `requires PartialOrd[T = …]` on `sm910.gen.none.bare`"],
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

/// Is `pattern` proved: `Some(true)` for one definite solution, `Some(false)` for none, `None`
/// while undecided.
fn holds(kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str) -> Option<bool> {
    let goal = crate::common::query_pattern_term(kb, pattern);
    let got = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
    match got.as_slice() {
        [] => Some(false),
        [one] if one.is_definite() => Some(true),
        _ => None,
    }
}

/// `Chain`'s `eq` is a binding, `chainEq`, which compares the rest of a chain with `eq` again.
const CHAIN: &str = r#"namespace sm910.chain
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}
  sort Chain
    entity link(n: Int64, next: Chain)
    entity stop(n: Int64)
  end
  operation stopEq(a: Int64, y: Chain) -> Bool =
    match y
      case stop(b) -> eq(a, b)
      case link(b, r) -> false
  operation linkEq(a: Int64, r: Chain, y: Chain) -> Bool =
    match y
      case stop(b) -> false
      case link(b, s) -> if eq(a, b) then eq(r, s) else false
  operation chainEq(x: Chain, y: Chain) -> Bool =
    match x
      case stop(a) -> stopEq(a, y)
      case link(a, r) -> linkEq(a, r, y)
  namespace Chain
    provides PartialEq[T = Chain, eq = chainEq]
  end
  operation build(k: Int64, tail: Int64) -> Chain =
    if Int64.lte(k, 0) then stop(tail) else link(k, build(Int64.sub(k, 1), tail))
  operation apart() -> Bool = eq(build(20, 1), build(20, 2))
  operation same() -> Bool = eq(build(40, 1), build(40, 1))
  rule apartGoal() :- eq(build(40, 1), build(40, 2))
  rule sameGoal() :- eq(build(40, 1), build(40, 1))
end
"#;

/// An `eq` a binding supplies is the call's member at load, as a carrier's own member is (decided
/// with the user 2026-11-08): a call of `eq` at `Chain` runs `chainEq`, and so does the call
/// inside it, so a chain compares to any depth in both bodies. Fails with the equality clause
/// back in `resolve_at_goal` (a call of `eq` keeping the provider's table row, which holds no
/// binding): each nested `eq` then goes through the builtin and the equality bridge, and at the
/// bridge's re-entry cap the four are undecided.
#[test]
fn a_binding_eq_is_the_calls_member() {
    let mut interp = crate::common::interp_for(CHAIN);
    for (entry, want) in [("apart", false), ("same", true)] {
        let got = interp.call(&format!("sm910.chain.{entry}"), &[]);
        assert!(
            matches!(got, Ok(Value::Bool(b)) if b == want),
            "{entry} answers {want}; got {got:?}"
        );
    }
    let mut kb = crate::common::load_kb_with(CHAIN);
    for (pattern, want) in [("sm910.chain.apartGoal()", false), ("sm910.chain.sameGoal()", true)] {
        assert_eq!(holds(&mut kb, pattern), Some(want), "`{pattern}`");
    }
}

/// Identical operands of a carrier that provides `Eq` are equal by the law `eq_refl`, whatever
/// its `eq` says (kernel-language §8.3), in both bodies and whether the `eq` is a member or a
/// binding: `Own` writes `eq = false` as its member, `Loop` binds `neverEq`. The resolver applied
/// the law before it read the pin; an operation body entered the pinned member, and `own()`
/// answered 0. Fails with the law out of `dispatch_resolved_operation`: `own()` and `bound()`
/// answer 0.
#[test]
fn identical_operands_of_a_lawful_carrier_are_equal() {
    let src = r#"namespace sm910.refl
  import anthill.prelude.{Int64, Bool, PartialEq, Eq}
  sort Own
    import anthill.prelude.{Int64, Bool, PartialEq, Eq}
    entity ow(v: Int64)
    provides PartialEq[Own]
    provides Eq[Own]
    operation eq(x: Own, y: Own) -> Bool = false
  end
  sort Loop
    entity lp(v: Int64)
  end
  operation neverEq(x: Loop, y: Loop) -> Bool = false
  namespace Loop
    provides PartialEq[T = Loop, eq = neverEq]
    provides Eq[T = Loop, eq = neverEq]
  end
  operation own() -> Int64 = if PartialEq.eq(ow(v: 1), ow(v: 1)) then 1 else 0
  operation bound() -> Int64 = if PartialEq.eq(lp(v: 1), lp(v: 1)) then 1 else 0
  operation ownApart() -> Int64 = if PartialEq.eq(ow(v: 1), ow(v: 2)) then 1 else 0
  rule ownGoal() :- PartialEq.eq(ow(v: 1), ow(v: 1))
  rule boundGoal() :- PartialEq.eq(lp(v: 1), lp(v: 1))
end
"#;
    for (entry, want) in [("own", 1), ("bound", 1), ("ownApart", 0)] {
        assert_eq!(
            crate::common::run_int64(src, &format!("sm910.refl.{entry}")),
            Ok(want),
            "{entry}"
        );
    }
    let mut kb = crate::common::load_kb_with(src);
    for pattern in ["sm910.refl.ownGoal()", "sm910.refl.boundGoal()"] {
        assert_eq!(holds(&mut kb, pattern), Some(true), "`{pattern}`");
    }
}

/// A generic operation bound as a lawful carrier's `eq` keeps the law at that carrier alone: it
/// is called at other types too, where `Eq` says nothing. `never[A]` answers `false` for every
/// pair; bound as `X`'s `eq` beside `provides Eq[T = X]`, `eq(xx(1), xx(1))` is `true` by the law,
/// and `never(1, 1)` at `Int64` is `false`, as its body says. Found by /code-review: with the law
/// keyed by the member alone (`EqLaw::AtItsCarriers` read as `Always`) `atInt()` answers 1;
/// with the generic member given no law (read as `Never`) `atX()` answers 0.
#[test]
fn a_generic_binding_keeps_the_law_at_its_carrier_alone() {
    let src = r#"namespace sm910.gen
  import anthill.prelude.{Int64, Bool, PartialEq, Eq}
  operation never[A](x: A, y: A) -> Bool = false
  sort X
    entity xx(n: Int64)
  end
  namespace X
    import anthill.prelude.{PartialEq, Eq}
    provides PartialEq[T = X, eq = never]
    provides Eq[T = X]
  end
  operation atInt() -> Int64 = if never(1, 1) then 1 else 0
  operation atX() -> Int64 = if PartialEq.eq(xx(1), xx(1)) then 1 else 0
  operation apartX() -> Int64 = if PartialEq.eq(xx(1), xx(2)) then 1 else 0
end
"#;
    for (entry, want) in [("atInt", 0), ("atX", 1), ("apartX", 0)] {
        assert_eq!(
            crate::common::run_int64(src, &format!("sm910.gen.{entry}")),
            Ok(want),
            "{entry}"
        );
    }
}
