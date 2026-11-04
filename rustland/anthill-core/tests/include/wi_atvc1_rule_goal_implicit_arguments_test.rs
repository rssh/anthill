//! WI-20261102-ATVC1 — RULE → RULE IMPLICIT ARGUMENTS (060-implementation §7.3, S7): a goal of
//! another rule receives its caller's requirement dictionaries, and a sort's bracket on a
//! rule-body goal is read.
//!
//! A clause whose goal calls a relation that takes dictionaries — a requirement read, or the
//! callee's own forward slots — hands the goal what the clause itself was handed for them: the
//! goal rides in a citation marker whose FORWARD slot is a parameter of the clause, routed by
//! whoever cites the clause as the callee's position would be routed were the citer to cite the
//! callee itself. A goal of the clause's own relation at the clause's own column types hands
//! on what the clause took; a bracketed goal hands its callee the bracket's instance, built at
//! load.
//!
//! BACK-OUT, measured one axis at a time (each a temporary switch in one build, removed):
//!  * [P] the pass off — no goal carries anything: every row through a rule answers the
//!    callee's own (`-1`), the recursion row `(0, 0)`, every bracket row reads all instances;
//!  * [F] forward slots routed as nothing — the rows through a non-recursive rule;
//!  * [R] a citation routing no forward slot — the same rows as [F];
//!  * [O] a recursive goal passing nothing — `a_recursive_goal_hands_on_what_its_clause_took`;
//!  * [B] a bracket's instance not built — the decision-B rows;
//!  * [M] the edge reading a goal's argument type alone, not met with its column's — the
//!    decision-B rows;
//!  * [C] a forwarded argument typed by the clause's stamps alone, not by the citation's column
//!    type — the connective rows (`|`, `not`), whose variables have no stamp;
//!  * [N] a forward slot nothing routed left unbound when its clause opens — the uncited `not`
//!    rows, which flounder;
//!  * [X] no refusal of an unread bracket — the two refusal rows.
//!
//! The direct citations, a goal at literals, a goal whose callee takes nothing and the
//! mutually recursive pair pass under every axis, by design: they are the controls and the
//! stated limit.

use anthill_core::eval::Value;

const ORD_PRELUDE: &str = r#"
  import anthill.prelude.{Int64, String, List, Bool, Error, EmptyStream, Relation, Ord, WeakOrd, PartialOrd, PartialEq, Eq}
  import anthill.prelude.List.{nil, cons}

  sort Ascending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end
  sort Descending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
  sort Util
    operation sign[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)
  end
  sort Pr[T]
    entity pr(a: T, b: T)
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{ORD_PRELUDE}\n{body}end\n")
}

/// An operation of `ns` returning an `Int64`; a trap fails the row at its own call.
fn int(interp: &mut anthill_core::eval::Interpreter, ns: &str, op: &str) -> i64 {
    match interp.call(&format!("{ns}.{op}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{op}: expected an Int64, got {other:?}"),
    }
}

/// `driver[A](x: A, y: A) requires WeakOrd[T = A] = <rule>(x, y).head.c`, and its two rivals'
/// calls at `(1, 5)`: `Descending` answers `4`, `Ascending` `-4`, `Int64`'s own `-1`.
fn cite_pair(op: &str, rule: &str) -> String {
    format!(
        "  operation {op}[A](x: A, y: A) -> Int64 effects {{Error, Error[EmptyStream]}}\n    \
         requires WeakOrd[T = A] = {rule}(x, y).head.c\n  \
         operation {op}D() -> Int64 effects {{Error, Error[EmptyStream]}} =\n    \
         {op}[A = Int64, WeakOrd = Descending](1, 5)\n  \
         operation {op}A() -> Int64 effects {{Error, Error[EmptyStream]}} =\n    \
         {op}[A = Int64, WeakOrd = Ascending](1, 5)\n"
    )
}

fn pair(interp: &mut anthill_core::eval::Interpreter, ns: &str, op: &str) -> (i64, i64) {
    (int(interp, ns, &format!("{op}D")), int(interp, ns, &format!("{op}A")))
}

/// THE TICKET'S PROGRAM. `outer` has no condition of its own and calls `cmp`, whose condition
/// is `compare`'s: cited through `outer`, `cmp` is handed the rival its caller chose, and so
/// through a second rule (`outer2`). Uncited, `outer` hands nothing and `cmp` derives
/// `Int64`'s own. FAILS under [P], [F] and [R]: `(-1, -1)` through `outer` and `outer2`. The
/// direct citation `(4, -4)` and the uncited `-1` pass under every axis — the controls.
#[test]
fn a_rule_goal_hands_its_callee_the_callers_dictionary() {
    let ns = "atvc1.ord";
    let body = format!(
        "  rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)\n  \
         rule outer(?a, ?b, ?c) :- cmp(?a, ?b, ?c)\n  \
         rule outer2(?a, ?b, ?c) :- outer(?a, ?b, ?c)\n{}{}{}  \
         operation plain() -> Int64 effects {{Error, Error[EmptyStream]}} = outer(1, 5).head.c\n",
        cite_pair("viaCmp", "cmp"),
        cite_pair("viaOuter", "outer"),
        cite_pair("viaOuter2", "outer2"),
    );
    let mut interp = crate::common::interp_for(&program(ns, &body));
    assert_eq!(pair(&mut interp, ns, "viaCmp"), (4, -4), "CONTROL: cited directly");
    assert_eq!(pair(&mut interp, ns, "viaOuter"), (4, -4), "through `outer`");
    assert_eq!(pair(&mut interp, ns, "viaOuter2"), (4, -4), "through `outer2` and `outer`");
    assert_eq!(int(&mut interp, ns, "plain"), -1, "CONTROL: uncited, `cmp` derives its own");
}

/// EVERY KIND OF READ A CALLEE TAKES, handed on through a rule: a WRITTEN `require`, the
/// SLOTS of an operation's own `requires` (`Util.sign`), and a read witnessed by a variable
/// that is no column (`?x` of `?p <=> pr(a: ?x, b: ?y)`), whose instance the callee's clause
/// typing gives from the column the goal binds. FAILS under [P], [F] and [R]: `(-1, -1)` each.
#[test]
fn every_kind_of_read_is_handed_on() {
    let ns = "atvc1.kinds";
    let body = format!(
        "  rule cmpW(?a, ?b, ?c) :- ?d = require[WeakOrd[T]], WeakOrd.compare(?a, ?b, ?c)\n  \
         rule outW(?a, ?b, ?c) :- cmpW(?a, ?b, ?c)\n  \
         rule cmpS(?a, ?b, ?c) :- Util.sign(?a, ?b, ?c)\n  \
         rule outS(?a, ?b, ?c) :- cmpS(?a, ?b, ?c)\n  \
         rule order(?p, ?c) :- ?p <=> pr(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)\n  \
         rule outO(?p, ?c) :- order(?p, ?c)\n{}{}  \
         operation viaO[A](p: Pr[T = A]) -> Int64 effects {{Error, Error[EmptyStream]}}\n    \
         requires WeakOrd[T = A] = outO(p).head.c\n  \
         operation viaOD() -> Int64 effects {{Error, Error[EmptyStream]}} =\n    \
         viaO[A = Int64, WeakOrd = Descending](Pr.pr(a: 1, b: 5))\n  \
         operation viaOA() -> Int64 effects {{Error, Error[EmptyStream]}} =\n    \
         viaO[A = Int64, WeakOrd = Ascending](Pr.pr(a: 1, b: 5))\n",
        cite_pair("viaW", "outW"),
        cite_pair("viaS", "outS"),
    );
    let mut interp = crate::common::interp_for(&program(ns, &body));
    assert_eq!(pair(&mut interp, ns, "viaW"), (4, -4), "a written `require`");
    assert_eq!(pair(&mut interp, ns, "viaS"), (4, -4), "an operation's own `requires`");
    assert_eq!(pair(&mut interp, ns, "viaO"), (4, -4), "a read witnessed by a body variable");
}

/// A GOAL IN A CONNECTIVE'S SLOT is handed on as a body goal is: a branch of `|`, a negand.
/// Its arguments are the clause's head variables, which the clause's typing stamps nowhere
/// else, so they are typed at the citation's column types, as a read's witness is. FAILS under
/// [P], [F], [R] and [C]: `ord` `(-1, -1)`, `notGreater` `(1, 1)`.
///
/// AND UNCITED, a negand whose clause's caller passed nothing is decided, alone or in a
/// connective: its forward slot is bound to `__unrouted` when the clause opens. FAILS under [N]:
/// `notGreater(1, 5)` and `notBoth(1, 5)` flounder.
#[test]
fn a_goal_in_a_connective_is_handed_on() {
    let ns = "atvc1.conn";
    let body = format!(
        "  rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)\n  \
         rule ord(?a, ?b, ?c) :- cmp(?a, ?b, ?c) | cmp(?b, ?a, ?c)\n  \
         rule notGreater(?a, ?b) :- not(cmp(?a, ?b, 4))\n  \
         rule notBoth(?a, ?b) :- not(cmp(?a, ?b, 4) & Int64.lt(?a, ?b))\n  \
         rule uncited(1) :- notGreater(1, 5), notBoth(1, 5)\n{}  \
         operation viaNot[A](x: A, y: A) -> Int64 effects {{Error}}\n    \
         requires WeakOrd[T = A] = notGreater(x, y).takeN(5).length()\n  \
         operation viaNotD() -> Int64 effects {{Error}} = viaNot[A = Int64, WeakOrd = Descending](1, 5)\n  \
         operation viaNotA() -> Int64 effects {{Error}} = viaNot[A = Int64, WeakOrd = Ascending](1, 5)\n",
        cite_pair("viaOrd", "ord"),
    );
    let src = program(ns, &body);
    let mut interp = crate::common::interp_for(&src);
    assert_eq!(pair(&mut interp, ns, "viaOrd"), (4, -4), "a branch of `|`");
    assert_eq!(
        pair(&mut interp, ns, "viaNot"),
        (0, 1),
        "a negand: `Descending` compares `(1, 5)` to 4, `Ascending` to -4",
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.uncited")),
        Some(1),
        "uncited: `Int64`'s own compares to -1, and the negand is decided",
    );
}

/// A RECURSIVE GOAL HANDS ON WHAT ITS CLAUSE TOOK, where it calls at the clause's own column
/// types: `sorted(?t)` with `?t` at the type of `?l`. FAILS under [P] and [O]: `(0, 0)` — the
/// top call compares through the caller's rival and every level below through `Int64`'s own.
///
/// STATED LIMIT, passes either way: a goal of ANOTHER relation in the same recursion hands on
/// nothing. `evenS` and `oddS` call each other, so neither's layout is final before the
/// other's; each derives `Int64`'s own below the top, and `[5, 3, 1, 0]` reads unsorted under
/// `Descending` — `(0, 0)` where handing the rival on answers `(1, 0)`.
#[test]
fn a_recursive_goal_hands_on_what_its_clause_took() {
    let ns = "atvc1.rec";
    let body = "  \
        rule sorted(?l) :- ?l <=> nil()\n  \
        rule sorted(?l) :- ?l <=> cons(?h, nil())\n  \
        rule sorted(?l) :- ?l <=> cons(?h, ?t), ?t <=> cons(?h2, ?r), WeakOrd.compare(?h, ?h2, ?c), \
             Int64.lte(?c, 0), sorted(?t)\n  \
        rule evenS(?l) :- ?l <=> nil()\n  \
        rule evenS(?l) :- ?l <=> cons(?h, ?t), ?t <=> cons(?h2, ?r), WeakOrd.compare(?h, ?h2, ?c), \
             Int64.lte(?c, 0), oddS(?t)\n  \
        rule oddS(?l) :- ?l <=> cons(?h, nil())\n  \
        rule oddS(?l) :- ?l <=> cons(?h, ?t), ?t <=> cons(?h2, ?r), WeakOrd.compare(?h, ?h2, ?c), \
             Int64.lte(?c, 0), evenS(?t)\n  \
        operation isSorted[A](l: List[T = A]) -> Int64 effects {Error} requires WeakOrd[T = A] =\n    \
          sorted(l).takeN(1).length()\n  \
        operation isEven[A](l: List[T = A]) -> Int64 effects {Error} requires WeakOrd[T = A] =\n    \
          evenS(l).takeN(1).length()\n  \
        operation sortedD() -> Int64 effects {Error} = isSorted[A = Int64, WeakOrd = Descending]([5, 3, 1])\n  \
        operation sortedA() -> Int64 effects {Error} = isSorted[A = Int64, WeakOrd = Ascending]([5, 3, 1])\n  \
        operation evenD() -> Int64 effects {Error} = isEven[A = Int64, WeakOrd = Descending]([5, 3, 1, 0])\n  \
        operation evenA() -> Int64 effects {Error} = isEven[A = Int64, WeakOrd = Ascending]([5, 3, 1, 0])\n";
    let mut interp = crate::common::interp_for(&program(ns, body));
    assert_eq!(pair(&mut interp, ns, "sorted"), (1, 0), "the rival reaches every level");
    assert_eq!(
        pair(&mut interp, ns, "even"),
        (0, 0),
        "STATED LIMIT: across a mutual recursion the rival stops at the top",
    );
}

/// A GOAL AT LITERALS is at an instance fixed where it is written: `cmp(1, 5, ?c)` compares
/// `Int64`s, whichever `WeakOrd[T = A]` the citer holds, as `WeakOrd.compare(1, 5)` in an
/// operation body that `requires WeakOrd[T = A]` would. CONTROL, passes under every axis.
#[test]
fn a_goal_at_literals_reads_its_own_instance() {
    let ns = "atvc1.lit";
    let body = "  \
        rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)\n  \
        rule atLit(?c) :- cmp(1, 5, ?c)\n  \
        operation viaLit[A](x: A) -> Int64 effects {Error, Error[EmptyStream]} requires WeakOrd[T = A] =\n    \
          atLit.head.c\n  \
        operation litD() -> Int64 effects {Error, Error[EmptyStream]} = viaLit[A = Int64, WeakOrd = Descending](1)\n";
    let mut interp = crate::common::interp_for(&program(ns, body));
    assert_eq!(int(&mut interp, ns, "litD"), -1);
}

const BRACKET: &str = r#"
namespace atvc1.br
  import anthill.prelude.{Int64, String, Map, Relation, Error}
  import anthill.reflect.SortDomain
  sort Colour
    entity red
    entity green
  end
  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- src(?x)
  end
  sort WI = Wrap[T = Int64]
  fact src(1)
  fact src("a")
  fact src(red)
"#;

fn bracket(rules: &str) -> String {
    format!("{BRACKET}{rules}end\n")
}

/// DECISION B — A SORT'S BRACKET ON A RULE-BODY GOAL IS READ: the goal hands its callee the
/// bracket's instance, so `Wrap[T = Int64].el(?x)` answers `1` alone over `src`'s `1`, `"a"`
/// and `red`, and `Wrap[T = Colour].el(?x)` `red` alone — in a negand too, and through the
/// spellings that are the same goal: an alias fixing the parameter (`WI.el`) and a dot on a
/// written type (`(Wrap[T = Int64]).el`). Each was refused at load from 2827691a, because a
/// rule goal passed its callee nothing. FAILS under [P], [B] and [M]: every instance answers.
/// The bare goal answers all three under every axis, and an operation's goal reads its own
/// bracket as it always did — the controls.
#[test]
fn a_bracket_on_a_rule_body_goal_is_read() {
    let mut kb = crate::common::load_kb_with(&bracket(
        "  rule atInt(?x) :- Wrap[T = Int64].el(?x)\n  \
         rule atColour(?x) :- Wrap[T = Colour].el(?x)\n  \
         rule negated(1) :- not(Wrap[T = Int64].el(\"a\"))\n  \
         rule alias(?x) :- WI.el(?x)\n  \
         rule dotted(?x) :- (Wrap[T = Int64]).el(?x)\n  \
         rule bare(?x) :- Wrap.el(?x)\n  \
         rule op(?m) :- Map[K = String, V = Int64].empty(?m)\n",
    ));
    let ints = |kb: &mut anthill_core::kb::KnowledgeBase, rel: &str| -> Vec<Option<i64>> {
        crate::common::definite_unary(kb, &format!("atvc1.br.{rel}"))
            .iter()
            .map(|v| crate::common::scalar_int(kb, v))
            .collect()
    };
    for rel in ["atInt", "alias", "dotted"] {
        assert_eq!(ints(&mut kb, rel), [Some(1)], "{rel}: the `Int64` instance alone");
    }
    let colour = crate::common::definite_unary(&mut kb, "atvc1.br.atColour");
    assert_eq!(colour.len(), 1, "the `Colour` instance alone: {colour:?}");
    assert_eq!(crate::common::constructor_qn(&kb, &colour[0]), "atvc1.br.Colour.red");
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "atvc1.br.negated"),
        Some(1),
        "`\"a\"` is no `Int64`, so the negand holds"
    );
    assert_eq!(
        crate::common::definite_unary(&mut kb, "atvc1.br.bare").len(),
        3,
        "CONTROL: the bare goal reads every instance"
    );
    assert_eq!(
        crate::common::definite_unary(&mut kb, "atvc1.br.op").len(),
        1,
        "CONTROL: an operation's goal reads its own bracket"
    );
}

/// WHERE NOTHING READS A BRACKET IT IS REFUSED: on a relation named as a VALUE in a rule
/// body, and on a goal of a relation with no clause of its own — `SortDomain[T =
/// Colour].fill(?x)`, a spec's rule. FAILS under [X]: both load. Each advised repair is run:
/// the value written as a goal (the row above), or cited from an operation body, which
/// answers `1`; and the domain as the sort's `domain` relation, which answers both colours.
#[test]
fn a_bracket_nothing_reads_is_refused_and_its_repairs_answer() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&bracket("  rule asValue(?v) :- ?v <=> Wrap[T = Int64].el\n")),
        &[
            "type bracket on `atvc1.br.Wrap.el` in a rule body is not read where the relation is no goal",
            "Write it as a goal",
        ],
        "a relation as a value",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&bracket("  rule filled(?x) :- SortDomain[T = Colour].fill(?x)\n")),
        &["`anthill.reflect.Fillable.fill` has no clause of its own", "`Colour.domain(?x)`"],
        "a spec's rule",
    );
    let mut interp = crate::common::interp_for(&bracket(
        "  operation cited() -> Int64 effects {Error} = Wrap[T = Int64].el.takeN(5).length()\n  \
         rule domain(?x) :- Colour.domain(?x)\n",
    ));
    assert_eq!(int(&mut interp, "atvc1.br", "cited"), 1, "cited from an operation body");
    let mut kb = crate::common::load_kb_with(&bracket("  rule domain(?x) :- Colour.domain(?x)\n"));
    assert_eq!(crate::common::definite_unary(&mut kb, "atvc1.br.domain").len(), 2);
}

/// A LATER LOAD THAT GIVES A CALLEE ANOTHER CLAUSE routes its callers' goals again: `cmp`'s
/// layout gains the new clause's read, `outer`'s marker is routed for it, and the citation is
/// handed on through `outer` to both clauses. The re-routed goal takes the forward slot it had
/// and mints one for the new clause's read, so `outer`'s frame grows by that one; FAILS with the
/// reuse backed out (by two: the old slot is left behind in the frame). And before the stale marker was routed again, a marker
/// one slot short of its callee's layout reached the resolver.
#[test]
fn a_later_load_routes_a_goal_again_for_its_callees_new_clause() {
    let ns = "atvc1.later";
    let body = format!(
        "  rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)\n  \
         rule outer(?a, ?b, ?c) :- cmp(?a, ?b, ?c)\n{}  \
         operation count[A](x: A, y: A) -> Int64 effects {{Error}}\n    \
         requires WeakOrd[T = A] = outer(x, y).takeN(5).length()\n  \
         operation countD() -> Int64 effects {{Error}} = count[A = Int64, WeakOrd = Descending](1, 5)\n",
        cite_pair("viaOuter", "outer"),
    );
    let mut kb = crate::common::load_kb_with(&program(ns, &body));
    let outer = kb.rule_id_by_qn(&format!("{ns}.outer")).expect("`outer` is loaded");
    let frame = kb.rule_globals(outer).len();
    let later = format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, WeakOrd}}\n  \
         rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?b, ?a, ?c)\nend\n"
    );
    crate::common::expect_loaded(crate::common::load_in_a_later_call(
        &mut kb,
        &later,
        Default::default(),
    ));
    assert_eq!(
        kb.rule_globals(outer).len(),
        frame + 1,
        "the re-routed goal reuses its forward slot and mints one for the new read",
    );
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp);
    assert_eq!(int(&mut interp, ns, "viaOuterD"), 4, "the first clause, through `Descending`");
    assert_eq!(int(&mut interp, ns, "countD"), 2, "both clauses answer");
}

/// AN OPERATION BODY CITES THROUGH AN ALIAS as the rule-body goal `WI.el(?x)` does: a relation
/// named through `sort WI = Wrap[T = Int64]` as the receiver of a further dot is cited at the
/// alias's parameters, as the whole name `WI.el` and the applied `WI.el()` are. FAILS on the tree
/// before (measured on 97973301): `WI.el.takeN(5)` was refused, "type parameter `T` of `Wrap` is
/// not determined at this citation". The bare `Wrap.el.takeN(5)` stays refused for it — the
/// control.
#[test]
fn an_operation_body_cites_through_an_alias_as_a_goal_does() {
    let mut interp = crate::common::interp_for(&bracket(
        "  operation viaAlias() -> Int64 effects {Error} = WI.el.takeN(5).length()\n  \
         operation viaAliasApplied() -> Int64 effects {Error} = WI.el().takeN(5).length()\n",
    ));
    assert_eq!(int(&mut interp, "atvc1.br", "viaAlias"), 1);
    assert_eq!(int(&mut interp, "atvc1.br", "viaAliasApplied"), 1);
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&bracket(
            "  operation bare() -> Int64 effects {Error} = Wrap.el.takeN(5).length()\n",
        )),
        &["is not determined at this citation of `atvc1.br.Wrap.el`"],
        "CONTROL: nothing fixes `T`",
    );
}
