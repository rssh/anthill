//! WI-20261126-EZQGX — a qualified name that names nothing, written in a contract clause's
//! argument, is refused at load, as the same name in an operation body is:
//! `requires below(n, Spec.limm)`, where `Spec` declares no `limm`, is
//! "`….Spec.limm` names nothing: the sort `….Spec` declares no `limm`"
//! (`Loader::refuse_contract_clause_path_naming_nothing`, `LoadError::DottedNameNamesNothing`).
//!
//! It stayed the converter's chain `field_access(Spec, limm)`. Its selector is a member name,
//! which WI-20261126-78B4M's refusal of a bare name does not judge, and 78B4M's qualified
//! reading answers only a name that resolves. So on an operation no spec stands over it loaded
//! clean, and on an override it was refused only as strengthening the precondition (MEASURED,
//! the ticket's probes, on 74d52327c).
//!
//! What a dotted name in a contract clause can also be, and which must not be refused: a field
//! read on a value — a parameter, `result`, a const — a member a provision of the sort lends,
//! a member read through a requirement's name or a type parameter, a type alias's member, a
//! constructor's field, and a member a spec's provision converts to.
//!
//! BACK-OUT, measured on a binary of this file and 78B4M's (every row of both green as is), 13
//! rows here (each change made by hand, the binary run, the change undone):
//!
//!  * The refusal backed out (`refuse_contract_clause_path_naming_nothing` reporting nothing):
//!    7 RED — `a_member_a_sort_declares_nowhere_is_refused`, `a_member_a_namespace_declares_
//!    nowhere_is_refused`, `the_ensures_list_is_judged_too`, `an_override_is_refused_for_the_
//!    name`, `a_longer_path_is_refused_once_at_its_missing_segment`, `a_member_an_aliased_
//!    sort_declares_nowhere_is_refused` and `an_internal_member_is_refused_as_that_access`
//!    (each loads, the override refused only as a strengthening). GREEN either way, BY DESIGN, the controls,
//!    `a_first_segment_naming_nothing_is_refused_once`, and `a_comparison_over_it_is_refused_
//!    once`: a comparison's operand is typed as an operation body's projection (§5.4), which
//!    refused this name already, so the row pins that the two report it once.
//!  * A provision's lent member not exempt: RED is `a_member_a_provision_lends_loads` alone.
//!  * A type alias judged among its own members, not its sort's: RED are `an_alias_member_
//!    loads` (`CA.T` refused) and `a_member_an_aliased_sort_declares_nowhere_is_refused`
//!    (named through `CA`, not the sort).
//!  * Every type alias let through, as the first cut did (found by `/code-review`): RED is
//!    `a_member_an_aliased_sort_declares_nowhere_is_refused` alone.
//!  * A hidden whole name let through, as the first cut did (found by `/code-review`): RED is
//!    `an_internal_member_is_refused_as_that_access` alone.
//!  * Every prefix judged, not only one that resolves (a prefix with no answer reported at the
//!    outer node too): RED are `a_longer_path_is_refused_once_at_its_missing_segment` and
//!    `a_first_segment_naming_nothing_is_refused_once`, each reported twice.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `Spec`, holding the const `lim` and a const `origin` of an entity type; a namespace
/// `inner` holding the const `k`; and `below`, which holds of anything, so a precondition over
/// it is proved at a call whatever its arguments.
const PRELUDE: &str = r#"
  import anthill.prelude.{Int64}
  rule below(?a, ?b) :- true
  entity Pt(x: Int64)
  sort Spec
    const lim: Int64 = 5
    const origin: Pt = Pt(x: 0)
  end
  namespace inner
    const k: Int64 = 1
  end
"#;

/// A program in namespace `ns`: the prelude, then `body`.
fn program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{PRELUDE}{body}\nend\n")
}

/// `ns`'s program with one operation `h(n)` carrying `clauses`, which answers `n`.
fn with_op(ns: &str, clauses: &str) -> String {
    program(
        ns,
        &format!(
            r#"
  sort A
    entity mk
    operation h(n: Int64) -> Int64
{clauses}
      = n
  end
"#
        ),
    )
}

/// The program is refused, naming `tokens`, `count` refusals in all.
fn refused(ns: &str, src: &str, tokens: &[&str], count: usize) -> Vec<String> {
    let errs = load_errors_of(src);
    assert_refused_naming(&errs, tokens, ns);
    assert_eq!(errs.len(), count, "{ns}: {count} refusal(s), got: {errs:?}");
    errs
}

// ── (1) a member nothing declares is refused ──────────────────────────────

#[test]
fn a_member_a_sort_declares_nowhere_is_refused() {
    // THE TICKET'S ROW, on an operation no spec stands over. Located at the name.
    let errs = refused(
        "ezq.sort",
        &with_op("ezq.sort", "      requires below(n, Spec.limm)"),
        &["`ezq.sort.Spec.limm` names nothing: the sort `ezq.sort.Spec` declares no `limm`"],
        1,
    );
    // The fixture's line 17 (its first line is empty), the name at column 25.
    assert!(errs[0].starts_with("17:25:"), "located at the name, got: {}", errs[0]);
}

#[test]
fn a_member_a_namespace_declares_nowhere_is_refused() {
    refused(
        "ezq.ns",
        &with_op("ezq.ns", "      requires below(n, inner.kk)"),
        &["`ezq.ns.inner.kk` names nothing: the namespace `ezq.ns.inner` declares no `kk`"],
        1,
    );
}

#[test]
fn the_ensures_list_is_judged_too() {
    refused(
        "ezq.post",
        &with_op("ezq.post", "      ensures below(result, Spec.limm)"),
        &["`ezq.post.Spec.limm` names nothing"],
        1,
    );
}

#[test]
fn an_override_is_refused_for_the_name() {
    // THE TICKET'S OVERRIDE ROW: refused for the name, beside the strengthened precondition
    // its clause still is (no clause of the spec's restates a name that names nothing).
    let src = program(
        "ezq.over",
        r#"
  sort S
    sort T = ?
    operation f(s: T, n: Int64) -> Int64
      requires below(n, Spec.lim)
  end
  sort Impl
    entity mk
    provides S[T = Impl]
    operation f(s: Impl, n: Int64) -> Int64
      requires below(n, Spec.limm)
      = n
  end
"#,
    );
    refused(
        "ezq.over",
        &src,
        &["`ezq.over.Spec.limm` names nothing", "it strengthens the precondition"],
        2,
    );
}

#[test]
fn a_longer_path_is_refused_once_at_its_missing_segment() {
    // `Spec.nosuch.deep` is `Spec.nosuch` read `.deep`: the segment that is missing is named,
    // once.
    refused(
        "ezq.deep",
        &with_op("ezq.deep", "      requires below(n, Spec.nosuch.deep)"),
        &["`ezq.deep.Spec.nosuch` names nothing: the sort `ezq.deep.Spec` declares no `nosuch`"],
        1,
    );
}

#[test]
fn a_comparison_over_it_is_refused_once() {
    // A comparison is typed in the signature (§5.4); its operand is the same name, refused
    // once.
    refused(
        "ezq.cmp",
        &with_op("ezq.cmp", "      requires n = Spec.limm"),
        &["`ezq.cmp.Spec.limm` names nothing"],
        1,
    );
}

#[test]
fn a_first_segment_naming_nothing_is_refused_once() {
    // The root names nothing: the bare name's refusal (78B4M), not this one as well.
    refused(
        "ezq.root",
        &with_op("ezq.root", "      requires below(n, nosuchns.lim)"),
        &["names `nosuchns`, which resolves to nothing in the operation's scope"],
        1,
    );
}

#[test]
fn a_member_an_aliased_sort_declares_nowhere_is_refused() {
    // `CA` owns no members; its sort's are read, as an operation body reads them, and the
    // refusal names the sort.
    let src = program(
        "ezq.alias_typo",
        r#"
  import anthill.prelude.{String}
  sort P
    sort T = ?
    entity mkp(v: T)
  end
  sort CA = P[T = String]
  sort A
    entity mk
    operation h(n: Int64) -> Int64
      requires below(n, CA.Tt)
      = n
  end
"#,
    );
    refused(
        "ezq.alias_typo",
        &src,
        &["`ezq.alias_typo.P.Tt` names nothing: the sort `ezq.alias_typo.P` declares no `Tt`"],
        1,
    );
}

#[test]
fn an_internal_member_is_refused_as_that_access() {
    // `secret` is `Other`'s and hidden from `A`; the body refuses the same name the same way.
    let src = r#"
namespace ezq.hidden.lib
  import anthill.prelude.{Int64}
  sort Other
    internal const secret: Int64 = 1
  end
end
namespace ezq.hidden
  import anthill.prelude.{Int64}
  rule below(?a, ?b) :- true
  sort A
    entity mk
    operation h(n: Int64) -> Int64
      requires below(n, ezq.hidden.lib.Other.secret)
      = n
  end
end
"#;
    refused(
        "ezq.hidden",
        src,
        &["'ezq.hidden.lib.Other.secret' is internal to 'ezq.hidden.lib.Other'"],
        1,
    );
}

// ── (2) what is no path that names nothing loads ──────────────────────────

#[test]
fn a_field_read_on_a_value_loads_and_runs() {
    // A parameter's field, `result`'s, a const's, and the names that resolve.
    let src = program(
        "ezq.value",
        r#"
  sort A
    entity mk
    operation h(p: Pt, n: Int64) -> Pt
      requires below(p.x, Spec.origin.x), below(n, Spec.lim), below(n, inner.k)
      ensures below(result.x, p.x)
      = Pt(x: n + 6)
  end
  operation go() -> Int64 = A.h(Pt(x: 0), 1).x
"#,
    );
    assert_eq!(run_int64(&src, "ezq.value.go"), Ok(7));
}

#[test]
fn a_member_a_provision_lends_loads() {
    // `A` declares no `viaDefault`; its provision of `Mk` lends it, and an operation body reads
    // `A.viaDefault` as the dot on the sort.
    let src = program(
        "ezq.lent",
        r#"
  sort Mk
    sort C = ?
    operation e() -> C
    operation viaDefault() -> C = e()
  end
  sort A
    entity a(n: Int64)
    provides Mk[C = A]
    operation e() -> A = a(n: 1)
    operation h(n: Int64) -> Int64
      requires below(n, A.viaDefault)
      = n + 6
  end
  operation go() -> Int64 = A.h(1)
"#,
    );
    assert_eq!(run_int64(&src, "ezq.lent.go"), Ok(7));
}

#[test]
fn an_alias_member_loads() {
    // `CA.T` is `P`'s `T` read at the parameters `CA` fixes.
    let src = program(
        "ezq.alias",
        r#"
  import anthill.prelude.{String}
  sort P
    sort T = ?
    entity mkp(v: T)
  end
  sort CA = P[T = String]
  sort A
    entity mk
    operation h(n: Int64) -> Int64
      requires below(n, CA.T)
      = n + 6
  end
  operation go() -> Int64 = A.h(1)
"#,
    );
    assert_eq!(run_int64(&src, "ezq.alias.go"), Ok(7));
}

#[test]
fn members_read_through_a_requirement_a_constructor_or_a_conversion_load() {
    // `R.zero` through a requirement's name and `F.zero` through a type parameter, each read
    // through what it is bound to; `Colour.red.shade`, a constructor's field; `Numeric.add`,
    // the member a spec's provision converts to (it answers to its head's address).
    let src = program(
        "ezq.through",
        r#"
  import anthill.prelude.{Numeric}
  import anthill.prelude.algebra.{Ring}
  sort G
    sort F = ?
    requires R: Ring[F]
    entity g
    operation r(n: F) -> F
      requires below(n, R.zero)
      ensures below(result, F.zero)
      = n
  end
  sort Colour
    entity red(shade: Int64)
  end
  sort A
    entity mk
    operation h(n: Int64) -> Int64
      requires below(n, Colour.red.shade), below(n, Numeric.add)
      = n + 6
  end
  operation go() -> Int64 = A.h(1)
"#,
    );
    assert_eq!(run_int64(&src, "ezq.through.go"), Ok(7));
}

// ── (3) after EZQGX's delivery, fixed inline at the user's request ────────
//
// Two gaps its review named, both measured on 76196564c: a qualified name that names
// nothing in a GOAL slot of a contract clause (`requires Spec.limm` loaded — the goal check
// reads the chain's `field_access` functor, which is declared), and a compound in an
// argument whose functor names nothing (`requires n < nosuch(1)` loaded — a clause head and a
// rule body's data slot refuse it, a contract clause had no twin).
//
// BACK-OUT, measured on the same binary (36 rows, all green as is), 10 rows here:
//  * The path check gated on a data slot again: RED is `a_goal_path_naming_nothing_is_
//    refused` alone.
//  * The compound check backed out (`refuse_contract_clause_unknown_functor` reporting
//    nothing): RED are `an_unknown_compound_in_an_argument_is_refused`, `an_unknown_dotted_
//    compound_is_refused_as_a_path` and `an_unknown_bracket_head_is_refused`. GREEN either
//    way, BY DESIGN, the controls and `a_goal_compound_is_refused_once_by_the_goal_check`.
//  * The compound check reading the slot its children convert under, not its own: RED is
//    `a_goal_compound_is_refused_once_by_the_goal_check` alone (reported twice).
//  * A call through a binder or a requirement's name not exempt: RED is
//    `calls_through_a_binder_or_a_requirement_load` alone.
//  * A binder slot read as data: RED is `a_discharge_and_a_quantifier_are_judged_where_
//    they_hold_data` (`tuple` refused). A discharge's goal slots judged: the same row RED
//    (`Spec.hyp` refused twice).
//  * A minted node not exempt: RED are `written_constructions_and_calls_load_and_run`,
//    `calls_through_a_binder_or_a_requirement_load` and 78B4M's `a_lambdas_binder_is_not_
//    refused` — a list's, a tuple's and a lambda's markers declare nothing.

/// `ns`'s program with one operation `f(n, p)` carrying `clauses`, beside `Rel`'s operation
/// `twice` and rule `good`, a rule `ok`, and a sort `A` lending `Mk`'s `viaDefault`. No call
/// of `f`: a refused clause is a precondition no call proves, a refusal of its own
/// ([`with_op_and_call`] is the program that runs).
fn with_op_and_relations(ns: &str, clauses: &str) -> String {
    with_relations(ns, clauses, "")
}

/// [`with_op_and_relations`] with `go()`, which calls `f`.
fn with_op_and_call(ns: &str, clauses: &str) -> String {
    with_relations(ns, clauses, "  operation go() -> Int64 = A.f(1, Pt(x: 0))")
}

fn with_relations(ns: &str, clauses: &str, call: &str) -> String {
    program(
        ns,
        &format!(
            r#"
  rule ok(?a) :- true
  sort Rel
    rule good(?a) :- true
    operation twice(n: Int64) -> Int64 = n + n
  end
  sort Mk
    sort C = ?
    operation e() -> C
    operation viaDefault() -> C = e()
  end
  sort A
    entity mk(n: Int64)
    provides Mk[C = A]
    operation e() -> A = mk(n: 1)
    operation f(n: Int64, p: Pt) -> Int64
{clauses}
      = n + 6
  end
{call}
"#
        ),
    )
}

#[test]
fn a_goal_path_naming_nothing_is_refused() {
    for (ns, clause, tokens) in [
        ("ezq.g.req", "      requires Spec.limm", "`ezq.g.req.Spec.limm` names nothing"),
        ("ezq.g.ens", "      ensures inner.kk", "the namespace `ezq.g.ens.inner` declares no `kk`"),
        ("ezq.g.and", "      requires ok(n) & Spec.limm", "`ezq.g.and.Spec.limm` names nothing"),
        ("ezq.g.not", "      requires !(Spec.limm)", "`ezq.g.not.Spec.limm` names nothing"),
    ] {
        refused(ns, &with_op_and_relations(ns, clause), &[tokens], 1);
    }
}

#[test]
fn a_goal_path_that_names_something_loads() {
    // A relation cited by its qualified name, and a member a provision lends.
    for (ns, clause) in [
        ("ezq.g.rel", "      requires Rel.good"),
        ("ezq.g.lent", "      requires A.viaDefault"),
    ] {
        let errs = load_errors_of(&with_op_and_relations(ns, clause));
        assert!(errs.is_empty(), "{ns}: loads, got: {errs:?}");
    }
}

#[test]
fn an_unknown_compound_in_an_argument_is_refused() {
    for (ns, clause, list) in [
        ("ezq.c.lt", "      requires n < nosuch(1)", "requires"),
        ("ezq.c.arg", "      requires below(n, nosuch(1))", "requires"),
        ("ezq.c.ens", "      ensures below(result, nosuch(1))", "ensures"),
    ] {
        let named = format!("the `{list}` clause of operation `{ns}.A.f` names `nosuch`");
        refused(ns, &with_op_and_relations(ns, clause), &[&named, "resolves to nothing"], 1);
    }
}

#[test]
fn an_unknown_dotted_compound_is_refused_as_a_path() {
    // Named as the same name written without the parentheses is.
    for (ns, clause, tokens) in [
        ("ezq.d.sort", "      requires below(n, Spec.limm(1))", "the sort `ezq.d.sort.Spec` declares no `limm`"),
        ("ezq.d.ns", "      requires below(n, inner.kk(1))", "the namespace `ezq.d.ns.inner` declares no `kk`"),
        ("ezq.d.root", "      requires below(n, nosuchns.f(1))", "names `nosuchns`, which resolves to nothing"),
    ] {
        refused(ns, &with_op_and_relations(ns, clause), &[tokens], 1);
    }
}

#[test]
fn an_unknown_bracket_head_is_refused() {
    refused(
        "ezq.br",
        &with_op_and_relations("ezq.br", "      requires below(n, Fooo[T = Int64])"),
        &["names `Fooo`, which resolves to nothing"],
        1,
    );
}

#[test]
fn a_goal_compound_is_refused_once_by_the_goal_check() {
    // A goal is a proposition, and the goal check refuses one that names nothing.
    for (ns, clause) in [
        ("ezq.gc.top", "      requires nosuch(1)"),
        ("ezq.gc.not", "      requires !nosuch(1)"),
        ("ezq.gc.and", "      requires ok(n) & nosuch(1)"),
    ] {
        refused(ns, &with_op_and_relations(ns, clause), &["names `nosuch`, which is declared nowhere"], 1);
    }
}

#[test]
fn written_constructions_and_calls_load_and_run() {
    // A call of a declared operation, a construction, a lent member's call, a list, a tuple
    // and a lambda: what the converter MINTS for the literals declares nothing, and is no
    // name that names nothing.
    let src = with_op_and_call(
        "ezq.ok",
        "      requires below(n, Rel.twice(1)), below(n, Pt(x: 1)), below(n, A.viaDefault()), below(n, mk(n: 1))\n      \
         requires below(n, [1, 2]), below(n, (1, 2)), below(n, lambda (y: Int64) -> y + 1)",
    );
    assert_eq!(run_int64(&src, "ezq.ok.go"), Ok(7));
}

#[test]
fn calls_through_a_binder_or_a_requirement_load() {
    // `g(1)` calls the lambda's own parameter; `R.add(n, n)` the operation a requirement's
    // dictionary holds.
    let src = program(
        "ezq.bind",
        r#"
  import anthill.prelude.algebra.{Ring}
  rule known(?x, ?f) :- true
  sort G
    sort F = ?
    requires R: Ring[F]
    entity g
    operation r(n: F) -> F
      requires known(n, lambda (h: (Int64) -> Int64) -> h(1)), known(n, R.add(n, n))
      = n
  end
"#,
    );
    let errs = load_errors_of(&src);
    assert!(errs.is_empty(), "loads, got: {errs:?}");
}

#[test]
fn a_discharge_and_a_quantifier_are_judged_where_they_hold_data() {
    // A discharge's binder tuple and its hypotheses declare what they name, so the clause
    // loads (`(forall(?h), Spec.hyp -: Spec.hyp)` was refused twice for its hypothesis and
    // once for the binder tuple's `tuple`, found by `/code-review`); a data slot inside it is
    // judged, and a quantifier body's goal is.
    let src = |clause: &str| {
        program(
            "ezq.q",
            &format!(
                r#"
  import anthill.prelude.{{List}}
  sort A
    entity mk
    operation f(n: Int64, xs: List[T = Int64]) -> Int64
{clause}
      = n
  end
"#
            ),
        )
    };
    for clause in [
        "      requires (forall(?h), Spec.hyp -: Spec.hyp)",
        "      requires (forall(?h), hyp(?h) -: hyp(?h))",
        "      requires (forall ?x in xs: below(?x, Spec.lim))",
    ] {
        let errs = load_errors_of(&src(clause));
        assert!(errs.is_empty(), "`{clause}` loads, got: {errs:?}");
    }
    refused(
        "ezq.q",
        &src("      requires (forall(?h), hyp(?h) -: below(?h, Spec.limm))"),
        &["`ezq.q.Spec.limm` names nothing"],
        1,
    );
    refused(
        "ezq.q",
        &src("      requires (forall ?x in xs: Spec.limm)"),
        &["`ezq.q.Spec.limm` names nothing"],
        1,
    );
}
