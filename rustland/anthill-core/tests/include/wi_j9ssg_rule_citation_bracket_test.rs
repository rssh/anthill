//! WI-20261104-J9SSG — proposal 060.1, stage 1: A CITATION'S BRACKET READS WHAT THE RULE
//! DECLARES (§2) — an operation body's and a rule-body goal's — and what a declared
//! requirement supplies (§1).
//!
//! A rule declares its type parameters and requirements with the head's introducer, `rule
//! cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], …`, and a citation's bracket binds them as a
//! call's binds an operation's: `cmp[A = Int64](1, 5)`, `cmp[WeakOrd = down](x, y)`. What a
//! declared requirement supplies: a call at the clause's type parameter reads the guard's
//! dictionary however the parameter reached its argument, and a goal of a rule that declares the
//! same requirement at the caller's parameter passes the caller's own — at every turn of a
//! recursion. A relation has one parameter list (§8.4), and a parameter takes several
//! requirements, as an operation's does (§8.5).
//!
//! BACK-OUT, measured one axis at a time (each a temporary switch in one build, removed):
//!  * [B] a rule's bracket refused as on a callee with no type-parameter list — every bracket
//!    row fails to load, and the refusal rows give that refusal instead of their own;
//!  * [P] the selection not pinned where the guard's read is routed — a citation under two
//!    names is refused as naming neither, and a witness at the caller's parameter loads;
//!  * [D] a goal handing its callee a forward slot where the caller declares the requirement —
//!    the rows through `outer` answer `-1`, the recursion rows `0`;
//!  * [G] a call at a declared parameter reached through a column's type taking a read of its
//!    own — the recursion rows answer `0`;
//!  * [L] no check of one parameter list per relation — its two refusals load;
//!  * [U] no refusal of an introducer no column names — its row loads;
//!  * [R] a rule-body goal's bracket not routed — its witness rows read `Int64`'s own, and the
//!    refusals its routing raises load;
//!  * [M] the bracket left on the goal its marker wraps — the goal matches no clause;
//!  * [O] no refusal of the clause's own type parameter in a goal's bracket — an unresolved
//!    name instead;
//!  * [S] a second guard at one parameter refused, as before §8.5 — its row's load fails;
//!  * [Q] two guards of one instance both covering a call refused — `p2` refused;
//!  * [K] one bracket slot per spec, however many guards state it — the bracket on `p2` loads.
//!
//! The citation with no bracket, the bracket on a rule with no introducer, and the clauses
//! that declare one list or none pass under every axis: the controls.

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

  rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)
  rule plain(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)
"#;

const EFFECTS: &str = "effects {Error, Error[EmptyStream]}";

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

/// `ops` as nullary operations of `ns`, each `name = expr` answering an `Int64`, and each
/// called: `(name, answer)`.
fn answers(ns: &str, rules: &str, ops: &[(&str, &str)]) -> Vec<(String, i64)> {
    let body: String = ops
        .iter()
        .map(|(name, expr)| format!("  operation {name}() -> Int64 {EFFECTS} = {expr}\n"))
        .collect();
    let mut interp = crate::common::interp_for(&program(ns, &format!("{rules}{body}")));
    ops.iter()
        .map(|(name, _)| (name.to_string(), int(&mut interp, ns, name)))
        .collect()
}

fn expect(got: &[(String, i64)], want: &[(&str, i64)]) {
    let got: Vec<(&str, i64)> = got.iter().map(|(n, v)| (n.as_str(), *v)).collect();
    assert_eq!(got, want);
}

/// THE PROPOSAL'S PROGRAM (§2). The bracket binds the parameter by its name and by its
/// position, and the requirement by its spec's name — a witness, or a requirement of the
/// citing operation. FAILS under [B] (refused, no type-parameter list) and [P] (the citations
/// under two names refused as naming neither). `direct`, a citation with no bracket, answers
/// `4` under every axis.
#[test]
fn a_citations_bracket_binds_what_the_rule_declares() {
    let ns = "j9ssg.bracket";
    let rules = format!(
        "  operation two[A](x: A, y: A, d: Bool) -> Int64 {EFFECTS}\n    \
         requires up: WeakOrd[T = A], down: WeakOrd[T = A] =\n    \
         if d then cmp[WeakOrd = down](x, y).head.c else cmp[WeakOrd = up](x, y).head.c\n  \
         operation via[A](x: A, y: A) -> Int64 {EFFECTS} requires WeakOrd[T = A] = cmp(x, y).head.c\n"
    );
    let got = answers(
        ns,
        &rules,
        &[
            ("byName", "cmp[A = Int64](1, 5).head.c"),
            ("byPosition", "cmp[Int64](1, 5).head.c"),
            ("viaDesc", "cmp[A = Int64, WeakOrd = Descending](1, 5).head.c"),
            ("viaWitnessOnly", "cmp[WeakOrd = Descending](1, 5).head.c"),
            ("viaDown", "two[A = Int64, up = Ascending, down = Descending](1, 5, true)"),
            ("viaUp", "two[A = Int64, up = Ascending, down = Descending](1, 5, false)"),
            ("direct", "via[A = Int64, WeakOrd = Descending](1, 5)"),
        ],
    );
    expect(
        &got,
        &[
            ("byName", -1),
            ("byPosition", -1),
            ("viaDesc", 4),
            ("viaWitnessOnly", 4),
            ("viaDown", 4),
            ("viaUp", -4),
            ("direct", 4),
        ],
    );
}

/// The program with one operation `t` citing `expr`, and the load errors it gives.
fn refusals_of(ns: &str, expr: &str) -> Vec<String> {
    crate::common::load_errors_of(&program(
        ns,
        &format!("  operation t() -> Int64 {EFFECTS} = {expr}.head.c\n"),
    ))
}

fn assert_one_refusal(errs: &[String], text: &str, case: &str) {
    assert_eq!(errs.len(), 1, "{case}: {errs:?}");
    assert!(errs[0].contains(text), "{case}: expected `{text}` in {errs:?}");
}

/// A bracket entry that names nothing the rule declares is refused as on an operation, and
/// so is one the arguments contradict or a witness that does not provide the requirement at
/// the citation's type. FAILS under [B] — every row gives the no-type-parameter-list refusal —
/// and under [P], where the witness at the caller's parameter loads. The bracket on `plain`,
/// which declares nothing, is refused so under every axis — the control.
#[test]
fn a_bracket_entry_the_rule_does_not_declare_or_admit_is_refused() {
    let ns = "j9ssg.refused";
    for (expr, text) in [
        ("cmp[B = Int64](1, 5)", "unknown type-param 'B'"),
        ("cmp[Eq = Descending](1, 5)", "unknown type-param 'Eq'"),
        ("cmp[Int64, Int64](1, 5)", "the callee is over-applied"),
        ("cmp[A = Int64, A = Int64](1, 5)", "bound twice in one bracket"),
        ("cmp[A = String](1, 5)", "argument binding column `a` has an incompatible type"),
        ("cmp[WeakOrd = Descending](\"a\", \"b\")", "but not at the bindings this call"),
    ] {
        assert_one_refusal(&refusals_of(ns, expr), text, expr);
    }
    assert_one_refusal(
        &refusals_of(ns, "plain[A = Int64](1, 5)"),
        "a callee with no type-parameter list",
        "CONTROL: a rule with no introducer",
    );
    // At the caller's own parameter, a witness that provides the spec only at `Int64`.
    let errs = crate::common::load_errors_of(&program(
        ns,
        &format!(
            "  operation g[A](x: A, y: A) -> Int64 {EFFECTS} requires WeakOrd[T = A] =\n    \
             cmp[WeakOrd = Ascending](x, y).head.c\n"
        ),
    ));
    assert_one_refusal(&errs, "but not at the bindings this call", "a witness at the caller's parameter");
}

/// §8.3's refusal, where two requirements of the citing operation answer the citation, names
/// the bracket that chooses one where the rule declares the requirement, and the declaration
/// where it does not. The refusal's text, so it passes under every axis.
#[test]
fn two_names_at_a_citation_name_the_bracket_that_chooses() {
    let ns = "j9ssg.two";
    let two = |rule: &str| {
        format!(
            "  operation g2[A](x: A, y: A) -> Int64 {EFFECTS}\n    \
             requires up: WeakOrd[T = A], down: WeakOrd[T = A] = {rule}(x, y).head.c\n"
        )
    };
    let errs = crate::common::load_errors_of(&program(ns, &two("cmp")));
    assert_one_refusal(&errs, "write `cmp[WeakOrd = up](…)` or `cmp[WeakOrd = down](…)`", "a declaring rule");
    let errs = crate::common::load_errors_of(&program(ns, &two("plain")));
    assert_one_refusal(
        &errs,
        "declare it on `plain` with the head's introducer and its guard",
        "a rule that declares nothing",
    );
}

/// A GOAL AT THE CALLER'S INSTANCE PASSES THE CALLER'S REQUIREMENT (§1): `outer` declares what
/// `cmp` does, so its goal hands `cmp` the dictionary `outer` holds — the one its citation's
/// bracket selected. FAILS under [D] (`-1` for both bracket rows), [B] and [P] (refused, as in
/// the rows above). `held`, an operation
/// holding one requirement and citing `outer` with no bracket, answers `4` under every axis:
/// before, the goal's forward slot passed the same dictionary there.
#[test]
fn a_bracket_reaches_the_declared_rule_a_goal_calls() {
    let ns = "j9ssg.outer";
    let rules = format!(
        "  rule outer[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], cmp(?a, ?b, ?c)\n  \
         operation two[A](x: A, y: A) -> Int64 {EFFECTS}\n    \
         requires up: WeakOrd[T = A], down: WeakOrd[T = A] = outer[WeakOrd = down](x, y).head.c\n  \
         operation one[A](x: A, y: A) -> Int64 {EFFECTS} requires WeakOrd[T = A] = outer(x, y).head.c\n"
    );
    let got = answers(
        ns,
        &rules,
        &[
            ("viaDown", "two[A = Int64, up = Ascending, down = Descending](1, 5)"),
            ("viaWitness", "outer[A = Int64, WeakOrd = Descending](1, 5).head.c"),
            ("held", "one[A = Int64, WeakOrd = Descending](1, 5)"),
        ],
    );
    expect(&got, &[("viaDown", 4), ("viaWitness", 4), ("held", 4)]);
}

/// A RECURSION PASSES ITS DECLARED REQUIREMENT AT EVERY TURN (§1, the proposal's programs):
/// each clause that compares declares `[E]` and `WeakOrd[T = E]`, its `compare` reads that
/// guard though `?h` is an `E` only through `?l: List[T = E]`, and each goal hands the next
/// clause the guard's dictionary. `evenS`/`oddS` call each other, `skipN`/`chkN` too, and
/// `triA` → `triB` → `triC` → `triA` is a cycle of three. FAILS under [D] and under [G]: every
/// row `0`, as before this ticket — the clauses below the top compared with `Int64`'s own
/// order. The `Ascending` rows answer `0` under every axis, by design: the list is not
/// ascending.
#[test]
fn a_recursion_passes_its_declared_requirement_at_every_turn() {
    let ns = "j9ssg.rec";
    let rules = format!(
        "  rule evenS(?l) :- ?l <=> nil()\n  \
         rule evenS[E](?l: List[T = E]) :- WeakOrd[T = E], ?l <=> cons(?h, ?t),\n      \
         ?t <=> cons(?h2, ?r), WeakOrd.compare(?h, ?h2, ?c), Int64.lte(?c, 0), oddS(?t)\n  \
         rule oddS(?l) :- ?l <=> cons(?h, nil())\n  \
         rule oddS[E](?l: List[T = E]) :- WeakOrd[T = E], ?l <=> cons(?h, ?t),\n      \
         ?t <=> cons(?h2, ?r), WeakOrd.compare(?h, ?h2, ?c), Int64.lte(?c, 0), evenS(?t)\n  \
         operation isEven[A](l: List[T = A]) -> Int64 {EFFECTS} requires WeakOrd[T = A] =\n    \
         if evenS(l).isEmpty() then 0 else 1\n  \
         rule skipN[E](?l: List[T = E]) :- WeakOrd[T = E], ?l <=> cons(?h, ?t), chkN(?t)\n  \
         rule skipN(?l) :- ?l <=> nil()\n  \
         rule chkN[E](?l: List[T = E]) :- WeakOrd[T = E], ?l <=> cons(?h, ?t), ?t <=> cons(?h2, ?r),\n      \
         WeakOrd.compare(?h, ?h2, ?c), Int64.lte(?c, 0), skipN(?t)\n  \
         rule chkN(?l) :- ?l <=> nil()\n  \
         operation isSkip[A](l: List[T = A]) -> Int64 {EFFECTS} requires WeakOrd[T = A] =\n    \
         if skipN(l).isEmpty() then 0 else 1\n  \
         rule triA[E](?l: List[T = E]) :- WeakOrd[T = E], triB(?l)\n  \
         rule triB[E](?l: List[T = E]) :- WeakOrd[T = E], triC(?l)\n  \
         rule triC(?l) :- ?l <=> nil()\n  \
         rule triC(?l) :- ?l <=> cons(?h, nil())\n  \
         rule triC[E](?l: List[T = E]) :- WeakOrd[T = E], ?l <=> cons(?h, ?t), ?t <=> cons(?h2, ?r),\n      \
         WeakOrd.compare(?h, ?h2, ?c), Int64.lte(?c, 0), triA(?t)\n  \
         operation isTri[A](l: List[T = A]) -> Int64 {EFFECTS} requires WeakOrd[T = A] =\n    \
         if triA(l).isEmpty() then 0 else 1\n"
    );
    let at = |op: &str, witness: &str, list: &str| format!("{op}[A = Int64, WeakOrd = {witness}]({list})");
    let got = answers(
        ns,
        &rules,
        &[
            ("evenD", &at("isEven", "Descending", "[5, 3, 1, 0]")),
            ("evenA", &at("isEven", "Ascending", "[5, 3, 1, 0]")),
            ("skipD", &at("isSkip", "Descending", "[9, 5, 3]")),
            ("skipA", &at("isSkip", "Ascending", "[9, 5, 3]")),
            ("triDesc", &at("isTri", "Descending", "[5, 3, 1, 0]")),
            ("triAsc", &at("isTri", "Ascending", "[5, 3, 1, 0]")),
        ],
    );
    expect(
        &got,
        &[("evenD", 1), ("evenA", 0), ("skipD", 1), ("skipA", 0), ("triDesc", 1), ("triAsc", 0)],
    );
}

/// ONE PARAMETER LIST PER RELATION (§8.4): `p[E]` beside `p[F]`, and `q[A]` beside `q[A, B]`, are
/// refused at load, naming both lists. FAILS under [L]: both load. `s[E]` beside a clause that
/// declares none, and two clauses declaring `[E]` with different guards, load under every
/// axis — the controls.
#[test]
fn a_relation_has_one_parameter_list() {
    let ns = "j9ssg.list";
    let errs = crate::common::load_errors_of(&program(
        ns,
        "  rule p[E](?l: List[T = E]) :- WeakOrd[T = E], ?l <=> nil()\n  \
         rule p[F](?l: List[T = F]) :- WeakOrd[T = F], ?l <=> cons(?h, ?t)\n",
    ));
    assert_one_refusal(&errs, "declare different type-parameter lists, `[E]`", "[E] beside [F]");
    assert!(errs[0].contains("and `[F]`"), "{errs:?}");
    let errs = crate::common::load_errors_of(&program(
        ns,
        "  rule q[A](?x: A, ?y) :- WeakOrd[T = A], ?x <=> 1\n  \
         rule q[A, B](?x: A, ?y: B) :- WeakOrd[T = A], Eq[T = B], ?x <=> 1\n",
    ));
    assert_one_refusal(&errs, "`[A]`", "[A] beside [A, B]");
    assert!(errs[0].contains("and `[A, B]`"), "{errs:?}");
    let errs = crate::common::load_errors_of(&program(
        ns,
        "  rule s[E](?x: E) :- WeakOrd[T = E], ?x <=> 1\n  \
         rule s(?x) :- ?x <=> 2\n  \
         rule u[E](?x: E) :- WeakOrd[T = E], ?x <=> 1\n  \
         rule u[E](?x: E) :- Eq[T = E], ?x <=> 2\n",
    ));
    assert!(errs.is_empty(), "CONTROL: one list, or none: {errs:?}");
}

/// An introducer no head column's type names: its guard required a spec at a type no value
/// of the clause has, and was dropped, the call beside it reading `Int64`'s own. Refused.
/// FAILS under [U]: it loads.
#[test]
fn an_introducer_no_column_names_is_refused() {
    let errs = crate::common::load_errors_of(&program(
        "j9ssg.unused",
        "  rule p[A](?x, ?c) :- WeakOrd[T = A], WeakOrd.compare(?x, ?x, ?c)\n",
    ));
    assert_one_refusal(&errs, "rule type-variable `A` is the type of no head column", "unused introducer");
}

/// A RULE-BODY GOAL'S BRACKET READS WHAT ITS RELATION DECLARES (§2), as an operation body's
/// citation does: `cmp[A = Int64](1, 5, ?c)` is `Int64`'s own order, `cmp[WeakOrd =
/// Descending](1, 5, ?c)` the witness's — a provider chosen in a rule body, where before only
/// an operation could choose one. So in a negation and in a branch. FAILS under [R] (the
/// goal's bracket not routed): `viaDesc`, `viaWitness`, `neg` and `alt`'s second branch read
/// `Int64`'s own; under [M] (the bracket left on the goal the marker wraps): the goal matches
/// no clause, and the first row raises `empty_stream`. `plain`, a goal with no bracket,
/// answers `-1` under every axis.
#[test]
fn a_rule_body_goals_bracket_binds_what_the_rule_declares() {
    let ns = "j9ssg.goal";
    let rules = "  rule ints(?c) :- cmp[A = Int64](1, 5, ?c)\n  \
                 rule desc(?c) :- cmp[A = Int64, WeakOrd = Descending](1, 5, ?c)\n  \
                 rule witnessOnly(?c) :- cmp[WeakOrd = Descending](1, 5, ?c)\n  \
                 rule plainGoal(?c) :- cmp(1, 5, ?c)\n  \
                 rule neg(?c) :- ?c <=> 4, not(cmp[WeakOrd = Descending](1, 5, ?c))\n  \
                 rule negOwn(?c) :- ?c <=> 4, not(cmp[A = Int64](1, 5, ?c))\n  \
                 rule alt(?c) :- cmp[A = Int64](1, 5, ?c) | cmp[WeakOrd = Descending](1, 5, ?c)\n";
    let got = answers(
        ns,
        rules,
        &[
            ("viaInts", "ints().head.c"),
            ("viaDesc", "desc().head.c"),
            ("viaWitness", "witnessOnly().head.c"),
            ("plain", "plainGoal().head.c"),
            ("negHolds", "if neg().isEmpty() then 0 else 1"),
            ("negOwnHolds", "if negOwn().isEmpty() then 0 else 1"),
            ("altFirst", "alt().head.c"),
            ("altAtDesc", "if alt(4).isEmpty() then 0 else 1"),
            ("altAtOwn", "if alt(-1).isEmpty() then 0 else 1"),
            ("altElsewhere", "if alt(0).isEmpty() then 0 else 1"),
        ],
    );
    expect(
        &got,
        &[
            ("viaInts", -1),
            ("viaDesc", 4),
            ("viaWitness", 4),
            ("plain", -1),
            ("negHolds", 0),
            ("negOwnHolds", 1),
            ("altFirst", -1),
            ("altAtDesc", 1),
            ("altAtOwn", 1),
            ("altElsewhere", 0),
        ],
    );
}

/// The rule-body goal's bracket refused where an operation body's would be — a key the
/// relation does not declare, an argument it contradicts, a witness that does not provide at
/// the goal's type, a relation that declares nothing — and where nothing reads it: a citation
/// in a value slot, and the clause's own type parameter as an entry (the goal's arguments
/// typed at it pass the clause's requirement). FAILS under [O] for the last, which is then
/// an unresolved name, and under [R] for the three the goal's routing raises — the key, the
/// argument, the witness — which then load.
#[test]
fn a_rule_body_goals_bracket_is_refused_where_nothing_reads_it() {
    let ns = "j9ssg.goalrefused";
    for (rule, text) in [
        ("rule g(?c) :- plain[A = Int64](1, 5, ?c)", "a callee with no type-parameter list"),
        ("rule g(?c) :- cmp[B = Int64](1, 5, ?c)", "unknown type-param 'B'"),
        ("rule g(?c) :- cmp[A = Int64](\"a\", \"b\", ?c)", "incompatible type at the goal's bracket"),
        ("rule g(?c) :- cmp[WeakOrd = Descending](\"a\", \"b\", ?c)", "but not at the bindings this call"),
        ("rule g(?r) :- ?r <=> cmp[A = Int64](1, 5)", "is read where the relation is a goal, and is not here"),
        (
            "rule g[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], cmp[A = A](?a, ?b, ?c)",
            "the clause's own type parameter `A` written in a goal's bracket is not read",
        ),
    ] {
        let errs = crate::common::load_errors_of(&program(ns, &format!("  {rule}\n")));
        assert_one_refusal(&errs, text, rule);
    }
}

/// SEVERAL REQUIREMENTS AT ONE TYPE PARAMETER (§8.5), as an operation's `requires`: two specs at
/// `A` each cover their own calls and a citation's bracket selects either, and one spec written
/// twice with no name is two requirements — the clause loads, a caller's dictionary reaches it,
/// and a bracket selecting by the spec's name is refused as naming two, the operation's refusal.
/// FAILS under [S] (a second guard refused, as before): the load fails. Under [Q] (two
/// guards of one instance both covering the call refused): `p2` is refused, "covered by
/// distinct carrier requirements". Under [K] (one bracket slot per spec): the bracket on `p2`
/// loads.
#[test]
fn several_requirements_at_one_parameter_are_an_operations() {
    let ns = "j9ssg.several";
    let rules = format!(
        "  rule p[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], Eq[T = A], WeakOrd.compare(?a, ?b, ?c)\n  \
         rule same[A](?a: A, ?b: A) :- WeakOrd[T = A], Eq[T = A], Eq.eq(?a, ?b, true)\n  \
         rule p2[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)\n  \
         operation both[A](x: A, y: A) -> Int64 {EFFECTS} requires WeakOrd[T = A], Eq[T = A] =\n    \
         p(x, y).head.c\n  \
         operation one[A](x: A, y: A) -> Int64 {EFFECTS} requires WeakOrd[T = A] = p2(x, y).head.c\n"
    );
    let got = answers(
        ns,
        &rules,
        &[
            ("own", "p(1, 5).head.c"),
            ("bracket", "p[A = Int64, WeakOrd = Descending](1, 5).head.c"),
            ("caller", "both[A = Int64, WeakOrd = Descending](1, 5)"),
            ("eqHolds", "if same(3, 3).isEmpty() then 0 else 1"),
            ("eqFails", "if same(3, 4).isEmpty() then 0 else 1"),
            ("twiceOwn", "p2(1, 5).head.c"),
            ("twiceCaller", "one[A = Int64, WeakOrd = Descending](1, 5)"),
        ],
    );
    expect(
        &got,
        &[
            ("own", -1),
            ("bracket", 4),
            ("caller", 4),
            ("eqHolds", 1),
            ("eqFails", 0),
            ("twiceOwn", -1),
            ("twiceCaller", 4),
        ],
    );
    let errs = crate::common::load_errors_of(&program(
        ns,
        &format!(
            "{rules}  operation t() -> Int64 {EFFECTS} = p2[WeakOrd = Descending](1, 5).head.c\n"
        ),
    ));
    assert_one_refusal(&errs, "names more than one requirement slot", "a spec's name over two slots");
}
