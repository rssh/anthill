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
//!  * [D] a goal passing its callee nothing where the caller declares the requirement — the
//!    rows through `outer` answer `-1`, the recursion rows `0`;
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
//!  * [K] one bracket slot per spec, however many guards state it — the bracket on `p2` loads;
//!  * [W] a call through a named requirement not lowered — `up.compare` names nothing;
//!  * [Y] a bracket's named entries read as type parameters — `unknown type-param 'up'`;
//!  * [Z] no refusal of a goal two of the clause's named requirements answer — it loads.
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
  rule plain(?a, ?b, ?c) :- ?c <=> Int64.sub(?a, ?b)
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

/// A BRACKET ON A PAREN-LESS REFERENCE OF A DECLARING RULE IS REFUSED, as one alone on an
/// operation is (kernel-language §5.4; the user, 2026-11-05): in a `let`, before a field and
/// before a dot call, each once, naming the repair `cmpS[…]()`, which answers `4`. FAILS with
/// the dot receiver's refusal backed out (measured before it was added): the field and the
/// dot call each give two errors instead, "`cmpS` takes no type arguments: it is a declaration
/// of kind Goal" and "unknown functor … `cmpS.head`" / "`cmpS.takeN`". The `let` passes either
/// way.
#[test]
fn a_bracket_on_a_paren_less_reference_is_refused() {
    let ns = "j9ssg.bare";
    let rules = "  fact srcPair(1, 5)\n  \
                 rule cmpS[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], srcPair(?a, ?b), WeakOrd.compare(?a, ?b, ?c)\n";
    let said = "`cmpS[…]` is a bracket on an operation or a relation, which binds its type parameters and \
                is read only before a call's arguments, `cmpS[…](…)` — `cmpS[…]()` where none is written";
    for (case, body) in [
        ("let", "=\n    let r = cmpS[A = Int64, WeakOrd = Descending]\n    r.head.c"),
        ("field", "= cmpS[A = Int64, WeakOrd = Descending].head.c"),
        ("dot call", "= cmpS[A = Int64, WeakOrd = Descending].takeN(5).length()"),
    ] {
        let errs = crate::common::load_errors_of(&program(
            ns,
            &format!("{rules}  operation t() -> Int64 {EFFECTS} {body}\n"),
        ));
        assert_one_refusal(&errs, said, case);
    }
    expect(
        &answers(ns, rules, &[("repaired", "cmpS[A = Int64, WeakOrd = Descending]().head.c")]),
        &[("repaired", 4)],
    );
}

/// 060.1 §3 — A SPEC'S OWN RULE READS THE SPEC AT ITS OWN PARAMETER, as the spec's operations
/// do, and declares nothing: `le` in `sort Cmp2` calls `cmp2` at `T`, and a citation from an
/// operation holding `Cmp2[T = A]` hands it the caller's dictionary, `Up`'s `1` and `Down`'s
/// `0`; the spec's law `cmp2_refl` is written the same way. A citation at `T = Int64`, which
/// both `Up` and `Down` provide, is refused at load, naming both, as an operation's call
/// `Cmp2[T = Int64].cmp2(1, 5)` is. FAILS with the clause's sort read as no supplier of its own
/// spec: `le` is refused, "the clause declares none". FAILS with the citation's
/// unanswered route left to run time (measured before the refusal was added): it loads, and the
/// call raises.
#[test]
fn a_specs_own_rule_reads_the_spec_at_its_own_parameter() {
    let ns = "j9ssg.law";
    let spec = "  sort Cmp2\n    sort T = ?\n    operation cmp2(a: T, b: T) -> Int64\n    \
                rule le(?a: T, ?b: T) :- cmp2(?a, ?b, ?c), Int64.lte(?c, 0)\n    \
                constraint cmp2_refl: eq(cmp2(?a, ?a), 0) :- le(?a, ?a)\n  end\n  \
                sort Up\n    import anthill.prelude.Numeric.{sub}\n    provides Cmp2[T = Int64]\n    \
                operation cmp2(a: Int64, b: Int64) -> Int64 = sub(a, b)\n  end\n  \
                sort Down\n    import anthill.prelude.Numeric.{sub}\n    provides Cmp2[T = Int64]\n    \
                operation cmp2(a: Int64, b: Int64) -> Int64 = sub(b, a)\n  end\n  \
                import anthill.prelude.PartialEq.{eq}\n";
    let rules = format!(
        "{spec}  operation viaLaw[A](x: A, y: A) -> Int64 {EFFECTS} requires Cmp2[T = A] =\n    \
         Cmp2.le(x, y).takeN(1).length()\n"
    );
    expect(
        &answers(
            ns,
            &rules,
            &[
                ("up", "viaLaw[A = Int64, Cmp2 = Up](1, 5)"),
                ("down", "viaLaw[A = Int64, Cmp2 = Down](1, 5)"),
            ],
        ),
        &[("up", 1), ("down", 0)],
    );
    let errs = crate::common::load_errors_of(&program(
        ns,
        &format!("{spec}  operation tie() -> Int64 {EFFECTS} = Cmp2[T = Int64].le(1, 5).takeN(1).length()\n"),
    ));
    assert_one_refusal(
        &errs,
        "constructing `j9ssg.law.Cmp2[T = anthill.prelude.Int64]` is ambiguous among providers: j9ssg.law.Up, j9ssg.law.Down",
        "a citation two providers answer",
    );
}

/// §8.3's refusal, where two requirements of the citing operation answer the citation, names
/// the bracket that chooses one. A rule that would need the requirement without declaring it
/// is refused at its own clause (060.1 §1), so no citation of it reaches the refusal. The
/// refusal's text, so it passes under every axis.
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
    let errs = crate::common::load_errors_of(&program(
        ns,
        &format!("  rule needy(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)\n{}", two("needy")),
    ));
    assert_one_refusal(
        &errs,
        "a requirement of `WeakOrd` the clause declares",
        "a rule that declares nothing is refused at its clause",
    );
}

/// A GOAL AT THE CALLER'S INSTANCE PASSES THE CALLER'S REQUIREMENT (§1): `outer` declares what
/// `cmp` does, so its goal hands `cmp` the dictionary `outer` holds — the one its citation's
/// bracket selected, and `held`, an operation holding one requirement and citing `outer` with
/// no bracket, the one it holds. FAILS under [D] (`-1` for all three), [B] and [P] (refused, as
/// in the rows above).
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

/// `require WeakOrd[A]` IS THE GUARD `WeakOrd[A]` (§8.6): one requirement, written with the
/// keyword, positional or named, alone or beside another at the parameter. A `require` that
/// names no type parameter the head introduces is refused, where the guard written so loaded
/// and answered nothing; so is the keyword
/// anywhere but a rule's own body (a head, a constraint, an operation's `requires`), where
/// it parsed as a syntax error before the keyword existed. FAILS with the grammar's
/// `require_goal` backed out: no rule with the keyword parses. Under [N] (no refusal of a
/// `require` that folds into no guard): `g` and `h` load.
#[test]
fn require_with_the_keyword_is_the_guard() {
    let ns = "j9ssg.require";
    let rules = format!(
        "  rule rc[A](?a: A, ?b: A, ?c) :- require WeakOrd[A], WeakOrd.compare(?a, ?b, ?c)\n  \
         rule rcNamed[A](?a: A, ?b: A, ?c) :- require WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)\n  \
         rule rcTwo[A](?a: A, ?b: A, ?c) :- require WeakOrd[T = A], require Eq[T = A],\n      \
         WeakOrd.compare(?a, ?b, ?c)\n  \
         operation via[A](x: A, y: A) -> Int64 {EFFECTS} requires WeakOrd[T = A] = rc(x, y).head.c\n"
    );
    let got = answers(
        ns,
        &rules,
        &[
            ("viaDesc", "via[A = Int64, WeakOrd = Descending](1, 5)"),
            ("viaAsc", "via[A = Int64, WeakOrd = Ascending](1, 5)"),
            ("named", "rcNamed[A = Int64, WeakOrd = Descending](1, 5).head.c"),
            ("two", "rcTwo[A = Int64, WeakOrd = Descending](1, 5).head.c"),
        ],
    );
    expect(&got, &[("viaDesc", 4), ("viaAsc", -4), ("named", 4), ("two", 4)]);
    for (rule, text) in [
        (
            "rule g(?a, ?b, ?c) :- require WeakOrd[T = Int64], WeakOrd.compare(?a, ?b, ?c)",
            "and this one names none",
        ),
        ("rule h(?x) :- require(?x)", "and this one names none"),
        // Read only as a goal of a rule's own body: the grammar admits the keyword wherever a
        // goal list stands, and elsewhere its term would stand alone — as a head, a
        // constraint's goal, an operation's `requires` line.
        ("rule require(?x) :- ?x <=> 1", "is read only as a goal of a rule's body"),
        ("constraint c: false :- require WeakOrd[T = Int64]", "is read only as a goal of a rule's body"),
        (
            "operation f[A](x: A) -> Int64 requires require WeakOrd[T = A] = 1",
            "is read only as a goal of a rule's body",
        ),
    ] {
        let errs = crate::common::load_errors_of(&program(ns, &format!("  {rule}\n")));
        assert_one_refusal(&errs, text, rule);
    }
}

/// A REQUIREMENT UNDER A NAME (§8.6), `require up: WeakOrd[T = A]`: the body calls through it,
/// `up.compare(…)`, reading that dictionary and no other, and a citation's bracket binds it by
/// its name, `both[up = u, down = d](…)`, a witness or a requirement of the citing operation.
/// Two names at one type are two dictionaries; one name beside an unnamed line of its instance
/// is one requirement. Refused as an operation's would be: a call that names neither of two
/// names, a goal that two names answer, one name written twice, an unnamed line beside two
/// names, a member the spec does not declare, a name that also names something in scope (as an
/// introducer's is), and a bracket keyed by the spec's name over a named requirement (`unknown
/// type-param`, the operation's refusal). A call through a name reads its dictionary in a value
/// slot and under `not` as at a goal. FAILS under [W] (a call
/// through a name not lowered): `up.compare` names nothing; under [Y] (the bracket's named
/// entries read as type parameters): every bracketed row is refused, `unknown type-param 'up'`;
/// under [Z] (no refusal of a goal two names answer): its row loads, `up`'s taken.
#[test]
fn a_requirement_under_a_name_is_called_and_bound_by_it() {
    let ns = "j9ssg.named";
    let rules = format!(
        "  import anthill.prelude.Numeric.{{add, mul}}\n  \
         rule cmpN[A](?a: A, ?b: A, ?c) :- require up: WeakOrd[T = A], up.compare(?a, ?b, ?c)\n  \
         rule both[A](?a: A, ?b: A, ?c) :- require up: WeakOrd[T = A], require down: WeakOrd[T = A],\n      \
         up.compare(?a, ?b, ?u), down.compare(?a, ?b, ?d), ?c <=> add(mul(?u, 100), ?d)\n  \
         rule one[A](?a: A, ?b: A, ?c, ?d) :- require up: WeakOrd[T = A], WeakOrd[T = A],\n      \
         up.compare(?a, ?b, ?c), WeakOrd.compare(?a, ?b, ?d)\n  \
         rule inValue[A](?a: A, ?b: A, ?c) :- require up: WeakOrd[T = A], ?c <=> up.compare(?a, ?b)\n  \
         rule inNot[A](?a: A, ?b: A) :- require up: WeakOrd[T = A], not(up.compare(?a, ?b, 0))\n  \
         operation via[A](x: A, y: A) -> Int64 {EFFECTS} requires WeakOrd[T = A] = cmpN(x, y).head.c\n  \
         operation pass[A](x: A, y: A) -> Int64 {EFFECTS}\n    \
         requires u: WeakOrd[T = A], d: WeakOrd[T = A] = both[up = u, down = d](x, y).head.c\n"
    );
    let got = answers(
        ns,
        &rules,
        &[
            ("own", "cmpN(1, 5).head.c"),
            ("viaDesc", "via[A = Int64, WeakOrd = Descending](1, 5)"),
            ("viaAsc", "via[A = Int64, WeakOrd = Ascending](1, 5)"),
            ("passed", "pass[A = Int64, u = Ascending, d = Descending](1, 5)"),
            ("witnesses", "both[A = Int64, up = Descending, down = Ascending](1, 5).head.c"),
            ("oneNamed", "one[A = Int64, up = Descending](1, 5).head.c"),
            ("oneUnnamed", "one[A = Int64, up = Descending](1, 5).head.d"),
            ("valueSlot", "inValue[A = Int64, up = Descending](1, 5).head.c"),
            ("notHolds", "if inNot[A = Int64, up = Descending](1, 5).isEmpty() then 0 else 1"),
            ("notFails", "if inNot[A = Int64, up = Descending](3, 3).isEmpty() then 0 else 1"),
        ],
    );
    expect(
        &got,
        &[
            ("own", -1),
            ("viaDesc", 4),
            ("viaAsc", -4),
            ("passed", -396),
            ("witnesses", 396),
            ("oneNamed", 4),
            ("oneUnnamed", 4),
            ("valueSlot", 4),
            ("notHolds", 1),
            ("notFails", 0),
        ],
    );
    for (decl, text) in [
        (
            "rule g[A](?a: A, ?b: A, ?c) :- require up: WeakOrd[T = A], require down: WeakOrd[T = A],\n      \
             WeakOrd.compare(?a, ?b, ?c)",
            "write `up.compare(…)` or `down.compare(…)`",
        ),
        (
            "rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)\n  \
             rule g[A](?a: A, ?b: A, ?c) :- require up: WeakOrd[T = A], require down: WeakOrd[T = A],\n      \
             cmp(?a, ?b, ?c)",
            "the goal needs a requirement two of the clause's hold, `up` and `down`",
        ),
        (
            "rule g[A](?a: A, ?b: A, ?c) :- require up: WeakOrd[T = A], require up: WeakOrd[T = A],\n      \
             up.compare(?a, ?b, ?c)",
            "two requirements are written under the name `up`",
        ),
        (
            "rule g[A](?a: A, ?b: A, ?c) :- require up: WeakOrd[T = A], require down: WeakOrd[T = A],\n      \
             WeakOrd[T = A], up.compare(?a, ?b, ?c)",
            "an unnamed requirement stands beside 2 named ones",
        ),
        (
            "rule g[A](?a: A, ?b: A, ?c) :- require up: WeakOrd[T = A], up.nope(?a, ?b, ?c)",
            "declares no operation `nope`",
        ),
        (
            "sort up\n    operation compare(a: Int64, b: Int64, c: Int64) -> Bool = true\n  end\n  \
             rule g[A](?a: A, ?b: A, ?c) :- require up: WeakOrd[T = A], up.compare(?a, ?b, ?c)",
            "the requirement name `up`",
        ),
        (
            "rule g[A](?a: A, ?b: A, ?c) :- require up: WeakOrd[T = A], up.compare(?a, ?b, ?c)\n  \
             operation t() -> Int64 effects {Error, Error[EmptyStream]} = g[WeakOrd = Descending](1, 5).head.c",
            "unknown type-param 'WeakOrd'",
        ),
    ] {
        let errs = crate::common::load_errors_of(&program(ns, &format!("  {decl}\n")));
        assert_one_refusal(&errs, text, decl);
    }
}

/// `require[X]`, `?d = require[X]` AND `requires(X)` ARE NO LONGER WRITTEN (§5): each is
/// refused where it stands, once — a goal, a nested goal (a negand's conjunct, a branch of
/// `|`), with a space before the bracket, a constraint's goal, an operation's `requires`
/// list — naming the introducer's guard, the `require` keyword and the named form to write
/// instead, which the other rows of this file run. MEASURED on d39bd428: each loaded but
/// the nested `require[X]` (refused, "legal only as a bare rule-body goal") and the
/// constraint (refused by the typer, "expected a body call to one of `PartialEq`'s
/// operations"). A first cut refused `requires(X)` at a goal's top only, and `… |
/// requires(…)` loaded.
#[test]
fn the_removed_requirement_spellings_are_refused() {
    for (decl, written) in [
        (
            "rule a(?a, ?b, ?c) :- require[WeakOrd[T]], WeakOrd.compare(?a, ?b, ?c)",
            "`require[WeakOrd[T]]`",
        ),
        (
            "rule b(?a, ?b, ?c) :- ?d = require[WeakOrd[T]], WeakOrd.compare(?a, ?b, ?c)",
            "`?d = require[WeakOrd[T]]`",
        ),
        ("rule c(?x, ?y) :- requires(PartialEq[T]), PartialEq.eq(?x, ?y)", "`requires(PartialEq[T])`"),
        ("rule d(?x) :- ?x <=> 1, not(?x <=> 2 & require[WeakOrd[T]])", "`require[WeakOrd[T]]`"),
        (
            "rule e(?a, ?b, ?c) :- require [WeakOrd[T]], WeakOrd.compare(?a, ?b, ?c)",
            "`require [WeakOrd[T]]`",
        ),
        ("rule g(?x) :- ?x <=> 1 | requires(PartialEq[T = Int64])", "`requires(PartialEq[T = Int64])`"),
        ("constraint k: false :- requires(PartialEq[T = Int64])", "`requires(PartialEq[T = Int64])`"),
        (
            "operation f(x: Int64) -> Int64 requires requires(PartialEq[T = Int64]) = 1",
            "`requires(PartialEq[T = Int64])`",
        ),
    ] {
        let errs = crate::common::parse_errs(&program("j9ssg.removed", &format!("  {decl}\n")));
        assert_one_refusal(&errs, &format!("{written} is no longer written"), decl);
        assert!(
            errs[0].contains("`rule r[A](?x: A, …) :- Spec[T = A], …`")
                && errs[0].contains("`require Spec[T = A]`")
                && errs[0].contains("`require s: Spec[T = A]` and `s.op(…)`"),
            "{decl}: the repair names the guard, the keyword and the named form: {errs:?}"
        );
    }
}

/// The kernel's dictionary read written by a name — its address, its qualified name, an
/// import — is the removed form by another spelling, refused at load wherever it stands: a
/// rule body, a constraint's, an operation's. MEASURED on d39bd428: each rule loaded, the
/// typer rewriting the read as it rewrote `requires(X)`. With the loader's refusal backed out,
/// every row fails: the rules and the constraint load, and the operation is refused by the
/// typer alone, as an unknown functor. A program's own relation named `find_dictionary` is
/// not the kernel's and answers, the control.
#[test]
fn the_kernel_read_written_by_its_name_is_refused() {
    let program = |imports: &str, decl: &str| {
        format!(
            r#"namespace j9ssg.kread
  import anthill.prelude.Int64
{imports}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
{decl}
end
"#
        )
    };
    let address = "..anthill.kernel.find_dictionary";
    for (imports, decl, name) in [
        (
            "",
            "  rule a(?x, ?r) :- ..anthill.kernel.find_dictionary(Desc[T = Leaf]), \
             Desc.describe(?x, ?r)",
            address,
        ),
        (
            "",
            "  rule b(?x, ?r) :- ..anthill.kernel.find_dictionary(Desc[T = Leaf], out: ?d), \
             Desc.describe(?x, ?r)",
            address,
        ),
        (
            "",
            "  rule c(?x, ?r) :- anthill.kernel.find_dictionary(Desc[T = Leaf], out: ?d), \
             Desc.describe(?x, ?r)",
            "anthill.kernel.find_dictionary",
        ),
        (
            "  import anthill.kernel.find_dictionary",
            "  rule d(?x, ?r) :- find_dictionary(Desc[T = Leaf]), Desc.describe(?x, ?r)",
            "find_dictionary",
        ),
        (
            "",
            "  constraint k: false :- ..anthill.kernel.find_dictionary(Desc[T = Leaf], out: ?d)",
            address,
        ),
        (
            "",
            "  operation o(x: Leaf) -> Int64 = \
             if ..anthill.kernel.find_dictionary(Desc[T = Leaf]) then 1 else 2",
            address,
        ),
    ] {
        let errs = crate::common::load_errors_of(&program(imports, decl));
        assert!(
            errs.iter().any(|e| e.contains(&format!("`{name}` is the kernel's dictionary read"))
                && e.contains("`rule r[A](?x: A, …) :- Spec[T = A], …`")),
            "{decl}: refused, naming the introducer's guard: {errs:?}"
        );
    }
    let mut kb = crate::common::load_kb_with(&program(
        "",
        "  rule find_dictionary(?x) :- ?x <=> 7\n  rule own(?x) :- find_dictionary(?x)",
    ));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "j9ssg.kread.own"),
        Some(7),
        "a program's own `find_dictionary` answers"
    );
}

/// A GUARD HOLDS ITS SPEC'S `requires` CHAIN (§1, as an operation's `requires` line does):
/// `rule woven[C](?ls: C, ?n) :- FiniteCollection[C = C], size(?ls, ?n)` supplies the
/// `Iterable[…]` that `FiniteCollection` itself requires, so each `Box`'s length answers —
/// under `not`, in a branch of `|`, reached through `<=>`, two guards at two parameters, an
/// effect row written as an element (`E = {}`), and cited from an operation body.
/// MEASURED on d39bd428: each `size` call refused ("a requirement suppliable at this call
/// site"), where `require[FiniteCollection[C]]` answered `woven`. `Iterable`'s own `isEmpty`
/// under the guard answered there too, and passes either way. The controls: a call at a
/// parameter the guard is not at, `size(?ms, ?n)` under `?ms: D`, and one at an argument
/// nothing types, `size(?z, ?n)`, stay refused. FAILS with the guards not held (the six
/// `size` calls refused), with the clause's type variables read as open in the demand (the
/// first control loads), and with an open carrier left out of it (the second loads). With an
/// effect row refused as an element, `wovenE` is refused ("names neither a sort nor one of
/// `FiniteCollection`'s own type parameters").
#[test]
fn a_guard_holds_its_specs_requires_chain() {
    let program = |decls: &str| {
        format!(
            r#"namespace j9ssg.chain
  import anthill.prelude.{{List, String, Bool, Int64, FiniteCollection, WeakOrd, Error, EmptyStream}}
  import anthill.prelude.FiniteCollection.{{size}}
  import anthill.prelude.Iterable.{{isEmpty}}
  sort Box
    entity Box(items: List[T = String])
  end
  fact Box(items: ["a", "b"])
  fact Box(items: [])
{decls}
end
"#
        )
    };
    let mut kb = crate::common::load_kb_with(&program(
        "  rule woven[C](?ls: C, ?n) :- FiniteCollection[C = C], size(?ls, ?n)
  rule wovenE[C](?ls: C, ?n) :- FiniteCollection[C = C, E = {}], size(?ls, ?n)
  rule neg[C](?ls: C) :- FiniteCollection[C = C], not(size(?ls, 0))
  rule br[C](?ls: C, ?n) :- FiniteCollection[C = C], (size(?ls, ?n) | ?n <=> 9)
  rule via[C](?ls: C, ?n) :- FiniteCollection[C = C], ?l <=> ?ls, size(?l, ?n)
  rule two[C, D](?a: C, ?b: D, ?n, ?m) :- FiniteCollection[C = C], FiniteCollection[C = D], \
         size(?a, ?n), size(?b, ?m)
  rule emp[C](?ls: C, ?b) :- FiniteCollection[C = C], isEmpty(?ls, ?b)
  rule a_woven(?n) :- Box(items: ?ls), woven(?ls, ?n)
  rule a_wovenE(?n) :- Box(items: ?ls), wovenE(?ls, ?n)
  rule a_neg(?k) :- Box(items: ?ls), neg(?ls), size(?ls, ?k)
  rule a_br(?n) :- br([\"a\", \"b\"], ?n)
  rule a_via(?n) :- Box(items: ?ls), via(?ls, ?n)
  rule a_two_n(?n) :- two([\"a\"], [\"b\", \"c\", \"d\"], ?n, ?m)
  rule a_two_m(?m) :- two([\"a\"], [\"b\", \"c\", \"d\"], ?n, ?m)
  rule a_emp(?k) :- Box(items: ?ls), emp(?ls, true), size(?ls, ?k)
  sort U
    operation cited() -> Int64 effects {Error, Error[EmptyStream]} = \
      woven([\"a\", \"b\", \"c\"]).head.n
  end",
    ));
    for (rule, want) in [
        ("a_woven", vec![0, 2]),
        ("a_wovenE", vec![0, 2]),
        ("a_neg", vec![2]),
        ("a_br", vec![2, 9]),
        ("a_via", vec![0, 2]),
        ("a_two_n", vec![1]),
        ("a_two_m", vec![3]),
        ("a_emp", vec![0]),
    ] {
        let mut got: Vec<i64> = crate::common::definite_unary(&mut kb, &format!("j9ssg.chain.{rule}"))
            .iter()
            .map(|v| match v {
                Value::Int(i) => *i,
                other => panic!("{rule}: expected an Int column, got {other:?}"),
            })
            .collect();
        got.sort_unstable();
        assert_eq!(got, want, "`{rule}`");
    }
    // Cited from an operation body, the clause answers as from a goal.
    let mut interp = crate::common::interp_for(&program(
        "  rule woven[C](?ls: C, ?n) :- FiniteCollection[C = C], size(?ls, ?n)
  sort U
    operation cited() -> Int64 effects {Error, Error[EmptyStream]} = \
      woven([\"a\", \"b\", \"c\"]).head.n
  end",
    ));
    match interp.call("j9ssg.chain.U.cited", &[]) {
        Ok(Value::Int(3)) => {}
        other => panic!("`cited`: expected 3, got {other:?}"),
    }
    for (decl, why) in [
        (
            "  rule other[C, D](?ls: C, ?ms: D, ?n) :- FiniteCollection[C = C], WeakOrd[T = D], \
             size(?ms, ?n)",
            "a call at `D` is not held by a guard at `C`",
        ),
        (
            "  rule untyped[C](?ls: C, ?z, ?n) :- FiniteCollection[C = C], size(?z, ?n)",
            "a call at an argument nothing types is not held by a guard at `C`",
        ),
    ] {
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&program(decl)),
            &["FiniteCollection.size", "Iterable"],
            why,
        );
    }
}

