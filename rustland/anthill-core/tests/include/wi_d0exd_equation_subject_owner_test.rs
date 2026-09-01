//! WI-20260821-D0EXD — AN EQUATION'S SUBJECT MAY NOT NAME ANOTHER SCOPE'S **PREDICATE**.
//!
//! §"A rule head functor is resolved, not declared" reaches every head shape, an
//! equation's subject included: a head whose functor RESOLVES is a clause of what it
//! resolves to. For an equation that reading is coherent only where what it lands on is a
//! thing equations DEFINE. A rule-introduced PREDICATE is not one — an equation's clauses
//! index under the `eq`/`unify` CONNECTIVE and never under its subject (WI-898), so the
//! equation never becomes a clause of the predicate; the subject merely points at it, and
//! the equation-defined operation the writing scope meant to name ceases to exist there.
//!
//! ── WHAT WAS MEASURED, two arms one token apart ──────────────────────────────
//!
//! ```text
//!   namespace qlib
//!     rule f(2)                        -- 061: a body-less rule DECLARES a predicate
//!     sort Rec { entity r(n: Int64)    rule f() <=> 1 [simp] }
//!   end
//!     -> qlib.Rec.f ABSENT. `Rec.f()` = "unknown functor"; `f()` under `import qlib.*`
//!        = Int(1) — the sort's operation MOVED to the namespace.
//!   the same file with the declaration renamed `rule other(2)`
//!     -> the exact mirror: qlib.Rec.f present, `Rec.f()` = Int(1).
//! ```
//!
//! Both loaded and nothing was reported, so a caller written against either name was
//! right in exactly one of two programs that differ by a rename elsewhere.
//!
//! ── WHY REFUSED RATHER THAN SPLIT ───────────────────────────────────────────
//!
//! The language already refuses this pair wherever neither side is minted before phase 2:
//! `zi { rule f(true) <=> 7 [simp] }` beside `zj { import zi.*  rule f(1) :- true }` is
//! `NameIntroducedAtTwoVisibleScopes`, because both heads introduce and phase 2 reads a
//! pre-mint table. A 061 DECLARATION is minted in pass 1, so it is the ONE shape reaching
//! phase 2 already denoting — a hole in that refusal rather than a different question.
//! [`a_predicate_head_and_an_equation_subject_are_refused_when_neither_denotes`] is that
//! control, and it passes with this change backed out: it is the design's evidence, not
//! this change's.
//!
//! ── AND SCOPED TO **ANOTHER** SCOPE'S PREDICATE ─────────────────────────────
//!
//! 845G7's own principle: the shadow itself is not the defect, INVENTING it is. Where the
//! predicate is declared in the scope the equation is written in, one author wrote both,
//! the name carries both roles, and it works — driven below, in one file and in two.
//!
//! ── THE BACK-OUTS, each naming the line, each RUN ────────────────────────────
//!
//! * **THE REFUSAL** — in `equation_subject_lands_on_predicate`, return an empty `Vec`
//!   before the loop. **7 rows fail**: six here
//!   ([`the_two_arms_agree_about_the_sorts_operation`],
//!   [`an_imported_predicate_declaration_does_not_take_the_equation_either`],
//!   [`an_ambiguous_name_is_refused_only_when_every_candidate_is_a_predicate`],
//!   [`a_labelled_rules_own_name_is_a_relation_too`],
//!   [`a_global_head_that_imported_the_namespace_is_refused`],
//!   [`one_absorbed_subject_is_one_message`]) and wi980's
//!   `an_equation_subject_is_a_party_to_the_collision_too`.
//! * **THE SCOPE GUARD** — drop the `s != head.scope` test so a same-scope relation is
//!   refused too. **4 rows fail**:
//!   [`a_predicate_declared_where_the_equation_is_written_is_not_refused`],
//!   [`the_two_prescribed_repairs_both_answer`] (its per-scope half),
//!   [`an_ambiguous_name_is_refused_only_when_every_candidate_is_a_predicate`] (its
//!   driven repair) and wi980's per-scope remedy arm.
//! * **THE OPERATION EXEMPTION** — in `subject_may_not_name`, drop the early return
//!   entirely, so a name that is both a relation and an `operation` is refused. **1 row
//!   fails**: [`a_name_that_is_also_an_operation_is_not_this_refusal`].
//! * **THE `EquationFunctor` FILTER** — in `subject_may_not_name`, move
//!   `EquationFunctor` from the sweep's filter into the `Operation` early return, so any
//!   symbol CARRYING it is exempt. **1 row fails**:
//!   [`a_relation_that_also_carries_equations_is_still_a_relation`].
//! * **THE MIXED-GROUP PRESCRIPTION** — in `scan_definitions_with_sources`, read
//!   `equation_elsewhere` with `.all(..)` in place of `.any(..)`, so only an
//!   all-equation group gets the corrected sentence. **2 rows fail**:
//!   [`a_mixed_collision_groups_prescribed_owner_answers`] and wi980's
//!   `an_equation_subject_is_a_party_to_the_collision_too`.
//! * **THE LABEL KIND** — in `subject_may_not_name`, ask `has_kind(Goal)` in place of the
//!   `DECLARABLE_BY_A_RULE` sweep. **1 row fails**:
//!   [`a_labelled_rules_own_name_is_a_relation_too`].
//! * **THE `<global>` TARGET EXCLUSION** — drop the `s != global` test. **1 row fails**:
//!   [`a_global_predicate_is_not_a_party_to_this_refusal`].
//! * **THE `<global>` DIRECTION** — add back the `head.scope == global` early return the
//!   first cut had. **1 row fails**:
//!   [`a_global_head_that_imported_the_namespace_is_refused`].
//! * **THE GROUPING** — report per head instead of per `(scope, name)`. **1 row fails**:
//!   [`one_absorbed_subject_is_one_message`].
//! * **THE AMBIGUITY QUESTION** — at the REPORTING site, set `ambiguous: scopes.len() >
//!   1` in place of the flag carried from the ladder. **1 row fails**:
//!   [`two_files_reaching_two_relations_is_not_an_ambiguity`]. Backing it out at the
//!   per-head site instead (`owners.len() > 1`) fells NOTHING and measures a different
//!   thing — one head resolves ambiguously exactly when it has several owners, so the
//!   proxy only diverges from the question after the group MERGES.
//! * **THE AMBIGUOUS READING** — take `vec![v[0]]` in place of every candidate, or refuse
//!   when ANY is a relation rather than every one. **1 row fails** either way, in
//!   opposite directions:
//!   [`an_ambiguous_name_is_refused_only_when_every_candidate_is_a_predicate`].
//! * **THE `equation_elsewhere` PRESCRIPTION** — in `scan_definitions_with_sources`, set
//!   the flag to `false` unconditionally. **1 row fails**: wi980's
//!   `an_equation_subject_is_a_party_to_the_collision_too`, whose first arm reads the
//!   corrected sentence.
//!
//! ── AND A KIND CENSUS OF THE FIXTURES IS NOT ONE OF THE POPULATION ──────────
//!
//! The guard's first cut asked `has_kind(Goal)`, chosen from a census that instrumented
//! the head pass over the whole suite and read the resolved symbol's kinds: `Operation`,
//! `Goal`, `EquationFunctor`, `Entity`, `Sort`, `Namespace`. It separated cleanly, and it
//! was still the wrong list — `SymbolKind::Rule`, a LABELLED rule's own name, appears in
//! `DECLARABLE_BY_A_RULE` beside the other two and no fixture in the corpus wrote a label
//! that another scope's equation could reach. The guard now asks that constant, so a
//! fourth mint kind cannot leave it behind. Found by `/code-review`.
//!
//! ── A ZERO-ROW BACK-OUT IS NOT A DEAD GUARD ─────────────────────────────────
//!
//! The `Operation` exemption was DELETED in an earlier cut of this change, on the
//! measurement that backing it out failed **zero** rows across the whole suite, plus the
//! reasoning that an operation's symbol never gains `Goal` in a program that LOADS. Both
//! halves were true and the conclusion was wrong: this pass runs on programs that DO NOT
//! load, and `rule f(2)` beside `operation f() -> Int64` is exactly such a program — one
//! symbol carrying both kinds, 061 refusing the body-less rule, and this refusal adding a
//! second error that told the author to declare the operation on the preceding line. The
//! zero rows measured the FIXTURES, not the shape. `/code-review` constructed it;
//! [`a_name_that_is_also_an_operation_is_not_this_refusal`] is now the row that reaches
//! it, and the back-out above fells it.
//!
//! ── WHAT IT DOES NOT REACH, measured rather than assumed ────────────────────
//!
//! The GUARDED equation spelling (`rule f(?a) = 5 :- g(?a)`, which keeps `=`) never
//! reaches this pass: its subject is not collected as a rule head at all, so it mints
//! nothing at the sort with OR without a same-named declaration outside — measured, both
//! arms agree and neither has `Rec.f`. That is a pre-existing silence of the same family
//! as the paren-less nullary head (§8.6), untouched here and neither widened nor closed.
//! `===` is refused before any of this on its own ground (it is the identity TEST).
//!
//! ── THE CONTROL EACH ROW CARRIES ────────────────────────────────────────────
//!
//! "It loads" passes through both readings of every fixture here, and so does "it is
//! refused" — two identical failures satisfy an equality assert and measure nothing. So
//! every arm that is meant to WORK drives the citation and asserts the value the equation
//! rewrites to, and every arm that is meant to be refused asserts the token that names
//! this refusal rather than the family.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

/// The `Int` a driven citation answered with. `eval::Value` carries no `PartialEq`.
fn int_value(v: Value) -> i64 {
    match v {
        Value::Int(i) => i,
        other => panic!("expected an Int, got {other:?}"),
    }
}

/// The errors from loading `batches` one after another into one KB — a STAGED load, which
/// a second `load_all` into a live KB is (each batch runs its own
/// `scan_definitions`). The only way to reach a target minted by an EARLIER scan, which is
/// where a name carrying two rule-introduced roles becomes reachable.
fn staged_load_errors(batches: &[&str]) -> Vec<String> {
    use anthill_core::kb::load::{self, NullResolver};
    let mut kb = crate::common::load_stdlib_kb();
    let mut errs = Vec::new();
    for b in batches {
        let parsed = anthill_core::parse::parse(b).expect("parse");
        let refs = vec![&parsed];
        if let Err(e) = load::load_all(&mut kb, &refs, &NullResolver) {
            errs.extend(e.iter().map(|x| x.to_string()));
        }
    }
    errs
}

/// Does `qn` name anything at all? The PREDICATE-IDENTITY half of every claim here: an
/// equation's subject owns no clauses either way, so a clause count cannot tell an
/// absorbed subject from a present one.
fn present(kb: &KnowledgeBase, qn: &str) -> bool {
    kb.try_resolve_symbol(qn).is_some()
}

/// The sort body both arms share, verbatim. The only difference between the arms is the
/// namespace-level line, which is not about the sort at all.
const REC: &str = "  sort Rec\n    entity r(n: Int64)\n    rule f() <=> 1 [simp]\n  end\nend\n";

/// The citation that makes the sort's operation observable — driven, so an arm cannot
/// pass by the name merely existing.
const CITE_REC: &str =
    "namespace qcall\n  import qlib.{Rec}\n  operation g() -> Int64 = Rec.f()\nend\n";

#[test]
fn the_two_arms_agree_about_the_sorts_operation() {
    // THE TICKET'S OWN FIXTURE. The clashing arm is refused NAMING BOTH SITES — the
    // scope losing the operation and the scope declaring the predicate — where before it
    // loaded and moved the operation with nothing said.
    let clash = format!("namespace qlib\n  rule f(2)\n{REC}");
    for want in [
        "the equation subject `f` names the RELATION `f` declared in 'qlib'",
        "`qlib.Rec.f` would not exist",
        "make `f` in 'qlib' an `operation f(…) -> R` INSTEAD of a relation",
    ] {
        crate::common::expect_load_errors(crate::common::try_load_kb_with(&clash), &[want]);
    }
    // AND THE CAUSE IS NOW REPORTED WHERE IT IS WRITTEN. The ticket's own complaint was
    // that the only diagnostic named the CALLER, in a file holding neither definition and
    // mentioning neither of the two that collided. With the citation present the load
    // still fails at the call — nothing can be resolved that was never minted — but the
    // FIRST error is the located cause, in the file that has both.
    let with_call = format!("{clash}{CITE_REC}");
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&with_call),
        &[
            "the equation subject `f` names the RELATION `f` declared in 'qlib'",
            "type mismatch in Rec.f.apply",
        ],
    );
    // THE CONTROL, one token away, and it must REACH the equation rather than merely
    // match: the whole defect is that the two arms disagreed, and two identical failures
    // would satisfy that as well as two identical successes.
    let renamed = format!("namespace qlib\n  rule other(2)\n{REC}");
    let kb = crate::common::load_kb_with(&renamed);
    assert!(present(&kb, "qlib.Rec.f"), "CONTROL: the sort keeps its operation");
    assert!(!present(&kb, "qlib.f"), "CONTROL: and the namespace has no `f`");
    let mut interp = crate::common::interp_for(&format!("{renamed}{CITE_REC}"));
    assert_eq!(
        int_value(interp.call("qcall.g", &[]).expect("the control's citation answers")),
        1,
        "CONTROL: `Rec.f()` rewrites through the sort's own equation"
    );
}

#[test]
fn the_two_prescribed_repairs_both_answer() {
    // A REFUSAL NEEDS A REPAIR THAT HAS BEEN RUN — 845G7's own /code-review found this
    // message class naming an owner that, followed, made the refused program load clean
    // and stay split. Both of this message's repairs are driven here, to the value the
    // sort's equation rewrites to.
    //
    // REPAIR 1 — declare what the equations DEFINE, IN PLACE OF the predicate. The
    // fixture is the message's own text: the body-less `rule f(2)` is REPLACED by
    // `operation f() -> Int64`, not joined by it. `/code-review` caught the earlier
    // wording, which read as "add an `operation` in 'qlib'" — followed literally that is
    // a second declaration of one name, which 061 refuses, so the message prescribed a
    // program the loader rejects while this row quietly measured a different one.
    let mut owner = crate::common::interp_for(
        "namespace qlib\n  operation f() -> Int64\n  sort Rec\n    entity r(n: Int64)\n    \
         rule f() <=> 1 [simp]\n  end\nend\n\
         namespace qcall\n  import qlib.{f}\n  operation g() -> Int64 = f()\nend\n",
    );
    assert_eq!(
        int_value(owner.call("qcall.g", &[]).expect("the operation owner answers")),
        1,
        "an `operation` in the predicate's scope collects the sort's equation"
    );
    // REPAIR 2 — say they are separate. A body-less `rule` in the equation's OWN scope
    // gives the subject something local to land on, and the sort keeps its operation.
    let mut per_scope = crate::common::interp_for(
        "namespace qlib\n  rule f(2)\n  sort Rec\n    entity r(n: Int64)\n    rule f()\n    \
         rule f() <=> 1 [simp]\n  end\nend\n\
         namespace qcall\n  import qlib.{Rec}\n  operation g() -> Int64 = Rec.f()\nend\n",
    );
    assert_eq!(
        int_value(per_scope.call("qcall.g", &[]).expect("the per-scope repair answers")),
        1,
        "a declaration in the equation's own scope keeps the operation AT the sort"
    );
}

#[test]
fn an_imported_predicate_declaration_does_not_take_the_equation_either() {
    // THE SAME DEFECT ONE COORDINATE OVER, and the reason the rule is stated over what a
    // name RESOLVES to rather than over enclosure: a wildcard import reaches a sibling
    // namespace's declaration exactly as a sort reaches its parent's. Measured before the
    // fix: `zb.f` was ABSENT and the equation defined `za`'s predicate.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[
            "namespace za\n  rule f(?x)\n  rule f(1) :- true\nend\n",
            "namespace zb\n  import za.*\n  rule f(true) <=> 7 [simp]\nend\n",
        ]),
        &["the equation subject `f` names the RELATION `f` declared in 'za'"],
    );
    // THE CONTROL — the imported predicate under another name, so nothing is reached and
    // `zb` mints its own subject. Without it the row above would be satisfied by refusing
    // any equation in a scope that imports anything.
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        "namespace za2\n  rule other(?x)\n  rule other(1) :- true\nend\n",
        "namespace zb2\n  import za2.*\n  rule f(true) <=> 7 [simp]\nend\n",
    ]));
    assert!(present(&kb, "zb2.f"), "CONTROL: the subject is minted where it is written");
}

#[test]
fn a_predicate_declared_where_the_equation_is_written_is_not_refused() {
    // THE SHADOW ITSELF IS NOT THE DEFECT; INVENTING IT IS (845G7). One author writing
    // both in one scope gets a name that carries both roles, and it WORKS — so the rule
    // is stated over ANOTHER scope's predicate, not over the kind alone.
    //
    // BOTH SPELLINGS OF "one scope": one file, and the namespace reopened in two. The
    // second is the row that says the guard asks about the SCOPE and not about adjacency
    // in the text.
    let one_file = crate::common::load_kb_with(
        "namespace zc\n  rule f(?x)\n  rule f(true) <=> 7 [simp]\nend\n",
    );
    assert!(present(&one_file, "zc.f"), "one scope, one file");
    let two_files = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        "namespace zd\n  rule f(?x)\nend\n",
        "namespace zd\n  rule f(true) <=> 7 [simp]\nend\n",
    ]));
    assert!(present(&two_files, "zd.f"), "one scope, two files");
    // AND IT ANSWERS. `present` alone would pass for a name that exists and rewrites
    // nothing, which is exactly what the defect produced at the other scope.
    let mut interp = crate::common::interp_for(
        "namespace ze\n  sort Rec\n    entity r(n: Int64)\n    rule f(?x)\n    \
         rule f(false) <=> 2 [simp]\n  end\nend\n\
         namespace zec\n  import ze.{Rec}\n  operation g() -> Int64 = Rec.f(false)\nend\n",
    );
    assert_eq!(
        int_value(interp.call("zec.g", &[]).expect("the same-scope pair answers")),
        2,
        "a subject landing on its OWN scope's declaration still rewrites"
    );
}

#[test]
fn an_operation_is_still_what_an_equation_defines() {
    // THE 516,224-SITE ARM of the census, and the one this refusal must not touch: an
    // equation subject naming an `operation` in an ENCLOSING scope is how the sort's law
    // becomes the namespace operation's defining equation. Same shape as the refused
    // fixture in every respect but the declaration's keyword.
    let mut interp = crate::common::interp_for(
        "namespace zf\n  operation f(b: Bool) -> Int64\n  rule f(true) <=> 1 [simp]\n  \
         sort Rec\n    entity r(n: Int64)\n    rule f(false) <=> 2 [simp]\n  end\nend\n\
         namespace zfc\n  import zf.{f}\n  operation g() -> Int64 = f(false)\nend\n",
    );
    assert_eq!(
        int_value(interp.call("zfc.g", &[]).expect("the operation answers")),
        2,
        "the SORT's equation defines the NAMESPACE's operation"
    );
    let kb = crate::common::load_kb_with(
        "namespace zg\n  operation f(b: Bool) -> Int64\n  rule f(true) <=> 1 [simp]\n  \
         sort Rec\n    entity r(n: Int64)\n    rule f(false) <=> 2 [simp]\n  end\nend\n",
    );
    assert!(
        !present(&kb, "zg.Rec.f"),
        "and the subject introduces nothing at the sort — it named the operation"
    );
}

#[test]
fn a_predicate_head_and_an_equation_subject_are_refused_when_neither_denotes() {
    // THE DESIGN'S CONTROL, and it passes with this whole change backed out. It is why
    // the fixture above is REFUSED rather than split: the language already refuses this
    // exact pair wherever both heads introduce, so letting the DECLARATION spelling load
    // silently would be one hole in one rule, not a second rule.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[
            "namespace zi\n  rule f(true) <=> 7 [simp]\nend\n",
            "namespace zj\n  import zi.*\n  rule f(1) :- true\nend\n",
        ]),
        &["the rule head `f` introduces that name at 2 scopes"],
    );
}

#[test]
fn a_declaration_still_collects_a_predicate_head_from_an_inner_scope() {
    // THE SPLIT IS BY HEAD KIND, NOT A RETREAT FROM JOINING. 061's own paragraph — "a
    // declaration is what joins scopes, and that is the point of it" — is untouched: a
    // PREDICATE head in a sort still resolves through its enclosing scope to the
    // declaration and becomes a clause of it. Driven on both the joined and the
    // unreachable value, since a `p` that exists but answers nothing would leave a
    // presence assert unchanged.
    let mut kb = crate::common::load_kb_with(
        "namespace zk\n  rule p(?x)\n  rule p(1) :- true\n  sort Rec\n    \
         entity r(n: Int64)\n    rule p(2) :- true\n  end\nend\n",
    );
    assert!(!present(&kb, "zk.Rec.p"), "the inner head introduced nothing");
    let sym = kb.try_resolve_symbol("zk.p").expect("the declaration");
    assert_eq!(kb.rules_by_functor(sym).len(), 2, "one predicate, both clauses");
    for (goal, want) in [("zk.p(1)", 1), ("zk.p(2)", 1), ("zk.p(9)", 0)] {
        let g = crate::common::query_pattern_term(&mut kb, goal);
        assert_eq!(
            kb.resolve(&[g], &anthill_core::kb::resolve::ResolveConfig::default()).len(),
            want,
            "{goal}"
        );
    }
}

#[test]
fn an_ambiguous_name_is_refused_only_when_every_candidate_is_a_predicate() {
    // AN AMBIGUOUS SUBJECT IS STILL A SUBJECT. `Ambiguous` counts as denoting — the
    // reference position reports the ambiguity and a mint would bury it — so it reaches
    // this refusal too, and the two readings of "what did it land on" separate here.
    //
    // EVERY CANDIDATE A PREDICATE: whichever the ambiguity resolves to, the equation
    // would define a predicate, so this is the same defect and is refused ALONGSIDE the
    // ambiguity report rather than instead of it.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[
            "namespace am1\n  rule f(?x)\nend\n",
            "namespace am2\n  rule f(?y)\nend\n",
            "namespace am3\n  import am1.*\n  import am2.*\n  rule f(true) <=> 7 [simp]\nend\n",
        ]),
        &[
            // BOTH candidates, not whichever the resolver sorted first — naming one sent
            // the author to fix it and meet the identical error pointing at the other
            // (found by `/code-review`).
            "names the RELATION `f` declared in 'am1', 'am2'",
            "ambiguous symbol 'f' in scope 'am3'",
        ],
    );
    // ONE CANDIDATE AN OPERATION: there is a reading under which the program is meant, so
    // this refusal stands down and only the ambiguity is reported. Without this arm,
    // refusing on ANY candidate would look identical to refusing on every one.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[
            "namespace an1\n  rule f(?x)\nend\n",
            "namespace an2\n  operation f(b: Bool) -> Int64\nend\n",
            "namespace an3\n  import an1.*\n  import an2.*\n  rule f(true) <=> 7 [simp]\nend\n",
        ]),
        &["ambiguous symbol 'f' in scope 'an3'"],
    );
    // AND THE REPAIR IT PRESCRIBES HERE IS A DIFFERENT ONE, because the ordinary one is
    // not a repair for this shape: every candidate is a relation, so settling the
    // ambiguity settles nothing — whichever way it goes the equation lands on one.
    // `/code-review` drove the ordinary text and it still failed with the ambiguity.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[
            "namespace am1\n  rule f(?x)\nend\n",
            "namespace am2\n  rule f(?y)\nend\n",
            "namespace am3\n  import am1.*\n  import am2.*\n  rule f(true) <=> 7 [simp]\nend\n",
        ]),
        &[
            "Declare a body-less `rule f(…)` in 'am3' to keep this equation here",
            "ambiguous symbol 'f' in scope 'am3'",
        ],
    );
    // AND IT IS DRIVEN. The prescribed declaration must make the program load AND the
    // equation answer where it was written — "the refusal defeated by taking its own
    // advice" is the failure this row exists to prevent.
    let mut interp = crate::common::interp_for_files(&[
        "namespace bm1\n  rule f(?x)\nend\n",
        "namespace bm2\n  rule f(?y)\nend\n",
        "namespace bm3\n  import bm1.*\n  import bm2.*\n  rule f(?z)\n  \
         rule f(true) <=> 7 [simp]\n  operation g() -> Int64 = f(true)\nend\n",
    ]);
    assert_eq!(
        int_value(interp.call("bm3.g", &[]).expect("the prescribed declaration answers")),
        7,
        "the head-scope declaration keeps the equation where it was written"
    );
}


#[test]
fn a_name_that_is_also_an_operation_is_not_this_refusal() {
    // KINDS ARE A SET, AND ONE NAME CAN PLAY TWO ROLES. A scope holding both
    // `rule f(2)` and `operation f() -> Int64` carries ONE symbol with both, and an
    // equation about it is about the operation — so this refusal must stand down and
    // leave the program to the ONE fault it has, which 061 already reports at the
    // body-less rule's own line.
    //
    // FOUND BY `/code-review`. An earlier cut deleted the `Operation` exemption after its
    // back-out failed zero rows; the shape existed and no row reached it, and the refusal
    // then told the author to declare an `operation` that was on the preceding line.
    // THIS ROW IS THAT BACK-OUT'S MISSING WITNESS: restore the deletion and it fails.
    let errs = crate::common::try_load_kb_with(
        "namespace ql9\n  rule f(2)\n  operation f() -> Int64\n  sort Rec\n    \
         entity r(n: Int64)\n    rule f() <=> 1 [simp]\n  end\nend\n",
    )
    .err()
    .expect("061 refuses the body-less rule beside the operation");
    assert!(
        errs.iter().all(|e| !e.contains("names the RELATION")),
        "this refusal must not fire where the name is ALSO an operation: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("already declared in this scope as a Operation")),
        "CONTROL: the one fault the program has is still reported: {errs:#?}"
    );
}

#[test]
fn a_global_predicate_is_not_a_party_to_this_refusal() {
    // `<global>` IS NOT A PARTY TO ANY OF IT (§8.6), and this refusal takes the same
    // exclusion its sibling does. It is the one scope every file shares and nobody opts
    // into, so a namespace's equation must not be answerable for what a namespace-less
    // file happens to spell — and the repair such a message named pointed AT `<global>`.
    //
    // FOUND BY `/code-review`, measured before the exclusion: this pair was a hard load
    // error naming `'<global>'`.
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        "rule f(?x)\n",
        "namespace pg\n  rule f(true) <=> 7 [simp]\nend\n",
    ]));
    // AND THE ROW ASSERTS WHAT IT COSTS, not that it loaded — "it loads" is what this
    // file's header rules out, and `/code-review` caught this arm doing exactly that.
    // `pg.f` is ABSENT: the `<global>` predicate DID absorb the namespace's subject, and
    // nothing said so. That is the silence this scope has always taken, recorded here and
    // in the spec rather than discovered.
    assert!(
        !present(&kb, "pg.f"),
        "the cost of the exclusion: `<global>` absorbs the subject silently"
    );
    // THE CONTROL that makes the row mean something: the PREDICATE spelling of the same
    // pair does the same thing. Both spellings agree, which is the point — this refusal
    // does not single out equations at a scope the visibility rule already exempts.
    let ctl = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        "rule f(?x)\n",
        "namespace pg\n  rule f(1) :- true\nend\n",
    ]));
    assert!(!present(&ctl, "pg.f"), "CONTROL: `<global>` absorbs the predicate head too");
}

#[test]
fn a_global_head_that_imported_the_namespace_is_refused() {
    // THE OTHER DIRECTION, and the exclusion above must not reach it. `<global>` is
    // exempt as a TARGET because nobody opts into it; a `<global>` HEAD reaches a
    // namespace's name only through an import it wrote, so it opted in exactly as any
    // namespace does.
    //
    // FOUND BY `/code-review`: the first cut took the exclusion both ways and left this
    // defect live — measured, the program below loaded clean, `<global>.f` was ABSENT,
    // and `gg()` answered `Int(7)` out of `pgz`'s predicate.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[
            "namespace pgz\n  rule f(?x)\n  rule f(1) :- true\nend\n",
            "import pgz.*\nrule f(true) <=> 7 [simp]\n",
        ]),
        &["the equation subject `f` names the RELATION `f` declared in 'pgz'"],
    );
    // THE CONTROL — the same namespace-less file with NO import, so nothing is reached
    // and its subject is its own. Without it the row above would be satisfied by refusing
    // any equation written outside a namespace.
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        "namespace pgz2\n  rule f(?x)\n  rule f(1) :- true\nend\n",
        "rule f(true) <=> 7 [simp]\n",
    ]));
    assert!(present(&kb, "pgz2.f"), "CONTROL: the namespace keeps its predicate");
}

#[test]
fn a_labelled_rules_own_name_is_a_relation_too() {
    // A RULE'S OPERATION NAME IS ITS LABEL ELSE ITS HEAD FUNCTOR (052 §"Naming the
    // relation"), so a LABEL is a fourth thing a subject can land on and it reproduces
    // this defect verbatim — `SymbolKind::Rule`, listed in `DECLARABLE_BY_A_RULE` beside
    // `Goal` and `EquationFunctor`.
    //
    // FOUND BY `/code-review`, and the reason the guard now asks that constant rather
    // than spelling a list: the first cut named `Goal` alone. Measured before the fix —
    // the program below loaded clean, `lc2.f` was ABSENT, and `lc2.g()` answered
    // `Int(7)` out of `lc1`'s label symbol. The kind census that produced the `Goal`-only
    // reading had no fixture carrying a label, which is what a census of the FIXTURES
    // rather than the POPULATION misses.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[
            "namespace lc1\n  rule f: p(?x) :- q(?x)\n  rule q(1) :- true\n  rule p(?y)\nend\n",
            "namespace lc2\n  import lc1.*\n  rule f(true) <=> 7 [simp]\nend\n",
        ]),
        &["the equation subject `f` names the RELATION `f` declared in 'lc1'"],
    );
    // THE CONTROL — the same label under another spelling, so nothing is reached.
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        "namespace lc3\n  rule other: p(?x) :- q(?x)\n  rule q(1) :- true\n  rule p(?y)\nend\n",
        "namespace lc4\n  import lc3.*\n  rule f(true) <=> 7 [simp]\nend\n",
    ]));
    assert!(present(&kb, "lc4.f"), "CONTROL: the subject is minted where it is written");
}

#[test]
fn a_relation_that_also_carries_equations_is_still_a_relation() {
    // A NAME CAN BE BOTH, AND BEING BOTH IS NOT AN EXEMPTION. One scope may mint a
    // predicate head and an equation subject of one name — the visibility refusal needs
    // TWO scopes, so two heads at ONE scope is ordinary auto-declaration — and the symbol
    // then carries `Goal` and `EquationFunctor` together. A later scope's equation about
    // it is still absorbing a RELATION, and the writing scope still loses its name.
    //
    // FOUND BY `/code-review`. An earlier cut exempted any symbol CARRYING
    // `EquationFunctor`, on a doc claim that the pair could not be constructed; measured,
    // the program below loaded clean with `pzc9.f` ABSENT while the `Goal`-only control
    // was correctly refused. It takes a STAGED load to reach: within one scan neither head
    // denotes at phase 2, so the pair is the visibility refusal instead.
    let errs = staged_load_errors(&[
        "namespace pzb9\n  rule f(1) :- true\n  rule f(true) <=> 7 [simp]\nend\n",
        "namespace pzc9\n  import pzb9.*\n  rule f(false) <=> 8 [simp]\nend\n",
    ]);
    assert!(
        errs.iter().any(|e| e.contains("names the RELATION `f` declared in 'pzb9'")),
        "a relation carrying equations is still a relation: {errs:#?}"
    );
    // THE CONTROL — a BARE subject IS a join target, and must stay one. `Bool.ite` and
    // `Float.nonEqRefl` are the corpus's 12 such sites; without this arm "refuse when the
    // target carries `EquationFunctor`" would be indistinguishable from the rule above.
    let ok = staged_load_errors(&[
        "namespace pzf9\n  rule f(true) <=> 7 [simp]\nend\n",
        "namespace pzg9\n  import pzf9.*\n  rule f(false) <=> 8 [simp]\nend\n",
    ]);
    assert!(ok.is_empty(), "CONTROL: several laws about one bare subject: {ok:#?}");
}

#[test]
fn a_mixed_collision_groups_prescribed_owner_answers() {
    // THE `equation_elsewhere` PRESCRIPTION REACHES A MIXED GROUP — one scope introducing
    // by a PREDICATE head, another by an equation SUBJECT — and there the `operation` it
    // names has to collect both shapes, not just the equations. Only an all-equation group
    // was driven (`wi980 … zeq5`), so this arm of the message was prescribed unverified;
    // this repo's own rule is that a refusal needs a repair you have RUN. Found by
    // `/code-review`.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            "namespace mx\n  rule f(false) :- true\n  sort A\n    entity a(n: Int64)\n    \
             rule f(true) <=> 1 [simp]\n  end\nend\n",
        ),
        &["an `operation f(…) -> R` in 'mx' makes every one of those heads its own"],
    );
    // TAKEN, AND DRIVEN ON BOTH SHAPES: the equation rewrites through the operation, and
    // the PREDICATE head's clause survives as a clause of it — which is the half a
    // pure-equation fixture could not have measured.
    const REPAIRED: &str = "namespace mx2\n  operation f(b: Bool) -> Int64\n  \
                            rule f(false) :- true\n  sort A\n    entity a(n: Int64)\n    \
                            rule f(true) <=> 1 [simp]\n  end\nend\n";
    let mut kb = crate::common::load_kb_with(REPAIRED);
    let sym = kb.try_resolve_symbol("mx2.f").expect("the operation owner");
    assert_eq!(
        kb.rules_by_functor(sym).len(),
        1,
        "the PREDICATE head's clause is a clause of the operation"
    );
    let goal = crate::common::query_pattern_term(&mut kb, "mx2.f(false)");
    assert_eq!(
        kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default()).len(),
        1,
        "and it answers"
    );
    let mut interp = crate::common::interp_for(&format!(
        "{REPAIRED}namespace mx2c\n  import mx2.{{f}}\n  operation g() -> Int64 = f(true)\nend\n"
    ));
    assert_eq!(
        int_value(interp.call("mx2c.g", &[]).expect("the equation rewrites")),
        1,
        "and the SORT's equation defines the operation"
    );
}

#[test]
fn two_files_reaching_two_relations_is_not_an_ambiguity() {
    // ONE GROUP, TWO SCOPES, AND NO AMBIGUITY. The group is keyed on `(scope, name)`
    // while the ladder is asked per head on that head's OWN file's behalf (imports are
    // file-local, WI-995) — so a namespace reopened in two files with different imports
    // gives two UNAMBIGUOUS answers naming two different relations, and the message must
    // not tell the author to go settle an ambiguity that no error reports.
    //
    // FOUND BY `/code-review`: the prescription branched on `predicate_scopes.len() > 1`
    // as a proxy for `Ambiguous`, and this shape separates the two.
    let errs = crate::common::try_load_kb_with_files(&[
        "namespace pza\n  rule f(?x)\n  rule f(1) :- true\nend\n",
        "namespace pzb\n  rule f(?y)\n  rule f(2) :- true\nend\n",
        "namespace pzz\n  import pza.*\n  rule f(true) <=> 7 [simp]\nend\n",
        "namespace pzz\n  import pzb.*\n  rule f(false) <=> 8 [simp]\nend\n",
    ])
    .err()
    .expect("the subject is absorbed twice over");
    assert_eq!(errs.len(), 1, "one subject, one message: {errs:#?}");
    assert!(
        errs[0].contains("declared in 'pza', 'pzb'"),
        "both relations named: {errs:#?}"
    );
    assert!(
        !errs[0].contains("settling the ambiguity"),
        "nothing here is ambiguous, and no other error reports one: {errs:#?}"
    );
    // AND THE REPAIR IT DOES PRESCRIBE IS DRIVEN, both clauses through the one
    // declaration that keeps them where they were written.
    let mut interp = crate::common::interp_for_files(&[
        "namespace pza\n  rule f(?x)\n  rule f(1) :- true\nend\n",
        "namespace pzb\n  rule f(?y)\n  rule f(2) :- true\nend\n",
        "namespace pzz\n  rule f(?z)\n  import pza.*\n  rule f(true) <=> 7 [simp]\n  \
         operation g() -> Int64 = f(true)\nend\n",
        "namespace pzz\n  import pzb.*\n  rule f(false) <=> 8 [simp]\n  \
         operation h() -> Int64 = f(false)\nend\n",
    ]);
    assert_eq!(int_value(interp.call("pzz.g", &[]).expect("first clause")), 7);
    assert_eq!(int_value(interp.call("pzz.h", &[]).expect("second clause")), 8);
}

#[test]
fn one_absorbed_subject_is_one_message() {
    // THE RULE IS ABOUT THE NAME, so however many equations are written about it the
    // cause and the repair are one. Reporting per CLAUSE printed the identical text
    // twice, differing only in line and column — which is what this pass's sibling
    // refusal already avoids ("ONE MISSING DECLARATION IS ONE MESSAGE"). Found by
    // `/code-review`.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            "namespace dupq\n  rule f(2)\n  sort Rec\n    entity r(n: Int64)\n    \
             rule f(true) <=> 1 [simp]\n    rule f(false) <=> 2 [simp]\n  end\nend\n",
        ),
        // EXACTLY ONE — `expect_load_errors` asserts the count, which is the whole row.
        &["the equation subject `f` names the RELATION `f` declared in 'dupq'"],
    );
    // AND TWO DISTINCT SUBJECTS ARE STILL TWO MESSAGES, else "one message" would be
    // indistinguishable from "one message per program".
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            "namespace dupr\n  rule f(2)\n  rule h(3)\n  sort Rec\n    \
             entity r(n: Int64)\n    rule f(true) <=> 1 [simp]\n    \
             rule h(true) <=> 2 [simp]\n  end\nend\n",
        ),
        &[
            "the equation subject `f` names the RELATION `f` declared in 'dupr'",
            "the equation subject `h` names the RELATION `h` declared in 'dupr'",
        ],
    );
}
