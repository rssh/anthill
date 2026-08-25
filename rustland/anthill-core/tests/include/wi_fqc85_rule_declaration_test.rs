//! WI-20260821-FQC85 / proposal 061 — A LOGICAL RULE'S HEAD NAMES A **DECLARED**
//! PREDICATE.
//!
//! A predicate was the only name in the language with no declaration: four core
//! constructs, and only `rule` brought a name into existence as a side effect of USING
//! it — so the pass that decided a head's binding was the pass that created the name.
//! That is the whole of WI-980, which closed the ordering by asking a question the pass
//! cannot move. 061 removes the question. Two rules, and every row below drives one:
//!
//! * **No body ⇒ DECLARES, a body ⇒ asserts.** A body-less rule declares its head's
//!   predicate and asserts nothing; its name is minted in pass 1, like every other name
//!   (WI-321). `fact` is how a body-less ASSERTION is written, and it desugars to an
//!   explicit `:- true`.
//! * **Auto-declaration stops at the FILE.** A predicate whose heads are all in one file
//!   is declared by them; one with heads in more than one file must be declared, or the
//!   load is refused NAMING the files.
//!
//! ── EVERY ROW DRIVES THE GOAL ────────────────────────────────────────────────
//!
//! A rule head that binds nowhere still loads clean, and a declaration asserts nothing
//! BY DESIGN — so "it loads" passes through both the regression and the feature. What
//! separates the two readings is a clause count of 0 against 1 and an answer count of 0
//! against 1, and both are asserted at every site.
//!
//! An **absent** predicate and an **empty** one are also different, and the difference is
//! this proposal's own subject: `clauses(..)` answers `None` for a name nothing resolves
//! and `Some(0)` for a declared predicate with no clauses. A row that only counted
//! answers could not tell them apart.
//!
//! ── THE BACK-OUTS, each naming the line, each RUN ────────────────────────────
//!
//! All eight were applied and measured over this file plus `wi980_rule_head_order_test`
//! (39 rows), re-measured after /code-review's fixes, and re-measured again after
//! WI-20260822-J38JE — which moved one of them (see THE EMPTY CONJUNCTION). Each is present-but-wrong rather than deleted, so a control cannot fall
//! with the thing it controls.
//!
//! * **THE DECLARATION READING** — in `Loader::load_rule`, drop the `return` at the end
//!   of the `RuleReading::Declaration` arm so a body-less head asserts again (the
//!   pre-061 reading). **14 rows fail**: six here (`a_body_less_rule_declares_and_-
//!   asserts_nothing`, `a_declaration_gives_an_inner_scope_its_own_predicate`, and the
//!   four multi-file rows' declared arms, whose counts move because the declaration
//!   itself now stores a clause) and eight in wi980.
//! * **THE PASS-1 MINT** — in `scan_rule`, gate the `rule_reading(..) == Declaration`
//!   mint off, so a declaration introduces nothing and pass 3 decides the name as
//!   before. **12 rows fail**: five here, seven in wi980.
//! * **THE EMPTY CONJUNCTION** — in `load_rule`'s body loop, gate off the
//!   `is_empty_conjunction_goal` skip, so `:- true` carries a constant goal. **It felled
//!   24 rows when 061 shipped, and it fells NONE of them now** — WI-20260822-J38JE gave
//!   a boolean constant a reading in the RESOLVER (`step_init`), so a `:- true` the
//!   loader no longer strips is answered there instead, and every count below is
//!   unchanged. The strip is not thereby redundant: it is what keeps the body EMPTY, so
//!   `fact H` and `rule H :- true` remain the same clause, and the row that measures it
//!   is now `wi_j38je_boolean_goal_test::a_top_level_true_is_still_erased_at_load` —
//!   the only row the back-out fells. Re-measured, not inherited: a neighbouring guard
//!   absorbed this one's domain, which is exactly how a stated back-out goes stale.
//! * **THE FILE BOUNDARY** — in `scan_definitions_with_sources`, raise the
//!   `file_idxs.len() < 2` test so no predicate is ever reported. **6 rows fail**: the
//!   four multi-file rows' refusal arms, `an_equation_subject_written_in_two_files_is_-
//!   not_refused`'s CONTROL (its predicate twin stops being refused), and wi980's
//!   `a_chain_deeper_than_any_recursion_loads`. `a_single_file_predicate_is_auto_-
//!   declared` passes, which is what makes it the control.
//! * **THE `DeclaresNothing` VERDICT** — in `rule_reading`, answer `Clause` where it
//!   answers `DeclaresNothing`. **1 row fails**:
//!   `a_body_less_rule_that_can_declare_nothing_is_refused`. (Backing out the load-side
//!   ARM instead does not compile — the `match` is exhaustive, and that is its own
//!   guard.)
//! * **THE CARRIER CHECK** — in the `Declaration` arm, discard
//!   `declaration_clause_carrier`'s answer. **1 row fails**:
//!   `a_declaration_carries_no_clause_text`.
//! * **THE MINTED-HERE CHECK** — in the `Declaration` arm, make the scope-locals lookup
//!   always answer `Some`. **1 row fails**:
//!   `a_declaration_the_defining_pass_never_reached_is_refused`. (Its first version
//!   asked the LADDER instead, and /code-review measured the hole: a declaration named
//!   `eq` inside a `provides` block passed the guard, because the prelude's `eq` denotes
//!   from anywhere. That arm is now a row of its own.)
//! * **THE ALREADY-DECLARED CHECK** — in the same arm, drop the non-predicate kind from
//!   the search. **1 row fails**:
//!   `a_declaration_of_a_name_another_construct_owns_is_refused`.
//!
//! TWO CLAIMS IN AN EARLIER DRAFT OF THIS BLOCK WERE WRONG, and running the recipes is
//! what found them: `a_body_less_rule_that_can_declare_nothing_is_refused` and
//! `a_declaration_carries_no_clause_text` were each said to fall under THE DECLARATION
//! READING, and neither does — both refusals fire and return before the line that
//! back-out touches. They have their own guards, named above.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// How many solutions `pattern` has — the goal, driven through the shipped
/// query-pattern path, so a pattern whose functor lands on a different symbol resolves
/// against that symbol's clauses exactly as `anthill query` would.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// The clauses stored under the symbol `qn` names — `None` when nothing is named `qn`
/// at all. The distinction this file is about: a DECLARED predicate with no clauses is
/// `Some(0)`, an absent one is `None`.
fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

// ── The declaration reading ─────────────────────────────────────────────────

#[test]
fn a_body_less_rule_declares_and_asserts_nothing() {
    // THE RULE ITSELF. `rule p(?x)` brings `p` into existence and stores NO clause, so
    // the predicate EXISTS and answers nothing — and the rule that reads it answers
    // nothing either, which is what makes the declaration a declaration rather than a
    // universally-true fact.
    //
    // BACKED OUT (the declaration reading): this row FAILS on every assertion — `p` has
    // one clause and both goals answer 1, since `rule p(?x)` was a fact whose variable
    // head matches anything.
    const DECLARED: &str = "namespace fqc85.decl\n  rule p(?x)\n  \
                            rule uses(?y) :- p(?y)\nend\n";
    let mut kb = crate::common::load_kb_with(DECLARED);
    assert_eq!(
        clauses(&kb, "fqc85.decl.p"),
        Some(0),
        "the predicate EXISTS — declared — and holds no clause"
    );
    assert_eq!(answers(&mut kb, "fqc85.decl.p(1)"), 0, "so it answers nothing");
    assert_eq!(answers(&mut kb, "fqc85.decl.uses(1)"), 0, "and neither does its reader");

    // THE CONTROL, one token apart — PASSES EITHER WAY BY DESIGN under the pass-1-mint
    // back-out, and FAILS under the empty-conjunction one. Without it the row above
    // would be equally true of a loader that dropped the rule entirely.
    const ASSERTED: &str = "namespace fqc85.asrt\n  rule p(?x) :- true\n  \
                            rule uses(?y) :- p(?y)\nend\n";
    let mut ctrl = crate::common::load_kb_with(ASSERTED);
    assert_eq!(clauses(&ctrl, "fqc85.asrt.p"), Some(1), "CONTROL: `:- true` ASSERTS");
    assert_eq!(answers(&mut ctrl, "fqc85.asrt.p(1)"), 1, "CONTROL");
    assert_eq!(answers(&mut ctrl, "fqc85.asrt.uses(1)"), 1, "CONTROL");
}

#[test]
fn an_explicit_true_body_is_the_empty_conjunction() {
    // §6.1's DESUGARING, driven. `fact H` and `rule H :- true` must be the same program,
    // because 061 defines the first as the second. They are compared clause for clause
    // and answer for answer on one head shape.
    //
    // IT HAD TO BE MADE REAL, not merely prescribed. MEASURED before this change:
    // `rule p(1) :- true` LOADED CLEAN AND ANSWERED NOTHING — `true` is a
    // `boolean_literal`, so the body carried a constant goal that no clause and no
    // builtin resolves, and WI-1034's "names nothing" refusal cannot reach it because a
    // constant names no name. A migration written from the proposal's text alone would
    // have silently emptied every site it touched.
    //
    // BACKED OUT (the empty conjunction): this row FAILS — the `:- true` half answers 0
    // where the `fact` half answers 1.
    const SRC: &str = "namespace fqc85.tt\n  rule p(1) :- true\n  fact q(1)\n  \
                       rule readp(?x) :- p(?x)\n  rule readq(?x) :- q(?x)\nend\n";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(answers(&mut kb, "fqc85.tt.readp(1)"), 1, "`:- true` asserts");
    assert_eq!(answers(&mut kb, "fqc85.tt.readq(1)"), 1, "and so does `fact`");
    assert_eq!(
        clauses(&kb, "fqc85.tt.p"),
        Some(1),
        "one clause — the `true` contributed no goal, it IS the empty body"
    );
    // The one place the two spellings still differ, and it is a KNOWN GAP rather than a
    // consequence of the desugaring: a `fact` head introduces no scoped name, so `q`
    // reaches the bare global intern (WI-20260821-RDGQC owns the enumeration of which
    // head shapes introduce a name; kernel-language.md §6.1 records it).
    assert_eq!(
        clauses(&kb, "fqc85.tt.q"),
        None,
        "a `fact` head is NOT scoped where it is written — RDGQC, not this ticket"
    );
}

#[test]
fn a_declaration_gives_an_inner_scope_its_own_predicate() {
    // §WI-896's OWN REMEDY, WHICH HAD NO FORM. "A scope that wants its own predicate
    // where an enclosing one resolves declares it" — and until 061 the only way to
    // declare a predicate name was a body-less `operation`, which drags in a signature
    // and membership of the dispatch surface (059 §Definitions).
    //
    // AND IT IS ORDER-FREE, which is the pass-1 mint. Both orders are run: the
    // declaration written above its clause and below it.
    //
    // BACKED OUT (the pass-1 mint): this row FAILS in both orders — the declaration
    // mints nothing, so `Rec`'s heads join the enclosing `p` exactly as the control
    // below does, and `fqc85.remedy*.Rec.p` does not exist.
    for (ns, decl_first) in [("fqc85.remedya", true), ("fqc85.remedyb", false)] {
        let inner = if decl_first {
            "    rule p(?x)\n    rule p(2) :- true\n"
        } else {
            "    rule p(2) :- true\n    rule p(?x)\n"
        };
        let src = format!(
            "namespace {ns}\n  rule p(1) :- true\n  sort Rec\n    entity rec(n: Int64)\n\
             {inner}  end\nend\n"
        );
        let mut kb = crate::common::load_kb_with(&src);
        assert_eq!(clauses(&kb, &format!("{ns}.p")), Some(1), "{ns}: the outer keeps its own");
        assert_eq!(
            clauses(&kb, &format!("{ns}.Rec.p")),
            Some(1),
            "{ns}: the declaration took the name back for `Rec`"
        );
        assert_eq!(answers(&mut kb, &format!("{ns}.Rec.p(2)")), 1, "{ns}");
        assert_eq!(answers(&mut kb, &format!("{ns}.p(2)")), 0, "{ns}: and the outer cannot see it");
    }

    // THE CONTROL — the identical program with the declaration deleted. Under WI-980 it
    // JOINED, silently, and that is what made the declaration's effect visible. Since
    // WI-20260822-845G7 it is REFUSED instead, which is a stronger control and the same
    // one: "the declaration works" is still distinguished from "an inner head never
    // joins", because without any declaration the program does not load at all.
    //
    // The refusal names `fqc85.nodecl` as where a declaration belongs — the OTHER remedy
    // the message offers, and the one that produces the join this row's DECLARED arm
    // deliberately does not take.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            "namespace fqc85.nodecl\n  rule p(1) :- true\n  sort Rec\n    \
             entity rec(n: Int64)\n    rule p(2) :- true\n  end\nend\n",
        ),
        &["fqc85.nodecl, fqc85.nodecl.Rec"],
    );
    // AND THE OUTER DECLARATION IS THE JOIN. Same program, `rule p(?x)` at the namespace
    // instead of in the sort: one predicate, both clauses — the mirror of the arms above,
    // so the pair shows the declaration decides WHICH predicate rather than merely
    // silencing the refusal.
    let mut joined = crate::common::load_kb_with(
        "namespace fqc85.outerdecl\n  rule p(?x)\n  rule p(1) :- true\n  sort Rec\n    \
         entity rec(n: Int64)\n    rule p(2) :- true\n  end\nend\n",
    );
    assert_eq!(clauses(&joined, "fqc85.outerdecl.p"), Some(2), "one predicate, both clauses");
    assert_eq!(clauses(&joined, "fqc85.outerdecl.Rec.p"), None);
    assert_eq!(answers(&mut joined, "fqc85.outerdecl.p(2)"), 1);
}

#[test]
fn a_body_less_rule_that_can_declare_nothing_is_refused() {
    // FOUR SHAPES THAT NAME NO PREDICATE, each with the CONTROL that separates "this
    // shape is refused" from "this shape never loaded". Under 061 each of them would
    // assert nothing AND declare nothing, so the refusal is the loud reading of a
    // silent drop — and for two of them (the qualified head, the paren-less nullary) the
    // silence it replaces is a filed defect: WI-20260821-W9SD3 and WI-20260821-P85Z7.
    //
    // BACKED OUT (`rule_reading` answers `Clause` where it answers `DeclaresNothing`):
    // this row FAILS, and it is the ONLY one that does. It passes under every other
    // back-out in this file's list — including the declaration reading, which an earlier
    // draft of this comment credited: that recipe drops a `return` further down the same
    // arm, and these four refusals fire and return before it.
    for (label, src) in [
        (
            "a `⊥` denial names no predicate",
            "namespace fqc85.n0\n  rule base(1) :- true\n  rule ⊥\nend\n",
        ),
        (
            "a declaration declares ONE name",
            "namespace fqc85.n1\n  rule lawq: aq(1), bq(2)\nend\n",
        ),
        (
            "a qualified name REFERENCES, it never introduces",
            "namespace fqc85.n2\n  rule fqc85.n2.other(1)\nend\n",
        ),
        (
            "a paren-less nullary head carries no functor",
            "namespace fqc85.n3\n  rule holdsq\nend\n",
        ),
    ] {
        let errs = crate::common::try_load_kb_with(src)
            .err()
            .unwrap_or_else(|| panic!("{label}: expected a refusal, the fixture loaded clean"));
        assert!(
            errs.iter().any(|e| e.contains("declares nothing")),
            "{label}: got {errs:#?}"
        );
    }

    // THE CONTROLS — the same three shapes that CAN carry a body, with one. Each loads.
    // (The `⊥` control is a bodied denial, which is what a denial is for.)
    for (label, src) in [
        ("bodied denial", "namespace fqc85.c0\n  rule base(1) :- true\n  rule ⊥ :- base(9)\nend\n"),
        ("bodied multi-head", "namespace fqc85.c1\n  rule lawq: aq(1), bq(2) :- true\nend\n"),
        (
            "bodied paren-less nullary",
            "namespace fqc85.c3\n  rule base(1) :- true\n  rule holdsq :- base(1)\nend\n",
        ),
    ] {
        crate::common::try_load_kb_with(src)
            .unwrap_or_else(|errs| panic!("{label} must load: {errs:#?}"));
    }
}

#[test]
fn a_declaration_the_defining_pass_never_reached_is_refused() {
    // THE ONE POSITION PASS 1 DOES NOT DESCEND INTO: the interior of a `provides …
    // language … end` block, which no scan pass walks (WI-20260821-TTHRK, and
    // WI-20260821-RDGQC's enumeration of which head shapes introduce a name). Before 061
    // a body-less head there asserted its clause on the WI-476 bare intern — uncitable,
    // but present. Under the declaration reading it would introduce nothing AND assert
    // nothing, so the load says so.
    //
    // BACKED OUT (delete the `name_denotes_for_rule_head` guard in the Declaration arm):
    // this row FAILS — the fixture loads clean and `pvb.Widget.pvbdecl` resolves to
    // nothing, which is the silent drop the guard exists for.
    const SRC: &str = "namespace fqc85pvb\n  sort Widget\n                           import anthill.prelude.{Int64}\n                           operation w(x: Int64) -> Int64\n  end\n                         provides Widget language anthill\n    rule pvbdecl(?x)\n  end\nend\n";
    for (label, name) in [
        ("a name nothing else declares", "pvbdecl"),
        // THE ARM THE FIRST GUARD MISSED. It asked the LADDER, and `eq` denotes through
        // the prelude from anywhere — so this program loaded clean and its declaration
        // introduced nothing, one name away from the fixture above (found by
        // /code-review). The guard now asks the SCOPE'S OWN LOCALS: did pass 1 put
        // anything here.
        ("a name the prelude also declares", "eq"),
    ] {
        let errs = crate::common::try_load_kb_with(&SRC.replace("pvbdecl", name))
            .err()
            .unwrap_or_else(|| panic!("{label}: a declaration nothing minted must be refused"));
        assert!(
            errs.iter()
                .any(|e| e.contains("was never brought into existence")),
            "{label}: got {errs:#?}"
        );
    }

    // THE CONTROL — the same block with a BODY. It still loads (its clause lands on the
    // bare intern, which is TTHRK's gap and not this ticket's), so the row above
    // measures the declaration reading and not "a rule in a provides block is refused".
    let ctrl = crate::common::load_kb_with(&SRC.replace("rule pvbdecl(?x)", "rule pvbdecl(1) :- true"));
    let _ = ctrl;
}

#[test]
fn a_declaration_of_a_name_another_construct_owns_is_refused() {
    // PASS 1'S `define` MERGES, and a declaration that merges declares NOTHING. Measured
    // before this refusal (found by /code-review): `operation has(x) -> Bool` beside
    // `rule has(?x)` loaded clean with a `Goal` kind added to the OPERATION's own
    // symbol, and `sort Foo … end` beside `rule Foo(?x)` did the same to a SORT. The
    // line asserts nothing and introduces nothing — the no-op 059 R4 clause 3 refuses
    // for every other pair of declarations at one address.
    //
    // BOTH ORDERS, because the check must not depend on which the pass walked first —
    // that is the order dependence 061 exists to remove, which is why it is asked at
    // LOAD (where every name exists) and not at the mint.
    for (label, decl, rule) in [
        (
            "operation",
            "  operation has(x: Int64) -> Bool\n",
            "  rule has(?x)\n",
        ),
        ("sort", "  sort Foo\n    entity foo(n: Int64)\n  end\n", "  rule Foo(?x)\n"),
    ] {
        for (order, body) in [
            ("declaration first", format!("{decl}{rule}")),
            ("rule first", format!("{rule}{decl}")),
        ] {
            let src = format!(
                "namespace fqc85own\n  import anthill.prelude.{{Int64, Bool}}\n{body}end\n"
            );
            let errs = crate::common::try_load_kb_with(&src).err().unwrap_or_else(|| {
                panic!("{label}, {order}: expected a refusal, the fixture loaded clean")
            });
            assert!(
                errs.iter().any(|e| e.contains("is already declared in this scope")),
                "{label}, {order}: got {errs:#?}"
            );
        }
    }

    // THE CONTROL — the same pair with `:- true`, which is the remedy the message names:
    // a CLAUSE of the operation, which is what §8.6 calls a lemma about it. It loads and
    // it answers.
    let mut kb = crate::common::load_kb_with(
        "namespace fqc85lemma\n  import anthill.prelude.{Int64, Bool}\n           operation has(x: Int64) -> Bool\n  rule has(1) :- true\nend\n",
    );
    assert_eq!(answers(&mut kb, "fqc85lemma.has(1)"), 1, "CONTROL: the clause answers");
}

#[test]
fn a_declaration_carries_no_clause_text() {
    // A DECLARATION STORES NO CLAUSE, so a citation label, a description block, a `[…]`
    // tag, a `[t]` type-variable introducer and a typed column `?x: T` each have nothing
    // to attach to. Every one of them was SILENTLY DROPPED the moment this arm stopped
    // asserting — a label would define a `Rule` symbol that `using` then finds nothing
    // under, and a `[t]` can only ever be bounded by a body's `:- Spec[t]` guard, which
    // a declaration has no body for.
    //
    // BACKED OUT (the `Declaration` arm discards `declaration_clause_carrier`'s answer):
    // this row FAILS, and it is the only one that does. Not the declaration reading,
    // which an earlier draft of this comment credited — the carrier refusal returns
    // before the line that back-out touches.
    for (label, src) in [
        ("label", "namespace fqc85.l0\n  rule lab: p(?x)\nend\n"),
        // NO DESCRIPTION ARM. An earlier version of this row had one, spelled
        // `{< … >} rule lab: p(?x)` — which carries a LABEL, so it measured the arm
        // above and nothing about descriptions (found by /code-review). It cannot be
        // re-spelled: a description on an UNLABELED rule is a parse error (WI-1072, "no
        // stable target"), so a described declaration always has a label and the
        // description case is unreachable. The loader carries no arm for it either.
        ("tag", "namespace fqc85.l2\n  rule p(?x) [simp]\nend\n"),
        (
            "type-variable introducer",
            "namespace fqc85.l3\n  import anthill.prelude.{Int64, Eq}\n  rule p[t](?x, ?y)\nend\n",
        ),
        (
            "typed column",
            "namespace fqc85.l4\n  import anthill.prelude.{Int64}\n  rule p(?x: Int64)\nend\n",
        ),
    ] {
        let errs = crate::common::try_load_kb_with(src)
            .err()
            .unwrap_or_else(|| panic!("{label}: expected a refusal, the fixture loaded clean"));
        assert!(
            errs.iter().any(|e| e.contains("DECLARES the predicate")),
            "{label}: got {errs:#?}"
        );
    }
}

#[test]
fn an_equational_head_is_untouched_in_both_spellings() {
    // THE TICKET'S OWN CONTROL, and it PASSES EITHER WAY BY DESIGN. 061 governs LOGICAL
    // rules only: an equational rule extends unification, its clauses index under the
    // `eq`/`unify` CONNECTIVE rather than under its subject (WI-898), so the subject owns
    // no clauses and there is no predicate to declare. The two shapes share `body: None`
    // and are told apart by the head's functor — which is the reader the loader already
    // runs.
    //
    // Without this row, "a body-less rule declares" would be indistinguishable from
    // "a body-less rule stores nothing", and the 97 body-less equation heads in the
    // corpus would have gone inert in silence.
    const FIRES: &str = r#"
namespace fqc85.eqn
  import anthill.prelude.{Int64, Bool}
  sort C
    import anthill.prelude.{Int64, Bool}
    operation pick(cond: Bool, then: Int64, else: Int64) -> Int64
    rule pick(true, ?t, ?_) <=> ?t [simp]
    operation drive(n: Int64) -> Int64 = pick(true, 10, 20)
  end
end
"#;
    let mut interp = crate::common::interp_for(FIRES);
    match interp.call("fqc85.eqn.C.drive", &[anthill_core::eval::Value::Int(0)]) {
        Ok(anthill_core::eval::Value::Int(10)) => {}
        other => panic!("a body-less `<=>` equation must still fire; got {other:?}"),
    }

    // …and the NON-defining spellings keep their own refusals rather than becoming
    // declarations: a declaration reading that swallowed them would turn two located
    // errors into silence (WI-888 / WI-1090).
    for (connective, want) in [("=", "`pick(…) <=> …`"), ("===", "defines nothing")] {
        let src = FIRES
            .replace("<=>", connective)
            .replace("fqc85.eqn", "fqc85.eqn_ref")
            .replace(" [simp]", "");
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_else(|| panic!("`{connective}` at a body-less head must be refused"));
        assert!(
            errs.iter().any(|e| e.contains(want)),
            "`{connective}`: got {errs:#?}"
        );
    }
}

// ── Auto-declaration stops at the FILE boundary ─────────────────────────────
//
// THE FOUR SHAPES BELOW ARE WI-980'S OWN, and each was a measured cross-FILE
// ABSORPTION: one file's head moving another file's clause. Each is now a located
// refusal NAMING the files, and each loads — with the clauses on ONE predicate, driven —
// once the predicate is declared. Every one of them is run in BOTH arms, because a
// refusal without the declared twin would only show that the shape stopped working.
//
// MEASURED UNDER THE FILE-BOUNDARY BACK-OUT: every refusal arm in this section fails
// (the program loads clean, so `expect_refused` panics), while every DECLARED arm and
// `a_single_file_predicate_is_auto_declared` pass — which is what makes those controls
// rather than repetitions. Six rows in all, counting the equation row's own predicate
// control and wi980's chain.

/// The refusal's rendered message, or a panic naming the fixture that loaded clean.
///
/// TWO REFUSALS, ONE REPORT. An undeclared predicate is refused by whichever rule sees
/// it — the FILE rule when its heads sit at one scope in two files (the message names the
/// files), the VISIBILITY rule when two scopes that can see each other both introduce it
/// (the message names the scopes; WI-20260822-845G7). Either way there must be exactly
/// ONE report per predicate, not one per clause, and the caller says which message its
/// shape takes by what it asks the message to contain — a row that expected the other one
/// fails here rather than passing on "something was refused".
fn expect_refused(files: &[(&str, &str)], name: &str, want: &[&str]) {
    let errs = crate::common::try_load_kb_with_named_files(files)
        .err()
        .unwrap_or_else(|| panic!("`{name}` is undeclared and must be refused; it loaded clean"));
    let spanning: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains("and no declaration") || e.contains("none of them declares it"))
        .collect();
    assert_eq!(
        spanning.len(),
        1,
        "exactly ONE report per predicate, not one per clause; got {errs:#?}"
    );
    let msg = spanning[0];
    assert!(msg.contains(&format!("`{name}`")), "names the predicate: {msg}");
    for w in want {
        assert!(msg.contains(w), "the message must contain `{w}`: {msg}");
    }
}

#[test]
fn a_sibling_files_head_no_longer_moves_another_files_clause() {
    // MEASURED under WI-980: `zlib.q` 2→1 and `zdemo.q` 0→2 with the FIRST FILE
    // UNEDITED — a mint in one file of a scope captures a head in a sibling file,
    // because imports are file-local while symbols are per-scope (WI-995).
    const LIB: &str = "namespace zlibq\n  rule q(1) :- true\nend\n";
    const LIB_DECLARED: &str = "namespace zlibq\n  rule q(?x)\n  rule q(1) :- true\nend\n";
    const IMPORTER: &str = "namespace zdemoq\n  import zlibq.*\n  rule q(2) :- true\nend\n";
    const IMPORTER_SELECTED: &str =
        "namespace zdemoq\n  import zlibq.{q}\n  rule q(2) :- true\nend\n";
    const SIBLING: &str = "namespace zdemoq\n  sort Rec\n    entity rec(n: Int64)\n    \
                           rule q(3) :- true\n  end\nend\n";

    // SINCE 845G7 THE ABSORPTION IS IMPOSSIBLE RATHER THAN MERELY REFUSED: a head never
    // moves, so `zdemoq` can no longer capture `zlibq`'s clause whatever the file order.
    // What the program still lacks is a statement of which scope owns `q`, and the
    // VISIBILITY rule is what says so — naming all three scopes, where the file rule used
    // to name two files. The defect measured under WI-980 is reported either way; this
    // says which message it is now.
    // AND IT NAMES NO OWNER, deliberately: `zdemoq.Rec` reaches `zdemoq` through the
    // enclosing chain but NOT `zlibq`, because the import that carries it is written in
    // `zdemo.anthill` and imports are file-local (WI-995). So no single declaration
    // collects all three, and the message must not promise one — measured, an earlier cut
    // named `zlibq` (the sink of the direct reach graph) and following that advice left
    // `zdemoq.Rec.q` a separate predicate with no error at all. Found by `/code-review`.
    expect_refused(
        &[("zlib.anthill", LIB), ("zdemo.anthill", IMPORTER), ("zrec.anthill", SIBLING)],
        "q",
        &["zdemoq, zdemoq.Rec, zlibq", "No one of them is reachable from all the others"],
    );

    // DECLARED AND IMPORTED BY NAME — C666A makes the selection explicit: the importing
    // file's head is a clause of the imported predicate, while the sibling file (which
    // has no import) introduces its own.
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        ("zlib.anthill", LIB_DECLARED),
        ("zdemo.anthill", IMPORTER_SELECTED),
        ("zrec.anthill", SIBLING),
    ]));
    assert_eq!(clauses(&kb, "zlibq.q"), Some(2), "the declared predicate holds both clauses");
    assert_eq!(clauses(&kb, "zdemoq.q"), None, "the importer introduces nothing");
    assert_eq!(clauses(&kb, "zdemoq.Rec.q"), Some(1), "the sibling file introduces its own");
    assert_eq!(answers(&mut kb, "zlibq.q(2)"), 1);
    assert_eq!(answers(&mut kb, "zlibq.q(3)"), 0);
    assert_eq!(answers(&mut kb, "zdemoq.Rec.q(3)"), 1);
}

#[test]
fn a_cycle_can_no_longer_absorb_a_third_files_clause() {
    // MEASURED under WI-980's predecessor: six permutations of these three files gave
    // TWO different programs. The cycle itself is not what 061 removes — two scopes that
    // can each see the other still introduce separately, and each of those predicates is
    // written in ONE file (`mutual_visibility_introduces_separately_in_either_order`,
    // wi980). What it removes is the cycle member ABSORBING the third file's clause.
    //
    // ALL SIX ORDERS, in both arms — a refusal that depended on file order would be the
    // very defect this replaces.
    const A: &str = "namespace fqcA\n  import fqcB.*\n  rule p(1) :- true\nend\n";
    const A_DECLARED: &str =
        "namespace fqcA\n  import fqcB.*\n  rule p(?x)\n  rule p(1) :- true\nend\n";
    const B: &str = "namespace fqcB\n  import fqcA.*\n  rule p(2) :- true\nend\n";
    const B_SELECTED: &str = "namespace fqcB\n  import fqcA.{p}\n  rule p(2) :- true\nend\n";
    const S: &str = "namespace fqcA.sub\n  rule p(3) :- true\nend\n";

    for order in [
        [("a.anthill", A), ("b.anthill", B), ("s.anthill", S)],
        [("a.anthill", A), ("s.anthill", S), ("b.anthill", B)],
        [("b.anthill", B), ("a.anthill", A), ("s.anthill", S)],
        [("b.anthill", B), ("s.anthill", S), ("a.anthill", A)],
        [("s.anthill", S), ("a.anthill", A), ("b.anthill", B)],
        [("s.anthill", S), ("b.anthill", B), ("a.anthill", A)],
    ] {
        // NAMES THE SCOPES, NOT THE FILES (845G7): `fqcA`, `fqcA.sub` and `fqcB` all
        // introduce `p` and all reach each other, and the cycle means nothing in the
        // program names an owner — which the message has to say, and does.
        // NAMES `fqcA`: `fqcB` reaches it through its import and `fqcA.sub` through the
        // enclosing chain, so one declaration there really does collect all three — which
        // is the test the message's promise has to pass.
        expect_refused(
            &order,
            "p",
            &["fqcA, fqcA.sub, fqcB", "`rule p(…)` in 'fqcA'"],
        );
    }

    // DECLARED AND SELECTED — now every one of the six orders gives ONE program. The
    // declaration establishes the owner and `B`'s named import is C666A's explicit
    // non-enclosing opt-in; `fqcA.sub` reaches the owner lexically.
    for order in [
        [("a.anthill", A_DECLARED), ("b.anthill", B_SELECTED), ("s.anthill", S)],
        [("a.anthill", A_DECLARED), ("s.anthill", S), ("b.anthill", B_SELECTED)],
        [("b.anthill", B_SELECTED), ("a.anthill", A_DECLARED), ("s.anthill", S)],
        [("b.anthill", B_SELECTED), ("s.anthill", S), ("a.anthill", A_DECLARED)],
        [("s.anthill", S), ("a.anthill", A_DECLARED), ("b.anthill", B_SELECTED)],
        [("s.anthill", S), ("b.anthill", B_SELECTED), ("a.anthill", A_DECLARED)],
    ] {
        let mut kb =
            crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&order));
        assert_eq!(clauses(&kb, "fqcA.p"), Some(3), "order {order:?}");
        assert_eq!(clauses(&kb, "fqcB.p"), None, "order {order:?}");
        assert_eq!(clauses(&kb, "fqcA.sub.p"), None, "order {order:?}");
        for n in 1..=3 {
            assert_eq!(answers(&mut kb, &format!("fqcA.p({n})")), 1, "order {order:?}");
        }
    }
}

#[test]
fn one_address_split_across_two_files_no_longer_gives_two_programs() {
    // MEASURED under WI-980's predecessor: the same pair at one address gave one
    // predicate with two clauses or two predicates with one each, decided by which file
    // the loader read first. WI-980 made the two orders AGREE; 061 makes the shape say
    // which predicate it means.
    const OUTER: &str = "namespace fqc85.split\n  rule p(1) :- true\nend\n";
    const OUTER_DECLARED: &str = "namespace fqc85.split\n  rule p(?x)\n  rule p(1) :- true\nend\n";
    const INNER: &str = "namespace fqc85.split\n  sort Rec\n    entity rec(n: Int64)\n    \
                         rule p(2) :- true\n  end\nend\n";

    for order in [
        [("outer.anthill", OUTER), ("inner.anthill", INNER)],
        [("inner.anthill", INNER), ("outer.anthill", OUTER)],
    ] {
        // TWO SCOPES, so this is the VISIBILITY message even though the two files are
        // what WI-980 measured — `fqc85.split.Rec` sees `fqc85.split` through the
        // enclosing chain. `one_scope_reopened_in_two_files_must_declare_its_predicate`
        // (wi980) is the same address with ONE scope, and takes the file message.
        expect_refused(
            &order,
            "p",
            &["fqc85.split, fqc85.split.Rec", "`rule p(…)` in 'fqc85.split'"],
        );
    }
    for order in [
        [("outer.anthill", OUTER_DECLARED), ("inner.anthill", INNER)],
        [("inner.anthill", INNER), ("outer.anthill", OUTER_DECLARED)],
    ] {
        let mut kb =
            crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&order));
        assert_eq!(clauses(&kb, "fqc85.split.p"), Some(2), "ONE predicate, both clauses");
        assert_eq!(clauses(&kb, "fqc85.split.Rec.p"), None);
        assert_eq!(answers(&mut kb, "fqc85.split.p(2)"), 1);
        assert_eq!(answers(&mut kb, "fqc85.split.p(1)"), 1);
    }
}

#[test]
fn a_head_that_binds_through_its_own_files_import_is_still_a_second_file() {
    // WHY OWNERSHIP HAD TO BE KEYED PER `(scope, name, FILE)` (WI-995): two heads of one
    // predicate can sit in files with different imports, so the decision has to be taken
    // on behalf of the file the head is WRITTEN in. 061 does not need that key for this
    // shape any more — the two files are one predicate, so the shape is refused — but
    // the DECLARED arm still runs through the file-local import, and the same key
    // decides whether the importing file's head sees the declaration at all.
    const LIB: &str = "namespace fqc85_lib\n  rule q(1) :- true\nend\n";
    const LIB_DECLARED: &str = "namespace fqc85_lib\n  rule q(?x)\n  rule q(1) :- true\nend\n";
    const IMPORTER: &str =
        "namespace fqc85.viaimport.b\n  import fqc85_lib.*\n  rule q(2) :- true\nend\n";
    const IMPORTER_SELECTED: &str =
        "namespace fqc85.viaimport.b\n  import fqc85_lib.{q}\n  rule q(2) :- true\nend\n";
    // A third file scanned LAST, so a stale asking-file is a DIFFERENT file's and the row
    // cannot pass by the two coinciding.
    const TRAILING: &str = "namespace fqc85.viaimport.z\n  rule unrelated(3) :- true\nend\n";

    expect_refused(
        &[("lib.anthill", LIB), ("imp.anthill", IMPORTER), ("trail.anthill", TRAILING)],
        "q",
        &["fqc85.viaimport.b, fqc85_lib", "`rule q(…)` in 'fqc85_lib'"],
    );

    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        ("lib.anthill", LIB_DECLARED),
        ("imp.anthill", IMPORTER_SELECTED),
        ("trail.anthill", TRAILING),
    ]));
    assert_eq!(
        clauses(&kb, "fqc85_lib.q"),
        Some(2),
        "the importing file's head joins the declared predicate"
    );
    assert_eq!(clauses(&kb, "fqc85.viaimport.b.q"), None);
    assert_eq!(answers(&mut kb, "fqc85_lib.q(2)"), 1);
}

#[test]
fn a_single_scope_predicate_is_auto_declared() {
    // THE CONTROL FOR THE WHOLE SECTION, and it PASSES EITHER WAY BY DESIGN. Without a
    // row that LOADS, a rule refusing every rule head at all would look correct.
    //
    // ONE SCOPE, NOT MERELY ONE FILE, since WI-20260822-845G7. This row used to put the
    // second clause inside a `sort Rec` and call the pair auto-declared, on 061's
    // "a predicate whose heads are all written in one file". 845G7 narrows that to the
    // SCOPE — the pair now needs `rule p(?x)` to say which predicate it means — and the
    // narrowing is why this fixture moved rather than being deleted: the claim it
    // controls is still "an undeclared predicate can load", which is exactly one scope's
    // worth of clauses.
    let mut kb = crate::common::load_kb_with(
        "namespace fqc85.one\n  rule p(1) :- true\n  rule p(2) :- true\n  \
         sort Rec\n    entity rec(n: Int64)\n    rule other(3) :- true\n  end\nend\n",
    );
    assert_eq!(clauses(&kb, "fqc85.one.p"), Some(2), "CONTROL: one scope, one predicate");
    assert_eq!(answers(&mut kb, "fqc85.one.p(2)"), 1, "CONTROL");
    // And an inner scope introducing a name NOBODY else writes is untouched by the
    // visibility rule — the other half of the same control.
    assert_eq!(clauses(&kb, "fqc85.one.Rec.other"), Some(1), "CONTROL: a fresh inner name");
    assert_eq!(answers(&mut kb, "fqc85.one.Rec.other(3)"), 1, "CONTROL");
}

#[test]
fn an_operation_declaration_satisfies_the_file_rule() {
    // A DECLARATION IS A DECLARATION, whichever construct wrote it. The rule asks
    // whether the predicate was declared, not whether a body-less RULE declared it — so
    // an `operation` (the only way to declare a predicate name before 061, and the one
    // §WI-896 pointed at) takes clauses from two files exactly as the new form does.
    //
    // This is the DENOTES arm of the grouping, and it has no other row: a
    // grouping that counted every non-denoting head would refuse this program, which is
    // the shape 059's own dispatch surface is built on.
    //
    // PASSES EITHER WAY under the file-boundary back-out — it is a control, and what it
    // controls is the SCOPE of the refusal.
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        (
            "opdecl.anthill",
            "namespace fqc85op\n  import anthill.prelude.{Int64, Bool}\n  \
             operation has(x: Int64) -> Bool\n  rule has(1) :- true\nend\n",
        ),
        ("opclause.anthill", "namespace fqc85op\n  rule has(2) :- true\nend\n"),
    ]));
    assert_eq!(answers(&mut kb, "fqc85op.has(1)"), 1, "the declaring file's clause");
    assert_eq!(answers(&mut kb, "fqc85op.has(2)"), 1, "and the second file's");
    assert_eq!(answers(&mut kb, "fqc85op.has(9)"), 0);
}

#[test]
fn an_equation_subject_written_in_two_files_is_not_refused() {
    // EQUATIONS ARE OUT OF SCOPE — the other half of the control above. An equation's
    // clauses index under the `eq`/`unify` connective, so its subject owns none and
    // there is no predicate for the file rule to govern. Two files writing laws about one
    // subject are not "a predicate assembled by two parties".
    //
    // PASSES EITHER WAY under every back-out; it is here because the file rule reads a
    // list of rule heads that CONTAINS equation subjects, and filtering them out is a
    // line that can be deleted.
    const A: &str = "namespace fqc85.eqsplit\n  rule pickx(true) <=> 1 [simp]\nend\n";
    const B: &str = "namespace fqc85.eqsplit\n  rule pickx(false) <=> 2 [simp]\nend\n";
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        ("eqa.anthill", A),
        ("eqb.anthill", B),
    ]));
    // The subject IS one name at one scope, written in two files — which is exactly the
    // shape the predicate rule refuses. It owns no clauses, so there is nothing to
    // assemble and nothing to declare.
    assert_eq!(
        clauses(&kb, "fqc85.eqsplit.pickx"),
        Some(0),
        "an equation's subject owns no clauses — they index under the connective"
    );
    // THE CONTROL that makes the row mean something: the same two files with PREDICATE
    // heads instead of equations ARE refused.
    let errs = crate::common::try_load_kb_with_named_files(&[
        ("pa.anthill", "namespace fqc85.pxsplit\n  rule pickp(true) :- true\nend\n"),
        ("pb.anthill", "namespace fqc85.pxsplit\n  rule pickp(false) :- true\nend\n"),
    ])
    .err()
    .expect("CONTROL: the predicate spelling of the same two files IS refused");
    assert!(
        errs.iter().any(|e| e.contains("and no declaration")),
        "CONTROL: {errs:#?}"
    );
}
