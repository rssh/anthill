//! WI-980 / 059 R6, AS 061 AND WI-20260822-845G7 LEFT IT — A RULE HEAD DECLARES ITS
//! PREDICATE AT THE SCOPE IT IS WRITTEN IN, AND TWO SCOPES THAT CAN SEE EACH OTHER MAY
//! NOT BOTH INTRODUCE ONE NAME.
//!
//! ── WHAT THIS FILE USED TO MEASURE, AND WHY IT NO LONGER CAN ─────────────────
//!
//! WI-980's subject was ORDER: `rule p(1)` beside `sort Rec { rule p(2) }` loaded as ONE
//! predicate written one way round and TWO written the other, because the ladder that
//! decides a head was asked against a half-built name table. It closed that by asking a
//! question the pass cannot move — *does some scope this one can see already introduce
//! the name* — resolved through an `Ownership` fixpoint: an optimistic overlay, three
//! settling rules, an SCC tie-break, a `(scope, name, FILE)` key, a `<global>` two-roles
//! exception and a depth bound.
//!
//! 061 then made a predicate DECLARED rather than discovered, and 845G7 measured what was
//! left for the fixpoint to do. Instrumenting the verdict loop over the whole suite —
//! stdlib, `anthill-stl`, examples, `anthill-todo` and every fixture — gave **234,078**
//! head decisions:
//!
//! | verdict | count |
//! |---|---:|
//! | introduce at this scope | **233,917** |
//! | join ANOTHER scope's head | **161** |
//! | yield to an ordinary declaration | **0** |
//!
//! and 130 of the 161 were one fixture in this file, with every one of the remaining 22
//! distinct triples in a fixture written to exercise the fixpoint itself. **Zero** from
//! the shipped corpus. The machinery computed a constant for every real program, so it is
//! gone and the rule is:
//!
//! > An undeclared rule head declares its predicate at the scope it is WRITTEN IN. Two
//! > scopes that can see each other may not both introduce one name — declare it.
//!
//! Order-freedom is now a property of the rule rather than a result: nothing is asked
//! about any other head, so no order can enter. The rows below still run both orders,
//! because a claim that holds in only one order measures nothing and because the REFUSAL
//! must be order-free too.
//!
//! ── WHY THE SECOND HALF OF THE RULE IS A REFUSAL AND NOT A SPLIT ─────────────
//!
//! Removing the join replaces an ASSEMBLY hazard with a SHADOWING one, and they do not
//! take the same boundary. 059 §Definitions' FILE unit answers "a predicate assembled by
//! two parties that never agreed on it" — but one author writing
//! `demo { rule p(1) :- true; sort Rec { rule p(2) :- true } }` is not two parties. They
//! are one party who used to get ONE predicate and would otherwise silently get two,
//! because a scope's own name beats what it imports or inherits (`resolve_in_scope` reads
//! `locals` and returns before consulting any import or parent). A silent change of
//! meaning is worse than either reading, so the refusal is stated over VISIBILITY, and a
//! same-file pair is refused exactly as a cross-file one is. Corpus cost of the wider
//! rule, measured: zero, the same as the narrow one.
//!
//! THE SHADOW ITSELF IS NOT REFUSED. Every refusal row below carries a `declare in EACH
//! scope` arm that reproduces it exactly — the point is that it is then written down.
//!
//! ── THE CHANNELS, AND WHY THERE ARE SIX ──────────────────────────────────────
//!
//! Visibility reaches a scope by more than one edge, and a guard keyed on any one of them
//! answers the others by accident. Each channel is a different edge, and each runs its
//! REFUSED arm and both DECLARED arms:
//!
//! | channel | the edge |
//! |---|---|
//! | a sort body | the enclosing chain, into a sort |
//! | a nested ordinary namespace | the enclosing chain, into a namespace |
//! | a `requires` parent | a `requires` edge, which sits at no address |
//! | a facade importing its own submodule | a downward wildcard import PLUS the enclosing edge |
//! | a mutual-import cycle | two wildcard imports, and nothing names an owner |
//! | a one-way wildcard import | one wildcard import, and the imported scope is the owner |
//!
//! THE FOURTH CHANNEL IS WHY THE REACH IS ASKED OF THE RESOLVER AND NOT OF AN ADDRESS. A
//! `requires` parent sits at no particular address, so any key derived from the qualified
//! NAME answers it by text order — measured under the fixpoint, an attempt keyed on
//! address depth left [`requires_same_depth`] split in one order and joined in the other.
//!
//! ── THE CONTROLS, AND WHAT FAILS WITHOUT THEM ────────────────────────────────
//!
//! [`two_scopes_that_cannot_see_each_other_keep_their_own`] is the one that matters most:
//! without it, a "refusal" that fired on any two scopes sharing a short name would look
//! correct, and it would refuse most real programs. [`an_unmatched_inner_head_still_-
//! introduces`] is its twin one level down — a genuinely new inner name must still be
//! introduced. And [`the_captured_stdlib_predicate_survives`] holds the other end: a head
//! whose name RESOLVES is a CLAUSE of what it resolves to and never reaches this rule at
//! all, which is why refusing head/import coexistence here does not report the 99 stdlib
//! errors across 43 names WI-980 measured for refusing it generally.
//!
//! ── THE BACK-OUTS, all run, each naming a line rather than an idea ───────────
//!
//! * THE COLLISION REFUSAL — `let collisions = Vec::new();` in place of the
//!   `head_name_collisions(…)` call in sub-pass 3. VERIFIED, **14 rows fail**: every
//!   `*_must_declare_*` row's REFUSED arm, this file's chain and reopened-member rows,
//!   five in `wi_fqc85_rule_declaration_test` and `wi900`'s undeclared arm. The DECLARED
//!   arms pass either way, by design — they are what shows the refusal is about the
//!   silence and not about the shape.
//! * THE ASKING FILE — `set_asking_file(None)` in place of `set_asking_file(Some(file))`
//!   in [`head_name_reach`]. VERIFIED, **8 rows fail**, four here and three in
//!   `wi_fqc85_rule_declaration_test`: with imports no longer file-local the reach is
//!   transitive, so chains collapse and cycles gain members.
//! * THE FILE RULE — `continue` unconditionally in the file block. VERIFIED, **exactly 2
//!   rows fail**: [`one_scope_reopened_in_two_files_must_declare_its_predicate`] and
//!   `wi_fqc85_rule_declaration_test::an_equation_subject_written_in_two_files_is_not_-
//!   refused`, which is that rule's own exclusion.
//! * THE SUPPRESSION — drop the `collided.contains(&(owner, name))` test in the file
//!   block. VERIFIED, **exactly 1 row fails**:
//!   [`a_cycle_member_reopened_in_a_second_file_is_reported_once`], with two reports for
//!   one missing declaration.
//! * THE NAMED OWNER — `.find(|&cand| edges[&cand].is_empty())`, the SINK of the direct
//!   reach graph, in place of "reached by every other member". VERIFIED, **6 rows fail**:
//!   [`a_named_owner_must_be_reachable_from_every_other_member`], the chain, the facade,
//!   the cycle and two in `wi_fqc85_rule_declaration_test`. This is the one whose failure
//!   is silent in the shipped program rather than loud — following the sink's advice made
//!   a refused program LOAD with part of it still split.
//! * EQUATION SUBJECTS — put `head.introduced_by != RuleIntroduction::Predicate` back in
//!   the candidate filter of [`head_name_collisions`]. VERIFIED, **exactly 1 row fails**:
//!   [`an_equation_subject_is_a_party_to_the_collision_too`].
//! * `<global>` AS A CANDIDATE — drop `head.scope == global` from the same filter.
//!   VERIFIED, **exactly 1 row fails**:
//!   [`a_global_head_is_not_a_party_to_the_collision`], on its imported-namespace arm.
//!   (A `<global>` row whose scopes are DECLARED cannot measure it at all — their heads
//!   denote, so none becomes a candidate — and three of them did not, which is why that
//!   row carries an undeclared arm.) This is the ONLY back-out for that exclusion: the group is the UNDIRECTED closure of
//!   reach, so the overlay test [`head_name_reach`] used to carry could not hold in the
//!   direction that matters, and once the candidate-set exclusion shipped it could not
//!   fire at all — measured at ZERO rows and deleted. `/code-review` caught both the dead
//!   code and this file's stale claim that it cost one row.
//! * THE PER-FILE OWNER — `edges[&other].contains(&cand)`, the per-SCOPE union of reach,
//!   in place of the per-file `all`. VERIFIED, **exactly 1 row fails**:
//!   [`a_named_owner_must_be_reachable_from_every_other_member`], on its reopened-scope
//!   arm.
//!
//! ONE LINE HAS NO TARGETED BACK-OUT, and it is said rather than credited to a
//! neighbour. Taking every candidate pair as an edge instead of asking
//! [`head_name_reach`] — the crude way to remove the visibility test — fails **2204**
//! rows, because the stdlib alone writes many head names at scopes that cannot see each
//! other, and it stops loading. So no row *isolates* that line;
//! [`two_scopes_that_cannot_see_each_other_keep_their_own`] is the cheapest single
//! witness for what it is FOR, and the 2204 is the measurement of what it costs to lose.
//!
//! Every row DRIVES its goal. A rule head that binds nowhere still loads clean, so "it
//! loads" would keep passing through exactly the regression this suite exists for.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// How many solutions `pattern` has — the ticket's own instrument ("resolving the goal
/// after load; counts are answers"). Goes through the shipped query-pattern path, so a
/// pattern whose functor lands on a different symbol resolves against that symbol's
/// clauses, exactly as `anthill query` would.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// The clauses stored under the symbol `qn` names, or `None` when nothing is named
/// `qn` at all — the PREDICATE IDENTITY half of the claim, which the answer counts
/// alone do not pin: a `Rec.p` that exists but is never reached would leave every
/// count unchanged.
fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

/// The `Int` a driven citation answered with. `eval::Value` carries no `PartialEq`, so
/// every row that drives an operation has to name the variant it expects.
fn int_value(v: anthill_core::eval::Value) -> i64 {
    match v {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("expected an Int, got {other:?}"),
    }
}

/// The REFUSED arm: `src` must fail with the collision naming exactly `scopes`.
fn assert_collides(sources: &[&str], name: &str, scopes: &[&str]) {
    let want = format!(
        "the rule head `{name}` introduces that name at {} scopes, each of which \
         reaches or is reached by another of them — {}",
        scopes.len(),
        scopes.join(", ")
    );
    crate::common::expect_load_errors(crate::common::try_load_kb_with_files(sources), &[&want]);
}

/// The SHARED arm: one declaration at `owner` collects every head, and the inner scope
/// introduces nothing. `inner_qn` is asserted ABSENT rather than merely unreached — that
/// is the difference between the two readings, since a split program has a real inner
/// symbol carrying a clause the outer predicate never sees.
fn assert_shared(kb: &mut KnowledgeBase, owner: &str, inner_qn: &str, total: usize) {
    assert_eq!(
        clauses(kb, &format!("{owner}.p")),
        Some(total),
        "`{owner}.p` must be ONE predicate carrying every clause"
    );
    assert_eq!(
        clauses(kb, inner_qn),
        None,
        "`{inner_qn}` must not exist — the declaration is what the inner head resolves to"
    );
    for n in 1..=total {
        assert_eq!(answers(kb, &format!("{owner}.p({n})")), 1, "{owner}.p({n})");
    }
}

// ── Channel 1: a sort body ──────────────────────────────────────────────────

fn sort_body(ns: &str, rule_first: bool, decl: &str) -> String {
    let outer = format!("{decl}  rule p(1) :- true\n");
    let inner = "  sort Rec\n    entity rec(n: Int64)\n    rule p(2) :- true\n  end\n";
    let body = if rule_first {
        format!("{outer}{inner}")
    } else {
        format!("{inner}{outer}")
    };
    format!("namespace {ns}\n{body}end\n")
}

#[test]
fn a_sort_body_and_its_namespace_must_declare_a_shared_name() {
    // THE SHAPE WI-980 OPENED WITH, and the one 845G7 changes the answer to. The sort's
    // head sees the namespace's through the ENCLOSING chain, so both introduce `p` and
    // the program does not say which owns it. Refused in BOTH text orders — a refusal
    // that fired in only one would be the order dependence WI-980 removed, wearing a
    // different hat.
    for (ns, first) in [("wi980.body1", true), ("wi980.body2", false)] {
        assert_collides(
            &[&sort_body(ns, first, "")],
            "p",
            &[ns, &format!("{ns}.Rec")],
        );
    }
    // DECLARED AT THE NAMESPACE — one predicate, both clauses, the sort's clause reached
    // THROUGH it. This is the reading the fixpoint used to reach by inference.
    for (ns, first) in [("wi980.body3", true), ("wi980.body4", false)] {
        let mut kb = crate::common::load_kb_with(&sort_body(ns, first, "  rule p(?x)\n"));
        assert_shared(&mut kb, ns, &format!("{ns}.Rec.p"), 2);
    }
    // DECLARED IN THE SORT TOO — two predicates, one clause each, which is the SPLIT this
    // rule refuses to invent. It is legal because it is written.
    let mut kb = crate::common::load_kb_with(
        "namespace wi980.body5\n  rule p(?x)\n  rule p(1) :- true\n  sort Rec\n    \
         entity rec(n: Int64)\n    rule p(?x)\n    rule p(2) :- true\n  end\nend\n",
    );
    assert_eq!(clauses(&kb, "wi980.body5.p"), Some(1));
    assert_eq!(clauses(&kb, "wi980.body5.Rec.p"), Some(1));
    assert_eq!(answers(&mut kb, "wi980.body5.p(2)"), 0, "the sort's clause is its own");
    assert_eq!(answers(&mut kb, "wi980.body5.Rec.p(2)"), 1);
}

// ── Channel 2: a nested ordinary namespace ──────────────────────────────────

fn nested_ns(ns: &str, rule_first: bool, decl: &str) -> String {
    let outer = format!("{decl}  rule p(1) :- true\n");
    let inner = "  namespace inner\n    rule p(2) :- true\n  end\n";
    let body = if rule_first {
        format!("{outer}{inner}")
    } else {
        format!("{inner}{outer}")
    };
    format!("namespace {ns}\n{body}end\n")
}

#[test]
fn a_nested_namespace_and_its_parent_must_declare_a_shared_name() {
    // THE INNER SCOPE IS NOT A SORT HERE, which is the point: the rule is about the
    // enclosing CHAIN, not about sort-ness, and a guard keyed on sorts would pass
    // channel 1 and miss this.
    for (ns, first) in [("wi980.nest1", true), ("wi980.nest2", false)] {
        assert_collides(
            &[&nested_ns(ns, first, "")],
            "p",
            &[ns, &format!("{ns}.inner")],
        );
    }
    for (ns, first) in [("wi980.nest3", true), ("wi980.nest4", false)] {
        let mut kb = crate::common::load_kb_with(&nested_ns(ns, first, "  rule p(?x)\n"));
        assert_shared(&mut kb, ns, &format!("{ns}.inner.p"), 2);
    }
}

// ── Channel 3: two FILES at one address, and the 061 file rule ──────────────

#[test]
fn one_scope_reopened_in_two_files_must_declare_its_predicate() {
    // 061'S OWN RULE, and the half of it 845G7 leaves untouched: this is ONE scope, so
    // there is no collision to report — what makes it a fault is that two FILES wrote it,
    // and a predicate assembled by two parties must be declared (059 §Definitions).
    //
    // IT IS ALSO THE ROW THAT SEPARATES THE TWO REFUSALS. Same address, same name, one
    // scope: the collision rule is silent and the file rule speaks. Channel 1's rows are
    // the mirror — one file, two scopes — and the collision rule speaks there instead.
    const A: &str = "namespace wi980.split\n  rule p(1) :- true\nend\n";
    const B: &str = "namespace wi980.split\n  rule p(2) :- true\nend\n";
    for files in [[A, B], [B, A]] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with_files(&files),
            &["has rule heads in 2 files"],
        );
    }
    const A_DECL: &str = "namespace wi980.split\n  rule p(?x)\n  rule p(1) :- true\nend\n";
    for files in [[A_DECL, B], [B, A_DECL]] {
        let mut kb =
            crate::common::expect_loaded(crate::common::try_load_kb_with_files(&files));
        assert_eq!(
            clauses(&kb, "wi980.split.p"),
            Some(2),
            "one predicate, one scope, both files"
        );
        assert_eq!(answers(&mut kb, "wi980.split.p(1)"), 1);
        assert_eq!(answers(&mut kb, "wi980.split.p(2)"), 1);
    }
}

// ── Channel 4: a `requires` parent ──────────────────────────────────────────

/// `Spec` is a `requires` parent of `A`, so `A`'s head sees `Spec`'s along an edge that
/// sits at no address — `deeper` puts `Spec` one level further down to show the guard is
/// not reading depth. `decl` goes into `Spec`.
fn requires_src(ns: &str, spec_first: bool, deeper: bool, decl: &str) -> String {
    let (spec_open, spec_close, spec_path) = if deeper {
        ("  namespace mid\n", "  end\n", format!("{ns}.mid.Spec"))
    } else {
        ("", "", format!("{ns}.Spec"))
    };
    // `Spec` CARRIES NO ENTITY, and that is not cosmetic: measured, adding one makes the
    // `requires` edge stop carrying the name — `Spec.p` and `A.p` split and the program
    // loads clean, under 845G7 and under the fixpoint alike. That is a pre-existing
    // silence about `requires` on a data sort, unchanged here and filed rather than
    // absorbed into this row (WI-20260822-845G7's own notes).
    let spec =
        format!("{spec_open}  sort Spec\n{decl}    rule p(1) :- true\n  end\n{spec_close}");
    let explicit = if decl.is_empty() {
        String::new()
    } else {
        format!("    import {spec_path}.{{p}}\n")
    };
    let a = format!(
        "  sort A\n    requires {spec_path}\n{explicit}    entity a(n: Int64)\n    rule p(2) :- true\n  end\n"
    );
    let body = if spec_first {
        format!("{spec}{a}")
    } else {
        format!("{a}{spec}")
    };
    format!("namespace {ns}\n{body}end\n")
}

#[test]
fn a_requires_parent_and_its_user_must_declare_a_shared_name() {
    // FOUR PROGRAMS, because the `requires` edge is the one a depth- or address-derived
    // key gets backwards: measured under the fixpoint, such a key left the same-depth
    // pair split in one order and joined in the other, and made the deeper pair WORSE
    // than plain text order. Asking the resolver makes the direction of the `requires`
    // edge the only thing that matters.
    for (ns, spec_first, deeper) in [
        ("wi980.rq1", true, false),
        ("wi980.rq2", false, false),
        ("wi980.rq3", true, true),
        ("wi980.rq4", false, true),
    ] {
        let spec = if deeper {
            format!("{ns}.mid.Spec")
        } else {
            format!("{ns}.Spec")
        };
        assert_collides(
            &[&requires_src(ns, spec_first, deeper, "")],
            "p",
            &[&format!("{ns}.A"), &spec],
        );
    }
    // DECLARED IN THE SPEC AND IMPORTED BY NAME — C666A makes the explicit import the
    // opt-in that turns `A`'s head into a clause of the spec predicate. `requires` alone
    // still drives the collision rows above, but cannot append an unguarded clause.
    for (ns, spec_first, deeper) in [
        ("wi980.rq5", true, false),
        ("wi980.rq6", false, false),
        ("wi980.rq7", true, true),
        ("wi980.rq8", false, true),
    ] {
        let mut kb =
            crate::common::load_kb_with(&requires_src(ns, spec_first, deeper, "    rule p(?x)\n"));
        let spec = if deeper {
            format!("{ns}.mid.Spec")
        } else {
            format!("{ns}.Spec")
        };
        assert_eq!(clauses(&kb, &format!("{spec}.p")), Some(2), "{spec}.p");
        assert_eq!(clauses(&kb, &format!("{ns}.A.p")), None, "{ns}.A.p");
        assert_eq!(answers(&mut kb, &format!("{spec}.p(2)")), 1, "{spec}.p(2)");
    }
}

// ── Channel 5: a facade importing its own submodule ─────────────────────────

#[test]
fn a_facade_and_its_submodule_must_declare_a_shared_name() {
    // TWO EDGES AT ONCE: `fa` sees `inner` through the wildcard import and `inner` sees
    // `fa` through the enclosing chain. Under the fixpoint §"outermost-first" named a
    // winner between them and this idiom kept joining silently; now it says so.
    //
    // THE SUGGESTED OWNER IS STILL THE FACADE, and that is worth driving: the reach is
    // mutual, so the sink test finds nothing and the message falls to the unique
    // ENCLOSING member. A cycle between siblings gets no owner instead — see
    // [`a_mutual_import_cycle_must_declare_a_shared_name`], whose message differs here.
    const TWO: &str = "namespace fa1\n  import fa1.inner.*\n  rule p(1) :- true\n  \
                       namespace inner\n    rule p(2) :- true\n  end\nend\n";
    assert_collides(&[TWO], "p", &["fa1", "fa1.inner"]);
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[TWO]),
        &["a body-less `rule p(…)` in 'fa1', with a named import of that predicate"],
    );
    // ONE LEVEL DEEPER — the control on the reach being the real one. Measured under an
    // earlier tie-break that scanned scopes by ADDRESS PREFIX, the two-level shape worked
    // and the three-level shape became a three-error refusal; a rule read off addresses
    // would still pass the row above.
    const THREE: &str = "namespace fa2\n  import fa2.inner.*\n  rule p(1) :- true\n  \
                         namespace inner\n    rule p(2) :- true\n    namespace deep\n      \
                         rule p(3) :- true\n    end\n  end\nend\n";
    assert_collides(&[THREE], "p", &["fa2", "fa2.inner", "fa2.inner.deep"]);
    // DECLARED AT THE FACADE — all three clauses, at any depth.
    const THREE_DECL: &str = "namespace fa3\n  import fa3.inner.*\n  rule p(?x)\n  \
                              rule p(1) :- true\n  namespace inner\n    rule p(2) :- true\n    \
                              namespace deep\n      rule p(3) :- true\n    end\n  end\nend\n";
    let mut kb = crate::common::load_kb_with(THREE_DECL);
    assert_shared(&mut kb, "fa3", "fa3.inner.p", 3);
    assert_eq!(clauses(&kb, "fa3.inner.deep.p"), None);
}

// ── Channel 6: wildcard imports between siblings ────────────────────────────

#[test]
fn a_mutual_import_cycle_must_declare_a_shared_name() {
    // WI-20260821-E85J5's shape, now the general rule rather than a special case. Neither
    // member encloses the other and each reaches the other, so NOTHING IN THE PROGRAM
    // names an owner — which the message has to say, and does: it offers no scope.
    //
    // ONE FILE AND TWO, both refused. E85J5 shipped the two-file half alone, on 059's
    // file unit; 845G7 widened it because the hazard here is shadowing rather than
    // assembly and one author is still one author who gets a meaning they did not write.
    const A: &str =
        "namespace mA\n  import mB.*\n  rule p(1) :- true\n  rule usesp(?x) :- p(?x)\nend\n";
    const B: &str = "namespace mB\n  import mA.*\n  rule p(2) :- true\nend\n";
    for files in [[A, B], [B, A]] {
        assert_collides(&files, "p", &["mA", "mB"]);
    }
    let one_file = format!("{A}{B}");
    assert_collides(&[&one_file], "p", &["mA", "mB"]);
    // AND AN OWNER *IS* NAMED, because in a mutual cycle EVERY member is reached by every
    // other — so declaring at either collects the whole group, and remedy 1 below drives
    // exactly that. The message names the first in display order, deterministically.
    // An earlier version of this row asserted "nothing names an owner" here; that was
    // true of the SINK test it was written against and false of the program.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[&one_file]),
        &["a body-less `rule p(…)` in 'mA', with a named import of that predicate"],
    );

    // REMEDY 1 — DECLARE IT ONCE, in `mA`, and name it from `mB`. C666A rejects the
    // wildcard-only spelling; the selective import is the explicit opt-in to append.
    const A_DECL: &str = concat!(
        "namespace mA\n  import mB.*\n  rule p(?x)\n  rule p(1) :- true\n",
        "  rule usesp(?x) :- p(?x)\nend\n"
    );
    const B_SELECTED: &str = "namespace mB\n  import mA.{p}\n  rule p(2) :- true\nend\n";
    let mut shared =
        crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[A_DECL, B_SELECTED]));
    assert_eq!(clauses(&shared, "mA.p"), Some(2), "one predicate, both clauses");
    assert_eq!(clauses(&shared, "mB.p"), None, "`mB` introduced nothing");
    assert_eq!(answers(&mut shared, "mA.usesp(1)"), 1);
    assert_eq!(
        answers(&mut shared, "mA.usesp(2)"),
        1,
        "the import is LIVE — this is the row that reads 0 under a silent split"
    );

    // REMEDY 2 — DECLARE IT IN EACH, which says they are separate predicates. THE SHADOW
    // IS BACK, and that is the point: E85J5 measured `usesp(2)`=0 against a control of 1,
    // and it is refused only when nobody wrote it. Here it is written.
    const B_OWN: &str = "namespace mB\n  import mA.*\n  rule p(?x)\n  rule p(2) :- true\nend\n";
    let mut split =
        crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[A_DECL, B_OWN]));
    assert_eq!(clauses(&split, "mA.p"), Some(1), "two predicates, one clause each");
    assert_eq!(clauses(&split, "mB.p"), Some(1));
    assert_eq!(answers(&mut split, "mA.usesp(1)"), 1, "its own clause is reached");
    assert_eq!(
        answers(&mut split, "mA.usesp(2)"),
        0,
        "and the imported one is NOT — the declared local shadows the import, as written"
    );
    // THE CONTROL for that 0: the same import with nothing local to shadow it.
    const A_NO_OWN: &str = "namespace mA\n  import mB.*\n  rule usesp(?x) :- p(?x)\nend\n";
    let mut ctrl =
        crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[A_NO_OWN, B]));
    assert_eq!(answers(&mut ctrl, "mA.usesp(2)"), 1, "CONTROL: the import works");
    assert_eq!(answers(&mut ctrl, "mA.usesp(1)"), 0, "CONTROL: nothing local exists");
}

#[test]
fn a_one_way_import_must_declare_a_shared_name_and_the_owner_is_named() {
    // ONE EDGE, SO THE PROGRAM DOES NAME AN OWNER — `mD` is what `mC` imports and reaches
    // nothing itself, so the message offers it. That is the difference from the cycle
    // above, driven rather than described: same two scopes, same two heads, one import
    // instead of two, and a different message.
    const C: &str = "namespace mC\n  import mD.*\n  rule p(1) :- true\n  rule usesp(?x) :- p(?x)\nend\n";
    const D: &str = "namespace mD\n  rule p(2) :- true\nend\n";
    for files in [[C, D], [D, C]] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with_files(&files),
            &["a body-less `rule p(…)` in 'mD', with a named import of that predicate"],
        );
    }
    // AND THE OWNER IT NAMES IS THE ONE THAT WORKS, with C666A's explicit opt-in.
    const C_SELECTED: &str = "namespace mC\n  import mD.{p}\n  rule p(1) :- true\n  rule usesp(?x) :- p(?x)\nend\n";
    const D_DECL: &str = "namespace mD\n  rule p(?x)\n  rule p(2) :- true\nend\n";
    let mut kb =
        crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[C_SELECTED, D_DECL]));
    assert_eq!(clauses(&kb, "mD.p"), Some(2), "one predicate, both clauses");
    assert_eq!(clauses(&kb, "mC.p"), None);
    assert_eq!(answers(&mut kb, "mC.usesp(1)"), 1);
    assert_eq!(answers(&mut kb, "mC.usesp(2)"), 1, "the import is live");
}

#[test]
fn a_named_owner_must_be_reachable_from_every_other_member() {
    // THE MESSAGE'S PROMISE IS PART OF THE MESSAGE. When it names a scope it says
    // declaring there, with C666A's named imports where needed, makes every head a
    // clause of it, so the test that
    // picks the scope is "IS REACHED BY EVERY OTHER MEMBER" — not "reaches nothing".
    // The two differ exactly where reach is NOT transitive, which a wildcard import
    // always is not: it is never re-exported.
    //
    // THE CHAIN IS THE WITNESS. `zzA -> zzB -> zzC`: the sink is `zzC` and `zzA` cannot
    // see it. MEASURED under the sink test, the message named `zzC`, and FOLLOWING IT
    // made the program load clean with `zzA.cp` still a separate predicate and NO error
    // at all — the split the refusal exists to prevent, reached by taking its own advice.
    // Found by `/code-review`.
    //
    // BACKED OUT (`.find(|&cand| edges[&cand].is_empty())` in place of the all-reach
    // test): this row fails on the first assertion — `zzC` is named.
    const A: &str = "namespace zzA\n  import zzB.*\n  rule cp(1) :- true\nend\n";
    const B: &str = "namespace zzB\n  import zzC.*\n  rule cp(2) :- true\nend\n";
    const C: &str = "namespace zzC\n  rule cp(3) :- true\nend\n";
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[A, B, C]),
        &["No one of them is reachable from all the others"],
    );
    // AND THE OLD DECLARATION-ONLY ADVICE IS NOW REFUSED BY C666A — the second half of
    // the same measurement. Declaring in `zzC` cannot silently absorb `zzB` while
    // leaving `zzA` split; the joining wildcard head is a located error.
    const C_DECL: &str = "namespace zzC\n  rule cp(?x)\n  rule cp(3) :- true\nend\n";
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[A, B, C_DECL]),
        &["the unguarded rule head `cp` in 'zzB' joins predicate 'zzC.cp'"],
    );
    // AND THE SAME PROMISE ACROSS FILES, not only across hops. `pwA` is reopened in two
    // files and only ONE carries `import pwB.*`, so `pwB` is reached from one of `pwA`'s
    // files and not the other. MEASURED with the reach UNIONED per scope, the message
    // named `pwB` — and following it made the program LOAD CLEAN with `pwB.p` holding one
    // clause and `pwA.p` holding two, the import-carrying head never joining and nothing
    // reported. Found by `/code-review`, one coordinate over from the hop case above.
    //
    // BACKED OUT (`edges[&other].contains(&cand)` — the per-SCOPE union — in place of the
    // per-file `all`): this arm fails, `pwB` being named again.
    const A1: &str = "namespace pwA\n  import pwB.*\n  rule p(1) :- true\nend\n";
    const A2: &str = "namespace pwA\n  rule p(9) :- true\nend\n";
    const PWB: &str = "namespace pwB\n  rule p(2) :- true\nend\n";
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[A1, A2, PWB]),
        &["No one of them is reachable from all the others"],
    );
    // ITS CONTROL — the same three files with the import in BOTH of `pwA`'s, so `pwB` is
    // reached from every file and may be named. The declaration then collects all three
    // clauses, which is the promise being kept.
    const A2I: &str = "namespace pwA\n  import pwB.*\n  rule p(9) :- true\nend\n";
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[A1, A2I, PWB]),
        &["a body-less `rule p(…)` in 'pwB', with a named import of that predicate"],
    );
    const PWB_DECL: &str = "namespace pwB\n  rule p(?x)\n  rule p(2) :- true\nend\n";
    const A1_SELECTED: &str = "namespace pwA\n  import pwB.{p}\n  rule p(1) :- true\nend\n";
    const A2_SELECTED: &str = "namespace pwA\n  import pwB.{p}\n  rule p(9) :- true\nend\n";
    let all3 = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        A1_SELECTED,
        A2_SELECTED,
        PWB_DECL,
    ]));
    assert_eq!(clauses(&all3, "pwB.p"), Some(3), "CONTROL: all three clauses");
    assert_eq!(clauses(&all3, "pwA.p"), None, "CONTROL");

    // THE CONTROL — the same three scopes where every one of them CAN see one place:
    // `zzD` imports `zzF` directly rather than through `zzE`, so `zzF` is reachable from
    // all and the message may name it. Without this row the assertion above would be
    // satisfied by never naming an owner at all.
    const D: &str = "namespace zzD\n  import zzF.*\n  rule cp(1) :- true\nend\n";
    const E: &str = "namespace zzE\n  import zzF.*\n  rule cp(2) :- true\nend\n";
    const F: &str = "namespace zzF\n  rule cp(3) :- true\nend\n";
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_files(&[D, E, F]),
        &["a body-less `rule cp(…)` in 'zzF', with a named import of that predicate"],
    );
    const F_DECL: &str = "namespace zzF\n  rule cp(?x)\n  rule cp(3) :- true\nend\n";
    const D_SELECTED: &str = "namespace zzD\n  import zzF.{cp}\n  rule cp(1) :- true\nend\n";
    const E_SELECTED: &str = "namespace zzE\n  import zzF.{cp}\n  rule cp(2) :- true\nend\n";
    let mut ok = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        D_SELECTED,
        E_SELECTED,
        F_DECL,
    ]));
    assert_eq!(clauses(&ok, "zzF.cp"), Some(3), "CONTROL: the promise is kept");
    assert_eq!(clauses(&ok, "zzD.cp"), None, "CONTROL");
    assert_eq!(clauses(&ok, "zzE.cp"), None, "CONTROL");
    assert_eq!(answers(&mut ok, "zzF.cp(1)"), 1, "CONTROL");
}

#[test]
fn an_equation_subject_is_a_party_to_the_collision_too() {
    // 061 PUTS EQUATIONS OUTSIDE THE *DECLARATION* RULE — their clauses index under the
    // connective, so the subject owns none — and an earlier cut of this rule took that to
    // mean they are outside the VISIBILITY rule too. MEASURED, that was a silent split:
    // before 845G7 `zeq.Rec.f` did not exist (the inner subject joined the enclosing one)
    // and with equations excluded it does, one name becoming two symbols with nothing
    // said. That is the hazard this refusal exists for, permitted for half the head
    // shapes. Found by `/code-review`.
    //
    // BACKED OUT (`head.introduced_by != RuleIntroduction::Predicate` back in the
    // candidate filter of `head_name_collisions`): this row's first arm fails — the
    // program loads and `zeq.Rec.f` exists.
    const SPLIT: &str = "namespace zeq\n  rule f(true) <=> 1 [simp]\n  sort Rec\n    \
                         entity r(n: Int64)\n    rule f(false) <=> 2 [simp]\n  end\nend\n";
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(SPLIT),
        &["the rule head `f` introduces that name at 2 scopes, each of which reaches or is reached by another of them — zeq, zeq.Rec"],
    );
    // AND THE PRESCRIPTION IS THE ONE THAT WORKS, which is a different sentence than it
    // was: WI-20260821-D0EXD measured that the body-less `rule` owner this message used
    // to name DOES NOT COLLECT an equation subject written in another scope — taking the
    // advice traded this error for `EquationSubjectNamesAPredicate`, and before that
    // refusal existed it produced a program where the sort's operation had silently moved
    // to the namespace. So the owner half now names an `operation`, which is what
    // equations define.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(SPLIT),
        &["an `operation f(…) -> R` in 'zeq' makes every one of those heads its own"],
    );
    // BOTH PRESCRIBED REMEDIES DRIVEN, not merely loaded — an arm that only asserts a
    // load is what let the broken owner stand here for a day. `zeq5` is the owner half,
    // `zeq6` the per-scope half; each must ANSWER through the citation the split arm
    // could not reach.
    let mut owned = crate::common::interp_for(
        "namespace zeq5\n  operation f(b: Bool) -> Int64\n  rule f(true) <=> 1 [simp]\n  \
         sort Rec\n    entity r(n: Int64)\n    rule f(false) <=> 2 [simp]\n  end\nend\n\
         namespace zeq5c\n  import zeq5.{f}\n  operation g() -> Int64 = f(false)\nend\n",
    );
    assert_eq!(
        int_value(owned.call("zeq5c.g", &[]).expect("the operation owner answers")),
        2,
        "the `operation` owner collects the SORT's equation"
    );
    let mut split = crate::common::interp_for(
        "namespace zeq6\n  rule f(?x)\n  rule f(true) <=> 1 [simp]\n  sort Rec\n    \
         entity r(n: Int64)\n    rule f(?y)\n    rule f(false) <=> 2 [simp]\n  end\nend\n\
         namespace zeq6c\n  import zeq6.{Rec}\n  operation g() -> Int64 = Rec.f(false)\nend\n",
    );
    assert_eq!(
        int_value(split.call("zeq6c.g", &[]).expect("the per-scope declaration answers")),
        2,
        "a declaration in EACH scope keeps the sort's equation AT the sort"
    );
    // AND THE OWNER THE MESSAGE NO LONGER NAMES IS REFUSED — the row that pins why the
    // sentence changed. Without it the two arms above would pass with the old text.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            "namespace zeq2\n  rule f(?x)\n  rule f(true) <=> 1 [simp]\n  sort Rec\n    \
             entity r(n: Int64)\n    rule f(false) <=> 2 [simp]\n  end\nend\n",
        ),
        &["the equation subject `f` names the RELATION `f` declared in 'zeq2'"],
    );
    // THE CONTROL — distinct subjects, nothing to collide. Passes either way, and without
    // it "equations are refused" would be indistinguishable from "equations are refused
    // whenever a sort has one".
    let kb = crate::common::load_kb_with(
        "namespace zeq4\n  rule f(true) <=> 1 [simp]\n  sort Rec\n    \
         entity r(n: Int64)\n    rule g(false) <=> 2 [simp]\n  end\nend\n",
    );
    assert!(kb.try_resolve_symbol("zeq4.Rec.g").is_some(), "CONTROL: the fresh subject exists");
}

// ── The controls ────────────────────────────────────────────────────────────

#[test]
fn two_scopes_that_cannot_see_each_other_keep_their_own() {
    // THE CONTROL THE WHOLE RULE RESTS ON, and the one row whose absence would let a
    // refusal keyed on "two scopes share a short name" look correct while refusing most
    // real programs. `uA` and `uB` are siblings with no import, no `requires` and no
    // enclosure between them: two unrelated predicates that happen to share a name.
    //
    // BOTH ORDERS AND BOTH SPELLINGS — one file and two — because the visibility question
    // must not be answered by adjacency in the text or by which file arrived first.
    //
    // BACKED OUT (take every candidate pair as an edge in `head_name_collisions`): this
    // row fails — and so do 2203 others, the stdlib included, which is why the header
    // says no row ISOLATES that line. This is the cheapest witness for what it is for,
    // not a measurement of it.
    const A: &str = "namespace uA\n  rule p(1) :- true\n  rule usesp(?x) :- p(?x)\nend\n";
    const B: &str = "namespace uB\n  rule p(2) :- true\n  rule usesp(?x) :- p(?x)\nend\n";
    let one_file = format!("{A}{B}");
    for sources in [vec![A, B], vec![B, A], vec![one_file.as_str()]] {
        let mut kb =
            crate::common::expect_loaded(crate::common::try_load_kb_with_files(&sources));
        assert_eq!(clauses(&kb, "uA.p"), Some(1), "each scope keeps its own");
        assert_eq!(clauses(&kb, "uB.p"), Some(1));
        assert_eq!(answers(&mut kb, "uA.usesp(1)"), 1, "and each reaches only its own");
        assert_eq!(answers(&mut kb, "uA.usesp(2)"), 0);
        assert_eq!(answers(&mut kb, "uB.usesp(2)"), 1);
        assert_eq!(answers(&mut kb, "uB.usesp(1)"), 0);
    }
}

#[test]
fn a_global_head_is_not_a_party_to_the_collision() {
    // `<global>` IS THE ONE SCOPE NOBODY OPTS INTO — every file shares it, so a head
    // written inside a namespace must not collide with a top-level one. Fusing the two
    // questions fails either way round, both measured under the fixpoint: treat
    // `<global>` as a party and the stdlib's `modus_ponens` ceases to exist beside a
    // one-line user file; refuse the pair and the language's own documented first form
    // stops loading ([`the_documented_top_level_form_loads`]).
    //
    // Two shapes reach it by another route and must not collide through it: a sibling
    // cycle (which is refused on its own terms, so it is written DECLARED here) and an
    // ordinary parent/child pair beside a top-level head of the same name.
    // THE ROW THAT ACTUALLY EXERCISES THE EXCLUSION, and it must come first: an
    // UNDECLARED namespace head beside an UNDECLARED top-level one. `nd` reaches
    // `<global>` through the enclosing chain, so without the exclusion the two collide
    // and this program is refused. FOUND BY MEASUREMENT — the arms below declare their
    // names, so their heads DENOTE, never become candidates, and cannot reach the
    // exclusion at all; backed out, they were all still green.
    const G: &str = "rule p(0) :- true\n";
    const ND: &str = "namespace nd\n  rule p(5) :- true\nend\n";
    for files in [[G, ND], [ND, G]] {
        let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&files));
        assert_eq!(clauses(&kb, "p"), Some(1), "the top-level head keeps its own");
        assert_eq!(clauses(&kb, "nd.p"), Some(1), "and the namespace head keeps its own");
        assert_eq!(answers(&mut kb, "nd.p(5)"), 1);
        assert_eq!(answers(&mut kb, "nd.p(0)"), 0, "two predicates, not one");
        assert_eq!(answers(&mut kb, "p(0)"), 1);
    }

    // AND THE EXCLUSION HOLDS IN THE OTHER DIRECTION TOO — the one an overlay-only
    // exclusion does NOT give you. The group is built on the UNDIRECTED closure of reach,
    // so a namespace-less file that writes `import zzns.*` and a head of the same name
    // pulled `zzns` into a group with `<global>` and the pair was REFUSED, contradicting
    // this section's own rule; worse, the repair it named deleted the `<global>` head's
    // predicate, which is the absorption the exclusion forbids. Found by `/code-review`,
    // and fixed by dropping `<global>` from the CANDIDATE SET rather than only from the
    // overlay.
    //
    // WHAT THAT COSTS IS A NAMED SILENCE, not a repair: the top-level head does shadow
    // `zzns.gp` for its own file, and nothing says so. `<global>` is the one scope where
    // the language has always taken that trade — nobody opts into it, so it can neither
    // absorb a namespace's name nor refuse one — and the two clause counts below are what
    // pin the trade rather than assume it.
    const NS_IMPORTED: &str = "namespace zzns\n  rule gp(1) :- true\nend\n";
    const G_IMPORTS: &str = "import zzns.*\nrule gp(2) :- true\n";
    for files in [[NS_IMPORTED, G_IMPORTS], [G_IMPORTS, NS_IMPORTED]] {
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&files));
        assert_eq!(clauses(&kb, "gp"), Some(1), "the top-level head keeps its own");
        assert_eq!(clauses(&kb, "zzns.gp"), Some(1), "and so does the namespace it imports");
    }

    const CYCLE: &str = concat!(
        "namespace mA\n  import mB.*\n  rule p(?x)\n  rule p(1) :- true\nend\n",
        "namespace mB\n  import mA.*\n  rule p(?x)\n  rule p(2) :- true\nend\n"
    );
    for files in [[G, CYCLE], [CYCLE, G]] {
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&files));
        assert_eq!(clauses(&kb, "p"), Some(1), "the global head keeps its own clause");
        assert_eq!(clauses(&kb, "mA.p"), Some(1));
        assert_eq!(clauses(&kb, "mB.p"), Some(1));
    }
    const N: &str = "namespace outer\n  rule p(?x)\n  rule p(1) :- true\n  sort Rec\n    \
                     entity r(n: Int64)\n    rule p(2) :- true\n  end\nend\n";
    for files in [[G, N], [N, G]] {
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&files));
        assert_eq!(clauses(&kb, "p"), Some(1));
        assert_eq!(
            clauses(&kb, "outer.p"),
            Some(2),
            "the declared join is unaffected by the top-level head"
        );
        assert_eq!(clauses(&kb, "outer.Rec.p"), None);
    }
}

#[test]
fn a_cycle_member_reopened_in_a_second_file_is_reported_once() {
    // BOTH REFUSALS CAN SEE THIS PROGRAM: `wA` and `wB` collide, and `wA`'s own heads
    // span two files. ONE MISSING DECLARATION IS ONE MESSAGE — the collision's repair
    // fixes the file question too, so the file rule yields to it. Reporting both prints
    // one fault twice and prescribes two different owners for it.
    //
    // FOUND BY `/code-review` under WI-20260821-E85J5, where the suppression ran the
    // other way round; 845G7 reversed it, because the collision is now the message that
    // names every scope involved while the file rule names only one.
    //
    // BACKED OUT (drop the `collided.contains(&(owner, name))` test in the file block):
    // this row fails with TWO errors. [`a_mutual_import_cycle_must_declare_a_shared_name`]
    // passes either way — no member there spans files — which is what shows the two
    // blocks ask different questions rather than one guarding the other.
    const F1: &str = concat!(
        "namespace wA\n  import wB.*\n  rule p(1) :- true\nend\n",
        "namespace wB\n  import wA.*\n  rule p(2) :- true\nend\n"
    );
    const F2: &str = "namespace wA\n  import wB.*\n  rule p(9) :- true\nend\n";
    assert_collides(&[F1, F2], "p", &["wA", "wB"]);
    // THE REPAIR. One declaration in `wA`, named explicitly by `wB`, collects all three
    // clauses. C666A makes that named import part of the prescription.
    const F1_DECL: &str = concat!(
        "namespace wA\n  import wB.*\n  rule p(?x)\n  rule p(1) :- true\nend\n",
        "namespace wB\n  import wA.{p}\n  rule p(2) :- true\nend\n"
    );
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[F1_DECL, F2]));
    assert_eq!(clauses(&kb, "wA.p"), Some(3), "one predicate, all three clauses");
    assert_eq!(clauses(&kb, "wB.p"), None, "`wB` introduced nothing");
}

#[test]
fn a_declared_cycle_is_the_same_program_in_every_file_order() {
    // ORDER-FREEDOM, over the shape that used to break it. Two mutually importing
    // namespaces and a nested scope under one of them: MEASURED before WI-980, four of
    // the six file orders gave `nA.p` = 3 clauses with `nB.p` ABSENT and the other two
    // gave 2 and 1, because a verdict computed under a provisional cycle break was
    // memoised and then read by a site outside the cycle.
    //
    // ALL SIX ORDERS, not two: the defect was invisible in four of them.
    //
    // IT IS NOW ORDER-FREE BY CONSTRUCTION rather than by a fixpoint — nothing is asked
    // about any other head — and the row is kept because that is a claim about the
    // finished program, not about the mechanism that used to produce it. The
    // declarations are what make the program legal to ask about at all: without them
    // `nA`, `nB` and `nA.sub` collide, in all six orders, which is itself order-free.
    const A: &str = "namespace nA\n  import nB.*\n  rule p(?x)\n  rule p(1) :- true\nend\n";
    const B: &str = "namespace nB\n  import nA.*\n  rule p(?x)\n  rule p(2) :- true\nend\n";
    const S: &str = "namespace nA.sub\n  rule p(3) :- true\nend\n";
    for order in [[A, B, S], [A, S, B], [B, A, S], [B, S, A], [S, A, B], [S, B, A]] {
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&order));
        assert_eq!(clauses(&kb, "nA.p"), Some(2), "nA.p, order {order:?}");
        assert_eq!(clauses(&kb, "nB.p"), Some(1), "nB.p, order {order:?}");
        assert_eq!(clauses(&kb, "nA.sub.p"), None, "nA.sub.p, order {order:?}");
    }
    // CONTROL — the nested scope writing a DIFFERENT name. One clause each, every order,
    // and it passes with or without the declarations: without it the rows above would be
    // satisfied by any change that stopped the two members joining at all.
    const S2: &str = "namespace nA.sub\n  rule qq(3) :- true\nend\n";
    for order in [[A, B, S2], [S2, A, B]] {
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&order));
        assert_eq!(clauses(&kb, "nA.p"), Some(1), "CONTROL nA.p");
        assert_eq!(clauses(&kb, "nB.p"), Some(1), "CONTROL nB.p");
    }
}

/// Far past any depth the RECURSIVE first version of this pass could reach — it nested a
/// whole resolver walk per link, and MEASURED, 700 chained scopes sharing one head name
/// ABORTED THE PROCESS (`thread … has overflowed its stack`, SIGABRT) while the same 700
/// with DISTINCT head names loaded clean.
const PAST_THE_OLD_LIMIT: usize = 260;

#[test]
fn a_chain_deeper_than_any_recursion_is_one_collision() {
    // NO BOUND, BECAUSE NO RECURSION — and since 845G7, no rounds either. The recursive
    // version needed an arbitrary `OWNERSHIP_MAX_DEPTH`, which bought a located error at
    // the price of refusing chains that used to load; the round-based fixpoint that
    // replaced it had no recursion but cost SUPER-QUADRATIC time (measured marginal
    // ownership time, min of 3 in-process runs: n=200 -> 0.68s, n=300 -> 2.33s,
    // n=400 -> 7.63s, an exponent of 4.1 over the last step). Neither exists now: each
    // scope answers for itself, one resolver call per (scope, file), and the components
    // are one iterative sweep.
    //
    // THE WHOLE CHAIN IS ONE COLLISION, and that is the right answer rather than a
    // convenience: `deepI` imports `deepI+1`, so each link sees the next, and the
    // transitive closure of that is a single group in which every member shadows the one
    // it imports. ONE error, not 260 — the fault is the undeclared name, not each link.
    //
    // AND IT NAMES NO OWNER, which is the whole point of the test that picks one. A
    // wildcard import is NOT re-exported, so `deep0` cannot see `deep260`: no scope in
    // this group is reachable from all the others, and any single declaration would
    // leave part of the chain split. An earlier cut named the far end — the SINK of the
    // direct reach graph — and measured, following that advice made the program load
    // clean with the near end still a separate predicate and no error at all. Found by
    // `/code-review`; this row is what pins the repair.
    //
    // BACKED OUT (take every candidate pair as an edge in `head_name_collisions` instead
    // of asking `head_name_reach`): this row still passes — the chain IS fully connected,
    // so the two agree. It is named here because this row alone would let that
    // distinction go unmeasured; the header records that no row isolates that line, and
    // that the crude back-out costs 2204.
    let n = PAST_THE_OLD_LIMIT;
    let mut files: Vec<String> = (0..n)
        .map(|i| {
            format!(
                "namespace deep{i}\n  import deep{}.*\n  rule p({i}) :- true\nend\n",
                i + 1
            )
        })
        .collect();
    files.push(format!("namespace deep{n}\n  rule p({n}) :- true\nend\n"));
    let refs: Vec<&str> = files.iter().map(|s| s.as_str()).collect();
    let errs = crate::common::try_load_kb_with_files(&refs)
        .err()
        .expect("every link introduces `p` and sees the next, so the chain must be refused");
    assert_eq!(errs.len(), 1, "ONE collision, not one per link: {errs:#?}");
    assert!(
        errs[0].contains(&format!("at {} scopes, each of which reaches", n + 1)),
        "every link is in the group: {:?}",
        errs[0]
    );
    assert!(
        errs[0].contains("No one of them is reachable from all the others"),
        "no single declaration repairs a chain, and the message must not promise one: {:?}",
        errs[0]
    );
    assert!(
        !errs[0].contains("makes every one of those heads a clause of it"),
        "in particular it must not name an owner: {:?}",
        errs[0]
    );
    // TRUNCATED, not listed: 261 addresses is a message nobody reads.
    assert!(errs[0].contains("… and 255 more"), "the list is capped: {:?}", errs[0]);
}

// ── Rows carried over: a head that RESOLVES never reaches this rule ─────────

#[test]
fn an_unmatched_inner_head_still_introduces() {
    // PASSES EITHER WAY, BY DESIGN — and it is why the rows above are evidence of a
    // BINDING rule rather than of a blanket one. Nothing named `q` encloses the sort,
    // so the inner head still introduces, still scoped where written (WI-894), and its
    // clause is still reachable there. A fix that made every inner head join an
    // enclosing scope would break this row and leave all six above green.
    let mut kb = crate::common::load_kb_with(
        "namespace wi980.fresh\n  rule p(1) :- true\n  sort Rec\n    entity rec(n: Int64)\n    \
         rule q(2) :- true\n  end\nend\n",
    );
    assert_eq!(clauses(&kb, "wi980.fresh.Rec.q"), Some(1));
    assert_eq!(clauses(&kb, "wi980.fresh.q"), None);
    assert_eq!(answers(&mut kb, "wi980.fresh.Rec.q(2)"), 1);
}

#[test]
fn a_head_that_binds_is_not_an_owner() {
    // THE ROW THAT MEASURES THE RECURSION, and without it nothing does — every other row
    // in this file passes with the overlay degraded to "a head is WRITTEN in that scope".
    //
    // `zdemo` WRITES a head named `q`, and does not OWN it: its head reaches `zlib.q`
    // through `zdemo`'s own `import zlib.*`, so nothing named `q` is created at `zdemo`.
    // The import is FILE-LOCAL (WI-995), so the third file cannot use it either — which
    // is why `Rec` must introduce its own `q` rather than yield to a scope holding
    // nothing. Reading the text instead of resolving it gets this exactly backwards.
    //
    // BACKED OUT (overlay reports `heads.contains_key(&(s, name))` instead of
    // `owns(s, name)`): this row FAILS — the whole program is refused, `Rec` having
    // yielded to a name that resolves nowhere for it. Every other row still passes.
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        // 061: `q`'s clauses are in TWO files, so it is DECLARED — the refusal without
        // the declaration is pinned in `wi_fqc85_rule_declaration_test::a_sibling_files_-
        // head_no_longer_moves_another_files_clause`, which runs this same program.
        "namespace zlib\n  rule q(?x)\n  rule q(1) :- true\nend\n",
        "namespace zdemo\n  import zlib.{q}\n  rule q(2) :- true\nend\n",
        "namespace zdemo\n  sort Rec\n    entity rec(n: Int64)\n    rule q(3) :- true\n  end\nend\n",
    ]));
    assert_eq!(
        clauses(&kb, "zlib.q"),
        Some(2),
        "the importing file's head is a clause of the imported predicate"
    );
    assert_eq!(
        clauses(&kb, "zdemo.q"),
        None,
        "`zdemo` writes a head of that name and holds nothing under it"
    );
    assert_eq!(
        clauses(&kb, "zdemo.Rec.q"),
        Some(1),
        "so the sibling file's inner head introduces its own"
    );
    // DRIVEN both ways: each predicate answers its own clauses and not the other's.
    assert_eq!(answers(&mut kb, "zlib.q(2)"), 1);
    assert_eq!(answers(&mut kb, "zlib.q(3)"), 0);
    assert_eq!(answers(&mut kb, "zdemo.Rec.q(3)"), 1);
}

#[test]
fn a_rule_in_a_secondary_entry_is_still_refused() {
    // WI-980 asks for the SECONDARY-ENTRY spelling as the second channel. It does not
    // load: WI-1000 shipped 059 R3 after this ticket was written. Pinned here so the
    // substitution ([`nested_namespace_rule_written_second`]) is recorded rather than
    // silent — if R3's blanket ban is ever narrowed (WI-1001), this row fails and the
    // spelling the ticket actually named becomes available as a fourth channel.
    //
    // PASSES EITHER WAY, BY DESIGN: sub-pass 1b refuses before sub-pass 3 runs at all.
    // THE TWO HEADS CARRY DIFFERENT NAMES, deliberately. R3 refuses the `rule` whatever
    // it is called; spelling both `p` would ALSO collide them (845G7) and this row would
    // pin two refusals while claiming to pin one.
    for order in [
        "  rule p(1) :- true\n  sort Rec\n    entity rec(n: Int64)\n  end\n  \
         namespace Rec\n    rule secondary(2) :- true\n  end\n",
        "  sort Rec\n    entity rec(n: Int64)\n  end\n  namespace Rec\n    \
         rule secondary(2) :- true\n  end\n  rule p(1) :- true\n",
    ] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with(&format!("namespace wi980.sec\n{order}end\n")),
            &["`rule` is not allowed in a secondary entry of sort 'wi980.sec.Rec'"],
        );
    }
}

#[test]
fn a_head_binds_through_its_own_files_import() {
    // 061: two files, one predicate — DECLARED. The asking file still decides, one
    // phase earlier: whether `b`'s head sees the declaration at all is
    // `rule_head_ladder_answer` asked on `b`'s behalf, through `b`'s OWN import.
    const LIB: &str = "namespace wi980_lib\n  rule q(?x)\n  rule q(1) :- true\nend\n";
    const IMPORTER: &str =
        "namespace wi980.viaimport.b\n  import wi980_lib.{q}\n  rule q(2) :- true\nend\n";
    // A third file, scanned LAST, so a stale asking-file is a DIFFERENT file's and the
    // row cannot pass by the two coinciding.
    const TRAILING: &str = "namespace wi980.viaimport.z\n  rule unrelated(3) :- true\nend\n";

    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        LIB, IMPORTER, TRAILING,
    ]));
    assert_eq!(
        clauses(&kb, "wi980_lib.q"),
        Some(2),
        "the importing file's head must join the imported predicate"
    );
    assert_eq!(
        clauses(&kb, "wi980.viaimport.b.q"),
        None,
        "`q` denotes in `b` through `b`'s OWN import, so the head introduces nothing"
    );
    assert_eq!(answers(&mut kb, "wi980_lib.q(2)"), 1);
}

#[test]
fn nobody_yields_to_a_scope_that_mints_nothing() {
    // A HEAD MUST NEVER YIELD TO A PREDICATE THAT WILL NOT EXIST. `fb` imports its own
    // submodule AND `ext`; it yields to `ext`, so `fb.p` is never minted. `sib`, which
    // imports `fb`, must therefore NOT yield to `fb`.
    //
    // MEASURED before the fix: REFUSED — "no scope introduces the rule head 'p' written
    // in 'sib' … it yields to 'fb', which does not introduce it either". The tie-break
    // had memoised `owns(fb, p) = true` as a POLICY, discarding the value the loop
    // computed, so the overlay advertised an owner the mint loop never created.
    //
    // THE CONTROL IS THE SAME PROGRAM WITHOUT `import fb.inner.*` — one line, and it is
    // what shows the refusal was never about `sib`: it loaded clean before and must give
    // the IDENTICAL answer now.
    //
    // BACKED OUT (`owners_for`'s rule 2 admits a scope that reaches any CANDIDATE rather
    // than a settled OWNER): this test FAILS — `sib` yields into the hole again.
    // 061 DECLARES `p` in `ext`, because its three clauses arrive from three files.
    // COLLAPSING THE THREE INTO ONE FILE WAS TRIED AND IS WRONG: measured, `ext.p` then
    // holds FOUR clauses — with every import in one file, `sib` reaches `ext` THROUGH
    // `fb`'s own `import ext.*`, and the non-transitivity this row depends on is a
    // consequence of file-locality (WI-995), not of the import graph. The declaration
    // keeps all three files and every answer below.
    const EXT: &str = "namespace ext\n  rule p(?x)\n  rule p(9) :- true\nend\n";
    const FB: &str = "namespace fb\n  import fb.inner.*\n  import ext.{p}\n  rule p(1) :- true\n  \
                      namespace inner\n    rule p(2) :- true\n  end\nend\n";
    const FB_CONTROL: &str = "namespace fb\n  import ext.{p}\n  rule p(1) :- true\n  \
                              namespace inner\n    rule p(2) :- true\n  end\nend\n";
    const SIB: &str = "namespace sib\n  import fb.*\n  rule p(3) :- true\nend\n";

    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[EXT, FB, SIB]));
    assert_eq!(clauses(&kb, "ext.p"), Some(3), "ext owns its own and both of fb's");
    assert_eq!(clauses(&kb, "fb.p"), None, "fb yields to ext, so it mints nothing");
    assert_eq!(clauses(&kb, "sib.p"), Some(1), "sib cannot see ext, so it introduces");

    let ctrl = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
        EXT,
        FB_CONTROL,
        SIB,
    ]));
    assert_eq!(clauses(&ctrl, "ext.p"), Some(3), "CONTROL: identical without the import");
    assert_eq!(clauses(&ctrl, "fb.p"), None, "CONTROL");
    assert_eq!(clauses(&ctrl, "sib.p"), Some(1), "CONTROL");
}

#[test]
fn a_top_level_head_beside_an_import_reports_rather_than_aborting() {
    // A HEAD CAN REACH TWO OWNERS, and until this was fixed that ABORTED THE PROCESS.
    // The decision asks the ladder through an overlay that EXCLUDES `<global>` (a head
    // inside a namespace never yields to a name every file shares), while the loader's
    // own resolver of course still sees it. So `nb`'s head was decided "a clause of
    // `nd.p`" and then, once minted, found BOTH — a genuine ambiguity.
    //
    // MEASURED before the fix: `debug_assert_eq!` at kb/mod.rs — "head functor … is a
    // non-canonical same-FQN copy of resolved symbol" — aborted the test binary in every
    // file order, because `push_ambiguous_symbol` answered with `intern(name)` and for a
    // TOP-LEVEL candidate the short name IS the qualified name. In release, where the
    // assert is compiled out, the clause was stored under a divergent functor that (in
    // that assert's own words) "silently no-matches in both rule-firing indexes".
    //
    // BACKED OUT (`push_ambiguous_symbol` returns `self.kb.symbols.intern(name)` again):
    // this test does not fail — it ABORTS the whole test binary.
    // 061 DECLARES `nd.p`, because `nb`'s clause joins it from a second file. Without
    // the declaration the program collects that refusal TOO, and the row would be
    // pinning two defects at once; the ambiguity is what it is about, and the
    // declaration is what leaves it alone on the page.
    const G: &str = "rule p(0) :- true\n";
    const D: &str = "namespace nd\n  rule p(?x)\n  rule p(5) :- true\nend\n";
    const B: &str = "namespace nb\n  import nd.*\n  rule p(93) :- true\nend\n";
    for order in [[G, D, B], [D, B, G], [B, G, D]] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with_files(&order),
            &["ambiguous symbol 'p' in scope 'nb'"],
        );
    }
}

#[test]
fn a_global_head_is_never_yielded_to() {
    // `<global>` HAS TWO ROLES AND THEY ARE NOT THE SAME. It may OWN a name written at
    // it — a namespace-less file is the language's own first form, taught by
    // kernel-language.md's `**Forms:**` block and by `examples/classic-mini/ancestor` —
    // and it must never be YIELDED TO, because it is the one scope every file in the
    // program shares and nobody opts into.
    //
    // MEASURED with the two fused: a one-line `rule modus_ponens(7, 8)` in a file with no
    // namespace made `anthill.logic.Constructive.Constructive.modus_ponens` CEASE TO
    // EXIST and put the stdlib's own axiom under the user's predicate, loading clean.
    // Fused the other way, a top-level head introduced NOTHING and fell to the WI-476
    // bare intern, silently.
    //
    // NO BACK-OUT REACHES THIS ROW ANY MORE, and that is said rather than credited to a
    // line. The measured claim above is the fixpoint's; under 845G7 the stdlib axiom is a
    // 061 DECLARATION, so the user's head DENOTES nothing at `<global>` and could not
    // absorb it whatever the exclusion did. The exclusion that IS live is the candidate
    // set's, and [`a_global_head_is_not_a_party_to_the_collision`] is what measures it.
    // An earlier version of this comment named `head_name_reach`'s overlay test and
    // claimed this row failed without it; that test was dead and this row does not.
    // Found by `/code-review`.
    let mut kb = crate::common::load_kb_with("rule modus_ponens(7, 8) :- true\n");
    // `Some(0)`, not `Some(1)`, since 061: the stdlib's intuitionistic axioms are
    // DECLARATIONS — a rule with no body, which their own file has always described as
    // "named symbols" rather than facts. The row's discrimination is unchanged and is
    // exactly the empty-versus-absent one: with `<global>`'s two roles fused this read
    // `None` / `Some(2)`.
    assert_eq!(
        clauses(&kb, "anthill.logic.Constructive.Constructive.modus_ponens"),
        Some(0),
        "the stdlib axiom keeps its own predicate — declared, with no clauses"
    );
    assert_eq!(
        clauses(&kb, "modus_ponens"),
        Some(1),
        "and the top-level head owns the name it wrote, at `<global>`"
    );
    assert_ne!(
        kb.try_resolve_symbol("modus_ponens"),
        kb.try_resolve_symbol("anthill.logic.Constructive.Constructive.modus_ponens"),
        "two names, two symbols"
    );
    // THE CLAUSE COUNTS ARE THE MEASUREMENT, not a goal, and that is a limit of this
    // row rather than an omission. The stdlib axiom is GENERAL — its head has variables
    // — so it matches any pair a query could carry, and a goal cannot tell "answered by
    // its own clause" from "answered by the user's". `Some(1)` / `Some(1)` is what
    // discriminates: with the two roles fused it read `None` / `Some(2)`.
    assert_eq!(answers(&mut kb, "modus_ponens(7, 8)"), 1);
}

#[test]
fn the_documented_top_level_form_loads() {
    // kernel-language.md's `**Forms:**` block and `examples/classic-mini/ancestor/
    // README.md` both teach a namespace-less program. PASSES EITHER WAY today; it is
    // here because an earlier attempt at the row above REFUSED this shape, and five
    // documentation sites teach it.
    let mut kb = crate::common::load_kb_with(
        "rule parent(\"alice\", \"bob\") :- true\nrule ancestor(?x, ?z) :- parent(?x, ?z)\n",
    );
    assert_eq!(clauses(&kb, "parent"), Some(1));
    assert_eq!(clauses(&kb, "ancestor"), Some(1));
    assert_eq!(answers(&mut kb, "ancestor(\"alice\", \"bob\")"), 1);
}

#[test]
fn the_captured_stdlib_predicate_survives() {
    // THE CONTROL FOR THE YIELD RULE — PASSES EITHER WAY, BY DESIGN, and it is here to
    // bound that rule rather than to measure it. The same short name, written inside a
    // namespace, must still be an ordinary new predicate: the stdlib axiom keeps its own
    // qualified name and its one clause, and the user gets one of their own. A guard
    // keyed on the NAME rather than on the SCOPE would break this row and leave
    // [`a_global_head_is_never_yielded_to`] green — which is what makes the pair a pair.
    //
    // NOTHING HERE IS REFUSED, and an earlier version of this comment said otherwise —
    // it described the capture's program as "now refused" and this section as "the shape
    // that is refused rather than decided". There is no such refusal: WI-980 replaced it
    // with the two-roles rule, and BOTH rows in this section load through
    // `load_kb_with`, which panics on any load error. The guard that actually stands
    // behind them is the `head.scope == global` test in `head_name_collisions`'s
    // named here because the stale wording left it unattributed. The capture itself is
    // what [`a_global_head_is_never_yielded_to`] measures, from a KB that loads.
    let kb = crate::common::load_kb_with("namespace wi980.ok\n  rule modus_ponens(7, 8) :- true\nend\n");
    assert_eq!(
        clauses(&kb, "anthill.logic.Constructive.Constructive.modus_ponens"),
        Some(0),
        "the stdlib axiom keeps its own predicate — a 061 DECLARATION, so no clauses"
    );
    assert_eq!(clauses(&kb, "wi980.ok.modus_ponens"), Some(1));
}
