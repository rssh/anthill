//! WI-20261024-RMZQZ — WHAT PASS 1 DEFINES FOR A RULE IN A HOST `provides … language …
//! end` BLOCK IS DEFINED AT THE BLOCK'S TARGET SORT.
//!
//! A host block's clauses load in its target sort's scope (§10.2), and so do the names
//! its heads introduce (WI-20260821-TTHRK). Pass 1 defines a rule's label and the
//! predicate a body-less rule declares where the rule is written, and it cannot do that
//! for a host block: the target is known only once imports and alias heads are (sub-pass
//! 2b). Before this ticket neither was defined there. A labeled rule in a host block did
//! not load ("unresolved name 'law'"), with one head or several; and a declaration in one
//! was not a declaration to proposal 061, which then refused a predicate with clauses in
//! two files as undeclared. Sub-pass 2c defines both at the target, and wires the
//! imports sub-pass 2 deferred that name one, as it would have wired them had the name
//! been written in the sort's body.
//!
//! ── WHICH ROWS FAIL WHEN WHAT IS BACKED OUT ─────────────────────────────────
//!
//! Each back-out applied to `kb/load.rs`, this file and the NE0E4 suite run in a
//! temporary binary (36 rows, all green at baseline); MEASURED 2026-10-30.
//!
//! **BACK-OUT 1 — NO SUB-PASS 2C** (the state before this ticket). FAILS every row here
//! but [`a_block_whose_target_names_nothing_is_refused_once`], and NE0E4's `a_host_block_multi_head_rules_label_cites_the_scoped_clauses`. The
//! label rows fail on the ticket's load error but
//! [`the_enclosing_namespaces_label_does_not_take_a_host_blocks_rule`], which LOADS
//! CLEAN: the namespace's own `law` is visible from the target sort, so the host block's
//! rule was filed under it, and the namespace's label cited two rules of two scopes.
//!
//! **BACK-OUT 2 — DEFINE WHERE THE BLOCK IS WRITTEN** (sub-pass 2c defining at the
//! enclosing scope, as pass 1 does). FAILS the same eight. Where the target sort is
//! nested in the namespace the block is written in, a labeled rule loads, the label
//! resolving through the enclosing scope, and the sort's own label cites nothing; the
//! imported target does not see that namespace and fails on the load error.
//!
//! **BACK-OUT 3 — LABELS ONLY** (sub-pass 2c skipping a rule with no label, so a
//! declaration is not defined). FAILS
//! [`a_declaration_in_a_host_block_declares_its_predicate_for_every_file`] alone.
//!
//! **BACK-OUT 4 — NO IMPORT RETRY** (`wire_imports_of_host_block_names` not called).
//! FAILS [`a_host_block_name_is_imported_as_a_sort_bodys_is`] alone.
//!
//! **BACK-OUT 5 — LOAD A BLOCK WHOSE TARGET NAMES NOTHING** (`load_provides_block`'s
//! early return removed). FAILS [`a_block_whose_target_names_nothing_is_refused_once`]
//! alone, with three errors.
//!
//! PASS EITHER WAY, BY DESIGN: the other 27 rows of NE0E4.

use anthill_core::kb::KnowledgeBase;

/// DEFINITE answers to the unary predicate `qn`.
fn answers(kb: &mut KnowledgeBase, qn: &str) -> usize {
    crate::common::definite_unary(kb, qn).len()
}

/// The stored clauses a label `label` cites — empty when nothing is named `label`.
fn cited(kb: &KnowledgeBase, label: &str) -> Vec<usize> {
    let mut ids: Vec<usize> = kb
        .rule_ids_by_qn(label)
        .into_iter()
        .map(|r| r.index())
        .collect();
    ids.sort();
    ids
}

/// The clauses stored under the predicates `qns`.
fn stored(kb: &KnowledgeBase, qns: &[&str]) -> Vec<usize> {
    let mut ids: Vec<usize> = qns
        .iter()
        .flat_map(|qn| {
            let sym = kb
                .try_resolve_symbol(qn)
                .unwrap_or_else(|| panic!("`{qn}` names the head's predicate"));
            kb.rules_by_functor(sym)
        })
        .map(|r| r.index())
        .collect();
    ids.sort();
    ids
}

#[test]
fn a_labeled_rule_in_a_host_block_loads_and_cites_its_clause() {
    let src = "namespace zzRMZ.one\n  sort RecP\n    entity P(v: Int64)\n    \
               rule see(?x) :- pick(?x)\n  end\n  provides RecP language rust\n    \
               artifact \"x.rs\"\n    rule law: pick(1) :- true\n  end\nend\n";
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(answers(&mut kb, "zzRMZ.one.RecP.see"), 1, "the clause is the sort's");
    let law = cited(&kb, "zzRMZ.one.RecP.law");
    assert_eq!(law.len(), 1, "the label is defined at the target sort and cites the rule");
    assert_eq!(law, stored(&kb, &["zzRMZ.one.RecP.pick"]), "and that rule is the sort's clause");
    assert!(
        kb.try_resolve_symbol("zzRMZ.one.law").is_none(),
        "the label is not defined where the block is written"
    );
}

#[test]
fn two_carriers_blocks_writing_one_label_do_not_collide() {
    let src = "namespace zzRMZ.two\n  sort RecP\n    entity P(v: Int64)\n    \
               rule see(?x) :- pick(?x)\n  end\n  sort RecQ\n    entity Q(v: Int64)\n    \
               rule see(?x) :- pick(?x)\n  end\n  provides RecP language rust\n    \
               artifact \"x.rs\"\n    rule law: pick(1) :- true\n  end\n  \
               provides RecQ language rust\n    artifact \"y.rs\"\n    \
               rule law: pick(2), pick(3) :- true\n  end\nend\n";
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        (answers(&mut kb, "zzRMZ.two.RecP.see"), answers(&mut kb, "zzRMZ.two.RecQ.see")),
        (1, 2),
        "each carrier reads its own block's clauses"
    );
    let (p, q) = (cited(&kb, "zzRMZ.two.RecP.law"), cited(&kb, "zzRMZ.two.RecQ.law"));
    assert_eq!(p, stored(&kb, &["zzRMZ.two.RecP.pick"]), "RecP's label cites RecP's clause");
    assert_eq!(q, stored(&kb, &["zzRMZ.two.RecQ.pick"]), "RecQ's cites RecQ's two");
    assert_eq!((p.len(), q.len()), (1, 2), "and the two labels are two");
}

#[test]
fn the_enclosing_namespaces_label_does_not_take_a_host_blocks_rule() {
    let src = "namespace zzRMZ.ns\n  rule law: other(1) :- true\n  sort RecP\n    \
               entity P(v: Int64)\n    rule see(?x) :- pick(?x)\n  end\n  \
               provides RecP language rust\n    artifact \"x.rs\"\n    \
               rule law: pick(1) :- true\n  end\nend\n";
    let kb = crate::common::load_kb_with(src);
    assert_eq!(
        cited(&kb, "zzRMZ.ns.law"),
        stored(&kb, &["zzRMZ.ns.other"]),
        "the namespace's label cites its own rule only"
    );
    assert_eq!(
        cited(&kb, "zzRMZ.ns.RecP.law"),
        stored(&kb, &["zzRMZ.ns.RecP.pick"]),
        "and the host block's label is the sort's own"
    );
}

#[test]
fn a_rule_block_in_a_host_block_labels_each_entry() {
    let src = "namespace zzRMZ.blk\n  sort RecP\n    entity P(v: Int64)\n    \
               rule see(?x) :- pick(?x)\n  end\n  provides RecP language rust\n    \
               artifact \"x.rs\"\n    rule {\n      law: pick(1) :- true\n      \
               law2: pick(2), pock(1) :- true\n    }\n  end\nend\n";
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(answers(&mut kb, "zzRMZ.blk.RecP.see"), 2);
    let all = stored(&kb, &["zzRMZ.blk.RecP.pick", "zzRMZ.blk.RecP.pock"]);
    let (law, law2) = (cited(&kb, "zzRMZ.blk.RecP.law"), cited(&kb, "zzRMZ.blk.RecP.law2"));
    assert_eq!((law.len(), law2.len()), (1, 2), "one clause, then one per head");
    let mut both: Vec<usize> = law.into_iter().chain(law2).collect();
    both.sort();
    assert_eq!(both, all, "and together they are the sort's clauses");
}

#[test]
fn the_label_lands_where_the_clauses_land_however_the_target_is_written() {
    // The target is asked as the head census asks it (`host_block_target`): through an
    // import, through an alias, and as the base of a parameterized spec.
    for (case, decl, target) in [
        ("imported", "", "Rec"),
        ("alias", "  sort RecA = Rec\n", "RecA"),
        ("applied", "", "Rec[T = Int64]"),
    ] {
        let src = format!(
            "namespace zzRMZ.lib\n  sort Rec[T]\n    entity E(v: T)\n    \
             rule see(?x) :- pick(?x)\n  end\nend\n\
             namespace zzRMZ.side_{case}\n  import zzRMZ.lib.{{Rec}}\n{decl}  \
             provides {target} language rust\n    artifact \"x.rs\"\n    \
             rule law: pick(1) :- true\n  end\nend\n"
        );
        let mut kb = crate::common::load_kb_with(&src);
        assert_eq!(answers(&mut kb, "zzRMZ.lib.Rec.see"), 1, "{case}");
        assert_eq!(
            cited(&kb, "zzRMZ.lib.Rec.law"),
            stored(&kb, &["zzRMZ.lib.Rec.pick"]),
            "{case}: the label is the target sort's"
        );
    }
}

#[test]
fn a_declaration_in_a_host_block_declares_its_predicate_for_every_file() {
    // A predicate with clauses in two files must be declared (proposal 061). Written in
    // a host block, the declaration is the target sort's, as the block's clauses are.
    let a = "namespace zzRMZ.d2\n  sort RecP\n    entity P(v: Int64)\n    \
             rule see(?x) :- pick(?x)\n  end\n  provides RecP language rust\n    \
             artifact \"x.rs\"\n    rule pick(?x)\n    rule pick(1) :- true\n  end\nend\n";
    let b = "namespace zzRMZ.d2\n  provides RecP language cpp\n    artifact \"x.cpp\"\n    \
             rule pick(2) :- true\n  end\nend\n";
    let mut kb = crate::common::load_kb_with_user_files(&[
        crate::common::UserFile::Text(a),
        crate::common::UserFile::Text(b),
    ]);
    assert_eq!(answers(&mut kb, "zzRMZ.d2.RecP.see"), 2, "both files' clauses answer");
}

#[test]
fn a_host_block_name_is_imported_as_a_sort_bodys_is() {
    // A label and a declared predicate written in a host block are imported by every form
    // that imports them from the sort's own body: plain, selective, and selective one
    // scope below the base.
    let lib = "namespace zzRMZ.imp\n  sort RecP\n    entity P(v: Int64)\n  end\n  \
               provides RecP language rust\n    artifact \"x.rs\"\n    \
               rule law: pick(1) :- true\n    rule pock(?x)\n    rule pock(5) :- true\n  \
               end\nend\n";
    for (case, imports) in [
        ("plain", "import zzRMZ.imp.RecP.pock\n  import zzRMZ.imp.RecP.law"),
        ("selective", "import zzRMZ.imp.RecP.{pock, law}"),
        ("one scope below", "import zzRMZ.imp.{pock, law}"),
    ] {
        let src = format!(
            "{lib}namespace zzRMZ.use\n  {imports}\n  rule see(?x) :- pock(?x)\nend\n"
        );
        let mut kb = crate::common::load_kb_with(&src);
        assert_eq!(answers(&mut kb, "zzRMZ.use.see"), 1, "{case}: the import reaches `pock`");
    }
    // The control: a name the block does not define is still refused.
    let errors = crate::common::load_errors_of(&format!(
        "{lib}namespace zzRMZ.use\n  import zzRMZ.imp.RecP.{{nosuch}}\nend\n"
    ));
    assert!(
        errors.iter().any(|e| e.contains("unresolved import 'zzRMZ.imp.RecP.nosuch'")),
        "{errors:?}"
    );
}

#[test]
fn a_block_whose_target_names_nothing_is_refused_once() {
    // The target is the fault. Its rules have no sort to load in, so they are not loaded
    // and draw no error of their own; before, each label was reported unresolved "in
    // scope 'Missing'", and a mapping as an operation `Missing` does not declare.
    let errors = crate::common::load_errors_of(
        "namespace zzRMZ.miss\n  provides Missing language rust\n    artifact \"x.rs\"\n    \
         operation_map { foo: \"bar\" }\n    rule law: pick(1) :- true\n  end\nend\n",
    );
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("unresolved name 'Missing'"), "{errors:?}");
}
