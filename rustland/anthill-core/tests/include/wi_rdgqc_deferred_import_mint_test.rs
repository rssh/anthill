//! A DEFERRED SELECTIVE PREDICATE IMPORT REACHES THE MINT GUARD — so a head of the
//! imported name is a CLAUSE of what was imported, not a predicate of its own.
//!
//! THE DEFECT, and it is older than the ticket that found it (WI-20260821-RDGQC, while
//! measuring something else). A selective import of a PREDICATE is deferred to sub-pass
//! 4, because its target may not be minted until sub-pass 3 has run. Sub-pass 3 is the
//! MINT. So at mint time `import X.Rec.{freshp}` had not been wired into `Side`, the
//! ladder answered "nothing here means `freshp`", and a `freshp` head written there
//! declared a predicate of its own — leaving the import DEAD and the author's clause
//! silently attached to a different predicate from the one they named. On a program that
//! loads clean.
//!
//! IT IS NOT A CYCLE, which is why the guard can be a guard rather than a reordering.
//! The pending import names a QUALIFIED TARGET (`X.Rec.freshp`); the head would mint a
//! DIFFERENT name (`Side.freshp`); and `pending` is complete before sub-pass 3, the whole
//! pass-2 loop having run. So "did the author import this name into this scope" is
//! order-free — the property WI-980 rewrote this pass to have, and the reason the fix is
//! not the load-order change it first looked like.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! Drop the `|| pending_import_brings_in(…)` leg from the `denotes` computation in
//! `scan_definitions_with_sources`. **BOTH ROWS FAIL**, each on a different assertion:
//! [`a_head_under_a_deferred_selective_import_joins_what_was_imported`] finds
//! `Side.freshp` holding the clause (the import dead), and
//! [`the_import_is_what_decides_not_the_spelling`]'s control arm stops being refused.
//!
//! WRITTEN WITHOUT THE `fact` SPELLING, deliberately: the `rule … :- true` spelling is
//! the one that carried this defect, and a `fact` head dodged it for a reason that has
//! since gone away (it declared nothing at all). Driving the `rule` spelling keeps this
//! file measuring THIS fix rather than that one.

use anthill_core::kb::KnowledgeBase;

/// The clauses stored under `qn` — `None` when nothing is named `qn` at all, which is
/// the distinction this file is about.
fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

/// `Side` imports `Rec.freshp` BY NAME and writes a clause at it. The clause is
/// `Rec.freshp`'s, and `Side` declares nothing.
#[test]
fn a_head_under_a_deferred_selective_import_joins_what_was_imported() {
    // No secondary entry here, so 059 R3 has nothing to say and this row measures the
    // MINT alone — `Side` is an ordinary namespace beside the type.
    let src = "namespace dfi.plain\n  import anthill.prelude.{Int64}\n  \
               sort Rec\n    entity rec(n: Int64)\n    rule freshp(1) :- true\n  end\n  \
               namespace Side\n    import dfi.plain.Rec.{freshp}\n    \
               rule freshp(2) :- true\n  end\nend\n";
    let kb = crate::common::load_kb_with(src);
    assert_eq!(
        clauses(&kb, "dfi.plain.Rec.freshp"),
        Some(2),
        "the imported predicate holds BOTH clauses — the import is what the head named"
    );
    assert_eq!(
        clauses(&kb, "dfi.plain.Side.freshp"),
        None,
        "and `Side` declared nothing: a head under an import of that name REFERENCES"
    );
}

/// THE CONTROL THAT SAYS THE AXIS IS THE IMPORT. Without the import line, the same head
/// in the same scope DOES declare its own predicate — which is WI-894's rule working,
/// not the defect — and the two scopes then hold one clause each.
#[test]
fn the_import_is_what_decides_not_the_spelling() {
    let no_import = "namespace dfi.ctl\n  import anthill.prelude.{Int64}\n  \
                     sort Rec\n    entity rec(n: Int64)\n    rule freshp(1) :- true\n  end\n  \
                     namespace Side\n    rule freshp(2) :- true\n  end\nend\n";
    let kb = crate::common::load_kb_with(no_import);
    assert_eq!(
        clauses(&kb, "dfi.ctl.Rec.freshp"),
        Some(1),
        "no import, so the type's predicate keeps only its own clause"
    );
    assert_eq!(
        clauses(&kb, "dfi.ctl.Side.freshp"),
        Some(1),
        "and `Side` declares its own — the head is scoped where it is written (WI-894)"
    );

    // AND THE CONSEQUENCE FOR OWNERSHIP, which is what made the defect matter rather
    // than merely differ: with the import, the clause lands on the TYPE's predicate from
    // a second party's text, and 059 R3 refuses that assembly. Before the guard this
    // program loaded clean, because the clause never got there.
    let secondary = "namespace dfi.r3\n  import anthill.prelude.{Int64}\n  \
                     sort Rec\n    entity rec(n: Int64)\n  end\n  \
                     namespace Side\n    import dfi.r3.Rec.{freshp}\n    \
                     rule freshp(2) :- true\n  end\n  \
                     namespace Rec\n    rule freshp(1) :- true\n  end\nend\n";
    let errs = crate::common::try_load_kb_with(secondary)
        .err()
        .unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("assembled from more than one entry")
            && e.contains("'dfi.r3.Side'")),
        "R3 must refuse the cross-entry assembly the import creates; got {errs:#?}"
    );
}
