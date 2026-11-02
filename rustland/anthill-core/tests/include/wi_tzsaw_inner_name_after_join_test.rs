//! WI-20260821-TZSAW — a head that joins an enclosing declaration names nothing at its
//! own scope, and a third file citing that name is refused.
//!
//! `glib.S`'s head `p(1) :- true` declares `glib.S.p` while nothing enclosing declares
//! `p`. Once a sibling file declares `p` at `glib`, the same unchanged head resolves to
//! `glib.p` through the enclosing chain and is a clause of it (kernel-language.md
//! §"A declaration and an explicit path are what join scopes"), so `glib.S.p` is not a
//! name and `import glib.S.{p}` / `glib.S.p(?x)` in a file that names neither is refused.
//! The user chose this reading (2026-11-02) over keeping `glib.S.p` as a second name for
//! `glib.p`: a library that publishes `S.p` declares it in `S`.
//!
//! The ticket's own program, with the sibling's clause UNDECLARED, no longer reaches the
//! citing file at all: two scopes that see each other both introduce `p`, which is the
//! visibility refusal at the library's head. The ticket wrote its clauses body-less
//! (`rule p(1)`); since 061 that spelling declares and asserts nothing, so every clause
//! here is `rule p(n) :- true`, which is what the ticket meant.
//!
//! The refusal's first repair is the declaration that removes `glib.S.p`, so its text now
//! says so ("no other of those scopes then has a `p` of its own").
//!
//! BACK-OUT, measured. The head rule is not changed here; the rows pin what it gives,
//! measured against the mechanism they read — fqc85's THE PASS-1 MINT (in `scan_rule`,
//! gate the `RuleReading::Declaration` mint off): 2 of the 3 rows fail, each on the
//! visibility refusal; `an_undeclared_sibling_is_refused_at_the_library_heads` passes by
//! design. Removing the new clause from the refusal's text fails that row alone.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

const LIB_SORT: &str = "namespace glib\n  sort S\n    entity s(n: Int64)\n    \
                        rule p(1) :- true\n  end\nend\n";
const LIB_SORT_DECLARED: &str = "namespace glib\n  sort S\n    entity s(n: Int64)\n    \
                                 rule p(?x)\n    rule p(1) :- true\n  end\nend\n";
const LIB_SIBLING: &str = "namespace glib\n  rule p(2) :- true\nend\n";
const LIB_SIBLING_DECLARED: &str = "namespace glib\n  rule p(?x)\n  rule p(2) :- true\nend\n";
const USER_IMPORT: &str = "namespace guser\n  import glib.S.{p}\n  rule uses(?x) :- p(?x)\nend\n";
const USER_QUALIFIED: &str = "namespace guse2\n  rule uses(?x) :- glib.S.p(?x)\nend\n";

fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

#[test]
fn a_declaration_at_the_enclosing_scope_leaves_the_inner_scope_no_name() {
    // CONTROL — nothing encloses a declaration of `p`, so `S`'s head declares `glib.S.p`
    // and both citations answer its clause. Passes under the back-out by design.
    let mut ctrl = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        ("a.anthill", LIB_SORT),
        ("c.anthill", USER_IMPORT),
        ("c2.anthill", USER_QUALIFIED),
    ]));
    assert_eq!(clauses(&ctrl, "glib.S.p"), Some(1));
    assert_eq!(
        answers(&mut ctrl, "guser.uses(1)"),
        1,
        "CONTROL: the import answers"
    );
    assert_eq!(
        answers(&mut ctrl, "guse2.uses(1)"),
        1,
        "CONTROL: the qualified goal answers"
    );

    // THE JOIN — `a.anthill` unchanged, a sibling file declares `p` at `glib`: one
    // predicate, both clauses, and no `glib.S.p`. FAILS under the back-out: the sibling's
    // declaration is not minted before the heads are read, so the two heads introduce at
    // `glib` and `glib.S` and the pair is the visibility refusal.
    let mut joined = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        ("a.anthill", LIB_SORT),
        ("b.anthill", LIB_SIBLING_DECLARED),
    ]));
    assert_eq!(
        clauses(&joined, "glib.p"),
        Some(2),
        "one predicate, both clauses"
    );
    assert_eq!(
        clauses(&joined, "glib.S.p"),
        None,
        "`S`'s head declared nothing at `S`"
    );
    assert_eq!(answers(&mut joined, "glib.p(1)"), 1);
    assert_eq!(answers(&mut joined, "glib.p(2)"), 1);

    // AND THE CITATIONS ARE REFUSED, at the citing files — both spellings.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_named_files(&[
            ("a.anthill", LIB_SORT),
            ("b.anthill", LIB_SIBLING_DECLARED),
            ("c.anthill", USER_IMPORT),
            ("c2.anthill", USER_QUALIFIED),
        ]),
        &[
            "c.anthill:2:18: unresolved import 'glib.S.p'",
            "c.anthill:3:20: rule-body goal `p` names nothing",
            "c2.anthill:2:20: rule-body goal `glib.S.p` names nothing",
        ],
    );
}

#[test]
fn an_undeclared_sibling_is_refused_at_the_library_heads() {
    // The ticket's program. Refused once, at `S`'s head, naming both scopes — and nothing
    // is reported at the citing file, whose author wrote nothing wrong. Passes under the
    // pass-1-mint back-out by design: no declaration is involved.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with_named_files(&[
            ("a.anthill", LIB_SORT),
            ("b.anthill", LIB_SIBLING),
            ("c.anthill", USER_IMPORT),
        ]),
        &["a.anthill:4:5: the rule head `p` introduces that name at 2 scopes"],
    );
    // The library alone is refused the same way, and the first repair the message offers
    // says that it removes `glib.S.p` — the name a citing file would lose.
    let errs = crate::common::load_errors_of_files(&[LIB_SORT, LIB_SIBLING]);
    assert_eq!(errs.len(), 1, "{errs:#?}");
    for want in [
        "glib, glib.S — and none of them declares it",
        "a body-less `rule p(…)` in 'glib'",
        "no other of those scopes then has a `p` of its own",
    ] {
        assert!(errs[0].contains(want), "want `{want}`: {}", errs[0]);
    }
}

#[test]
fn a_declaration_in_the_inner_scope_keeps_its_name() {
    // The repair the spec names: `S` declares its own `p`, so the sibling's declaration
    // at `glib` is a separate predicate and the citations keep answering `S`'s clause —
    // and only it. FAILS under the back-out: neither declaration is minted before the
    // heads are read, so the pair is the visibility refusal.
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        ("a.anthill", LIB_SORT_DECLARED),
        ("b.anthill", LIB_SIBLING_DECLARED),
        ("c.anthill", USER_IMPORT),
        ("c2.anthill", USER_QUALIFIED),
    ]));
    assert_eq!(clauses(&kb, "glib.S.p"), Some(1));
    assert_eq!(clauses(&kb, "glib.p"), Some(1));
    for user in ["guser", "guse2"] {
        assert_eq!(answers(&mut kb, &format!("{user}.uses(1)")), 1, "{user}");
        assert_eq!(
            answers(&mut kb, &format!("{user}.uses(2)")),
            0,
            "{user}: not `glib.p`'s clause"
        );
    }
    assert_eq!(answers(&mut kb, "glib.p(2)"), 1);
    assert_eq!(answers(&mut kb, "glib.p(1)"), 0);
}
