//! WI-20260902-2SZ88 — AN ENTITY CONSTRUCTOR'S OCCURRENCE IS BUILT FROM ITS PARSE NODE.
//!
//! `Loader::build_body_atom_occurrence` used to hand every entity-headed and reflect-form
//! rule-body atom to `node_occurrence::materialize_from_handle_spanned`, which walks the
//! KB TERM. Everything the parse tree knew then had to be shipped alongside in side
//! tables keyed by the KB `TermId` — `Loader::parse_span_table` and
//! `Loader::parse_dot_chain_table` — AND THAT KEY CANNOT ANSWER A PER-SITE QUESTION.
//! `TermStore::alloc` returns an existing id on a hash hit, so a KB `TermId` denotes a
//! STRUCTURE: a minted `ns.rel` and a hand-written
//! `anthill.reflect.field_access(ns, rel)` are ONE id, which is the whole premise of
//! WI-20260901-92VA4. The table paid for that with a SET DIFFERENCE — the bit withheld
//! wherever a citation shares an id with a written call — so an exact `true` was lost.
//!
//! This ticket deletes the round-trip for the entity half: `Loader::entity_ctor_expr`
//! builds the occurrence while STANDING AT THE PARSE NODE, so every child recurses
//! through `build_body_atom_occurrence` and takes its own span and its own `dot_chain`
//! from `dotted_citation_name` of its own node. No key, no collision, no difference.
//!
//! ── WHY THE ENTITY HALF AND NOT THE REFLECT HALF ─────────────────────────────
//!
//! MEASURED, with the early return instrumented and the whole workspace suite run:
//! 127 097 nodes took it. 126 813 of them — **99.78%** — are plain entity constructors,
//! and reach the new arm. 284 are reflect-keyed (`ListLiteral` 192, `dot_apply` 49,
//! `if_expr` 9, the rest in ones and twos) and 1 was not an entity at all. A reflect
//! form's occurrence is not an `Expr::Apply` — `ListLiteral` builds `Expr::ListLit` —
//! and those shapes live in `visit_fn`, so they keep the round-trip and the tables.
//! **WI-20260902-2NXAC** took the three COLLECTION LITERALS (192 of that 284) off the
//! round-trip in the same way; its own file carries those rows.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! FOUR AXES, each backed out separately and run over the whole `wi_tests` binary.
//!
//! **1 — THE NATIVE ARM.** `Loader::entity_ctor_expr` made to return `None`
//! unconditionally, which sends every entity constructor down the round-trip again.
//! **EXACTLY ONE TEST HERE GOES RED:**
//! [`a_nullary_op_in_an_entity_constructor_argument_is_a_call`], on its two ENTITY rows
//! (1 → 0, both spellings), with its four controls green either way.
//!
//! **2 — THE POSITIONAL LOOP'S GUARD.** `Loader::lowered_child_occurrence` bypassed in the
//! positional loop only (a bare `build_body_atom_occurrence`), which is what the first cut
//! shipped. **EXACTLY ONE ROW FAILS:**
//! [`a_positional_effect_row_under_an_entity_head_does_not_panic`], and it fails by
//! PANICKING the loader rather than by an assertion.
//!
//! **3 — THE TABLES ON A TRANSFORMED SLOT.** `lowered_child_occurrence`'s materialize arm
//! made to call the table-less `materialize_from_handle`, the first cut's other defect.
//! **EXACTLY ONE ROW FAILS:** [`a_bare_value_at_an_option_field_keeps_its_span`], on its
//! `Option` row only — its plain-field control stays green, which is what says the axis is
//! the WRAP and not the entity head.
//!
//! **4 — THE DESCRIPTION SUPPRESSION.** `descs_emitted_by_convert` ignored, so both walks
//! emit. **EXACTLY ONE ROW FAILS:**
//! [`an_inline_description_under_an_entity_head_is_emitted_once`], on its entity row only;
//! its generic-atom control is 1 under every variant.
//!
//! MEASURED TOGETHER as well as apart: with axes 2, 3 and 4 reintroduced at once, exactly
//! those three tests fail and the other two pass — so no row here is standing in for
//! another's defect.
//!
//! ── THE DOT-CHAIN CLAIM IS A TWO-AXIS MEASUREMENT, NOT A TEST ────────────────
//!
//! The ticket's own subject — that the bit is now EXACT rather than conservative — has
//! no row here, and that is a finding rather than an omission. With the table INTACT it
//! supplies the right answer anyway, so any single-axis back-out is green; the
//! measurement needs the change and the table varied TOGETHER. Run by hand, both ways,
//! with `parse_dot_chain_table` made to return an EMPTY set:
//!
//! | rule body | baseline, table empty | with the change, table empty |
//! |---|---|---|
//! | `zz4n.inner.rel = 7`             | 1, typed `Relation` | 1, typed `Relation` |
//! | `[zz4n.inner.rel] = 7`           | 3, none typed | 3, none typed |
//! | `{zz4n.inner.rel} = 7`           | 3, none typed | 3, none typed |
//! | `(zz4n.inner.rel, 1) = 7`        | 3, none typed | 3, none typed |
//! | `boxed4n(v: zz4n.inner.rel) = 7` | **3, none typed** | **1, typed `Relation`** |
//!
//! EXACTLY ONE ROW MOVES and it is the entity one. The bare row is the control at the
//! top — it never took the early return and is green under every variant, so a run in
//! which only it stays green measures nothing. The three collection literals are the
//! control at the bottom: they are the reflect half, they still read the table, and
//! their staying red is what says the table was really emptied.
//!
//! The second axis agrees: with this change in, commenting out
//! `parse_dot_chain_table`'s `cited.retain(|k| !plain.contains(k))` leaves
//! `wi_4nekz_dotted_equation_operand_test` **8 of 8 green**, where on the baseline the
//! same back-out reddens `a_citation_beside_a_written_field_access_call_does_not_launder_it`.
//! The set difference stays only because the reflect half still keys on the same table.
//!
//! ── THE ACCEPTANCE ROW WI-20260902-2SZ88 ASKED FOR CANNOT BE WRITTEN ─────────
//!
//! That ticket asks for "a new row [showing] the citation in row three getting the ONE
//! true diagnosis rather than the three-segment cascade". MEASURED, it is not
//! observable — in EITHER field order, and on both trees:
//!
//! | rule body | errors | naming `Relation[` |
//! |---|---|---|
//! | `boxedc(v: zz4n.inner.rel, w: 1)` — control | 1 | 1 |
//! | `boxedc(v: <written call>, w: 1)` — control | 3 | 0 |
//! | `boxedc(v: <written call>, w: zz4n.inner.rel)` | 3 | 0 |
//! | `boxedc(v: zz4n.inner.rel, w: <written call>)` | 3 | 0 |
//!
//! Two unrelated behaviours mask it. The typer reports ONE entity-field mismatch per
//! atom (`boxedc(v: <citation>, w: <citation>)` reports one, not two), and a written
//! `field_access` call's own three per-leaf errors suppress the field diagnosis of every
//! sibling — row four is the proof, where the citation is FIRST and still says nothing.
//! Row two versus row three is the decisive control: an atom with NO citation at all
//! reports exactly what the collision reports, so the bit's value changes no output
//! here. The rows above are the same figures before and after this change.

use anthill_core::kb::resolve::ResolveConfig;

/// One program per row: an operation `seven()`, its applied twin `plus1`, and a
/// one-field entity to nest them in. The namespace tail is `hold` and the rule is `cc`
/// deliberately — a namespace whose tail matches the rule name SHADOWS it and every row
/// silently answers 0, which is not the defect any row here is about.
fn answers(body: &str) -> usize {
    let src = format!(
        "namespace zz2sz.hold\n  import anthill.prelude.Int64\n  \
         import anthill.prelude.List\n  \
         operation seven() -> Int64 = 7\n  \
         operation plus1(n: Int64) -> Int64 = n + 1\n  \
         sort Bva\n    entity boxedva(x: Int64)\n  end\n  \
         rule cc(1) :- {body}\nend\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    let goal = crate::common::query_pattern_term(&mut kb, "zz2sz.hold.cc(?v)");
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// **A — THE CAPABILITY.** A nullary operation named inside an entity constructor's
/// argument is that operation's CALL, in both spellings.
///
/// WI-20260902-CZJ2N made `:- seven` and `:- seven()` one occurrence so `reduce_op_value`
/// can open them; the early return bypassed that elaboration entirely, because
/// `nullary_canon` folds `Fn{seven,[],[]}` to `Term::Ref(seven)` and `visit_term`'s
/// `Term::Ref` arm builds a plain `Expr::Ref` that `reduce_op_value` hands straight back
/// un-reduced. So the operation was never called and the equation compared a SYMBOL with
/// a number.
///
/// MEASURED — definite answers, this fixture, baseline → with the change:
///
/// | body | before | after |
/// |---|---|---|
/// | `seven <=> 7`                              | 1 | 1 |
/// | `seven() <=> 7`                            | 1 | 1 |
/// | `plus1(6) <=> 7`                           | 1 | 1 |
/// | `boxedva(x: plus1(6)) <=> boxedva(x: 7)`   | 1 | 1 |
/// | `boxedva(x: seven) <=> boxedva(x: 7)`      | **0** | **1** |
/// | `boxedva(x: seven()) <=> boxedva(x: 7)`    | **0** | **1** |
///
/// THE FOURTH ROW IS THE CONTROL THAT MATTERS: an APPLIED operation nested in the same
/// entity constructor already answered 1, so nesting per se was never the defect and a
/// row set without it could not tell "the early return drops the nullary reading" from
/// "the early return drops reduction". The first three are the un-nested spellings, green
/// either way, which is what says this is about the ENCLOSING atom and not about `seven`.
///
/// This is WI-20260902-2NXAC's finding (1), on the half of that ticket this change
/// reaches. Its LIST-literal rows were still 0 when this shipped; 2NXAC closed them, and
/// `wi_2nxac_collection_literal_native_occurrence_test` carries them.
#[test]
fn a_nullary_op_in_an_entity_constructor_argument_is_a_call() {
    for (label, body, want) in [
        ("bare, un-nested — control, green either way", "seven <=> 7", 1),
        (
            "parens, un-nested — control, green either way",
            "seven() <=> 7",
            1,
        ),
        (
            "an APPLIED op, un-nested — control",
            "plus1(6) <=> 7",
            1,
        ),
        (
            "an APPLIED op INSIDE the entity — the control that says nesting is fine",
            "boxedva(x: plus1(6)) <=> boxedva(x: 7)",
            1,
        ),
        (
            "a BARE nullary op inside the entity — 0 before this ticket",
            "boxedva(x: seven) <=> boxedva(x: 7)",
            1,
        ),
        (
            "its PARENTHESISED spelling, lost the same way",
            "boxedva(x: seven()) <=> boxedva(x: 7)",
            1,
        ),
    ] {
        assert_eq!(
            answers(body),
            want,
            "{label}: `{body}` must answer {want}. A 0 on either of the last two rows is \
             the entity-constructor early return handing the atom to a TERM walk, where a \
             nullary op is a bare `Term::Ref` that `reduce_op_value` cannot open — so the \
             equation compares the SYMBOL `seven` with 7 and fails silently."
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// THE THREE REGRESSIONS THE FIRST CUT SHIPPED, each found by `/code-review` and
// each measured against the back-out before it was repaired. They are here rather
// than folded into A and C because they do not test the CAPABILITY — they test
// that making the walk native left the three things it walks PAST unchanged.
// ══════════════════════════════════════════════════════════════════════════════

/// **D — A POSITIONAL EFFECT-ROW AUX MUST NOT PANIC THE LOADER.**
///
/// A written effect-row binding rides as a `Term::ParseAux`, which
/// `build_body_atom_occurrence` meets with an `unreachable!`. The generic arm guards
/// every child with `lower_effect_row_aux_occ` first; the first cut of
/// `entity_ctor_expr` put that guard on the NAMED loop only, so a POSITIONAL one under
/// an entity head reached the panic.
///
/// MEASURED: baseline reports the two located load errors asserted below; the first cut
/// **panicked at `load.rs`'s `Term::ParseAux reached build_body_atom_occurrence`**. The
/// repair is `Loader::lowered_child_occurrence`, which both loops now go through, so the
/// two cannot drift apart again.
///
/// THE ASSERTION IS THE ERRORS, not merely "it did not panic": a repair that swallowed
/// the node would also not panic, and would lose two real diagnostics.
#[test]
fn a_positional_effect_row_under_an_entity_head_does_not_panic() {
    let src = "namespace zz2sz.f1\n  import anthill.prelude.Int64\n  \
               sort Bx\n    entity Bx(v: Int64)\n  end\n  \
               fact holds(1)\n  \
               rule rr(1) :- holds(Outer[k = Bx[{}]])\nend\n";
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_eq!(
        errs.len(),
        2,
        "a positional effect-row aux under an entity head must be REPORTED, not panicked \
         on and not swallowed: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("over-applied")),
        "…the bracket's own refusal: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("names nothing")),
        "…and the unknown functor's: {errs:#?}"
    );
}

/// **E — A VALUE WRITTEN AT AN `Option` FIELD KEEPS ITS SPAN.**
///
/// `wrap_bare_option_value` wraps a bare value written at an `Option[..]` field into
/// `some(…)`, so the lowered child is one node LARGER than the conversion of the parse
/// child and cannot be rebuilt from the parse node — it must be materialized, or
/// resolution stops matching (five `github_todo_test` rows, measured). The first cut
/// materialized it BARE, with no span table, which is WI-1035/1039's wrong location
/// coming back for everything under the wrap.
///
/// MEASURED — the same operation call, at an `Option` field and at a plain one:
///
/// | rule body | baseline | materialized bare | with the tables |
/// |---|---|---|---|
/// | `bo(v: fx("a"))`, `v: Option[T = Int64]` | `11:22` | **`1:1`** | `11:22` |
/// | `bo2(v: fx("a"))`, `v: Int64` — control  | `7:23`  | `7:23`  | `7:23`  |
///
/// THE CONTROL IS THE POINT: it is the same call under the same entity head, differing
/// only in whether the declared field type triggers the wrap. Without it, a run showing
/// `1:1` could as easily be "the entity path lost spans" as "the wrapped slot did", and
/// the repair would have been aimed at the wrong loop.
#[test]
fn a_bare_value_at_an_option_field_keeps_its_span() {
    for (label, sort_decl, ctor, want_col) in [
        (
            "an Option field — the value is WRAPPED in some(…) and must still locate",
            "  sort Bo\n    entity bo(v: Option[T = Int64])\n  end\n",
            "bo",
            ":22:",
        ),
        (
            "a plain field — the control, no wrap, unchanged throughout",
            "  sort Bo2\n    entity bo2(v: Int64)\n  end\n",
            "bo2",
            ":23:",
        ),
    ] {
        let src = format!(
            "namespace zz2sz.f2\n  import anthill.prelude.Int64\n  \
             import anthill.prelude.Option\n  \
             operation fx(n: Int64) -> Int64 = n\n\
             {sort_decl}  \
             rule r(1) :- {ctor}(v: fx(\"a\")) = 7\nend\n"
        );
        let errs = crate::common::try_load_kb_with(&src).err().unwrap_or_default();
        let located: Vec<&String> = errs.iter().filter(|e| e.contains("fx.n")).collect();
        assert_eq!(
            located.len(),
            1,
            "{label}: the ill-typed argument must be reported once: {errs:#?}"
        );
        assert!(
            !located[0].starts_with("1:1:"),
            "{label}: `1:1` is the empty-span sentinel rendering as a real position — a \
             WRONG location, not a missing one (WI-1035/1039): {:?}",
            located[0]
        );
        assert!(
            located[0].contains(want_col),
            "{label}: expected the column the argument is written at ({want_col}): {:?}",
            located[0]
        );
    }
}

/// **F — AND THE INLINE DESCRIPTION IS EMITTED ONCE.**
///
/// `entity_ctor_expr` calls `convert_term` on the whole subtree — that walk emits a
/// `DescriptionInfo` for every described variable in it — and then recurses into the same
/// children, whose `Term::Var(Var::Global(..))` arm emits them AGAIN. That arm's own
/// comment says it exists only because a generic atom never calls `convert_term`, and
/// that "entity / reflect-form atoms still emit via the `convert_term` call"; making
/// entity atoms native put both walks over one subtree.
///
/// `emit_desc_fact` indexes per target, so the second run makes a DISTINCT fact rather
/// than colliding with the first. MEASURED: **2** where the baseline gives 1.
///
/// THE CONTROL IS THE GENERIC ATOM in the same rule file — 1 under every variant, which
/// is what says the duplicate is the entity walk's and not the emitter's.
#[test]
fn an_inline_description_under_an_entity_head_is_emitted_once() {
    use anthill_core::kb::term::{Literal, Term};
    let source = "\
namespace zz2sz.f3
  import anthill.prelude.Int64
  sort Bx3
    entity bx(v: Int64)
  end
  rule has_value(?x)
    :- bx(v: ?x {< the entity-slot value >}?)
  rule ctl(?x)
    :- some_pred(?x {< the generic-atom value >}?)
end
";
    let mut kb = anthill_core::kb::KnowledgeBase::new();
    let parsed = anthill_core::parse::parse(source).expect("parse failed");
    // Stops before the typer: the subject is what the LOADER records, over a fixture
    // (`some_pred` is undeclared) that is deliberately incomplete for the passes above.
    anthill_core::kb::load::load_all_with(
        &mut kb,
        &[&parsed],
        &anthill_core::kb::load::NullResolver,
        anthill_core::kb::load::LoadOptions {
            run_typer: false,
            ..Default::default()
        },
    )
    .expect("load failed");
    let desc_sym = kb
        .try_resolve_symbol("anthill.reflect.DescriptionInfo")
        .expect("the reflect sort is registered by the prelude");
    for (label, needle) in [
        ("under an ENTITY head — 2 with the first cut", "the entity-slot value"),
        ("in a GENERIC atom — the control, 1 throughout", "the generic-atom value"),
    ] {
        let n = kb
            .rules_by_functor(desc_sym)
            .iter()
            .filter(|&&rid| {
                let head = kb.rule_head(rid);
                match kb.get_term(head) {
                    Term::Fn { named_args, .. } => named_args
                        .iter()
                        .find(|(f, _)| kb.local_name_of(*f) == "content")
                        .map(|(_, v)| *v)
                        .is_some_and(|v| {
                            matches!(kb.get_term(v), Term::Const(Literal::String(s)) if s == needle)
                        }),
                    _ => false,
                }
            })
            .count();
        assert_eq!(
            n, 1,
            "{label}: one written description is ONE fact. `emit_desc_fact` indexes per \
             target, so a second walk over the same subtree makes a distinct fact rather \
             than colliding — got {n}."
        );
    }
}
