//! WI-1099 — THE LIST-LITERAL OCCURRENCE'S TERM TWIN, and what happens to it on
//! the way to disk. Two questions, and neither is answered by the parse-level
//! surface mark this ticket's first half added (parse/ir.rs `collection_literals`,
//! read by `kb::load::list_literal_lowering`; driven by
//! `wi1096_list_literal_lowering_test::only_the_bracket_surface_is_the_list_literal`
//! and by `wi040_reserved_vocab_test::query_pattern_bare_list_literal_resolves_
//! qualified` on the query side).
//!
//! ── (A) THE TWIN WAS NOT REACHABLE FROM A RULE BODY, AND NOT FOR THE FILED REASON
//!
//! The ticket read the defect as a LOWERING one: the pattern an author would write
//! for a list-literal occurrence, `ListLiteral(?a, ?b)`, lowered to a `cons` spine
//! and so could never match the positional twin `occurrence_to_term` builds. The
//! mark fixes that half. MEASURED with the mark in place and before the change
//! here, every row of [`a_list_literal_occurrence_answers_a_meta_rule`] and
//! [`a_bracket_literal_occurrence_answers_the_cons_reading`] still returned ZERO —
//! including `occurrence_term(?e, cons(head: ?h, tail: ?t))` over an occurrence
//! spelled `cons(head: 1, tail: nil())`, which has no list literal in it at all.
//!
//! THE SECOND READER. The goal-form `occurrence_term(?e, pattern)` does not read
//! `occurrence_to_term` — it matches through the `ReflectedExpr` lens
//! (`term_view.rs`), and that lens reflected LITERAL LEAVES ONLY: every compound
//! `Expr` form read `Opaque`, which matches nothing. So the meta-rule style this
//! ticket cites from `docs/proposals/typing_pass_spec.anthill` —
//! `:- occurrence_term(?e, var_ref(name: ?n))` — could not be written for a list
//! literal, for a `var_ref`, or for anything but a literal. `occurrence_term` is
//! one name over two readers (value-domain `occurrence_term(occ) -> Term` DOES
//! call `occurrence_to_term`; the goal form does not), and the ticket measured the
//! shape of one and filed against the other.
//!
//! THE FIX IS UNIVERSAL, not a list-literal arm: the lens now DELEGATES to the
//! plain occurrence view for every form but `Expr::Const`, whose reflect reading
//! (`int_lit(value: …)`) is the one place the lens legitimately differs from the
//! twin. The plain view is already the twin, arm for arm, by explicit design
//! (WI-814 wrapped forms, WI-683/WI-1014 collection literals, WI-520
//! applications/constructors) — presenting `Opaque` for them was the WI-425
//! cross-carrier miss: a pattern the reifier WOULD build for an occurrence could
//! not be matched against that occurrence.
//!
//! WHAT IT IS NOT, driven by
//! [`the_goal_form_matches_the_twin_not_the_reflect_data_vocabulary`]: it does not
//! make `typing_pass_spec.anthill`'s `apply(fn: …, args: …)` /
//! `constructor(name: …, args: …)` patterns match. Those are the reflect-DATA
//! vocabulary, and an application's twin is the application. Reaching that
//! vocabulary is a different change with a different right shape (WI-246's
//! feedback: build rule-body atoms as occurrences natively in the front end,
//! rather than widen a lens into a second reading of `Expr` beside `occ_head`'s —
//! this change REMOVES such a second reading).
//!
//! ── (B) THE ROUND TRIP, AND WHY THE PRINTER COULD NOT BE THE PLACE
//!
//! `TermPrinter` renders a flat `ListLiteral` and a ground `cons` spine identically
//! as `[1, 2]` (MEASURED: `fact stored(ListLiteral(1, 2))` loads as
//! `anthill.reflect.ListLiteral/2p0n` and `fact spine([1, 2])` as
//! `anthill.prelude.List.cons/0p2n`, and both printed `[1, 2]`). Reloaded in a
//! position that declares nothing, `[1, 2]` is the spine (§4.6) — so the flat term
//! did not survive being written to disk.
//!
//! BOTH REMEDIES THE TICKET OFFERED ARE REFUTED:
//!
//!  - "give the reflect entity a distinct printed form" — the printer has no bit to
//!    read. The KB is hash-consed, so a `[1, 2]` the loader DECLINED to lower (a
//!    `Set[T = Int64]`-declared field, spec §4.6) and a written `ListLiteral(1, 2)`
//!    are the same `TermId`. The parse-time mark cannot be carried in: it exists
//!    only because parse terms are NOT deduped (the same reason
//!    `mark_type_application` lives there, WI-927).
//!  - "make the twin stop being positional" — the twin must be what the parser
//!    builds for `[…]`, which is positional. Giving it named args would reopen
//!    exactly the cross-carrier disagreement WI-1014 closed for `TupleLiteral`.
//!
//! SO THE TWO FORMS DO SHARE A PRINTED FORM — and the round trip is fixed one level
//! out, at the CALLER, because the two callers were asking different questions of
//! one function. `print_fact` needs text that RELOADS to this term; the file
//! store's retract needs a content KEY that is invariant under the loader's
//! lowering (`apply_retracts` compares a print of the on-disk PARSE term against a
//! print of the LOADED head, and §4.6 lowers between them). `TermPrinter::
//! reload_faithful` answers the first, the default answers the second, and
//! [`a_persisted_literal_is_still_retractable`] is the row that says they stay
//! compatible.
//!
//! ── WHICH TESTS FAIL WHEN EACH CHANGE IS BACKED OUT ──────────────────────────
//!
//! Back out the lens delegation (`ReflectedExpr` in term_view.rs — restore the
//! `_ => ViewHead::Opaque` head and the `None` / `Vec::new()` child reads) and
//! FOUR rows fail, MEASURED: [`a_list_literal_occurrence_answers_a_meta_rule`],
//! [`a_bracket_literal_occurrence_answers_the_cons_reading`],
//! [`the_twin_carries_its_elements_and_its_arity`], and
//! [`an_empty_literal_occurrence_answers_only_the_empty_pattern`].
//!
//! Back out the persist print (`print_fact` → `TermPrinter::over`) and THREE fail,
//! MEASURED: [`a_flat_list_literal_survives_persist_and_reload`],
//! [`the_persisted_text_names_the_entity_the_key_keeps_the_surface`], and
//! [`a_persisted_literal_is_still_retractable`] — the last on its on-disk TEXT row
//! and not on its behaviour, which is the point of the next paragraph.
//!
//! THE OTHER DIRECTION, and the row that measures the SPLIT rather than either
//! half: give `TermPrinter::over` the reload-faithful mode too (so the content key
//! moves with the persisted text) and exactly ONE row fails —
//! [`a_persisted_literal_is_still_retractable`], on "must be found by its content
//! key and dropped", leaving `fact held_flat(ListLiteral(1, 2))` on disk. The
//! parse-side key (`apply_retracts` → `TermPrinter::over`) and the KB-side key
//! (`FileStore::retract` → `TermPrinter::new`) would then disagree, and the retract
//! becomes a silent no-op. That failure is invisible to every other row here.
//!
//! PASS EITHER WAY, BY DESIGN — the attribution controls:
//! [`the_literal_wrapper_is_still_the_lenss_own`] (the `Expr::Const` arm the
//! delegation deliberately does NOT touch, plus the wi297 compound-pattern refusal
//! restated: the lens did not become "matches anything") and
//! [`the_named_arg_spelling_is_a_third_shape`] (WI-1096's guard — a
//! `ListLiteral(elements: …)` is neither of the two answers here and must match
//! neither).

use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::{ClauseKind, KnowledgeBase};
use anthill_core::persistence::file_store::{FileConvention, FileStore};
use anthill_core::persistence::print;
use anthill_core::persistence::Store;
use anthill_core::parse::desugar_target as dt;
use smallvec::SmallVec;

/// The DEFINITE solutions of a unary rule — a conditional one is an undischarged
/// goal, not an answer (the convention `wi1096_list_literal_lowering_test` sets).
fn decided(kb: &mut KnowledgeBase, name: &str) -> usize {
    crate::common::query_unary(kb, &format!("wi1099.twin.{name}"))
        .iter()
        .filter(|(_, definite)| *definite)
        .count()
}

/// Total solutions, conditional ones included — what a `.len()`-only assertion
/// would have called an answer.
fn any(kb: &mut KnowledgeBase, name: &str) -> usize {
    crate::common::query_unary(kb, &format!("wi1099.twin.{name}")).len()
}

/// Every probe hands the rule under test an OCCURRENCE — a rule-body goal argument
/// is carried as one — and each `synth_*` rule shows it through `occurrence_term`.
/// The two spellings of the same two-element list sit side by side so a row is
/// attributable to the SURFACE and not to the elements.
const TWIN_SRC: &str = r#"
namespace wi1099.twin
  import anthill.reflect.{Expr, ListLiteral, occurrence_term}
  import anthill.reflect.Expr.{int_lit, if_expr}
  import anthill.prelude.{Int64}
  import anthill.prelude.List.{cons, nil}

  rule synth_lit(?e, 1)   :- occurrence_term(?e, ListLiteral(?a, ?b))
  rule synth_cons(?e, 1)  :- occurrence_term(?e, cons(head: ?h, tail: ?t))
  rule synth_seven(?e, 1) :- occurrence_term(?e, ListLiteral(7, ?b))
  rule synth_nine(?e, 1)  :- occurrence_term(?e, ListLiteral(9, ?b))
  rule synth_one(?e, 1)   :- occurrence_term(?e, ListLiteral(?a))
  rule synth_empty(?e, 1) :- occurrence_term(?e, ListLiteral())
  rule synth_named(?e, 1) :- occurrence_term(?e, ListLiteral(elements: ?a))
  rule synth_wrapped(?e, 1) :- occurrence_term(?e, ListLiteral(int_lit(value: ?), ?b))
  rule synth_int(?e, 1)   :- occurrence_term(?e, int_lit(value: ?))
  rule synth_if(?e, 1)    :- occurrence_term(?e, if_expr(cond: ?c, then_branch: ?t, else_branch: ?el))

  rule by_name_lit(?n)  :- synth_lit(ListLiteral(1, 2), ?n)
  rule by_name_cons(?n) :- synth_cons(ListLiteral(1, 2), ?n)
  rule bracket_lit(?n)  :- synth_lit([1, 2], ?n)
  rule bracket_cons(?n) :- synth_cons([1, 2], ?n)
  rule spelled_cons(?n) :- synth_cons(cons(head: 1, tail: nil()), ?n)

  rule elem_seven(?n)   :- synth_seven(ListLiteral(7, 2), ?n)
  rule elem_nine(?n)    :- synth_nine(ListLiteral(7, 2), ?n)
  rule arity_one(?n)    :- synth_one(ListLiteral(7, 2), ?n)

  rule empty_matches(?n)  :- synth_empty(ListLiteral(), ?n)
  rule empty_vs_two(?n)   :- synth_empty(ListLiteral(1, 2), ?n)
  rule two_vs_empty(?n)   :- synth_lit(ListLiteral(), ?n)

  rule named_vs_twin(?n)  :- synth_named(ListLiteral(1, 2), ?n)
  rule wrapped_child(?n)  :- synth_wrapped(ListLiteral(1, 2), ?n)
  rule int_lit_row(?n)    :- synth_int(42, ?n)
  rule if_over_int(?n)    :- synth_if(42, ?n)
end
"#;

/// The vocabulary boundary, in its own fixture because it needs an operation to
/// call. `apply` / `constructor` are reflect-`Expr` ENTITIES and must be imported
/// by name or the body-term check refuses them outright.
const VOCAB_SRC: &str = r#"
namespace wi1099.vocab
  import anthill.reflect.{Expr, occurrence_term}
  import anthill.reflect.Expr.{apply, constructor}
  import anthill.prelude.{Int64}
  operation foo(x: Int64) -> Int64 = x

  rule synth_twin(?e, 1)  :- occurrence_term(?e, foo(?x))
  rule synth_apply(?e, 1) :- occurrence_term(?e, apply(fn: ?f, args: ?a))
  rule synth_ctor(?e, 1)  :- occurrence_term(?e, constructor(name: ?c, args: ?a))

  rule twin_row(?n)  :- synth_twin(foo(1), ?n)
  rule apply_row(?n) :- synth_apply(foo(1), ?n)
  rule ctor_row(?n)  :- synth_ctor(foo(1), ?n)
end
"#;

// ══════════════════════════════════════════════════════════════════
// (A) the occurrence twin, through the goal-form `occurrence_term`
// ══════════════════════════════════════════════════════════════════

/// THE HEADLINE — the meta-rule the ticket exists for. A `ListLiteral(1, 2)`
/// written by name at a goal-argument position is carried as an `Expr::ListLit`
/// occurrence (measured directly off the loaded rule body), and
/// `occurrence_term(?e, ListLiteral(?a, ?b))` matches its term twin. The `cons`
/// row beside it says the match reads the twin's SHAPE rather than answering for
/// any occurrence at all.
#[test]
fn a_list_literal_occurrence_answers_a_meta_rule() {
    let mut kb = crate::common::load_kb_with(TWIN_SRC);
    assert_eq!(
        decided(&mut kb, "by_name_lit"),
        1,
        "the twin of a list-literal occurrence IS `ListLiteral(e…)`, and a rule \
         body can now say so — before the lens delegation this was 0",
    );
    assert_eq!(
        any(&mut kb, "by_name_cons"),
        0,
        "…and it is not a `cons` — the row that stops a lens which matches anything",
    );
}

/// THE SURFACE DECIDES AT THE OCCURRENCE CARRIER TOO. The identical two-element
/// list written `[1, 2]` lowers before the occurrence is built (§4.6), so it
/// answers the `cons` reading and NOT the literal one — the exact mirror of the
/// row above. `spelled_cons` is the control that the `cons` reading is not
/// peculiar to a lowered literal.
#[test]
fn a_bracket_literal_occurrence_answers_the_cons_reading() {
    let mut kb = crate::common::load_kb_with(TWIN_SRC);
    assert_eq!(
        decided(&mut kb, "bracket_cons"),
        1,
        "`[1, 2]` is the List literal, so its occurrence is the spine",
    );
    assert_eq!(
        any(&mut kb, "bracket_lit"),
        0,
        "…and it is no longer matchable AS the reflect entity, which is what makes \
         the by-name row attributable to the surface",
    );
    assert_eq!(
        decided(&mut kb, "spelled_cons"),
        1,
        "a hand-spelled `cons(head: 1, tail: nil())` occurrence answers the same \
         reading — this row also returned 0 before the delegation, which is how the \
         defect was found to be wider than list literals",
    );
}

/// NOT A VACUOUS MATCH — the twin's ELEMENTS and ARITY are both readable through
/// the pattern. A lens that reported the right head but no children would pass the
/// headline row and fail both of these.
#[test]
fn the_twin_carries_its_elements_and_its_arity() {
    let mut kb = crate::common::load_kb_with(TWIN_SRC);
    assert_eq!(
        decided(&mut kb, "elem_seven"),
        1,
        "`ListLiteral(7, ?b)` matches `ListLiteral(7, 2)` — the element is read",
    );
    assert_eq!(
        any(&mut kb, "elem_nine"),
        0,
        "…and `ListLiteral(9, ?b)` does not: the elements DISCRIMINATE",
    );
    assert_eq!(
        any(&mut kb, "arity_one"),
        0,
        "a one-element pattern does not match a two-element literal",
    );
}

/// THE EMPTY LITERAL, at both ends of the arity check — `ListLiteral()` is a real
/// nullary application here (measured: it loads as `ListLiteral/0p0n`, not a bare
/// name), so it is the one case where "no children" is the right answer and must
/// still not match a populated literal.
#[test]
fn an_empty_literal_occurrence_answers_only_the_empty_pattern() {
    let mut kb = crate::common::load_kb_with(TWIN_SRC);
    assert_eq!(decided(&mut kb, "empty_matches"), 1);
    assert_eq!(
        any(&mut kb, "empty_vs_two"),
        0,
        "the empty pattern must not match a two-element literal",
    );
    assert_eq!(
        any(&mut kb, "two_vs_empty"),
        0,
        "…nor the two-element pattern the empty literal",
    );
}

/// CONTROL — WI-1096's guard, restated at this carrier. `ListLiteral(elements: …)`
/// is a THIRD shape: not the bracket surface, not the positional twin. It must
/// match neither answer, and this row passes with either change here backed out.
#[test]
fn the_named_arg_spelling_is_a_third_shape() {
    let mut kb = crate::common::load_kb_with(TWIN_SRC);
    assert_eq!(
        any(&mut kb, "named_vs_twin"),
        0,
        "a named-arg pattern does not match the positional twin",
    );
}

/// CONTROL — the one form the delegation deliberately does NOT delegate. A literal
/// occurrence still reflects as `int_lit(value: …)` (its twin is the bare
/// `Term::Const`, so this wrapper is the lens's own reading and the whole reason
/// the lens exists), and a compound pattern over it still FAILS — the wi297 pin
/// `wi297_occurrence_term_compound_pattern_fails_not_panics` restated here as the
/// row that says the delegation did not turn the lens into a wildcard. Both pass
/// either way.
///
/// AND THE WRAPPER IS AT THE ROOT ONLY — driven by the third row, which a review
/// pass asked for. A child is handed back as the occurrence itself and is read in
/// its PLAIN shape, so a literal ELEMENT matches as `7`
/// ([`the_twin_carries_its_elements_and_its_arity`]) and NOT as `int_lit(value: 7)`.
/// That is the shipped idiom, not an oversight: descend with `sub_occurrences` and
/// reflect each child with its own `occurrence_term` — which is what
/// `typing_test.rs`'s `wi297_..._sub_occurrences` row does. Unchanged by this
/// ticket (before it the whole pattern matched nothing), and stated because the
/// lens's own doc would otherwise read as if the wrap were recursive.
#[test]
fn the_literal_wrapper_is_still_the_lenss_own() {
    let mut kb = crate::common::load_kb_with(TWIN_SRC);
    assert_eq!(
        decided(&mut kb, "int_lit_row"),
        1,
        "`42` still reflects as `int_lit(value: 42)`",
    );
    assert_eq!(
        any(&mut kb, "if_over_int"),
        0,
        "…and an `if_expr` pattern over it still matches nothing",
    );
    assert_eq!(
        any(&mut kb, "wrapped_child"),
        0,
        "…and a nested `int_lit(value: ?)` does not match a literal ELEMENT: the \
         reflect wrap is applied to the occurrence the builtin was HANDED, not to \
         its children",
    );
}

/// THE SCOPE BOUNDARY, DRIVEN — what the goal form matches is the TERM TWIN, and
/// NOT the reflect-DATA vocabulary. MEASURED on one `foo(1)` occurrence: the twin
/// spelling `foo(?x)` answers, while `apply(fn: ?f, args: ?a)` and
/// `constructor(name: ?c, args: ?a)` — what `docs/proposals/typing_pass_spec.
/// anthill`'s `synth` rules are written in — do not.
///
/// The row exists so this delivery is not read as "the typing-pass spec's rules
/// now run". Reaching THAT vocabulary is a different change, and per WI-246's
/// feedback its right shape is building rule-body atoms as occurrences natively in
/// the front end — not a wider lens, which would put a second reading of `Expr`
/// beside `occ_head`'s. This change removes such a second reading; it does not add
/// one.
#[test]
fn the_goal_form_matches_the_twin_not_the_reflect_data_vocabulary() {
    let mut kb = crate::common::load_kb_with(VOCAB_SRC);
    let n = |kb: &mut KnowledgeBase, r: &str| {
        crate::common::query_unary(kb, &format!("wi1099.vocab.{r}")).len()
    };
    assert_eq!(
        n(&mut kb, "twin_row"),
        1,
        "an application occurrence shows as the term it applies — its twin",
    );
    assert_eq!(n(&mut kb, "apply_row"), 0, "not as `apply(fn:, args:)`");
    assert_eq!(
        n(&mut kb, "ctor_row"),
        0,
        "nor as `constructor(name:, args:)`"
    );
}

// ══════════════════════════════════════════════════════════════════
// (B) the round trip
// ══════════════════════════════════════════════════════════════════

/// A flat `ListLiteral` in an UNDECLARED position, its `cons`-spine twin, and the
/// empty flat literal — the three terms whose printed forms this half is about.
const RT_SRC: &str = r#"
namespace wi1099.rt
  import anthill.prelude.{Int64}
  -- WI-20260825-5W3RJ: a WRITTEN `ListLiteral(…)` is an ordinary reference to the
  -- reflect entity and is imported like any other name. The RELOAD half below
  -- deliberately does NOT import it — the persisted text has to carry its own address,
  -- which is what `reload_faithful` now prints.
  import anthill.reflect.{ListLiteral}
  fact stored(ListLiteral(1, 2))
  fact spine([1, 2])
  fact empty_stored(ListLiteral())
end
"#;

/// `<qualified functor>/<pos>p<named>n` of a term — enough to tell the flat
/// literal from the spine, which is the whole question here.
fn shape(kb: &KnowledgeBase, t: TermId) -> String {
    match kb.get_term(t) {
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => format!(
            "{}/{}p{}n",
            kb.qualified_name_of(*functor),
            pos_args.len(),
            named_args.len()
        ),
        other => panic!("expected a compound term, got {other:?}"),
    }
}

/// The head term of the single fact `pattern`'s functor names, and its first
/// positional argument.
fn fact_head_and_arg(kb: &mut KnowledgeBase, pattern: &str) -> (TermId, TermId) {
    let probe = crate::common::query_pattern_term(kb, pattern);
    let sym = match kb.get_term(probe) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("pattern `{pattern}` is {other:?}"),
    };
    let rids = kb.rules_by_functor(sym);
    assert_eq!(rids.len(), 1, "exactly one fact for `{pattern}`");
    let head = kb.rule_head(rids[0]);
    let arg = match kb.get_term(head) {
        Term::Fn { pos_args, .. } => pos_args[0],
        other => panic!("head is {other:?}"),
    };
    (head, arg)
}

/// THE ROUND-TRIP ROW the ticket asks for, driven through the shipped rendering
/// (`print_fact`, what `FileStore::persist` writes) and a real reload. Both terms
/// come back as themselves, which before this change only the spine did.
#[test]
fn a_flat_list_literal_survives_persist_and_reload() {
    let mut kb = crate::common::load_kb_with(RT_SRC);
    crate::common::supply_invocation_imports(&mut kb, &["wi1099.rt.*"]);

    let mut written = String::new();
    let mut before: Vec<String> = Vec::new();
    for p in ["stored(?x)", "spine(?x)", "empty_stored(?x)"] {
        let (head, arg) = fact_head_and_arg(&mut kb, p);
        before.push(shape(&kb, arg));
        written.push_str(&print::print_fact(&kb, head, None));
    }
    assert_eq!(
        before,
        vec![
            format!("{}/2p0n", dt::qualified(dt::LIST_LITERAL)),
            "anthill.prelude.List.cons/0p2n".to_string(),
            format!("{}/0p0n", dt::qualified(dt::LIST_LITERAL)),
        ],
        "the three terms this row is about are genuinely different in the KB — \
         the premise of the whole half",
    );

    // WI-20260825-5W3RJ — THE RELOAD SCOPE MUST IMPORT WHAT THE PERSISTED TEXT NAMES.
    // A store writes bare `fact …` lines with no header of its own (no `namespace`, no
    // `import` — checked across `FileStore` / `IndexedFileStore` / `ItemPerFileStore`),
    // so the scope it is loaded back into supplies them. Before this ticket the reflect
    // vocabulary resolved from anywhere through the desugaring vocab's reserved-name
    // rung, and this line was not needed; now it is the same obligation every other
    // name carries. Drop the reflect import and `stored` comes back as an ordinary
    // unresolved `ListLiteral` — a different symbol under the same spelling.
    let mut kb2 = crate::common::load_kb_with(&format!(
        "namespace wi1099.rt2\n  import anthill.prelude.{{Int64}}\n  \
         import anthill.reflect.{{ListLiteral}}\n{written}end\n"
    ));
    crate::common::supply_invocation_imports(&mut kb2, &["wi1099.rt2.*"]);
    let after: Vec<String> = ["stored(?x)", "spine(?x)", "empty_stored(?x)"]
        .iter()
        .map(|p| {
            let (_, arg) = fact_head_and_arg(&mut kb2, p);
            shape(&kb2, arg)
        })
        .collect();
    assert_eq!(
        after, before,
        "each fact reloads as the term it was: before this change `stored` came \
         back as the `cons` spine, because it was written `[1, 2]`",
    );
}

/// THE TWO QUESTIONS, SIDE BY SIDE, on one term — the row that says the fix is a
/// CALLER split and not a printer flip. What goes to disk names the entity; the
/// content key keeps the lowering-invariant surface, which is what
/// [`a_persisted_literal_is_still_retractable`] then depends on.
#[test]
fn the_persisted_text_names_the_entity_the_key_keeps_the_surface() {
    let mut kb = crate::common::load_kb_with(RT_SRC);
    crate::common::supply_invocation_imports(&mut kb, &["wi1099.rt.*"]);

    let (flat, _) = fact_head_and_arg(&mut kb, "stored(?x)");
    let (spine, _) = fact_head_and_arg(&mut kb, "spine(?x)");
    let (empty, _) = fact_head_and_arg(&mut kb, "empty_stored(?x)");

    assert_eq!(
        print::print_fact(&kb, flat, None),
        "fact stored(ListLiteral(1, 2))\n"
    );
    assert_eq!(
        print::print_fact(&kb, empty, None),
        "fact empty_stored(ListLiteral())\n",
        "the EMPTY flat literal keeps its parentheses, or it reloads as a bare name",
    );
    assert_eq!(
        print::print_fact(&kb, spine, None),
        "fact spine([1, 2])\n",
        "the spine is unchanged — `[…]` is exactly the text that reloads to it",
    );

    let key = |t| print::TermPrinter::new(&kb).print_term(t);
    assert_eq!(key(flat), "stored([1, 2])");
    assert_eq!(key(spine), "spine([1, 2])");
    assert_eq!(
        key(empty),
        "empty_stored([])",
        "the content key is untouched, and still maps the two forms to ONE text — \
         which is what makes it invariant under the loader's lowering",
    );
}

/// THE COMPATIBILITY ROW — a runtime-asserted fact carrying a flat `ListLiteral`
/// is persisted, then RETRACTED, and the block leaves the file. This is the path
/// the content key serves (`IndexedFileStore` falls back to it for facts with no
/// source span, i.e. exactly the ones `persist` wrote), so it is where a
/// persist-print change would show up as a silent no-op on disk.
///
/// THE ONLY ROW THAT MEASURES THE SPLIT. Move the content key to the
/// reload-faithful mode as well and this is the single test that fails, on the
/// "must be dropped" assertion — the two key sites (`apply_retracts` over the
/// PARSE file, `FileStore::retract` over the KB head) stop agreeing and the fact
/// stays on disk with no error anywhere. The spine rows beside it are the control:
/// they pass under every variation, since `[…]` was always both answers for them.
#[test]
fn a_persisted_literal_is_still_retractable() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let mut kb = crate::common::load_kb_with(RT_SRC);

    let list_literal = kb.resolve_symbol(dt::qualified(dt::LIST_LITERAL));
    let one = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(1)));
    let two = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(2)));
    let flat = kb.alloc(Term::Fn {
        functor: list_literal,
        pos_args: SmallVec::from_slice(&[one, two]),
        named_args: SmallVec::new(),
    });
    let spine = kb.build_list(&[one, two]);

    let sort = ClauseKind::Fact;
    let domain = kb.intern("wi1099");
    let mk = |kb: &mut KnowledgeBase, name: &str, arg: TermId| {
        let f = kb.intern(name);
        let head = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_elem(arg, 1),
            named_args: SmallVec::new(),
        });
        (head, kb.assert_fact(head, sort, domain, None))
    };
    let (flat_head, flat_id) = mk(&mut kb, "held_flat", flat);
    let (spine_head, spine_id) = mk(&mut kb, "held_spine", spine);
    let (keep_head, _keep_id) = mk(&mut kb, "held_keep", flat);

    for h in [flat_head, spine_head, keep_head] {
        store.persist(&kb, h, sort, domain, None).unwrap();
    }
    store.flush(&kb).unwrap();
    let path = dir.path().join("facts.anthill");
    let after_persist = std::fs::read_to_string(&path).unwrap();
    // THE SHORT SPELLING IS LOAD-BEARING, measured under WI-20260825-5W3RJ. Making
    // reload-faithful mode print `anthill.reflect.ListLiteral(1, 2)` — so a persisted
    // fact carries its own address and needs no import to reload — fails the "must be
    // dropped" assertion below and leaves the fact on disk silently, exactly as this
    // row's doc predicts. The persist print and the content key are one decision.
    assert!(after_persist.contains("held_flat(ListLiteral(1, 2))"));
    assert!(after_persist.contains("held_spine([1, 2])"));

    for id in [flat_id, spine_id] {
        assert!(store.retract(&kb, id).unwrap(), "retract is buffered");
        kb.retract(id);
    }
    store.flush(&kb).unwrap();

    let after_retract = std::fs::read_to_string(&path).unwrap();
    assert!(
        !after_retract.contains("held_flat"),
        "the flat literal's fact must be found by its content key and dropped — a \
         persist print the key cannot match would leave it on disk, silently: \
         {after_retract}",
    );
    assert!(
        !after_retract.contains("held_spine"),
        "…and the spine's too, which is the control: {after_retract}",
    );
    assert!(
        after_retract.contains("held_keep"),
        "…while the fact that was not retracted stays: {after_retract}",
    );
}
