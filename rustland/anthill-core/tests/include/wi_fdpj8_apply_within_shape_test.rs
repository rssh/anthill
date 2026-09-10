//! **WI-20260910-FDPJ8 (second half) — A WOVEN CALL IS NOT `Opaque`, AND ITS THREE
//! PRODUCERS BUILD ONE SHAPE.**
//!
//! `Expr::ApplyWithin` headed [`ViewHead::Opaque`], and the reason recorded at that
//! head argued against a DIFFERENT head than the one it excluded. It rejected a
//! TRANSPARENT head — functor = the CALLEE — because "its faithful term twin is the
//! WRAPPED reflect shape `apply_within(fn = …, args = …, requirements = …)`, whose
//! head functor is `apply_within` and NOT the callee". Every word of that is right,
//! and all of it argues FOR the wrapped head, which `expr_wrapped_shape` already
//! serves for `dot_apply` / `var_ref` / `lambda_expr` / `if_expr` / `let_expr` /
//! `proof_stmt` / `match_expr`. `ApplyWithin` was simply missing from that table.
//!
//! `Opaque` is payload-free, so this was not a precision loss: two structurally
//! DIFFERENT woven calls compared EQUAL and shared a `GoalKey` — the failure mode
//! `wrapped_expr_head`'s own WI-1014 paragraph spells out for the same collapse.
//!
//! # One shape, from one declaration
//!
//! The canonical form is the ENTITY's, because `apply_within` IS one:
//!
//! ```anthill
//! entity apply_within(fn: Symbol, args: List[ApplyArg],
//!                     requirements: List[NodeOccurrence],
//!                     type_args: Option[T = List[type_arg]])
//! ```
//!
//! Three producers disagreed with it, each in its own direction:
//!
//! | producer | was | now |
//! |---|---|---|
//! | `record_apply_within_concrete` (term) | carried `pos_args` the entity has none of; hand-ordered named args | no positionals, through `canonicalize_record_named_args` |
//! | `visit_fn` `"apply_within"` (term → occurrence) | read a `type_args` field the entity did not declare | the entity declares it |
//! | `weave_covered_call` (occurrence) | carried `type_args` with nowhere to go | ditto |
//!
//! The `type_args` field was MISSING from the declaration rather than deliberately
//! absent: `apply` beside it has had `type_args: Option[T = List[type_arg]]` since
//! WI-1013, the occurrence carries the channel, and the reader already read it. So
//! reader and occurrence agreed with each other and disagreed with the schema.
//!
//! `record_apply_within_concrete`'s positional channel was DEAD as well as
//! undeclared — measured, not assumed: its only caller, `req_insertion::
//! materialize_apply`, hardcodes `pos_args: SmallVec::new()`. So dropping it (and the
//! parameter, so a future caller cannot hand it positionals to discard in silence)
//! moves no value any program ever produced.
//!
//! # What each row measures, and what fails when the change is backed out
//!
//! | back out | red rows |
//! |---|---|
//! | **(H)** the `Expr::ApplyWithin` arm of `expr_wrapped_shape_inner` | [`a_woven_call_heads_as_its_reflect_twin`], [`a_woven_call_and_its_term_twin_read_alike`] |
//! | **(T)** `try_occurrence_to_term`'s `Expr::ApplyWithin` arm | [`a_woven_call_and_its_term_twin_read_alike`] |
//! | **(F)** the `type_args` field on the `apply_within` declaration | [`the_declaration_carries_every_field_its_producers_build`] |
//!
//! Each was applied on its own and left EXACTLY those rows red — (H) with the head
//! reported as `Opaque`, (T) with the twin reported as `⊥`. (T) is the row that says
//! the two halves are not interchangeable: the head alone still leaves the view
//! announcing children the term twin has not got.
//!
//! No row is claimed for `record_apply_within_concrete`'s two changes. The positional
//! channel it stopped writing was already empty at its only caller, and the
//! canonicalization it now goes through was already in declared order — so neither
//! moves a stored byte today, and a row asserting otherwise would be measuring the
//! fixture rather than the change. They are shipped because the SHAPE must come from
//! one place: the next field added to the entity, or a reordered declaration, is what
//! they are there for.
//!
//! CONTROLS — each passes with all three backed out:
//!
//!  * `wi1040_require_clause_dictionary_test` in full — the weave's own suite, and the
//!    producer of every occurrence this file reads. It is what says the head changed
//!    and the DISPATCH did not.
//!  * [`a_plain_call_in_the_same_clause_is_unmoved`] — the same rule body's
//!    un-woven `Expr::Apply`, which heads TRANSPARENTLY (functor = the callee) and
//!    must keep doing so. The two wrappers are not interchangeable: `Apply` has a
//!    direct term spelling (`dbl(2)`), `ApplyWithin` has only the reflect wrap.

use anthill_core::kb::node_occurrence::{occurrence_to_term, Expr, NodeOccurrence};
use anthill_core::kb::term_view::{views_structurally_equal, TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;
use std::rc::Rc;

use crate::common::load_kb_with;

/// A clause carrying `require[Desc[T]]` over a covered call written in the WI-938
/// arity+1 GOAL form, which is the only shape `collect_covered_calls` weaves — it
/// weaves only callees that hook recognizes (`functional_relation_arity`), so an
/// operand-position call produces no `Expr::ApplyWithin` at all. Lifted from
/// `wi1040_require_clause_dictionary_test`'s own fixture, which is the producer's
/// suite. `unwoven` is a PLAIN call, for the control row.
///
/// THE FIRST CUT OF THIS FIXTURE WROTE THE CALL AS AN `eq` OPERAND and produced ZERO
/// woven calls — caught by `sole_woven_call`'s count assertion rather than by a row
/// quietly passing over an occurrence that was never there.
const SRC: &str = r#"namespace fdpj8_aw
  import anthill.prelude.Int64
  import anthill.prelude.PartialEq.{eq}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  operation plain(n: Int64) -> Int64 = n

  rule woven(?x, ?r) :- require[Desc[T]], Desc.describe(?x, ?r)
  rule unwoven(?r) :- eq(?r, plain(3))
end
"#;

/// Every occurrence in `qn`'s rule bodies, depth-first — the woven call is nested
/// inside the `eq` goal, so a top-level scan of the body atoms would not reach it.
fn body_occurrences(kb: &KnowledgeBase, qn: &str) -> Vec<Rc<NodeOccurrence>> {
    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("`{qn}` must resolve"));
    let mut out = Vec::new();
    for rid in kb.rules_by_functor_iter(sym).collect::<Vec<_>>() {
        let mut stack: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
        while let Some(occ) = stack.pop() {
            if let Some(expr) = occ.as_expr() {
                anthill_core::kb::node_occurrence::for_each_child(expr, |c| {
                    stack.push(Rc::clone(c))
                });
            }
            out.push(occ);
        }
    }
    out
}

/// The one `Expr::ApplyWithin` the weave produced in `qn`'s body.
fn sole_woven_call(kb: &KnowledgeBase, qn: &str) -> Rc<NodeOccurrence> {
    let mut found: Vec<Rc<NodeOccurrence>> = body_occurrences(kb, qn)
        .into_iter()
        .filter(|o| matches!(o.as_expr(), Some(Expr::ApplyWithin { .. })))
        .collect();
    assert_eq!(
        found.len(),
        1,
        "`{qn}`'s body must hold exactly ONE woven call — 0 means the weave did not \
         fire and every row below would be measuring nothing",
    );
    found.pop().unwrap()
}

/// THE HEAD. `Functor{apply_within, 0 positional, 3 named}` — the entity's own shape
/// — where it was `ViewHead::Opaque`.
///
/// FAILS when the `Expr::ApplyWithin` arm is removed from `expr_wrapped_shape_inner`:
/// the head falls through to `_ => ViewHead::Opaque` and the `assert` names it.
#[test]
fn a_woven_call_heads_as_its_reflect_twin() {
    let mut kb = load_kb_with(SRC);
    let occ = sole_woven_call(&kb, "fdpj8_aw.woven");
    let aw = kb
        .try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .expect("the reflect entity must resolve");

    match occ.head(&kb) {
        ViewHead::Functor {
            functor: Some(f),
            pos_arity,
            named_arity,
        } => {
            assert_eq!(
                kb.qualified_name_of(f),
                kb.qualified_name_of(aw),
                "the head functor is the WRAP, `apply_within` — not the callee, which \
                 would disagree with the term twin, and not `Opaque`",
            );
            assert_eq!(
                (pos_arity, named_arity),
                (0, 3),
                "`entity apply_within(fn, args, requirements, type_args)` declares no \
                 positionals; `type_args` is CONDITIONAL and this call carries no \
                 bracket, so three named children",
            );
        }
        other => panic!(
            "a woven call must not head as {other:?} — `Opaque` is payload-free, so \
             two structurally different woven calls compare EQUAL under it"
        ),
    }

    let keys: Vec<String> = occ
        .named_keys(&kb)
        .into_iter()
        .map(|k| kb.local_name_of(k).to_string())
        .collect();
    assert_eq!(
        keys,
        vec!["fn", "args", "requirements"],
        "the keys are the ENTITY's fields in DECLARED order, which is the discrim \
         tree's order",
    );
}

/// THE TWIN, and the reason the head and this arm had to land together: a head with
/// no term twin is not agreement, only a different disagreement — the view announcing
/// children `occurrence_to_term` answers `Bottom` for.
///
/// FAILS when either half is backed out: without the head arm the view says `Opaque`
/// and the functors differ; without the `try_occurrence_to_term` arm the twin is `⊥`.
#[test]
fn a_woven_call_and_its_term_twin_read_alike() {
    let mut kb = load_kb_with(SRC);
    let occ = sole_woven_call(&kb, "fdpj8_aw.woven");
    let occ_head = occ.head(&kb);
    let occ_keys = occ.named_keys(&kb);

    let twin = occurrence_to_term(&mut kb, &occ);
    assert!(
        !matches!(kb.get_term(twin), anthill_core::kb::term::Term::Bottom),
        "the twin must be a real term — `⊥` is what the missing arm produced, and it \
         is the partial-twin shape WI-815 hardened `fingerprint_into` against",
    );
    assert_eq!(
        format!("{:?}", anthill_core::eval::Value::term(twin).head(&kb)),
        format!("{occ_head:?}"),
        "WI-425's isomorphism: the occurrence and its term twin present ONE head",
    );
    assert_eq!(
        anthill_core::eval::Value::term(twin).named_keys(&kb),
        occ_keys,
        "…and one key set, or a consumer reading one carrier decides differently \
         from a consumer reading the other",
    );

    // DEEP, not just the head and the key set. Every child this ticket had to build by
    // hand sits BELOW that level, and the first cut of this row stopped at the top.
    //
    // WHAT IT CATCHES, MEASURED rather than listed: building the `args` spine's cells
    // with the wrong reflect constructor (`type_arg` for `ApplyArg`) fails HERE and
    // passes both assertions above.
    //
    // WHAT IT DOES NOT CATCH, said because the first draft of this comment claimed it
    // did and the probe falsified that: swapping `plain_occurrence_list`'s
    // nullary-`Fn{nil}` for a bare `Expr::Ref(nil)` leaves this row GREEN. `head`
    // canonicalizes `Ref(f)` and a nullary `Fn{f}` to ONE `ViewHead::nullary` (WI-436),
    // so the two conventions are view-IDENTICAL by design and no view comparison can
    // separate them. That choice is about the stored bytes and the discrim keying, and
    // it is made — with its reason — at that function, not measured here.
    assert!(
        views_structurally_equal(&kb, &occ, &anthill_core::eval::Value::term(twin)),
        "the occurrence and its term twin must be structurally EQUAL all the way \
         down: one shape, whichever carrier a reader holds",
    );
}

/// THE DECLARATION carries every field its producers build — the `type_args` channel
/// `visit_fn` already read and `weave_covered_call` already carried.
///
/// FAILS when `type_args` is dropped from the `apply_within` entity: the field list
/// comes back three long.
#[test]
fn the_declaration_carries_every_field_its_producers_build() {
    let kb = load_kb_with(SRC);
    let aw = kb
        .try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .expect("the reflect entity must resolve");
    let fields: Vec<String> = kb
        .entity_field_names(aw)
        .expect("`apply_within` is an entity, so it has a declared field list")
        .iter()
        .map(|s| kb.local_name_of(*s).to_string())
        .collect();
    assert_eq!(
        fields,
        vec!["fn", "args", "requirements", "type_args"],
        "`apply_within` mirrors `apply`'s `type_args` slot — the occurrence carries \
         the channel and `visit_fn` reads it, so a schema without it is the one of \
         the three that is wrong",
    );
}

/// THE CONTROL. A plain call in a rule body is an `Expr::Apply`, and it heads
/// TRANSPARENTLY — functor = the CALLEE — because it HAS a direct term spelling
/// (`plain(3)`), which `try_occurrence_to_term` builds. The two wrappers are not
/// interchangeable, and this row is what says the change above reached the woven form
/// only. Passes with every back-out in the table applied.
#[test]
fn a_plain_call_in_the_same_clause_is_unmoved() {
    let kb = load_kb_with(SRC);
    let plain = kb
        .try_resolve_symbol("fdpj8_aw.plain")
        .expect("`plain` must resolve");
    let found = body_occurrences(&kb, "fdpj8_aw.unwoven")
        .into_iter()
        .find(|o| matches!(o.as_expr(), Some(Expr::Apply { functor, .. }) if *functor == plain))
        .expect("the un-woven body holds a plain `plain(3)` call");
    assert!(
        matches!(
            found.head(&kb),
            ViewHead::Functor { functor: Some(f), pos_arity: 1, .. } if f == plain
        ),
        "a plain call heads as its CALLEE at its own arity — the transparent reading \
         the woven form must NOT take, since its term twin is the `apply_within` wrap",
    );
}
