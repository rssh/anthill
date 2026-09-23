//! WI-20260911-5G28A, L3 — THE PAREN-LESS BRACKETED CITATION `Sort[…].rel` lowers to the
//! same zero-argument call the applied `Sort[…].rel()` builds
//! (`convert::convert_paren_less_citation`), so both spellings reach one lowering and the
//! bracket is validated either way.
//!
//! BACK-OUT, measured one axis at a time (each run, not predicted):
//!  * [C] the converter — in `parse/convert.rs`, drop the `"field_access" if …
//!    "application"` arm of the term dispatch and the `Some(o) if o.kind() ==
//!    "application"` rung of `is_value_receiver`. 7 red: `the_paren_less_bracket_is_
//!    validated` (loads clean: the bindings were erased), `a_bracketed_chain_followed_by_a_
//!    projection_is_a_citation` (three "expected resolved name" errors), `a_let_bound_
//!    citation_is_a_relation_value` (one), `a_bracketed_goal_in_a_rule_body_is_the_goal`
//!    (it answers 0 rows while its bare twin answers 1 — a silent wrong answer, under which
//!    `not(…)` would succeed), `a_nested_sort_after_the_bracket_is_refused` (loads clean: the
//!    bracket was erased on the way to `Outer.Inner.op`), `a_bracket_on_a_zero_field_
//!    constructor_meets_the_sweep` (loads clean) and `a_paren_less_bracket_on_an_operation_
//!    is_refused` (on its message: "zero.name: expected resolved name").
//!  * [U] the unresolved skip — in `kb/load.rs`, `refuse_paren_less_non_rule` without its
//!    `def.kinds().is_empty()` test. 1 red: `a_typo_after_the_bracket_draws_one_error`
//!    (a second error, quoting the unresolved dotted name as the member).
//!  * [R] the refusal — the `refuse_paren_less_non_rule` call removed. 2 red:
//!    `a_paren_less_bracket_on_an_operation_is_refused` (loads clean: a CALL the author did
//!    not write) and `a_nested_sort_after_the_bracket_is_refused` (only the typer's
//!    "unknown functor" is left, about a sort it knows).
//!  * [G] the rule-compound gate — `!self.lowering_rule_compound_expr` dropped from the
//!    refusal's call site. 1 red: `a_rule_body_data_slot_takes_the_applied_reading` (a
//!    load error on the `if`, one level below a data slot that loads).
//!
//! The query-pattern twin of the refusal — `load::query_bracket_errors` — is a CLI row
//! (`anthill-cli`'s `wi_5g28a_query_bracket_test`), because a pattern is converted there.
//!
//! PASS EITHER WAY, BY DESIGN: `both_spellings_answer_the_same_count` under [C] (the erased
//! bracket still left the flattened name `Wrap.tag.takeN`, which reached the same rule) —
//! it pins that the lowering did not change what the paren-less spelling answers;
//! `a_typo_after_the_bracket_draws_one_error` under [C] (the flattened chain drew one
//! error too — the row guards [U] alone); and the bare twin inside
//! `a_bracketed_goal_in_a_rule_body_is_the_goal` under every axis.
//!
//! NOT IN THIS SLICE, said so a green row is not read as more: the citation still types
//! its column at the clause's own `T` (`got Wrap[T = ?T]` for a bound `?x: Wrap[T = T]`),
//! the same for both spellings — the bracket is read and validated, not yet pinned.
//! A RULE-BODY DATA SLOT takes the applied reading too: `?y <=> Box[T = Int64].zero` binds
//! the call's 0, as `Box[T = Int64].zero()` and a bare one-segment `zero` do (§5.4), where
//! it used to bind the data term `zero` the bare DOTTED `Box.zero` still binds there.

use anthill_core::persistence::print::TermPrinter;

/// `Colour`, `Wrap[T]` and its two-row `tag`, followed by the operations `ops` declares.
fn fixture(ops: &str) -> String {
    format!(
        "namespace zz5g28al3\n\
         \x20 import anthill.prelude.{{Int64, EmptyStream}}\n\
         \x20 sort Colour\n\
         \x20   entity red\n\
         \x20   entity green\n\
         \x20 end\n\
         \x20 sort Wrap[T]\n\
         \x20   entity wrap(v: T)\n\
         \x20   rule tag(?x) :- ?x <=> wrap(red()) | ?x <=> wrap(green())\n\
         \x20 end\n\
         {ops}\
         end\n"
    )
}

#[test]
fn the_paren_less_bracket_is_validated() {
    // The applied twin `Wrap[W = Colour].tag()` was already refused with this message;
    // the paren-less one loaded clean because its bindings never reached a lowering.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            "namespace zz5g28al3w\n\
             \x20 import anthill.prelude.{Int64}\n\
             \x20 sort Colour\n\
             \x20   entity red\n\
             \x20 end\n\
             \x20 sort Wrap[T]\n\
             \x20   entity wrap(v: T)\n\
             \x20   rule tag(?x) :- ?x <=> wrap(red())\n\
             \x20 end\n\
             \x20 operation go() -> Int64 effects {Error} = Wrap[W = Colour].tag.takeN(5).length()\n\
             end\n",
        ),
        &["has no type parameter named 'W'"],
    );
}

#[test]
fn a_bracketed_chain_followed_by_a_projection_is_a_citation() {
    // DRIVEN, not loaded: the chain must evaluate to the rule's first row. Before, the
    // instantiation root matched no citation reader (they want a name-rooted chain) and
    // each segment was an unresolved name.
    let mut interp = crate::common::interp_for(&fixture(
        "  operation first() -> Wrap[T = Colour] effects {Error, Error[EmptyStream]}\n\
         \x20   = Wrap[T = Colour].tag.head.x\n",
    ));
    let out = interp.call("zz5g28al3.first", &[]).expect("first evaluates");
    let rendered = match &out {
        anthill_core::eval::Value::Node(occ) => {
            TermPrinter::new(interp.kb()).print_occurrence(occ)
        }
        other => format!("{other:?}"),
    };
    assert!(
        rendered.contains("red") && !rendered.contains("green"),
        "`Wrap[T = Colour].tag.head.x` must answer the FIRST row, wrap(red()), got `{rendered}`",
    );
}

#[test]
fn a_let_bound_citation_is_a_relation_value() {
    // The citation as a VALUE on its own, not as a dot receiver: this reaches the
    // converter's term-dispatch arm without the `is_value_receiver` rung, so it is the row
    // that separates the two halves of [C].
    let mut interp = crate::common::interp_for(&fixture(
        "  operation viaLet() -> Int64 effects {Error} =\n\
         \x20   let r = Wrap[T = Colour].tag\n\
         \x20   r.takeN(5).length()\n",
    ));
    match interp.call("zz5g28al3.viaLet", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(n, 2, "both rows of `tag`"),
        other => panic!("viaLet: expected Int(2), got {other:?}"),
    }
}

#[test]
fn both_spellings_answer_the_same_count() {
    // CONTROL — passes with the change backed out, BY DESIGN (see the module header).
    // It pins that the new lowering did not change what the paren-less spelling answers.
    let mut interp = crate::common::interp_for(&fixture(
        "  operation n_bare() -> Int64 effects {Error} = Wrap[T = Colour].tag.takeN(5).length()\n\
         \x20 operation n_applied() -> Int64 effects {Error} = Wrap[T = Colour].tag().takeN(5).length()\n",
    ));
    for op in ["zz5g28al3.n_bare", "zz5g28al3.n_applied"] {
        match interp.call(op, &[]) {
            Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(n, 2, "{op}"),
            other => panic!("{op}: expected Int(2), got {other:?}"),
        }
    }
}

#[test]
fn a_bracketed_goal_in_a_rule_body_is_the_goal() {
    // A rule body is the other lowering the marked node reaches, and there it takes the
    // applied reading with no refusal. Before, `:- Wrap[T = Colour].holds` was a
    // `field_access` term heading no clause: it loaded clean and answered NOTHING, where
    // the bare `:- Wrap.holds` and the applied `:- Wrap[T = Colour].holds()` answer.
    let mut kb = crate::common::load_kb_with(
        "namespace zz5g28al3g\n\
         \x20 sort Colour\n\
         \x20   entity red\n\
         \x20 end\n\
         \x20 sort Wrap[T]\n\
         \x20   entity wrap(v: T)\n\
         \x20   rule holds :- true\n\
         \x20 end\n\
         \x20 rule viaBracket(1) :- Wrap[T = Colour].holds\n\
         \x20 rule viaBare(1) :- Wrap.holds\n\
         end\n",
    );
    assert_eq!(
        crate::common::definite_unary(&mut kb, "zz5g28al3g.viaBare").len(),
        1,
        "CONTROL: the bare goal answers — passes under every back-out, by design",
    );
    assert_eq!(
        crate::common::definite_unary(&mut kb, "zz5g28al3g.viaBracket").len(),
        1,
        "the bracketed paren-less goal must answer as the bare one does",
    );
}

#[test]
fn a_rule_body_data_slot_takes_the_applied_reading() {
    // The ONE silent answer change of the delivery, pinned so it cannot move unseen. In a
    // rule-body DATA slot the marked node is the applied call, so a nullary operation is
    // CALLED — as `Box[T = Int64].zero()` and §5.4's bare one-segment `zero` are — where
    // it used to bind the data term `zero` (which the bare DOTTED `Box.zero` still binds).
    //
    // And a rule's COMPOUND expression is a rule body too: `refuse_paren_less_non_rule`
    // is skipped under `lowering_rule_compound_expr`, so the `if` below loads. With that
    // gate backed out it is a load error one `if` deeper than a spelling that loads.
    let mut kb = crate::common::load_kb_with(
        "namespace zz5g28al3d\n\
         \x20 import anthill.prelude.{Int64, Bool}\n\
         \x20 sort Box[T]\n\
         \x20   entity box(v: Int64)\n\
         \x20   operation zero() -> Int64 = 0\n\
         \x20 end\n\
         \x20 rule dataSlot(?y) :- ?y <=> Box[T = Int64].zero\n\
         \x20 rule applied(?y) :- ?y <=> Box[T = Int64].zero()\n\
         \x20 rule inIf(?y) :- ?y <=> (if true then Box[T = Int64].zero else 1)\n\
         end\n",
    );
    for rel in ["zz5g28al3d.dataSlot", "zz5g28al3d.applied"] {
        let rows = crate::common::definite_unary(&mut kb, rel);
        assert_eq!(rows.len(), 1, "{rel}: one definite row");
        assert_eq!(
            crate::common::scalar_int(&kb, &rows[0]),
            Some(0),
            "{rel}: the nullary operation is CALLED in a data slot, got {:?}",
            rows[0],
        );
    }
    assert_eq!(
        crate::common::definite_unary(&mut kb, "zz5g28al3d.inIf").len(),
        1,
        "the compound expression is not refused and answers",
    );
}

#[test]
fn a_paren_less_bracket_on_an_operation_is_refused() {
    // Paren-less is the RULE-citation spelling: the bare `Box.zero` names no operation
    // either (an unresolved name). The bracketed one must not become a silent call — which
    // it does without the refusal, because the lowering is the zero-argument call and
    // `zero` takes no arguments.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            "namespace zz5g28al3o\n\
             \x20 import anthill.prelude.{Int64}\n\
             \x20 sort Box[T]\n\
             \x20   entity box(v: Int64)\n\
             \x20   operation zero() -> Int64 = 0\n\
             \x20 end\n\
             \x20 operation go() -> Int64 = Box[T = Int64].zero\n\
             end\n",
        ),
        &["`Box[…].zero` without parentheses is a RULE citation, and `zero` is an operation \
           — call it `Box[…].zero()`"],
    );
}

#[test]
fn a_nested_sort_after_the_bracket_is_refused() {
    // `Inner` is a SORT: nothing on this path reads `Outer`'s bracket. Before, the chain
    // flattened to `Outer.Inner.op` with the bracket ERASED and loaded clean. The second
    // error is the typer's verdict on the zero-argument call the node stays — the one the
    // applied `Outer[T = Int64].Inner()` draws — left standing on purpose (see
    // `refuse_paren_less_non_rule`).
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            "namespace zz5g28al3n\n\
             \x20 import anthill.prelude.{Int64}\n\
             \x20 sort Outer[T]\n\
             \x20   entity outer(v: T)\n\
             \x20   sort Inner\n\
             \x20     entity inner\n\
             \x20     operation op() -> Int64 = 1\n\
             \x20   end\n\
             \x20 end\n\
             \x20 operation go() -> Int64 = Outer[T = Int64].Inner.op()\n\
             end\n",
        ),
        &[
            "`Outer[…].Inner` without parentheses is a RULE citation, and `Inner` names no \
             rule — a type bracket before a dot is read by a rule citation or an operation \
             call and by nothing else, so here it would bind nothing; drop it (`Outer.Inner`)",
            "got unknown functor",
        ],
    );
}

#[test]
fn a_bracket_on_a_zero_field_constructor_meets_the_sweep() {
    // WI-20260902-2NXAC's "NOT COVERED" row, closed as a side effect of the lowering: the
    // paren-less spelling used to be a `field_access` chain that never carried the bracket
    // to `check_unconsumed_recv_types`, so `?v <=> Bx[T = Int64].nada` LOADED CLEAN where
    // the applied `Bx[T = Int64].nada()` was refused. It is now the applied term, refused
    // by the same sweep with the same words.
    let errs = crate::common::try_load_kb_with(
        "namespace zz5g28al3z\n\
         \x20 import anthill.prelude.Int64\n\
         \x20 sort Bx\n\
         \x20   sort T = ?\n\
         \x20   entity bx(k: Int64)\n\
         \x20   entity nada\n\
         \x20 end\n\
         \x20 rule cc(1) :- ?v <=> Bx[T = Int64].nada\n\
         end\n",
    )
    .err()
    .unwrap_or_default();
    crate::common::assert_refused_naming(
        &errs,
        &["companion receiver's type bracket is not read here", "`Bx.nada`"],
        "a bracket on a zero-field constructor, written paren-less",
    );
}

#[test]
fn a_typo_after_the_bracket_draws_one_error() {
    // An UNRESOLVED member is the typer's to report, as it is for the bare `Wrap.tagg`:
    // the paren-less refusal must not add a second error about a name that has no kind
    // to be "not a rule".
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&fixture(
            "  operation typo() -> Int64 effects {Error} = Wrap[T = Colour].tagg.takeN(5).length()\n",
        )),
        &["got unknown functor"],
    );
}
