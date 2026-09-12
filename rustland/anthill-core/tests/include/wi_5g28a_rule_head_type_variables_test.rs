//! WI-20260911-5G28A — RULE HEAD TYPE VARIABLES: opened per CITATION at the typer, read
//! off the VALUE at the resolver, minted for UNWRITTEN parameters at the loader.
//!
//! FIVE AXES, FIVE BACK-OUTS. Each group names the one edit that reddens it; a row that
//! passes with its axis backed out is marked as a control and says so.
//!
//!  A. `typing::relation_reference_type_applied`'s `type_mentions_flex_var` arm —
//!     make it fall through to `types_compatible`.
//!  B. `typing::pin_bound_from_value` — return `TypeBoundPin::NotApplicable` always.
//!  C. `KnowledgeBase::assert_rule_debruijn_with_bound_vars` — drop the `bound_vars` loop.
//!  D. `load::expand_unwritten_type_params`'s `Term::Ref` arm — return `t` unchanged.
//!  E. `resolve::domain_member_goal_is_undetermined` — return `false`.
//!
//! AXIS E IS NOT A RED, IT IS A HANG, and that is the measurement: with the mode-(out)
//! guard removed, `anylist` opens a choice point per derived domain and the search is a
//! product of two infinite streams. `an_undetermined_element_type_delays_rather_than_
//! enumerating` therefore asserts that the query RETURNS, with the member goal standing
//! in its residual.

use anthill_core::kb::term::Term;
use anthill_core::kb::term::TermId;
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;

// ── fixtures ───────────────────────────────────────────────────────────────────

/// The head that TIES two columns to one unwritten element type, plus an operation that
/// cites it with `params` and declares `ret`.
fn tied(params: &str, ret: &str) -> String {
    format!(
        "namespace zz5g28a\n\
         \x20 import anthill.prelude.{{List, Int64, String, EmptyStream}}\n\
         \n\
         \x20 rule my_rule(?x: List[T = ?t], ?res: List[T = ?t]) :- ?res <=> ?x\n\
         \n\
         \x20 operation o({params}) -> {ret}\n\
         \x20   effects {{Error, Error[EmptyStream]}}\n\
         \x20   = my_rule(x).head.res\n\
         end\n"
    )
}

/// The SAME program with the tie written out CONCRETELY — group A's control fixture. Its
/// columns mention no variable, so the new arm is never reached and all three rows read
/// the same with axis A backed out.
fn exact(params: &str, ret: &str) -> String {
    format!(
        "namespace zz5g28a\n\
         \x20 import anthill.prelude.{{List, Int64, String, EmptyStream}}\n\
         \n\
         \x20 rule my_rule(?x: List[T = Int64], ?res: List[T = Int64]) :- ?res <=> ?x\n\
         \n\
         \x20 operation o({params}) -> {ret}\n\
         \x20   effects {{Error, Error[EmptyStream]}}\n\
         \x20   = my_rule(x).head.res\n\
         end\n"
    )
}

// ── A. THE TYPER — a head's type variables open per CITATION ────────────────────

#[test]
fn a_concrete_argument_pins_the_tied_column() {
    crate::common::expect_loaded(crate::common::try_load_kb_with(&tied(
        "x: List[T = Int64]",
        "List[T = Int64]",
    )));
}

#[test]
fn a_mismatched_return_is_refused_through_the_pin() {
    // THE MESSAGE IS THE EVIDENCE, not merely the refusal. `?t := Int64` from the
    // argument, so the surviving `res` column walks out as `List[T = Int64]` and the
    // declared `List[T = String]` is what mismatches. Before this ticket the same program
    // was refused one step EARLIER — at the column bind, "argument binding column `x` has
    // an incompatible type" — which is also what the ACCEPTING row above said, so the two
    // were indistinguishable.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&tied("x: List[T = Int64]", "List[T = String]")),
        &["expected List[T = String], got List[T = Int64]"],
    );
}

#[test]
fn a_rigid_argument_pins_the_tie_to_its_own_projection() {
    crate::common::expect_loaded(crate::common::try_load_kb_with(&tied(
        "x: List, y: List",
        "List[T = x.T]",
    )));
}

#[test]
fn the_other_receivers_projection_is_refused() {
    // No receiver re-keying (path-dependent-types.md §4.1's deferred ζ step) is involved:
    // in a RULE the tie IS a variable, so `?t := o.x.T` and `y.T` is a different neutral —
    // refused by ordinary σ-equality of one projection.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&tied("x: List, y: List", "List[T = y.T]")),
        &["expected List[T = y.T], got List[T = x.T]"],
    );
}

#[test]
fn the_accepted_rigid_row_evaluates() {
    // IT LOADS IS NOT IT WORKS. The row above is a TYPING verdict; this drives the same
    // operation and asserts the VALUE, so a tie that typed clean and resolved to nothing
    // would be caught here. Driven through a nullary wrapper so the arguments are written
    // in anthill rather than assembled as host `Value`s.
    let src = "namespace zz5g28ae\n\
               \x20 import anthill.prelude.{List, Int64, String, EmptyStream}\n\
               \n\
               \x20 sort Letter\n\
               \x20   entity a\n\
               \x20   entity b\n\
               \x20 end\n\
               \n\
               \x20 rule my_rule(?x: List[T = ?t], ?res: List[T = ?t]) :- ?res <=> ?x\n\
               \n\
               \x20 operation op4(x: List, y: List) -> List[T = x.T]\n\
               \x20   effects {Error, Error[EmptyStream]}\n\
               \x20   = my_rule(x).head.res\n\
               \n\
               \x20 operation drive() -> List[T = Letter]\n\
               \x20   effects {Error, Error[EmptyStream]}\n\
               \x20   = op4([a(), b()], [1])\n\
               end\n";
    let mut interp = crate::common::interp_for(src);
    let out = interp.call("zz5g28ae.drive", &[]).expect("drive evaluates");
    // RENDERED, not `{:?}`-ed. The answer is a `Value::Node`, whose Debug is an occurrence
    // tree of `Symbol(1234)` handles — it contains no `a`, no `b` and no `1` as CONTENT, so
    // a `contains` over it measures the word "Span" and the digits of symbol ids. A first
    // cut asserted on that and passed vacuously.
    let rendered = match &out {
        anthill_core::eval::Value::Node(occ) => TermPrinter::new(interp.kb()).print_occurrence(occ),
        other => format!("{other:?}"),
    };
    // BOTH HALVES: that it IS `x`'s list, and that it is NOT `y`'s — the second is the
    // whole claim the rigid tie makes, and without it the row would pass on an operation
    // that returned either argument.
    assert!(
        rendered.contains('a') && rendered.contains('b'),
        "op4([a(), b()], [1]) must answer the FIRST list by value, got `{rendered}`",
    );
    assert!(
        !rendered.contains('1'),
        "it must be `x`'s list and not `y`'s — a `1` means the tie resolved to the wrong \
         argument, got `{rendered}`",
    );
}

// ── A-control: the exactly-typed head reads the same either way ─────────────────

#[test]
fn control_an_exact_column_accepts_its_own_type() {
    crate::common::expect_loaded(crate::common::try_load_kb_with(&exact(
        "x: List[T = Int64]",
        "List[T = Int64]",
    )));
}

#[test]
fn control_an_exact_column_refuses_a_wrong_return() {
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&exact("x: List[T = Int64]", "List[T = String]")),
        &["expected List[T = String], got List[T = Int64]"],
    );
}

#[test]
fn control_an_exact_column_refuses_a_rigid_argument() {
    // A rigid is not `Int64`, and this stays a COLUMN-BIND refusal: the column type
    // mentions no variable, so the new arm is not reached. PASSES EITHER WAY BY DESIGN.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&exact("x: List, y: List", "List[T = x.T]")),
        &["argument binding column `x` has an incompatible type"],
    );
}

// ── B/C. THE RESOLVER — the type read off the value, and opened per firing ──────

const RES: &str = "namespace zz5g28ar\n\
                   \x20 import anthill.prelude.{List, Int64, String}\n\
                   \x20 rule my_rule(?x: List[T = ?t], ?res: List[T = ?t]) :- ?res <=> ?x\n\
                   \x20 rule answers([1, 2]) :- my_rule([1, 2], ?r), ?r <=> [1, 2]\n\
                   \x20 rule mismatched([1, 2]) :- my_rule([1, 2], [\"a\"])\n\
                   \x20 rule two_calls(1) :- my_rule([1, 2], ?a), my_rule([\"s\"], ?b)\n\
                   end\n";

#[test]
fn a_tied_head_answers_definite_with_an_empty_residual() {
    // AXIS B. Before this ticket the same goal answered `?r = [1, 2]` as a CONDITIONAL,
    // carrying `domain([1, 2], List(T: ?t))` twice undischarged — the value was ground,
    // its type was known, and the bound PARKED. `definite_unary` is what makes the
    // difference assertable: `query_unary(..).len()` counts a floundered answer too.
    let mut kb = crate::common::load_kb_with(RES);
    assert_eq!(
        crate::common::definite_unary(&mut kb, "zz5g28ar.answers").len(),
        1,
        "the tie must DECIDE, not residualize",
    );
}

#[test]
fn the_tie_refutes_a_mismatched_second_column() {
    // AXIS B, the refuting direction: `?x` pins `?t := Int64` into the answer σ, so the
    // `?res` goal is checked against `List[Int64]` and `["a"]` fails.
    let mut kb = crate::common::load_kb_with(RES);
    assert_eq!(
        crate::common::definite_unary(&mut kb, "zz5g28ar.mismatched").len(),
        0,
    );
}

#[test]
fn the_bound_variable_is_opened_per_firing() {
    // AXIS C, and it is the row the ticket's own text got wrong: 5G28A states "the
    // variable is opened per resolution", and on the delivered tree it was NOT — a bound's
    // `?t` was a `Var::Global` in no frame (`globals` was `[x, res]`, while the twin rule
    // `p(?x) :- q(?x, ?y)` had its BODY-ONLY `?y` in the frame). Nothing had ever bound one,
    // so the sharing was invisible; the (in, out) read of axis B is what makes it a leak.
    // MEASURED with the frame admission backed out: this answers NO SOLUTIONS, because the
    // first call's `?t := Int64` refutes the second call's `List[T = String]`.
    let mut kb = crate::common::load_kb_with(RES);
    assert_eq!(
        crate::common::definite_unary(&mut kb, "zz5g28ar.two_calls").len(),
        1,
        "two citations of one rule are two instantiations of its bound's variable",
    );
}

// ── D. THE LOADER — an unwritten parameter becomes a rule-scoped variable ───────

const NEST: &str = "namespace zz5g28an\n\
                    \x20 import anthill.prelude.{List}\n\
                    \x20 sort Letter\n\
                    \x20   entity a\n\
                    \x20   entity b\n\
                    \x20   entity c\n\
                    \x20 end\n\
                    \x20 rule nest(?w: List[T = List]) :- ?w <=> [[a()]]\n\
                    \x20 rule anylist(?w: List) :- true\n\
                    \x20 rule nested_row([[a()]]) :- nest(?w), ?w <=> [[a()]]\n\
                    end\n";

/// The stored bound of `qn`'s single clause, rendered.
fn bound_of(kb: &KnowledgeBase, qn: &str) -> String {
    let rid = kb
        .rule_id_by_qn(qn)
        .unwrap_or_else(|| panic!("no rule {qn}"));
    let bounds = kb.rule_type_bounds(rid);
    assert_eq!(bounds.len(), 1, "{qn} has exactly one bound");
    TermPrinter::new(kb).print_term(bounds[0].1)
}

#[test]
fn an_unwritten_parameter_becomes_a_rule_scoped_variable() {
    // AXIS D. `Ref(List)` and the nullary `Fn{List}` are ONE spelling (WI-20260902-CZJ2N)
    // and neither names an element type; before this ticket `?w: List` stayed `Ref(List)`
    // and WI-743's determinacy gate SKIPPED its member goal, silently.
    let kb = crate::common::load_kb_with(NEST);
    let b = bound_of(&kb, "zz5g28an.anylist");
    assert!(
        b.contains("List") && b.contains('?'),
        "an unwritten parameter must be written as a variable, got `{b}`",
    );
}

#[test]
fn the_expansion_is_recursive_at_every_depth() {
    // AXIS D, the nested row: `List[T = List]` writes the INNER sort's parameter too.
    let kb = crate::common::load_kb_with(NEST);
    let b = bound_of(&kb, "zz5g28an.nest");
    let depth = b.matches("List").count();
    assert!(depth >= 2, "both `List`s must survive, got `{b}`");
    assert!(
        b.contains('?'),
        "the inner `List`'s unwritten parameter must be a variable, got `{b}`",
    );
}

#[test]
fn a_bound_body_decides_in_one_row() {
    // AXES B+D together, and the row WI-743 measured at 20: `nest`'s body binds `?w`
    // outright, so it has at most ONE answer. With the determinacy gate lifted and the
    // (in, out) read backed out (axis B) this reddens to the 20 rows WI-743 recorded.
    let mut kb = crate::common::load_kb_with(NEST);
    assert_eq!(
        crate::common::definite_unary(&mut kb, "zz5g28an.nested_row").len(),
        1
    );
}

// ── the generated member goal is PRESENT ───────────────────────────────────────

/// Does `qn`'s clause carry a body goal on `functor_qn`?
fn body_mentions(kb: &KnowledgeBase, qn: &str, functor_qn: &str) -> bool {
    let Some(target) = kb.try_resolve_symbol(functor_qn) else {
        return false;
    };
    let rid = kb
        .rule_id_by_qn(qn)
        .unwrap_or_else(|| panic!("no rule {qn}"));
    kb.rule_body_nodes(rid).iter().any(|n| {
        matches!(
            TermView::head(&anthill_core::eval::Value::Node(n.clone()), kb),
            ViewHead::Functor { functor: Some(f), .. } if f == target
        )
    })
}

#[test]
fn a_variable_bearing_bound_still_gets_its_member_goal() {
    // AXES B+D's enablement: WI-743 gated the member goal at LOAD on the bound naming a
    // determinate type, which a `?t` bound never does. Lifting that gate is what lets a
    // typed head with an unwritten or tied parameter GENERATE at all — and it is safe only
    // because the value now pins the type (axis B) and mode (out) delays (axis E).
    let kb = crate::common::load_kb_with(NEST);
    assert!(
        body_mentions(&kb, "zz5g28an.anylist", "anthill.kernel.domain_member"),
        "the member goal must be generated for a `?t`-bearing bound",
    );
    assert!(body_mentions(
        &kb,
        "zz5g28an.nest",
        "anthill.kernel.domain_member"
    ));
}

// ── E. MODE (out) OVER AN UNDETERMINED TYPE DELAYS ─────────────────────────────

#[test]
fn an_undetermined_element_type_delays_rather_than_enumerating() {
    // AXIS E, and its back-out HANGS rather than reddens (see the module header): with the
    // guard removed, `domain_member(?h, ?t)` — the element goal inside the derived `List`
    // clause — unifies with the head of EVERY derived clause, and the search is a product
    // of two infinite streams whose fairness is WI-20260911-09E6M's.
    //
    // WHAT IT MUST DO INSTEAD: come back, with NO definite row and the member goal standing
    // in the residual — visible and loud at the drain on WI-737's route, where WI-743's
    // load-time gate said nothing at all.
    let mut kb = crate::common::load_kb_with(NEST);
    let rows = crate::common::query_unary(&mut kb, "zz5g28an.anylist");
    assert!(
        rows.iter().all(|(_, definite)| !*definite),
        "an unpinned element type cannot yield a DEFINITE row",
    );
    assert!(!rows.is_empty(), "the goal must residualize, not vanish");
}

// ── DECISION A: the `[T]` introducer keeps its refusal, and names the other spelling ──

#[test]
fn an_unbounded_introducer_names_the_tie_spelling_as_its_repair() {
    // THE DECISION THE TICKET ASKED TO SETTLE. WI-582's `[T]` + `:- Spec[T]` records the
    // SPEC — `rule_head_bound_alias` substitutes the introducer by the spec's own symbol,
    // so the installed bound is nominal and the annotation is proposal 060 §3's requirement
    // anchor. This ticket's `?t` is a TIE with nothing required of it. Merging them would
    // let ONE spelling mean "same type as" in one clause and "provides this spec" in
    // another, decided by whether a guard appears elsewhere — so the refusal stands, and
    // what changes is that an author who wanted the tie is now TOLD which spelling it is.
    //
    // The back-out for this row is the message itself; the refusal half is
    // `wi_pw9a0_rule_tvar_in_bound_test::an_unbounded_introducer_reports_one_fault_not_two`,
    // which asserts the same error by its prefix and passes either way BY DESIGN.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            "namespace zz5g28ai\n\
             \x20 import anthill.prelude.{Int64}\n\
             \x20 rule g[A](?a: A, ?b) :- one(?a, ?b)\n\
             \x20 rule one(1, 2) :- true\n\
             end\n",
        ),
        // ONE error, so ONE expected string: `expect_load_errors` pairs them positionally
        // and asserts the COUNT, so three substrings would demand three separate errors.
        // The repair clause is the half this row is about; the refusal half is
        // `wi_pw9a0_rule_tvar_in_bound_test::an_unbounded_introducer_reports_one_fault_not_two`,
        // which also pins that this fault is reported exactly ONCE.
        &["write the variable in the bound itself — `?x: List[T = ?A]`"],
    );
}

// ── F. THE CORPUS CENSUS, asserted rather than grepped ─────────────────────────

#[test]
fn the_shipped_corpus_has_no_unwritten_parameter_in_a_rule_head_bound() {
    // THE POPULATION, NOT A FIXTURE. The acceptance asks how many corpus typed heads change
    // their answer count under the loader's expansion and the gate lift. This asks the KB:
    // every bound the stdlib installs must already name its parameters in full, so the
    // expansion is a no-op for all of them and NO corpus answer count moves.
    //
    // It is also the tripwire for the other direction: a future stdlib rule written
    // `?x: List` starts generating a member goal, and this row is where that is noticed.
    let kb = crate::common::load_kb_with(
        "namespace zz5g28acensus\n  import anthill.prelude.{List}\nend\n",
    );
    let mut unwritten: Vec<String> = Vec::new();
    for rid in kb.live_rule_ids() {
        for (_, bound) in kb.rule_type_bounds(rid) {
            if term_mentions_bare_parameterised_sort(&kb, *bound) {
                unwritten.push(TermPrinter::new(&kb).print_term(*bound));
            }
        }
    }
    assert!(
        unwritten.is_empty(),
        "corpus bounds naming a parameterised sort bare: {unwritten:?}",
    );
}

/// A `Term::Ref` / nullary `Term::Fn` on a sort that DECLARES type parameters — the shape
/// `load::expand_unwritten_type_params` rewrites. Reads the stored (De Bruijn-closed) term,
/// which is what the sweep left behind.
fn term_mentions_bare_parameterised_sort(kb: &KnowledgeBase, t: TermId) -> bool {
    match kb.get_term(t) {
        Term::Ref(s) => !kb.type_params_of_sort(*s).is_empty(),
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            if pos_args.is_empty() && named_args.is_empty() {
                return !kb.type_params_of_sort(*functor).is_empty();
            }
            let children: Vec<_> = pos_args
                .iter()
                .copied()
                .chain(named_args.iter().map(|&(_, c)| c))
                .collect();
            children
                .into_iter()
                .any(|c| term_mentions_bare_parameterised_sort(kb, c))
        }
        _ => false,
    }
}
