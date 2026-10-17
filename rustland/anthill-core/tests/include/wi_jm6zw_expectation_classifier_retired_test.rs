//! WI-20260824-JM6ZW (proposal 055 umbrella A, `docs/design/055-implementation.md` §10 step
//! 6 and §8) — THE EXPECTED `Type` NO LONGER CLASSIFIES. It validates a type value the
//! walks recorded; it decides nothing about what an expression is.
//!
//! RETIRED: the typer's `type_slot_arg_hint` and its gate `arg_names_sort`, the
//! `sort_app_hint` and the `Apply` frame's WI-707 arm it fed, `check_bare_ref`'s WI-206
//! arm, the declared-type lookups that existed only to feed the hint (`has_sort_arg`,
//! `has_sort_field`), and `expects_reflect_type`, which had no other caller.
//!
//! THE FINDING, which the ticket said would belong here and not in a later one: the hint
//! was still LOAD-BEARING, for RULE BODIES. Measured with a probe at the four retired arms
//! over the whole workspace (2026-10-17): every firing was a rule body (`wi710`, `wi839`,
//! `wi1058`, `wi927`, `wi_9r5hn`, `wi_9wvt7`, `wi_rxt6s`) — the operation-body walk
//! records every type value since WAHB6, the rule-body walk recorded none. With the hint
//! gone and nothing else changed, 8 rows of those files failed (back-out (3) below). The
//! rule-body walk (`Loader::build_body_atom_occurrence_inner`) now records them as the
//! operation-body walk does — a bare sort in a data slot (`Loader::body_bare_type_value`)
//! and a nested bracketed sort application — and the 8 pass. The clause each such body
//! matches is unmoved: the node heads as the term it was
//! ([`the_clause_a_rule_body_matches_is_unmoved`]).
//!
//! ── BACK-OUTS, MEASURED (2026-10-17) over this file and its peers — `wi206`, `wi707`,
//! `wi709`, `wi710`, `wi927`, `wi839`, `wi1058`, `wi_9r5hn`, `wi_9wvt7`, `wi_rxt6s`,
//! `wi_wahb6`, `wi_q0093`, `wi_a3fy2`, `wi_tcsgt`, `dotted_nullary_op_call_test`, `wi92va4`,
//! `wi_5g28a`, `wi_51w18`, `wi_96ztm`, `wi_gfs6a`, `wi_mhrn1`, `wi_qmfc5`: 286 rows ──
//!
//! (1) THE HINTS RESTORED, THE RECORD KEPT (the six typer files as they were): 3 fail, all
//!     here, and NOT ONE PEER ROW — which is what says the hint carries nothing any more.
//!     [`a_sort_applied_with_parentheses_is_no_type_application`] fails because the hint
//!     read `is_modifiable(Cell(Int64))` as `Cell[Int64]` over the written surface and the
//!     program loaded; [`a_plain_reference_to_a_sort_is_refused_where_a_type_is_expected`]
//!     and [`a_sort_headed_application_is_no_type_where_a_type_is_expected`] ask the typer
//!     the retired question directly.
//!
//! (2) THE RECORD REMOVED, THE HINTS GONE (both walks' predicates forced off): 93 fail —
//!     every WI-206 and WI-707 row that reads a type value, the WAHB6 / Q0093 / RXT6S /
//!     TCSGT / A3FY2 rows that do, and here every row whose fixture holds a sort written
//!     as a value, because with nothing recording it such a fixture does not load (the
//!     clause control included — it is a control of worlds (1) and (3), not of this one).
//!     What passes here is what reads no recorded sort: the forgotten-parentheses row (a
//!     free-standing entity is recorded by no walk), the namespace-first row (a relation
//!     goal's argument is checked by the loader, not typed) and the two hand-built rows.
//!
//! (3) ONLY THE RULE-BODY RECORD REMOVED (hints gone): 11 fail — the 8 peer rows,
//!     `wi1058::a_type_application_in_a_rule_body_is_not_a_call`,
//!     `wi710::a_rule_body_type_pattern_with_variable_arguments_still_loads`,
//!     `wi839::a_rule_body_type_application_still_loads`, `wi927`'s two eponymous-bracket
//!     rows and `wi_9r5hn`'s three rule-body rows; and here
//!     [`a_rule_body_records_a_bare_sort_as_a_type_value`],
//!     [`a_rule_body_records_a_bracketed_sort_application_as_a_type_value`] and
//!     [`a_whole_equation_rhs_is_recorded_as_its_bare_twin_is`].
//!     [`a_rule_body_type_value_is_the_term_an_operation_body_evaluates_to`] PASSES there,
//!     and it is worth knowing why: a `<=>` operand's call arguments are not typed (see
//!     below), so nothing refuses the unrecorded node, and eval's `reduce_var` /
//!     sort-headed `Apply` arms answer it with the same term. It pins the VALUE; the
//!     record rows are what measure the record.
//!
//! (4) `denoted_type_value`'s free-standing-entity arm removed: 1 fails,
//!     [`a_forgotten_parentheses_construction_names_the_denoted_type`].
//!
//! THE PIECES `/code-review` ASKED FOR, one back-out each, 1 row apiece unless said:
//!   * `term_depth > 1` back in the walk's `type_value` gate —
//!     [`a_whole_equation_rhs_is_recorded_as_its_bare_twin_is`];
//!   * a dotted name's segments not given the non-value role —
//!     `dotted_nullary_op_call_test::an_eq_operand_is_typed_and_run_as_the_call`;
//!   * the `require[Spec]` slot not given it — 8 rows of `wi_51w18`, `wi_96ztm`, `wi_gfs6a`,
//!     `wi_mhrn1`, `wi_qmfc5` (named at `Loader::in_non_value_role`);
//!   * WI-710's gate as it was (`kind_of`, no `type_value` disjunct) —
//!     [`a_type_value_s_arguments_are_checked_whatever_order_its_name_was_declared_in`];
//!   * `substitute_to_occurrence` not recording — the unit row
//!     `simp_rewrite::tests::a_sort_in_a_term_built_rhs_is_recorded_as_a_type_value`.
//!
//! PASS EITHER WAY BY DESIGN: [`the_clause_a_rule_body_matches_is_unmoved`] in worlds (1)
//! and (3) (it pins what the record must NOT move), and the shadowing half of the
//! forgotten-parentheses row.
//!
//! NO RULE-BODY DESTINATION ROW, and the reason is measured rather than skipped: a rule
//! body checks no destination a type value could be refused at. `?x <=> needs_int("s")`
//! over `needs_int(n: Int64)` loads, and so does `rule r(?x: Int64) :- ?x <=> "s"` — the
//! control that says this is not about type values. The operation-body rows of
//! `wi_q0093_type_value_occurrence_matrix_test` are where §8's wrong-destination text is
//! driven.

use std::rc::Rc;

use anthill_core::eval::Value;
use anthill_core::intern::SymbolKind;
use anthill_core::kb::node_occurrence::{for_each_child, value_to_term, Expr, NodeOccurrence};
use anthill_core::kb::term::Term;
use anthill_core::kb::typing::{sort_functor_of_view, type_check_node, TypeError, TypingEnv};
use anthill_core::kb::KnowledgeBase;
use anthill_core::span::{SourceId, SourceSpan};

use crate::common::{load_errors_of, load_kb_with, load_stdlib_kb, query_unary};

const SRC: &str = r#"
namespace test.jm6zw
  import anthill.prelude.{Bool, Cell, Int64, Type}
  import anthill.reflect.{is_modifiable}

  operation id_ty(t: Type) -> Type = t
  operation bare() -> Type = Cell
  operation applied() -> Type = Cell[V = Int64]

  rule rb_bare(?x) :- ?x <=> id_ty(Cell)
  rule rb_applied(?x) :- ?x <=> id_ty(Cell[V = Int64])
  rule ob_bare(?x) :- ?x <=> bare()
  rule ob_applied(?x) :- ?x <=> applied()
  rule rb_modifiable(?x) :- ?x <=> is_modifiable(Cell[V = Int64])

  fact holds(Cell)
  fact holds(Cell[V = Int64])
  rule holds_bare(1) :- holds(Cell)
  rule holds_applied(2) :- holds(Cell[V = Int64])
end
"#;

/// Every node of `rule_qn`'s stored body, outermost first.
fn rule_body_nodes(kb: &KnowledgeBase, rule_qn: &str) -> Vec<Rc<NodeOccurrence>> {
    let sym = kb
        .try_resolve_symbol(rule_qn)
        .unwrap_or_else(|| panic!("{rule_qn} must resolve"));
    let rids = kb.rules_by_functor(sym);
    assert_eq!(rids.len(), 1, "{rule_qn}: one clause");
    let mut out = Vec::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rids[0]).to_vec();
    while let Some(n) = stack.pop() {
        if let Some(e) = n.as_expr() {
            for_each_child(e, |c| stack.push(Rc::clone(c)));
        }
        out.push(n);
    }
    out
}

/// The type values in a rule body that are not the argument of another type value.
fn outer_type_values(kb: &KnowledgeBase, rule_qn: &str) -> Vec<Rc<NodeOccurrence>> {
    let nodes = rule_body_nodes(kb, rule_qn);
    let inner: Vec<*const NodeOccurrence> = nodes
        .iter()
        .filter_map(|n| match n.as_expr() {
            Some(Expr::TypeValue {
                pos_args,
                named_args,
                ..
            }) => Some(
                pos_args
                    .iter()
                    .chain(named_args.iter().map(|(_, a)| a))
                    .map(Rc::as_ptr)
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flatten()
        .collect();
    nodes
        .into_iter()
        .filter(|n| matches!(n.as_expr(), Some(Expr::TypeValue { .. })))
        .filter(|n| !inner.contains(&Rc::as_ptr(n)))
        .collect()
}

/// No plain reference to a sort is left in the body — the shape the retired hint re-read.
fn assert_no_plain_sort_reference(kb: &KnowledgeBase, rule_qn: &str) {
    for n in rule_body_nodes(kb, rule_qn) {
        if let Some(Expr::Ref(s) | Expr::Ident(s) | Expr::VarRef { name: s }) = n.as_expr() {
            assert!(
                !kb.has_kind(*s, SymbolKind::Sort),
                "{rule_qn}: `{}` is still a plain reference",
                kb.qualified_name_of(*s)
            );
        }
    }
}

/// The answer's TERM, whatever carrier it rides: a rule body hands an operation its operand
/// as the occurrence (`Value::Node`, WI-20260827-3ZNBC), so `id_ty`'s answer is the node it
/// was given, where an operation body's evaluated type value is a `Value::Term`. One term
/// either way is the claim; the carrier was a `Node` before this ticket too.
fn answer_term(kb: &mut KnowledgeBase, rule_qn: &str) -> anthill_core::kb::term::TermId {
    let rows = query_unary(kb, rule_qn);
    assert_eq!(rows.len(), 1, "{rule_qn}: one answer, got {rows:?}");
    value_to_term(kb, &rows[0].0)
        .unwrap_or_else(|e| panic!("{rule_qn}: a type term, got {:?} ({e:?})", rows[0].0))
}

/// THE RECORD, bare face: `id_ty(Cell)` in a rule body holds an `Expr::TypeValue`, not the
/// `Expr::Ref` the hint used to re-read from `id_ty`'s declared `Type`.
#[test]
fn a_rule_body_records_a_bare_sort_as_a_type_value() {
    let kb = load_kb_with(SRC);
    let tvs = outer_type_values(&kb, "test.jm6zw.rb_bare");
    assert_eq!(tvs.len(), 1, "one type value in `?x <=> id_ty(Cell)`");
    match tvs[0].as_expr() {
        Some(Expr::TypeValue {
            head,
            pos_args,
            named_args,
        }) => {
            assert_eq!(kb.local_name_of(*head), "Cell");
            assert!(pos_args.is_empty() && named_args.is_empty(), "the BARE face");
        }
        _ => unreachable!(),
    }
    assert_no_plain_sort_reference(&kb, "test.jm6zw.rb_bare");
}

/// THE RECORD, applied face, and its argument is recorded too — the inner `Int64` is a
/// type value by the same rule, not by a `Type` pushed down from the application.
#[test]
fn a_rule_body_records_a_bracketed_sort_application_as_a_type_value() {
    let kb = load_kb_with(SRC);
    let tvs = outer_type_values(&kb, "test.jm6zw.rb_applied");
    assert_eq!(tvs.len(), 1, "one outer type value in `id_ty(Cell[V = Int64])`");
    let Some(Expr::TypeValue {
        head, named_args, ..
    }) = tvs[0].as_expr()
    else {
        unreachable!()
    };
    assert_eq!(kb.local_name_of(*head), "Cell");
    assert_eq!(named_args.len(), 1);
    assert_eq!(kb.local_name_of(named_args[0].0), "V");
    match named_args[0].1.as_expr() {
        Some(Expr::TypeValue { head, .. }) => assert_eq!(kb.local_name_of(*head), "Int64"),
        other => panic!(
            "the type argument is itself a recorded type value, got {:?}",
            other.map(std::mem::discriminant)
        ),
    }
    assert_no_plain_sort_reference(&kb, "test.jm6zw.rb_applied");
}

/// DRIVEN: a rule body's type value evaluates to the SAME term an operation body's does —
/// bare to `Ref(Cell)`, applied to `Cell[V = Int64]`'s term — and a reflect op reads it.
#[test]
fn a_rule_body_type_value_is_the_term_an_operation_body_evaluates_to() {
    let mut kb = load_kb_with(SRC);
    let rb_bare = answer_term(&mut kb, "test.jm6zw.rb_bare");
    let ob_bare = answer_term(&mut kb, "test.jm6zw.ob_bare");
    let cell = kb.try_resolve_symbol("anthill.prelude.Cell").expect("Cell");
    assert!(matches!(kb.get_term(rb_bare), Term::Ref(s) if *s == cell));
    assert_eq!(rb_bare, ob_bare, "one term from both bodies, bare");

    let rb_applied = answer_term(&mut kb, "test.jm6zw.rb_applied");
    let ob_applied = answer_term(&mut kb, "test.jm6zw.ob_applied");
    assert!(
        matches!(kb.get_term(rb_applied), Term::Fn { functor, .. } if *functor == cell),
        "an applied type term, got {:?}",
        kb.get_term(rb_applied)
    );
    assert_eq!(rb_applied, ob_applied, "one term from both bodies, applied");

    let rows = query_unary(&mut kb, "test.jm6zw.rb_modifiable");
    assert_eq!(rows.len(), 1);
    assert!(
        matches!(rows[0].0, Value::Bool(true)),
        "`is_modifiable(Cell[V = Int64])` in a rule body, got {:?}",
        rows[0].0
    );
}

/// CONTROL — PASSES EITHER WAY BY DESIGN: the record moves no clause. A goal holding a sort
/// still matches the fact that holds it, each face its own fact and not the other's
/// (`Ref(Cell)` and `Cell[V = Int64]` do not unify — proposal 055 §7).
#[test]
fn the_clause_a_rule_body_matches_is_unmoved() {
    let mut kb = load_kb_with(SRC);
    let bare = query_unary(&mut kb, "test.jm6zw.holds_bare");
    let applied = query_unary(&mut kb, "test.jm6zw.holds_applied");
    assert_eq!(bare.len(), 1, "`holds(Cell)` matches `fact holds(Cell)` only: {bare:?}");
    assert_eq!(
        applied.len(),
        1,
        "`holds(Cell[V = Int64])` matches its own fact only: {applied:?}"
    );
}

/// THE DIAGNOSTIC proposal 055 §2 names as the uniform rule's residual risk: a construction
/// with its parentheses forgotten. A free-standing entity's bare name — and an eponymous
/// sort's — denotes the TYPE, so `use_leaf(Leaf)` is refused, and now says which type it
/// was handed rather than only `got Type`.
///
/// The SHADOWING half passes either way by design: a parameter or a `let` spelled `Leaf` is
/// a binder of its own and denotes no type, so its mismatch carries no suffix.
#[test]
fn a_forgotten_parentheses_construction_names_the_denoted_type() {
    let errs = load_errors_of(
        r#"
namespace test.jm6zwf
  import anthill.prelude.{Int64, String}
  entity Leaf(name: String)
  sort Ep
    entity Ep(name: String)
  end
  operation use_leaf(l: Leaf) -> String = l.name
  operation use_ep(e: Ep) -> String = e.name
  operation forgot_arg() -> String = use_leaf(Leaf)
  operation forgot_ret() -> Leaf = Leaf
  operation forgot_ep() -> String = use_ep(Ep)
  operation shadow(Leaf: String) -> Int64 = Leaf
end
"#,
    );
    let with = |needle: &str| errs.iter().filter(|e| e.contains(needle)).count();
    assert_eq!(
        with("expected Leaf, got Type (Leaf)"),
        2,
        "the argument and the return each name the type `Leaf`: {errs:?}"
    );
    assert_eq!(with("expected Ep, got Type (Ep)"), 1, "{errs:?}");
    assert!(
        errs.iter()
            .any(|e| e.contains("expected Int64, got String") && !e.contains("(Leaf)")),
        "a binder spelled `Leaf` denotes no type: {errs:?}"
    );
}

/// THE SURFACE GATE, which the hint overrode: `Cell(Int64)` is a construction (proposal 055
/// §2), and `Cell` is not its own constructor. In a `Type`-declared slot the hint read it as
/// `Cell[Int64]` and the program LOADED; it is refused now as everywhere else, naming the
/// bracket spelling. FAILS with the hints restored (back-out (1)).
#[test]
fn a_sort_applied_with_parentheses_is_no_type_application() {
    let errs = load_errors_of(
        r#"
namespace test.jm6zwp
  import anthill.prelude.{Bool, Cell, Int64}
  import anthill.reflect.{is_modifiable}
  operation p() -> Bool = is_modifiable(Cell(Int64))
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains("unknown functor")
            && e.contains("`Cell` names a sort")
            && e.contains("`Cell[…]`")),
        "expected the surface-gate refusal, got {errs:?}"
    );
}

/// FOUND BY `/code-review`: an equation's RHS is the one VALUE the rule-body walk meets at
/// its top, where a depth gate copied from WI-710's check (a top-level body atom is a goal)
/// left a whole bracketed RHS the `Expr::Apply` nothing types any more, while its bare twin
/// was recorded. Both faces evaluate through the `@[simp]` rewrite now, and a reflect op
/// reads the applied one. FAILS with `term_depth > 1` restored to the walk's `type_value`
/// gate: `applied` and `modApplied` are refused as a sort applied as a call.
#[test]
fn a_whole_equation_rhs_is_recorded_as_its_bare_twin_is() {
    let mut kb = load_kb_with(
        r#"
namespace test.jm6zwe
  import anthill.prelude.{Bool, Cell, Int64, Type}
  import anthill.reflect.{is_modifiable}
  rule tyApplied() <=> Cell[V = Int64] @[simp]
  rule tyBare() <=> Cell @[simp]
  operation applied() -> Type = tyApplied()
  operation bare() -> Type = tyBare()
  operation modApplied() -> Bool = is_modifiable(tyApplied())
  rule rApplied(?x) :- ?x <=> applied()
  rule rBare(?x) :- ?x <=> bare()
  rule rMod(?x) :- ?x <=> modApplied()
end
"#,
    );
    let cell = kb.try_resolve_symbol("anthill.prelude.Cell").expect("Cell");
    let applied = answer_term(&mut kb, "test.jm6zwe.rApplied");
    assert!(
        matches!(kb.get_term(applied), Term::Fn { functor, .. } if *functor == cell),
        "the applied RHS evaluates to `Cell[V = Int64]`'s term, got {:?}",
        kb.get_term(applied)
    );
    let bare = answer_term(&mut kb, "test.jm6zwe.rBare");
    assert!(matches!(kb.get_term(bare), Term::Ref(s) if *s == cell));
    let rows = query_unary(&mut kb, "test.jm6zwe.rMod");
    assert_eq!(rows.len(), 1);
    assert!(matches!(rows[0].0, Value::Bool(true)), "got {:?}", rows[0].0);
}

/// FOUND BY `/code-review`: the walk's two gates — the one that DECIDES a node is a type
/// value and WI-710's that checks its arguments — must ask the same question, or a name the
/// first admits is read by nobody. `Box` declared as a namespace before its sort carries
/// `Sort` second, so `kind_of` misses it where `has_kind` does not; and a relation goal's
/// argument is a term the typer never checks, so the loader's check is the only one there
/// is. FAILS with WI-710's gate as it was (`term_depth > 1 && … && kind_of == Sort`): the
/// stray `W` loads.
#[test]
fn a_type_value_s_arguments_are_checked_whatever_order_its_name_was_declared_in() {
    let errs = load_errors_of(
        r#"
namespace test.jm6zwn
  import anthill.prelude.{Int64}
  namespace Box
  end
  sort Box[V]
    entity box(v: V)
  end
  fact holds(Box[V = Int64])
  rule r(1) :- holds(Box[W = Int64])
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains("no type parameter named 'W'")),
        "the stray type argument is refused, got {errs:?}"
    );
}

fn occ(expr: Expr) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(expr, SourceSpan::new(SourceId::from_raw(0), 0, 0), None)
}

fn type_expected(kb: &mut KnowledgeBase) -> Value {
    Value::term(kb.make_sort_ref_by_name("anthill.prelude.Type"))
}

/// THE RETIRED QUESTION, ASKED DIRECTLY: a plain `Ref(Cell)` — the shape no walk produces
/// any more — typed where a `Type` is expected. The WI-206 arm read it as the type value;
/// now the expectation decides nothing and the typer names the producer's omission. The
/// recorded twin, typed with no expectation at all, is the type value (the control).
#[test]
fn a_plain_reference_to_a_sort_is_refused_where_a_type_is_expected() {
    let mut kb = load_stdlib_kb();
    let cell = kb.try_resolve_symbol("anthill.prelude.Cell").expect("Cell");
    let env = TypingEnv::empty();
    let expected = type_expected(&mut kb);
    let plain = type_check_node(&mut kb, &env, &occ(Expr::Ref(cell)), Some(expected));
    assert!(
        matches!(plain, Err(TypeError::UnclassifiedTypeValue { sort, .. }) if sort == cell),
        "a plain sort reference is refused, not read through the expectation: {:?}",
        plain.as_ref().err()
    );
    let recorded = occ(Expr::TypeValue {
        head: cell,
        pos_args: Vec::new(),
        named_args: Vec::new(),
    });
    let r = type_check_node(&mut kb, &env, &recorded, None).expect("the recorded twin types");
    let ty = sort_functor_of_view(&kb, &r.ty).map(|s| kb.local_name_of(s).to_string());
    assert_eq!(ty.as_deref(), Some("Type"), "the recorded twin is a `Type`");
}

/// The applied twin of the row above: a sort-headed `Expr::Apply` — what a bracketed
/// application was before the walks recorded it — is no type application because a `Type`
/// is expected. The WI-707 arm typed it `Type`; it is the call it is spelled as now.
#[test]
fn a_sort_headed_application_is_no_type_where_a_type_is_expected() {
    let mut kb = load_stdlib_kb();
    let cell = kb.try_resolve_symbol("anthill.prelude.Cell").expect("Cell");
    let int64 = kb.try_resolve_symbol("anthill.prelude.Int64").expect("Int64");
    let env = TypingEnv::empty();
    let expected = type_expected(&mut kb);
    let arg = occ(Expr::TypeValue {
        head: int64,
        pos_args: Vec::new(),
        named_args: Vec::new(),
    });
    let apply = occ(Expr::Apply {
        functor: cell,
        pos_args: vec![arg],
        named_args: Vec::new(),
        type_args: Vec::new(),
        recv_type: None,
    });
    let r = type_check_node(&mut kb, &env, &apply, Some(expected));
    assert!(
        matches!(r, Err(TypeError::UnknownApplyFunctor { name, .. }) if name == cell),
        "a sort-headed application is the call it is spelled as: {:?}",
        r.as_ref().err()
    );
}
