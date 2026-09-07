//! WI-20260824-Q0093 (proposal 055 umbrella A step 2 — `docs/design/055-implementation.md`
//! §3's occurrence matrix, judged by its §9 controls) — EVERY CHILD WHOSE GRAMMAR/IR ROLE
//! IS `ValueExpression` IN AN OPERATION EXPRESSION ADMITS A CLASSIFIED NOMINAL TYPE VALUE,
//! AND THE ADJACENT NON-VALUE ROLE AT EACH FAMILY DOES NOT.
//!
//! WHAT THIS FILE MEASURES, AND WHAT ITS PEER MEASURES. WI-20260824-WAHB6 put the
//! classification at the LOADER, unconditionally, so the widening did not arrive family by
//! family — it arrived for every position at once, and `wi_wahb6_type_value_classification_-
//! test`'s rows measure the RECORD (the occurrence says what it is; the two carriers key
//! alike). These rows measure the CONSUMERS: each §3 family is DRIVEN — resolved or
//! evaluated, with the resulting `Type` value asserted — its destination check is exercised
//! where it has one, and the head / callee / pattern / binder / label / member-name /
//! metadata-key beside it is pinned unchanged.
//!
//! ALREADY COVERED BY THAT PEER and deliberately not repeated here: the operation RESULT
//! (bare and applied), the unannotated `let` value and continuation, a type ARGUMENT inside
//! a type application, the eponymous-constructor control and the local-shadows-a-sort
//! control.
//!
//! ── THREE FAMILIES NEEDED A CODE ARM, WHICH IS THE FINDING THIS TICKET ASKED FOR ──
//!
//! (1) THE `if` CONDITION AND THE `match` ARM GUARD HAD NO DESTINATION AT ALL. §3 admits a
//!     type value at both on the strength of "ordinary typing rejects `Type` as a Boolean
//!     condition". It did not: the condition's type was computed and dropped, so
//!     `if Cell then …` loaded — and so did `if "x" then …` and `if 1 then …`, which is the
//!     control saying the hole was never about type values. Both slots are now checked by
//!     [`boolean_position_error`] (`typing.rs`), through the predicate an ARGUMENT gets —
//!     which also refuses two shapes that used to load, each measured rather than assumed:
//!     a relation-valued condition or guard (it failed at EVAL with the same `expected
//!     Bool, got Relation`) and a value at a rigid type parameter (refused identically in
//!     an argument slot). Both are driven by
//!     [`the_boolean_destination_is_the_arguments_predicate_not_a_second_opinion`].
//!
//! (2) THE WRONG-DESTINATION DIAGNOSTIC COULD NOT NAME WHAT WAS DENOTED. §8 asks for
//!     `expected String, got Type (Cell[Int64])`; the message said `got Type`, because the
//!     `actual` a mismatch carries is the expression's TYPE and every type value has the
//!     same one. `TypeError::TypeMismatch.denoted` carries the surface now, filled by the
//!     one renderer the op-argument / entity-field / let-annotation / op-return channels
//!     share, and by the branch join for the `if` / `match` arm families.
//!
//! (3) THE CLASSIFIER ASKED THE PRIMARY KIND, WHICH IS A DECLARATION-ORDER QUESTION.
//!     `bare_name_denotes_type` asked `kind_of` and its own doc asked this ticket for a row
//!     that separates `kind_of` from `has_kind`. The row is `namespace Box` written before
//!     `sort Box`: that program did not load while the same two declarations in the other
//!     order loaded and evaluated. Both faces ask `has_kind` now — the bare one and
//!     `build_load`'s `is_type_value`, because they are one question about one name and
//!     keyed apart they would classify the two faces of the SAME name differently in one
//!     declaration order. That is also the reading the rest of the repo had already
//!     settled (WI-956 for the kind gates, proposal 059 §"told apart by the address" for
//!     this very namespace/sort pair); see `bare_name_denotes_type`'s doc for why the
//!     population the old note feared is already excluded by its second conjunct.
//!
//! ── TWO THINGS THIS TICKET FOUND AND REPORTS RATHER THAN REPAIRS ──
//!
//! (a) A COLLECTION LITERAL'S ELEMENTS WERE NOT CHECKED AGAINST THE DECLARED ELEMENT TYPE —
//!     at all, for any element type, so the `literals` family's list and set halves had no
//!     negative destination to drive. `operation f() -> List[T = String] = ["a", Cell]`
//!     loaded, and so did `["a", 1]`, which was the control saying this was a missing
//!     collection-literal check and not a type value slipping through one. Reported here
//!     rather than repaired, and pinned in both directions so the report could not rot.
//!     THE PIN DID ITS JOB: WI-20260826-7JDWY landed that check, this row failed naming its
//!     own comment, and it is now
//!     [`a_collection_literal_element_type_is_checked_for_every_element_alike`] — the
//!     family has a negative destination, and it names what the element denotes.
//!
//! (b) THE INTERPRETER NEVER EVALUATES A `match` ARM GUARD, so the guard family's RUNTIME
//!     half cannot be driven by anyone. `MatchDispatch` picks the first arm whose PATTERN
//!     matches, and `match n case x | eq(x, 1) -> "one" case _ -> "other"` answers `"one"`
//!     for every `n` — no type value anywhere in that fixture, which is the control. The
//!     guard's type value is driven at LOAD instead; both halves are in
//!     [`a_match_arm_guards_type_value_is_classified_and_validated_at_load`].
//!
//! ── WHICH ROWS FAIL ON A BACK-OUT, MEASURED — one back-out at a time, `wi_tests` filtered
//! to this file, 24 rows; every count below is a run ──
//!
//! * BOTH LOADER PREDICATES NEUTRALIZED (`bare_name_denotes_type` and `build_load`'s
//!   `is_type_value` forced `false` — WAHB6's own back-out): **15 fail, 9 pass**. Every
//!   operation-expression driving row fails, most as LOAD errors (with no classification
//!   the written sort names go back to being unresolved names), and both
//!   negative-destination rows fail because the message reverts to an unresolved name.
//! * `boolean_position_error` FORCED TO `None`: **2 fail** —
//!   [`a_boolean_position_refuses_a_type_value_and_says_which_slot`] and
//!   [`the_boolean_destination_is_the_arguments_predicate_not_a_second_opinion`]. Nothing
//!   else in the workspace changes, which is the other half of that arm's claim.
//! * `denoted_type_value` FORCED TO `None`: **2 fail** —
//!   [`a_string_or_bool_destination_names_the_denoted_sort`] and the boolean-position row,
//!   on the `(Cell…)` suffix alone. Every driving row stays green, because a denotation in
//!   a message changes no program's meaning.
//! * BOTH CLASSIFIERS REVERTED TO `kind_of`: **2 fail** —
//!   [`a_sort_declared_after_a_namespace_of_the_same_name_still_denotes`] on the
//!   namespace-first order, which is the whole of finding (3), and
//!   [`a_newly_classified_head_still_has_its_type_arguments_checked`], whose
//!   newly-admitted head stops existing.
//! * `check_sort_type_args`'s OWN GATE REVERTED TO `kind_of` (the classifier left
//!   widened — the desync `/code-review` found): **1 fails** —
//!   [`a_newly_classified_head_still_has_its_type_arguments_checked`], and only its
//!   namespace-first half; the plain-sort control in the same row stays green, which is
//!   what says the check itself was never broken, only skipped for the names the
//!   classifier had newly admitted.
//!
//! THE 9 THAT SURVIVE THE FIRST BACK-OUT, and why each is the right outcome. FOUR are the
//! adjacent-role controls (`a_pattern_binder_…`, `a_lambda_binder_…`,
//! `a_field_label_and_member_name_…`, `a_metadata_key_…`): they pin readings this ticket
//! must NOT move, so green in both worlds is what they are for. TWO MORE are green in both
//! worlds for the same reason —
//! [`the_boolean_destination_is_the_arguments_predicate_not_a_second_opinion`], which asks
//! about a `Relation` and a rigid `?T` and never about a type value, and
//! [`a_sort_sharing_its_name_with_a_rule_head_is_unmoved_by_the_widening`], which is where
//! the widening does NOT reach. THE OTHER THREE ARE A
//! FINDING ABOUT WHERE THEIR CARRIER IS — [`an_operation_metadata_value_denotes`],
//! [`a_bounded_quantifier_collection_of_type_values_drives`] and
//! [`a_match_arm_guards_type_value_is_classified_and_validated_at_load`] do not go through
//! the operation-expression path at all: a metadata block and a rule body are lowered by
//! `convert_term`, whose own `is_type_app` gate (WI-927) classified them before this
//! umbrella existed, and the guard row's load-time refusal is the type-ARGUMENT check on
//! that same substrate. They are pinned here because Q0093's family list names those
//! families; what they measure is the boundary umbrella B (WI-20260823-53W12) owns, and
//! that is why neutralizing umbrella A's record leaves them standing.

use anthill_core::eval::Value;
use anthill_core::intern::SymbolKind;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;

use crate::common::{interp_for, list_heads, load_kb_with, try_load_kb_with};

/// The matrix fixture: one operation per §3 family, each written twice where the family
/// admits both faces — a BARE `Cell` and an APPLIED `Cell[V = Int64]`.
///
/// `id_ty` is the driver. A row that only asked `is_modifiable(Cell)` would measure
/// WI-206's fact table; handing the argument back as the result makes the row assert the
/// TYPE TERM that actually arrived at the callee.
const SRC: &str = r#"
namespace test.q0093
  import anthill.prelude.{Bool, Cell, Int64, List, Set, String, Type}
  import anthill.reflect.{is_modifiable}

  operation id_ty(t: Type) -> Type = t

  sort Holder
    entity Holder(t: Type)
  end

  -- application: positional and named call arguments
  operation arg_pos_bare() -> Type = id_ty(Cell)
  operation arg_pos_applied() -> Type = id_ty(Cell[V = Int64])
  operation arg_named_bare() -> Type = id_ty(t: Cell)
  operation arg_named_applied() -> Type = id_ty(t: Cell[V = Int64])

  -- application: constructor field values, and the entity they build
  operation ctor_bare() -> Holder = Holder(t: Cell)
  operation ctor_applied_field() -> Type = Holder(t: Cell[V = Int64]).t

  -- conditionals: both branches
  operation if_then(c: Bool) -> Type = if c then Cell[V = Int64] else Cell

  -- matching: scrutinee, branch body, arm guard
  operation match_scrutinee() -> Type = match Cell[V = Int64] case t -> t
  operation match_body(n: Int64) -> Type = match n case 0 -> Cell[V = Int64] case _ -> Cell
  -- functions: lambda body
  operation lambda_body() -> Type =
    let f = lambda () -> Cell[V = Int64]
    f()
  operation lambda_body_bare() -> Type =
    let f = lambda () -> Cell
    f()

  -- literals: collection, set and named-tuple element values
  operation list_elems() -> List[T = Type] = [Cell, Cell[V = Int64]]
  operation set_elems() -> Set[T = Type] = {Cell, Cell[V = Int64]}
  operation tuple_elems() -> (bare: Type, applied: Type) = (bare: Cell, applied: Cell[V = Int64])

  -- expression composition: parenthesized expression and infix operands
  operation paren() -> Type = (Cell[V = Int64])
  operation paren_bare() -> Type = (Cell)
  operation infix_same_face() -> Bool = Cell === Cell
  operation infix_two_faces() -> Bool = Cell === Cell[V = Int64]

  -- proofs: the `conclude` goal's argument, and the continuation after `end`
  operation proof_cont() -> Type =
    proof p conclude is_modifiable(Cell[V = Int64])
    end Cell[V = Int64]
  operation proof_cont_bare() -> Type =
    proof q conclude is_modifiable(Cell)
    end Cell

  -- a type argument that is an operation PARAMETER: non-ground until the call
  operation wrap(t: Type) -> Type = Cell[V = ?t]
  operation wrapped() -> Type = wrap(Int64)
end
"#;

/// `Ref(Cell)` — what a BARE nominal type evaluates to. Proposal 055 §7: the two faces are
/// structurally different terms, and this is not the empty application.
fn assert_bare_cell(kb: &KnowledgeBase, v: &Value, what: &str) {
    match kb.get_term(term_id(v, what)).clone() {
        Term::Ref(s) => assert_eq!(kb.local_name_of(s), "Cell", "{what}: the denoted sort"),
        other => panic!("{what}: expected the bare `Ref(Cell)`, got {other:?}"),
    }
}

/// `Cell(V: Ref(Int64))` — the canonical parameterized type term an APPLIED nominal type
/// evaluates to, argument included (the argument is classified by the same loader rule, so
/// a row that stopped at the head would not notice it going back to a var-ref).
fn assert_applied_cell(kb: &KnowledgeBase, v: &Value, what: &str) {
    match kb.get_term(term_id(v, what)).clone() {
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            assert_eq!(kb.local_name_of(functor), "Cell", "{what}: the head sort");
            assert!(pos_args.is_empty(), "{what}: `Cell[V = …]` binds V by name");
            assert_eq!(named_args.len(), 1, "{what}: one type argument");
            assert_eq!(kb.local_name_of(named_args[0].0), "V", "{what}: the label");
            match kb.get_term(named_args[0].1).clone() {
                Term::Ref(s) => assert_eq!(kb.local_name_of(s), "Int64", "{what}: V binds"),
                other => panic!("{what}: V must bind `Ref(Int64)`, got {other:?}"),
            }
        }
        other => panic!("{what}: expected `Cell(V: Int64)`, got {other:?}"),
    }
}

fn term_id(v: &Value, what: &str) -> TermId {
    match v {
        Value::Term { id, .. } => *id,
        other => panic!("{what}: expected a `Type` value on the Term carrier, got {other:?}"),
    }
}

// ── DRIVING ROWS, one per §3 family ────────────────────────────────────────────

/// APPLICATION — a positional and a named call argument, in both faces. The four
/// operations differ only in the argument's SURFACE, so they measure the argument position
/// rather than `id_ty`.
#[test]
fn a_call_argument_denotes_positionally_and_by_name() {
    let mut interp = interp_for(SRC);
    for (op, applied) in [
        ("arg_pos_bare", false),
        ("arg_pos_applied", true),
        ("arg_named_bare", false),
        ("arg_named_applied", true),
    ] {
        let qn = format!("test.q0093.{op}");
        let v = interp.call(&qn, &[]).unwrap_or_else(|e| panic!("{op}: {e:?}"));
        if applied {
            assert_applied_cell(interp.kb(), &v, op);
        } else {
            assert_bare_cell(interp.kb(), &v, op);
        }
    }
}

/// APPLICATION — a CONSTRUCTOR's field value, driven by reading the field back out, plus
/// the adjacent role at this family: the constructor HEAD, which is a callee and not a
/// value. `Holder(t: Cell)` must still build a `Holder`; only the field is a type value.
#[test]
fn a_constructor_field_value_denotes_and_the_head_still_constructs() {
    let mut interp = interp_for(SRC);
    let field = interp
        .call("test.q0093.ctor_applied_field", &[])
        .unwrap_or_else(|e| panic!("ctor_applied_field: {e:?}"));
    assert_applied_cell(interp.kb(), &field, "ctor_applied_field");

    // THE CONTROL. The head is the adjacent non-value role, so the same source that makes
    // the FIELD a type value must leave the construction alone.
    let built = interp
        .call("test.q0093.ctor_bare", &[])
        .unwrap_or_else(|e| panic!("ctor_bare: {e:?}"));
    match &built {
        Value::Entity { functor, named, .. } => {
            assert_eq!(interp.kb().local_name_of(*functor), "Holder");
            assert_eq!(named.len(), 1, "one field");
            assert_bare_cell(interp.kb(), &named[0].1, "the Holder's field");
        }
        other => panic!("`Holder(t: Cell)` must construct a Holder, got {other:?}"),
    }
}

/// CONDITIONALS — the `then` and the `else`, one face each, selected by the condition so
/// each branch is actually evaluated rather than merely typed.
#[test]
fn both_if_branches_denote() {
    let mut interp = interp_for(SRC);
    let t = interp
        .call("test.q0093.if_then", &[Value::Bool(true)])
        .unwrap_or_else(|e| panic!("if_then(true): {e:?}"));
    assert_applied_cell(interp.kb(), &t, "the then-branch");
    let f = interp
        .call("test.q0093.if_then", &[Value::Bool(false)])
        .unwrap_or_else(|e| panic!("if_then(false): {e:?}"));
    assert_bare_cell(interp.kb(), &f, "the else-branch");
}

/// MATCHING — the SCRUTINEE (bound by the arm's binder and handed back, so the value that
/// was matched on is the one asserted) and a BRANCH BODY, each in one face.
#[test]
fn a_match_scrutinee_and_a_branch_body_denote() {
    let mut interp = interp_for(SRC);
    let s = interp
        .call("test.q0093.match_scrutinee", &[])
        .unwrap_or_else(|e| panic!("match_scrutinee: {e:?}"));
    assert_applied_cell(interp.kb(), &s, "the scrutinee");

    let hit = interp
        .call("test.q0093.match_body", &[Value::Int(0)])
        .unwrap_or_else(|e| panic!("match_body(0): {e:?}"));
    assert_applied_cell(interp.kb(), &hit, "the first arm's body");
    let miss = interp
        .call("test.q0093.match_body", &[Value::Int(1)])
        .unwrap_or_else(|e| panic!("match_body(1): {e:?}"));
    assert_bare_cell(interp.kb(), &miss, "the wildcard arm's body");
}

/// MATCHING, THE ARM GUARD — DRIVEN AT LOAD, BECAUSE NOTHING CAN DRIVE IT AT EVAL.
///
/// THE SECOND HALF FIRST, since it decides what this row can claim: THE INTERPRETER NEVER
/// EVALUATES A GUARD. `Interpreter`'s `MatchDispatch` clones `branch.guard` into its await
/// state and then picks the first arm whose PATTERN matches, so
/// `match n case x | eq(x, 1) -> "one" case _ -> "other"` answers `"one"` for EVERY `n` —
/// asserted below, on a fixture with no type value anywhere in it, which is the control
/// that says this is not a proposal-055 question but a missing arm in eval. Reported in
/// this ticket's delivery note; until it is repaired the guard family's RUNTIME half
/// cannot be driven by this file or by anything else.
///
/// WHAT IS DRIVEN, then: the guard's own type value, through a load-time check only a
/// CLASSIFIED one can reach. `Cell[W = Int64]` written inside a guard is refused naming
/// the parameter `Cell` actually declares — the WI-709 type-argument fit check, which runs
/// on the classified node — while `Cell[V = Int64]` in the same slot loads. An unclassified
/// guard would report an unresolved name instead, and an unvisited guard would report
/// nothing at all, so the pair separates all three outcomes. The guard's own `Bool`
/// destination is the row [`a_boolean_position_refuses_a_type_value_and_says_which_slot`].
#[test]
fn a_match_arm_guards_type_value_is_classified_and_validated_at_load() {
    let program = |guard: &str, ns: &str| {
        format!(
            r#"
namespace test.q0093g{ns}
  import anthill.prelude.{{Bool, Cell, Int64, String, Type}}
  import anthill.reflect.{{is_modifiable}}

  operation f(n: Int64) -> String =
    match n
      case x | {guard} -> "a"
      case _ -> "b"
end
"#
        )
    };
    try_load_kb_with(&program("is_modifiable(Cell[V = Int64])", "ok"))
        .unwrap_or_else(|e| panic!("an applied type value in a guard must load: {e:?}"));

    let errs = match try_load_kb_with(&program("is_modifiable(Cell[W = Int64])", "bad")) {
        Err(errs) => errs,
        Ok(_) => panic!("an undeclared type parameter inside a guard must be refused"),
    };
    assert!(
        errs.iter()
            .any(|e| e.contains("no type parameter named 'W'") && e.contains("V")),
        "the guard's type value must reach the type-ARGUMENT check (WI-709), which names \
         the parameter the sort declares; got {errs:?}",
    );

    // THE CONTROL FOR THE EVAL HALF — no type value in sight, and the guard is still
    // ignored. When the evaluator learns to consult a guard, this assertion fails and
    // names this row's doc.
    let src = r#"
namespace test.q0093gr
  import anthill.prelude.{Bool, Int64, String}
  import anthill.prelude.PartialEq.{eq}

  operation pick(n: Int64) -> String =
    match n
      case x | eq(x, 1) -> "one"
      case _ -> "other"
end
"#;
    let mut interp = interp_for(src);
    let v = interp
        .call("test.q0093gr.pick", &[Value::Int(7)])
        .unwrap_or_else(|e| panic!("pick(7): {e:?}"));
    assert!(
        matches!(&v, Value::Str(s) if s == "one"),
        "MEASURED: eval ignores the arm guard, so `pick(7)` takes the guarded arm. If this \
         now answers \"other\", the evaluator has been taught to consult guards — delete \
         this control and drive the guard family at eval, which is what this row wants. \
         Got {v:?}",
    );
}

/// FUNCTIONS — a lambda BODY, driven by applying the lambda. The `let` is unannotated, so
/// nothing hands the body an expected type either.
#[test]
fn a_lambda_body_denotes() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.q0093.lambda_body", &[])
        .unwrap_or_else(|e| panic!("lambda_body: {e:?}"));
    assert_applied_cell(interp.kb(), &v, "the lambda body");
    let b = interp
        .call("test.q0093.lambda_body_bare", &[])
        .unwrap_or_else(|e| panic!("lambda_body_bare: {e:?}"));
    assert_bare_cell(interp.kb(), &b, "the lambda body, bare face");
}

/// LITERALS — collection, set and NAMED-TUPLE element values, each carrying one of each
/// face so the row also pins that the two do not collapse into one term inside a literal.
#[test]
fn list_set_and_tuple_elements_denote() {
    let mut interp = interp_for(SRC);

    let list = interp
        .call("test.q0093.list_elems", &[])
        .unwrap_or_else(|e| panic!("list_elems: {e:?}"));
    let elems = list_heads(&list);
    assert_eq!(elems.len(), 2, "two list elements");
    assert_bare_cell(interp.kb(), &elems[0], "list element 0");
    assert_applied_cell(interp.kb(), &elems[1], "list element 1");

    let set = interp
        .call("test.q0093.set_elems", &[])
        .unwrap_or_else(|e| panic!("set_elems: {e:?}"));
    match &set {
        Value::Entity { pos, .. } => {
            assert_eq!(pos.len(), 2, "two set elements, got {set:?}");
            assert_bare_cell(interp.kb(), &pos[0], "set element 0");
            assert_applied_cell(interp.kb(), &pos[1], "set element 1");
        }
        other => panic!("expected a set literal value, got {other:?}"),
    }

    let tuple = interp
        .call("test.q0093.tuple_elems", &[])
        .unwrap_or_else(|e| panic!("tuple_elems: {e:?}"));
    match &tuple {
        Value::Tuple { pos, named } => {
            assert!(pos.is_empty(), "the tuple is written with labels");
            assert_eq!(named.len(), 2);
            assert_eq!(interp.kb().local_name_of(named[0].0), "bare");
            assert_bare_cell(interp.kb(), &named[0].1, "the `bare` component");
            assert_eq!(interp.kb().local_name_of(named[1].0), "applied");
            assert_applied_cell(interp.kb(), &named[1].1, "the `applied` component");
        }
        other => panic!("expected a named tuple, got {other:?}"),
    }
}

/// EXPRESSION COMPOSITION — a parenthesized expression, and both operands of an infix
/// operator. `===` is `struct_eq`, so the second row also drives proposal 055 §7 through
/// the operator: a bare and an applied type value are NOT the same term.
#[test]
fn a_parenthesized_expression_and_infix_operands_denote() {
    let mut interp = interp_for(SRC);
    let p = interp
        .call("test.q0093.paren", &[])
        .unwrap_or_else(|e| panic!("paren: {e:?}"));
    assert_applied_cell(interp.kb(), &p, "the parenthesized expression");
    let pb = interp
        .call("test.q0093.paren_bare", &[])
        .unwrap_or_else(|e| panic!("paren_bare: {e:?}"));
    assert_bare_cell(interp.kb(), &pb, "the parenthesized expression, bare face");

    for (op, want) in [("infix_same_face", true), ("infix_two_faces", false)] {
        let qn = format!("test.q0093.{op}");
        let v = interp.call(&qn, &[]).unwrap_or_else(|e| panic!("{op}: {e:?}"));
        assert!(
            matches!(v, Value::Bool(b) if b == want),
            "{op}: both operands must denote, and the two faces must not compare equal — \
             expected {want}, got {v:?}",
        );
    }
}

/// PROOFS — the `conclude` goal's argument and the continuation after `end`. The
/// continuation is what the operation returns, so asserting it drives both: an ill-typed
/// `conclude` argument fails the operation before the continuation is reached.
#[test]
fn a_proof_conclude_goal_and_its_continuation_denote() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.q0093.proof_cont", &[])
        .unwrap_or_else(|e| panic!("proof_cont: {e:?}"));
    assert_applied_cell(interp.kb(), &v, "the proof continuation");
    let b = interp
        .call("test.q0093.proof_cont_bare", &[])
        .unwrap_or_else(|e| panic!("proof_cont_bare: {e:?}"));
    assert_bare_cell(interp.kb(), &b, "the proof continuation, bare face");
}

/// A LOGICAL-VARIABLE TYPE ARGUMENT, per §9's fifth requirement: the argument is the
/// operation's own parameter (`Cell[V = ?t]`), so the type is NOT ground where it is
/// written and only the CALL decides it. Driven through `wrap(Int64)`, which must produce
/// the same canonical term the literal `Cell[V = Int64]` produces.
#[test]
fn a_type_argument_that_is_an_operation_parameter_stays_non_ground_until_the_call() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.q0093.wrapped", &[])
        .unwrap_or_else(|e| panic!("wrapped: {e:?}"));
    assert_applied_cell(interp.kb(), &v, "the substituted type argument");
}

/// METADATA VALUES — an operation's `meta [Key: <type value>]`, read back through the
/// `OperationInfo` record, in both faces. The KEY beside it is the adjacent non-value role
/// and is pinned by [`a_metadata_key_spelled_like_a_sort_stays_a_key`].
#[test]
fn an_operation_metadata_value_denotes() {
    let src = r#"
namespace test.q0093meta
  import anthill.prelude.{Cell, Int64, Type}

  operation tagged() -> Int64
    meta [Bare: Cell, Applied: Cell[V = Int64]]
    = 1
end
"#;
    let kb = load_kb_with(src);
    let sym = kb
        .try_resolve_symbol("test.q0093meta.tagged")
        .expect("tagged resolves");
    let rec = anthill_core::kb::op_info::lookup_operation_info(&kb, sym)
        .expect("the operation's info record");
    let read = |key: &str| {
        anthill_core::kb::load::meta_value(&kb, rec.meta, key)
            .unwrap_or_else(|| panic!("the `{key}` metadata entry"))
    };
    assert_bare_cell(&kb, &Value::term(read("Bare")), "the `Bare` metadata value");
    assert_applied_cell(
        &kb,
        &Value::term(read("Applied")),
        "the `Applied` metadata value",
    );
}

/// QUANTIFICATION — the bounded quantifier's COLLECTION, driven in both directions
/// (`forall` over two modifiable types holds; over a list containing `Int64` it does not,
/// and `some` over the same list does).
///
/// WRITTEN IN A RULE BODY BECAUSE THAT IS THE ONLY PLACE THE CONSTRUCT EXISTS (§5.3): there
/// is no operation-expression surface for it, so strictly this family's carrier belongs to
/// umbrella B (WI-20260823-53W12). It is driven here because Q0093's family list names it
/// and the collection position is what §3's `quantification` row is about; the rule-body
/// GOAL positions around it are B's.
#[test]
fn a_bounded_quantifier_collection_of_type_values_drives() {
    let src = r#"
namespace test.q0093q
  import anthill.prelude.{Cell, Int64, Type, Bool}
  import anthill.reflect.{is_modifiable}

  rule all_modifiable(?ok) :-
    (forall ?t in [Cell, Cell[V = Int64]]: is_modifiable(?t)), ?ok <=> true
  rule not_all_modifiable(?ok) :-
    (forall ?t in [Int64, Cell]: is_modifiable(?t)), ?ok <=> true
  rule some_modifiable(?ok) :-
    (some ?t in [Int64, Cell]: is_modifiable(?t)), ?ok <=> true
end
"#;
    let mut kb = load_kb_with(src);
    for (qn, want) in [
        ("test.q0093q.all_modifiable", true),
        ("test.q0093q.not_all_modifiable", false),
        ("test.q0093q.some_modifiable", true),
    ] {
        let answers = crate::common::query_unary(&mut kb, qn);
        assert_eq!(
            !answers.is_empty(),
            want,
            "{qn}: the quantifier must range over the type values in its collection, \
             got {answers:?}",
        );
    }
}

// ── NEGATIVE DESTINATIONS ──────────────────────────────────────────────────────

/// §9(2) — A `String` OR `Bool` DESTINATION REFUSES A TYPE VALUE, AND THE MESSAGE NAMES
/// THE DENOTED SORT (design §8). One row per channel that can carry the rejection, because
/// each is a different check: the op RETURN, an op ARGUMENT, an entity FIELD, an `if`
/// branch and a `match` branch (both through the branch join), a parenthesized expression
/// and a `proof` continuation (which report as the enclosing operation's return, the
/// wrapper being transparent to types).
#[test]
fn a_string_or_bool_destination_names_the_denoted_sort() {
    let cases: &[(&str, &str, &str, &str)] = &[
        (
            "op-return",
            "expected String",
            "Type (Cell[V = Int64])",
            r#"operation f() -> String = Cell[V = Int64]"#,
        ),
        (
            "op-return, Bool destination",
            "expected Bool",
            "Type (Cell)",
            r#"operation f() -> Bool = Cell"#,
        ),
        (
            "op-arg",
            "expected String",
            "Type (Cell)",
            r#"operation g(s: String) -> String = s
  operation f() -> String = g(Cell)"#,
        ),
        (
            "entity-field",
            "expected String",
            "Type (Cell[V = Int64])",
            r#"sort H
    entity H(s: String)
  end
  operation f() -> H = H(s: Cell[V = Int64])"#,
        ),
        (
            "if branch",
            "expected String",
            "Type (Cell)",
            r#"operation f() -> String = if true then "a" else Cell"#,
        ),
        (
            "match branch",
            "expected String",
            "Type (Cell)",
            r#"operation f() -> String = match 0 case 0 -> "a" case _ -> Cell"#,
        ),
        (
            "parenthesized",
            "expected String",
            "Type (Cell)",
            r#"operation f() -> String = (Cell)"#,
        ),
        (
            "proof continuation",
            "expected String",
            "Type (Cell)",
            r#"operation f() -> String =
    proof p conclude is_modifiable(Cell)
    end Cell"#,
        ),
    ];
    for (i, (what, expected, denoted, body)) in cases.iter().enumerate() {
        let src = format!(
            r#"
namespace test.q0093neg{i}
  import anthill.prelude.{{Bool, Cell, Int64, String, Type}}
  import anthill.reflect.{{is_modifiable}}

  {body}
end
"#
        );
        let errs = match try_load_kb_with(&src) {
            Err(errs) => errs,
            Ok(_) => panic!("{what}: a type value in a {expected} slot must not load"),
        };
        assert!(
            errs.iter()
                .any(|e| e.contains(expected) && e.contains(denoted)),
            "{what}: expected `{expected}, got {denoted}` — the destination mismatch of \
             proposal 055 §2 with the denotation §8 asks for — got {errs:?}",
        );
    }
}

/// §9(2) FOR THE TWO BOOLEAN POSITIONS, which had no destination check at all until this
/// ticket: an `if` CONDITION and a `match` arm GUARD.
///
/// EACH IS ASSERTED WITH A NON-TYPE CONTROL BESIDE IT. A `String` in the same slot must be
/// refused by the same message, because the arm added here is a BOOLEAN check and not a
/// type-value check — an assertion that only refused `Type` would be satisfied by a gate
/// keyed on the wrong question. And a genuine `Bool` in both slots must still load, or the
/// arm would be refusing everything.
#[test]
fn a_boolean_position_refuses_a_type_value_and_says_which_slot() {
    let program = |body: &str, i: usize| {
        format!(
            r#"
namespace test.q0093bool{i}
  import anthill.prelude.{{Bool, Cell, Int64, String, Type}}
  import anthill.prelude.PartialEq.{{eq}}

  {body}
end
"#
        )
    };
    let refused: &[(&str, &str, &str, &str)] = &[
        (
            "if condition, type value",
            "if.condition",
            "got Type (Cell)",
            r#"operation f() -> Type = if Cell then Cell else Int64"#,
        ),
        (
            "if condition, String control",
            "if.condition",
            "got String",
            r#"operation f() -> Type = if "x" then Cell else Int64"#,
        ),
        (
            "match guard, type value",
            "match.guard",
            "got Type (Cell)",
            r#"operation f(n: Int64) -> String = match n case x | Cell -> "a" case _ -> "b""#,
        ),
        (
            "match guard, String control",
            "match.guard",
            "got String",
            r#"operation f(n: Int64) -> String = match n case x | "y" -> "a" case _ -> "b""#,
        ),
    ];
    for (i, (what, slot, actual, body)) in refused.iter().enumerate() {
        let errs = match try_load_kb_with(&program(body, i)) {
            Err(errs) => errs,
            Ok(_) => panic!("{what}: a non-Boolean {slot} must not load"),
        };
        assert!(
            errs.iter()
                .any(|e| e.contains(slot) && e.contains("expected Bool") && e.contains(actual)),
            "{what}: expected `{slot} … expected Bool, {actual}`, got {errs:?}",
        );
    }

    // …and the arm refuses nothing that was legal: a `Bool` condition and a `Bool` guard.
    for (i, body) in [
        r#"operation f(c: Bool) -> Type = if c then Cell else Int64"#,
        r#"operation f(n: Int64) -> String = match n case x | eq(x, 1) -> "a" case _ -> "b""#,
    ]
    .iter()
    .enumerate()
    {
        try_load_kb_with(&program(body, 100 + i))
            .unwrap_or_else(|e| panic!("a Boolean {body} must still load: {e:?}"));
    }
}

/// THE PRICE OF BORROWING THE ARGUMENT'S PREDICATE, stated as rows rather than as a
/// sentence: the `Bool` destination refuses two shapes that used to LOAD, and each is
/// here with the thing that says the refusal is right.
///
/// (1) A RELATION-VALUED condition — `if warm(c) then …` over `rule warm(?c) :- …` — is
/// the goal-shaped spelling the guard slot's own Γ narrowing invites, and it never ran:
/// with the check backed out it loads and then dies at EVAL with `EvalError::TypeMismatch
/// { expected: "Bool", got: "Relation" }` (the guard twin dies as an internal frame
/// error). The runtime already had this rule; the load now says the same thing with a
/// span. That measurement cannot be an assertion here — the check is in — so what IS
/// asserted is the refusal plus the message the runtime used, and the eval half is
/// recorded at [`boolean_position_error`]'s site where the back-out lives.
///
/// (2) A RIGID TYPE PARAMETER (`operation f[T](c: T) = if c then …`) is refused as
/// `got ?T` — and the SAME value in an ARGUMENT slot is refused identically, which is
/// the pairing that makes this the argument's predicate rather than a new opinion about
/// conditions. Both halves are driven below, so a future divergence between the two slots
/// fails here rather than being argued about. It does cost a program that ran (`poly(true)`
/// evaluated); §8.1's rule for a body that pins a parameter its signature quantified is
/// what says the refusal is the right one, and the repair is `c: Bool`.
#[test]
fn the_boolean_destination_is_the_arguments_predicate_not_a_second_opinion() {
    let relation = r#"
namespace test.q0093rel
  import anthill.prelude.{Bool, Int64, String}

  sort Colour
    entity red
    entity blue
  end
  rule warm(?c) :- ?c <=> red
  operation f(c: Colour) -> String = if warm(c) then "w" else "x"
end
"#;
    let errs = match try_load_kb_with(relation) {
        Err(errs) => errs,
        Ok(_) => panic!("a relation-valued condition must be refused at LOAD — it fails at eval"),
    };
    assert!(
        errs.iter()
            .any(|e| e.contains("if.condition") && e.contains("expected Bool") && e.contains("Relation")),
        "the load-time refusal must say what the RUNTIME said (`expected Bool, got \
         Relation`), one phase earlier and with a span; got {errs:?}",
    );

    // The rigid-parameter pair: the condition slot and the argument slot, same value,
    // same message. Written as one fixture so nothing but the POSITION differs.
    let rigid = r#"
namespace test.q0093rig
  import anthill.prelude.{Bool, Int64, String}

  operation sink(b: Bool) -> String = "s"
  operation in_condition[T](c: T) -> String = if c then "w" else "x"
end
"#;
    let cond_errs = match try_load_kb_with(rigid) {
        Err(errs) => errs,
        Ok(_) => panic!("a rigid type parameter in a condition must be refused"),
    };
    let arg = r#"
namespace test.q0093rig2
  import anthill.prelude.{Bool, Int64, String}

  operation sink(b: Bool) -> String = "s"
  operation in_argument[T](c: T) -> String = sink(c)
end
"#;
    let arg_errs = match try_load_kb_with(arg) {
        Err(errs) => errs,
        Ok(_) => panic!("a rigid type parameter in an argument slot must be refused"),
    };
    assert!(
        cond_errs
            .iter()
            .any(|e| e.contains("if.condition") && e.contains("expected Bool") && e.contains("?T")),
        "the condition slot: {cond_errs:?}",
    );
    assert!(
        arg_errs
            .iter()
            .any(|e| e.contains("sink.b") && e.contains("expected Bool") && e.contains("?T")),
        "the argument slot, which is where the verdict comes from: {arg_errs:?}",
    );
}

/// THE FAMILY WHOSE NEGATIVE DESTINATION DID NOT EXIST, AND NOW DOES — this row was
/// written as a REPORT, pinned in both directions so it could not rot, and it ended the way
/// it said it would: WI-20260826-7JDWY landed the collection-literal element check and the
/// two `unwrap_or_else` assertions failed, naming this comment.
///
/// WHAT IT NOW MEASURES is the `literals` row of §3 having a real negative destination on
/// its list and set halves: a type value in a `String` element slot is refused AND NAMES
/// WHAT IT DENOTES (`got Type (Cell)`), which is design §8's ask, at the element that
/// carries it. The `["a", 1]` row stays, with its polarity flipped, and so does its JOB:
/// it says the check is about ELEMENTS and not about type values, because a repair that
/// refused only `Type` would leave it RED. (While the rows asserted a load, the same
/// separation ran the other way — green under a `Type`-only repair. `/code-review` caught
/// the sentence still describing the pre-flip row.)
///
/// The tuple row beside them is unchanged and is still the contrast that made the gap
/// visible: a named tuple's components were checked all along.
#[test]
fn a_collection_literal_element_type_is_checked_for_every_element_alike() {
    let program = |ret: &str, body: &str, i: usize| {
        format!(
            r#"
namespace test.q0093elem{i}
  import anthill.prelude.{{Cell, Int64, List, Set, String, Type}}

  operation f() -> {ret} = {body}
end
"#
        )
    };
    let refusal = |ret: &str, body: &str, i: usize, what: &str| -> Vec<String> {
        match try_load_kb_with(&program(ret, body, i)) {
            Err(errs) => errs,
            Ok(_) => panic!("{what} must be refused"),
        }
    };
    // THE NEGATIVE DESTINATION: a type value in a `String` element slot, named at the
    // element that carries it and printed as what it DENOTES.
    let type_value = refusal(
        "List[T = String]",
        r#"["a", Cell]"#,
        0,
        "a `Type` in a `List[T = String]` element",
    );
    assert!(
        type_value.iter().any(|e| {
            e.contains("list.element 2 (collection-element)")
                && e.contains("expected String")
                && e.contains("got Type (Cell)")
        }),
        "the element that carries the type value, and its denotation: {type_value:?}",
    );
    // THE CONTROL, polarity flipped: an `Int64` in the same slot is refused too, which is
    // what says the check is about ELEMENTS and not about type values — a repair that
    // refused only `Type` would leave this row RED.
    let ordinary = refusal(
        "List[T = String]",
        r#"["a", 1]"#,
        1,
        "an Int64 in a `List[T = String]`",
    );
    assert!(
        ordinary
            .iter()
            .any(|e| e.contains("list.element 2 (collection-element)")
                && e.contains("expected String, got Int64")),
        "the CONTROL: an ordinary wrong element is refused the same way: {ordinary:?}",
    );
    let set_half = refusal(
        "Set[T = String]",
        r#"{"a", Cell}"#,
        2,
        "a `Type` in a `Set[T = String]` element",
    );
    assert!(
        set_half
            .iter()
            .any(|e| e.contains("set.element 2 (collection-element)")
                && e.contains("expected String")),
        "the set half of the same check: {set_half:?}",
    );

    // THE CONTRAST — a named tuple's components ARE checked, so the same type value is
    // refused there, and the message names the component that carries it.
    let errs = match try_load_kb_with(&program(
        "(a: String, b: String)",
        r#"(a: "x", b: Cell)"#,
        3,
    )) {
        Err(errs) => errs,
        Ok(_) => panic!("a named tuple's components must be checked"),
    };
    assert!(
        errs.iter()
            .any(|e| e.contains("expected (a: String, b: String)") && e.contains("b: Type")),
        "the tuple mismatch must show the `Type` in the component that carries it, \
         got {errs:?}",
    );
}

// ── ADJACENT-ROLE CONTROLS ─────────────────────────────────────────────────────

/// PATTERN — a `match` arm pattern spelled like a sort is a BINDER, not a type value: it
/// captures the scrutinee, and the arm body's reference to that name is the binder's.
/// Driven rather than asserted structurally: the operation returns `7`, which only the
/// binding reading can produce.
#[test]
fn a_pattern_binder_spelled_like_a_sort_binds() {
    let src = r#"
namespace test.q0093pat
  import anthill.prelude.{Cell, Int64, Type}

  operation f() -> Int64 = match 7 case Cell -> Cell
end
"#;
    let mut interp = interp_for(src);
    let v = interp
        .call("test.q0093pat.f", &[])
        .unwrap_or_else(|e| panic!("f: {e:?}"));
    assert!(
        matches!(v, Value::Int(7)),
        "`case Cell -> Cell` must bind the scrutinee and return it, got {v:?}",
    );
}

/// BINDER — the same control one family over: a lambda's parameter spelled like a sort is
/// a binder, and its body's reference is to the binder.
#[test]
fn a_lambda_binder_spelled_like_a_sort_binds() {
    let src = r#"
namespace test.q0093lam
  import anthill.prelude.{Cell, Int64, Type}

  operation f() -> Int64 =
    let g = lambda (Cell: Int64) -> Cell
    g(7)
end
"#;
    let mut interp = interp_for(src);
    let v = interp
        .call("test.q0093lam.f", &[])
        .unwrap_or_else(|e| panic!("f: {e:?}"));
    assert!(
        matches!(v, Value::Int(7)),
        "`lambda (Cell: Int64) -> Cell` must return its argument, got {v:?}",
    );
}

/// LABEL and MEMBER NAME — a field spelled like a sort: the label in `L(Cell: 7)` and the
/// member in `.Cell` are names, not value positions, so neither is classified and the
/// field's `Int64` value survives both.
#[test]
fn a_field_label_and_member_name_spelled_like_a_sort_stay_names() {
    let src = r#"
namespace test.q0093lbl
  import anthill.prelude.{Cell, Int64, Type}

  sort L
    entity L(Cell: Int64)
  end
  operation f() -> Int64 = L(Cell: 7).Cell
end
"#;
    let mut interp = interp_for(src);
    let v = interp
        .call("test.q0093lbl.f", &[])
        .unwrap_or_else(|e| panic!("f: {e:?}"));
    assert!(
        matches!(v, Value::Int(7)),
        "a label and a member name spelled like a sort must stay names, got {v:?}",
    );
}

/// METADATA KEY — the key half of the `metadata` row: `meta [Cell: Cell]` keeps the key as
/// a key and classifies only the value. Read through the same accessor the driving row
/// uses, so the two cannot disagree about which half is which.
#[test]
fn a_metadata_key_spelled_like_a_sort_stays_a_key() {
    let src = r#"
namespace test.q0093mk
  import anthill.prelude.{Cell, Int64, Type}

  operation tagged() -> Int64
    meta [Cell: Cell]
    = 1
end
"#;
    let kb = load_kb_with(src);
    let sym = kb
        .try_resolve_symbol("test.q0093mk.tagged")
        .expect("tagged resolves");
    let rec = anthill_core::kb::op_info::lookup_operation_info(&kb, sym).expect("info record");
    let v = anthill_core::kb::load::meta_value(&kb, rec.meta, "Cell")
        .expect("the entry is still keyed by the name `Cell`");
    assert_bare_cell(&kb, &Value::term(v), "the metadata value under the `Cell` key");
}

/// `TypeExpr` CHILD — a genuine type annotation is not a value position and must not be
/// read as one. The return type `Option[T = Type]` is a `TypeExpr` (its `Type` names a
/// sort in TYPE position, where it always denoted) while the body's `Cell` is the value
/// expression; the operation must still build the `some(…)` wrapper around a type value.
#[test]
fn a_type_annotation_position_is_not_a_value_position() {
    let src = r#"
namespace test.q0093ann
  import anthill.prelude.{Cell, Int64, Option, Type}
  import anthill.prelude.Option.{some}

  operation f() -> Option[T = Type] = some(Cell)
end
"#;
    let mut interp = interp_for(src);
    let v = interp
        .call("test.q0093ann.f", &[])
        .unwrap_or_else(|e| panic!("f: {e:?}"));
    match &v {
        Value::Entity { functor, pos, named } => {
            assert_eq!(interp.kb().local_name_of(*functor), "some");
            let payload = pos
                .first()
                .or_else(|| named.first().map(|(_, v)| v))
                .unwrap_or_else(|| panic!("`some(…)` must carry its payload, got {v:?}"));
            assert_bare_cell(interp.kb(), payload, "the Option payload");
        }
        other => panic!("expected `some(Cell)`, got {other:?}"),
    }
}

/// A NEWLY-CLASSIFIED HEAD'S TYPE ARGUMENTS ARE STILL VALIDATED — the check the
/// classifier's widening could have walked straight past.
///
/// FOUND BY `/code-review`, and it is the "one name, two questions" shape: the classifier
/// decides which applications reach the WI-709 type-argument check, and
/// `check_sort_type_args` opened by asking `kind_of` — the spelling the classifier had
/// just stopped using. Measured before the repair: with `namespace Box … end sort Box …
/// end`, the expression `Box[Zork = String, Zork = Bool, Int64, String]` — an undeclared
/// param, a duplicate of it, and two positionals against a one-parameter sort — LOADED
/// CLEAN, while the same expression under a plain `sort Box` was refused. Both gates ask
/// `has_kind` now, and this row is the pair: the newly-admitted head and the plain one
/// must be refused ALIKE, and a well-formed binding on the newly-admitted head must still
/// load (or the repair would have bought its loudness by refusing everything).
#[test]
fn a_newly_classified_head_still_has_its_type_arguments_checked() {
    let program = |decls: &str, args: &str, ns: &str| {
        format!(
            r#"
namespace test.q0093ta{ns}
  import anthill.prelude.{{Int64, String, Bool, Type}}

  {decls}
  operation f() -> Type = Box[{args}]
end
"#
        )
    };
    let namespace_first =
        "namespace Box\n  end\n  sort Box\n    sort V = ?\n    entity mk(x: V)\n  end";
    let plain = "sort Box\n    sort V = ?\n    entity mk(x: V)\n  end";

    for (what, decls, ns) in [
        ("a sort beside a namespace of the same name", namespace_first, "a"),
        ("CONTROL: a plain sort", plain, "b"),
    ] {
        let errs = match try_load_kb_with(&program(
            decls,
            "Zork = String, Zork = Bool, Int64, String",
            ns,
        )) {
            Err(errs) => errs,
            Ok(_) => panic!(
                "{what}: an undeclared type parameter must be refused — the classifier \
                 decides what REACHES this check, so the two must be keyed alike",
            ),
        };
        assert!(
            errs.iter()
                .any(|e| e.contains("no type parameter named 'Zork'") && e.contains("V")),
            "{what}: {errs:?}",
        );
        // …and the check is not simply refusing everything on that head.
        try_load_kb_with(&program(decls, "V = Int64", &format!("{ns}ok")))
            .unwrap_or_else(|e| panic!("{what}: a declared binding must still load: {e:?}"));
    }
}

/// A SORT SHARING ITS NAME WITH A RULE HEAD IS WHERE THE WIDENING DOES NOT REACH, and
/// this row says so in both declaration orders because that is the axis the widening is
/// about.
///
/// `/code-review` read the widening as able to steal a relation citation from such a name
/// — the hazard WAHB6's note named — and asked for it in the order this file had not
/// measured. Measured in BOTH: a rule head that RESOLVES mints no kind (§"A rule head
/// functor is resolved, not declared"), and `scan_definitions` pass 1 defines every sort
/// in every file before pass 3 reads a single head, so the head cannot be "first" whatever
/// the source order says — `kinds == [Sort]` either way, `kind_of` and `has_kind` agree,
/// and the reading is the same before and after. (The body-less `rule Both(?x)`
/// DECLARATION form, which does mint a predicate, is refused outright when a sort holds
/// the name, so it cannot build the pair either.)
///
/// PASSES EITHER WAY BY DESIGN: it pins a reading neither spelling of the classifier
/// moves. What it would catch is a future change that let a rule head add a kind to a sort
/// symbol — which under `has_kind` would then decide this name's reading.
#[test]
fn a_sort_sharing_its_name_with_a_rule_head_is_unmoved_by_the_widening() {
    let program = |decls: &str, ns: &str| {
        format!(
            r#"
namespace test.q0093rh{ns}
  import anthill.prelude.{{Int64, Type}}

  {decls}
  operation f() -> Type = Both
end
"#
        )
    };
    let rule_first = "rule Both(?x) :- ?x <=> 1\n  sort Both\n    entity mk(x: Int64)\n  end";
    let sort_first = "sort Both\n    entity mk(x: Int64)\n  end\n  rule Both(?x) :- ?x <=> 1";

    for (what, decls, ns) in [
        ("rule head written first", rule_first, "a"),
        ("sort written first", sort_first, "b"),
    ] {
        let src = program(decls, ns);
        let kb = load_kb_with(&src);
        let sym = kb
            .try_resolve_symbol(&format!("test.q0093rh{ns}.Both"))
            .expect("Both resolves");
        assert_eq!(
            kb.kind_of(sym),
            Some(SymbolKind::Sort),
            "{what}: a rule head that RESOLVES mints no kind, in either order",
        );
        assert!(
            !kb.has_kind(sym, SymbolKind::Goal),
            "{what}: …so the symbol carries no Goal kind for the widening to newly read",
        );
        let mut interp = interp_for(&src);
        let v = interp
            .call(&format!("test.q0093rh{ns}.f"), &[])
            .unwrap_or_else(|e| panic!("{what}: {e:?}"));
        match interp.kb().get_term(term_id(&v, what)).clone() {
            Term::Ref(s) => assert_eq!(interp.kb().local_name_of(s), "Both", "{what}"),
            other => panic!("{what}: expected `Ref(Both)`, got {other:?}"),
        }
    }
}

/// THE CLASSIFIER ASKS WHICH ROLES A NAME PLAYS, NOT WHICH KEYWORD CAME FIRST.
///
/// `namespace Box … end` before `sort Box … end` gives `Box` the kinds `[Namespace, Sort]`;
/// the same two declarations in the other order give `[Sort, Namespace]`. They are one
/// program written twice, so a bare `Box` in a `Type` slot must denote in both — under the
/// `kind_of` (first-declared) spelling the first program did not load at all.
///
/// This is the separating row `bare_name_denotes_type`'s doc asked this ticket for; the
/// third assertion is the one that fails when that predicate is reverted to `kind_of`.
#[test]
fn a_sort_declared_after_a_namespace_of_the_same_name_still_denotes() {
    let program = |decls: &str, ns: &str| {
        format!(
            r#"
namespace test.q0093ord{ns}
  import anthill.prelude.{{Int64, Type}}

  {decls}
  operation f() -> Type = Box
  operation g() -> Type = Box[V = Int64]
end
"#
        )
    };
    let namespace_first =
        "namespace Box\n  end\n  sort Box\n    sort V = ?\n    entity mk(x: V)\n  end";
    let sort_first =
        "sort Box\n    sort V = ?\n    entity mk(x: V)\n  end\n  namespace Box\n  end";

    for (what, decls, ns) in [
        ("namespace first", namespace_first, "a"),
        ("sort first", sort_first, "b"),
    ] {
        let src = program(decls, ns);
        // The kinds are a SET, and the two orders differ only in which element is first.
        let kb = load_kb_with(&src);
        let sym = kb
            .try_resolve_symbol(&format!("test.q0093ord{ns}.Box"))
            .expect("Box resolves");
        assert!(
            kb.has_kind(sym, SymbolKind::Sort) && kb.has_kind(sym, SymbolKind::Namespace),
            "{what}: `Box` plays both roles either way",
        );

        // …and BOTH FACES denote the same type in both orders, which is the point. The
        // applied face is asked here too because the two are one question about one name:
        // keyed apart, an order would classify the bare `Box` and not `Box[V = Int64]`,
        // and WAHB6's "the two carriers key alike" would hold in one order only.
        let mut interp = interp_for(&src);
        let bare = interp
            .call(&format!("test.q0093ord{ns}.f"), &[])
            .unwrap_or_else(|e| panic!("{what}, bare: {e:?}"));
        match interp.kb().get_term(term_id(&bare, what)).clone() {
            Term::Ref(s) => assert_eq!(interp.kb().local_name_of(s), "Box", "{what}"),
            other => panic!("{what}: expected `Ref(Box)`, got {other:?}"),
        }
        let applied = interp
            .call(&format!("test.q0093ord{ns}.g"), &[])
            .unwrap_or_else(|e| panic!("{what}, applied: {e:?}"));
        match interp.kb().get_term(term_id(&applied, what)).clone() {
            Term::Fn {
                functor,
                named_args,
                ..
            } => {
                assert_eq!(interp.kb().local_name_of(functor), "Box", "{what}");
                assert_eq!(named_args.len(), 1, "{what}: `Box[V = Int64]` binds V");
            }
            other => panic!("{what}: expected `Box(V: Int64)`, got {other:?}"),
        }
    }
}
