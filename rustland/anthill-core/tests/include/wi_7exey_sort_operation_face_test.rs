//! WI-20261022-7EXEY — A SORT THAT SHARES ITS NAME WITH AN OPERATION HAS A TYPE FACE.
//!
//! WI-751 admits `sort Positive … end` beside `operation Positive(x)`. A sort with no data
//! reading of its name has one identity (kernel-language.md §4.4), and this pair had one
//! too, so `Positive[T = A]` was stored as `Positive(T: A)` — the same term, headed by the
//! same symbol, as a call — and every reader of a stored clause took it as the call.
//! WI-974 refused the bracketed requirement where it was written. Now the pair's type
//! reading has the face a constructor's has (`KnowledgeBase::declaration_has_type_face`):
//! a type context names it `Positive†`, the plain symbol keeps the operation, and so
//! `requires Positive[T = A]` is the requirement written and `requires Positive(x)` the
//! call, in either declaration order. Decided with the user, 2026-10-22: a BARE
//! `Positive` in a data context is the operation, its type there is written `Positive[]`,
//! and reflect's `kind` says `Operation` for the plain symbol and `Sort` for the face.
//!
//! WHAT FAILS WITH THE CHANGE BACKED OUT is listed at each row, by these names (measured
//! 2026-10-22, each part alone, over this file, `wi974_kind_set_order_twin_test` and
//! `wi_jb6rs_type_face_test`; every part fails a row):
//!   * NO FACE — `type_context_face` and `type_face_of` minting for constructors only, the
//!     plain symbol still the operation where it is applied (the parent's reading);
//!   * FACE FOR CONSTRUCTORS — `declaration_has_type_face` itself minting for `Entity`
//!     only, which also makes `is_type_value_head` read the plain symbol as the type in
//!     every position;
//!   * BARE IS THE TYPE — `is_type_value_head` without its `declaration_has_type_face`
//!     exclusion: the face is minted, and the plain symbol is the type bare and applied;
//!   * KIND — `reflect_kind`'s case for the plain symbol;
//!   * TYPE SLOT — the loader's type slot asking `is_type_value_head` rather than
//!     `has_type_reading`, so a name that is an operation lowers there as a value place;
//!   * GOAL FACE — the rule-body walk heading a bracket at a goal by the face;
//!   * BINDING FACE — the rule-body walk giving a bracket's binding the face only for a
//!     constructor (`Loader::body_data_slot_name`, as before);
//!   * SLOT — `KnowledgeBase::binding_type_face` giving the face at an operation slot too;
//!   * RULE SLOT — the rule-body walk not handing that rule the binding's slot;
//!   * FRAME — the op-body bracket frame not reading the slot of an entry that is an
//!     operation (`build_load`), so it stays the operation at a type slot too;
//!   * LEAF — the op-body leaf giving such an entry its face before the slot is read
//!     (`push_leaf_occ`);
//!   * ALIAS — `resolve_sort_alias` and `value_alias` asked for the symbol as given, not
//!     its declaration's;
//!   * FACE KINDS — `KnowledgeBase::kinds` leaving `Operation` on a face;
//!   * SEALED — `check_operations_beside_a_sealed_type` refusing nothing.
//!
//! Outside this file: FACE FOR CONSTRUCTORS and BARE IS THE TYPE fail `wi974`'s
//! precondition row and `wi_jb6rs`'s `a_sort_has_one_reading_and_names_nothing_to_apply`
//! (the operation applied); NO FACE fails `wi974`'s bracket-requirement row; TYPE SLOT
//! fails `wi974`'s type-slot row (`Modify[Both]` lowered as a value place).
use anthill_core::eval::Value;
use anthill_core::kb::load::{self, LoadOptions};
use anthill_core::kb::term::Term;
use anthill_core::kb::term_view::{TermView, ViewHead};

use crate::common::{
    interp_for, load_errors_of, load_errors_of_files, load_in_a_later_call, load_kb_with,
    query_unary, rendered_load_errors, run_int64, type_application,
};

/// The spec, its provision, a caller that requires it, and the entry `goF`.
const SPEC: &str = "  sort Positive\n    sort T = ?\n    operation sign(x: T) -> Int64\n  end\n";
/// The predicate of the same name, a caller that requires its call, and the entry `goG`.
const PREDICATE: &str = "  operation Positive(x: Int64) -> Bool = x > 0\n";

fn program(decls: &str, uses: &str) -> String {
    format!(
        "namespace test.x7exey\n  import anthill.prelude.{{Int64, Bool}}\n{decls}  sort Amount\n    \
         entity amount(v: Int64)\n  end\n  operation amountSign(a: Amount) -> Int64 =\n    \
         match a\n      case amount(v) -> v\n{uses}end\n"
    )
}

const USES_SPEC: &str = "  namespace Amount\n    provides Positive[T = Amount, sign = amountSign]\n  \
                         end\n  operation f[A](a: A) -> Int64 requires Positive[T = A] = \
                         Positive.sign(a)\n  operation goF() -> Int64 = f(amount(v: 5))\n";
const USES_PREDICATE: &str =
    "  operation g(x: Int64) -> Int64 requires Positive(x) = x\n  operation goG() -> Int64 = g(3)\n";
const BREAKS_PREDICATE: &str = "  operation goBad() -> Int64 = g(0 - 1)\n";

/// The ticket's example, in both orders: `f` dispatches through the provision its bracket
/// requires, and `g`'s precondition is the operation's call — `g(3)` runs and `g(-1)` is
/// refused. The CONTROLS are the spec alone and the predicate alone.
///
/// BACKED OUT: NO FACE — `f` is refused in both orders, its requirement read as the
/// precondition `Positive(T: A)`; FACE FOR CONSTRUCTORS and BARE IS THE TYPE — `g`'s
/// precondition is read as the spec. The two controls pass either way, by design.
#[test]
fn the_requirement_and_the_call_both_work_in_both_orders() {
    let uses = format!("{USES_SPEC}{USES_PREDICATE}");
    for (order, decls) in [
        ("the spec first", format!("{SPEC}{PREDICATE}")),
        ("the predicate first", format!("{PREDICATE}{SPEC}")),
    ] {
        let src = program(&decls, &uses);
        assert_eq!(run_int64(&src, "test.x7exey.goF"), Ok(5), "{order}: `f` is the requirement written");
        assert_eq!(run_int64(&src, "test.x7exey.goG"), Ok(3), "{order}: `g(3)` holds its precondition");
        let errs = load_errors_of(&program(&decls, &format!("{uses}{BREAKS_PREDICATE}")));
        assert!(
            errs.iter().any(|e| e.contains("unsatisfied precondition")),
            "{order}: `g(-1)` breaks `requires Positive(x)`; got {errs:#?}",
        );
    }
    // CONTROLS: each half alone.
    assert_eq!(run_int64(&program(SPEC, USES_SPEC), "test.x7exey.goF"), Ok(5), "the spec alone");
    assert_eq!(
        run_int64(&program(PREDICATE, USES_PREDICATE), "test.x7exey.goG"),
        Ok(3),
        "the predicate alone",
    );
    let errs = load_errors_of(&program(PREDICATE, &format!("{USES_PREDICATE}{BREAKS_PREDICATE}")));
    assert!(
        errs.iter().any(|e| e.contains("unsatisfied precondition")),
        "the predicate alone: `g(-1)` is refused; got {errs:#?}",
    );
}

/// A bracket written as a rule-body GOAL is the sort's atom, in both orders: answered by a
/// fact of that bracket whichever order its bindings are written in, and with a binding
/// left open. The rule-body walk headed a GOAL's bracket by the plain symbol, where the
/// clause converter and the query converter head it by the face, so it was the
/// operation's call — refused for labels the operation does not have. The CONTROL is the
/// spec alone. The same walk headed an eponymous entity's bracket goal by the constructor,
/// so the fact its bracket stored (WI-20260902-JB6RS) was never found; that is the last
/// case.
///
/// BACKED OUT: GOAL FACE — the pair's two orders are refused, "named argument 'T' names
/// no parameter of this operation", and the eponymous entity's goal answers nothing
/// (measured alone); NO FACE and FACE FOR CONSTRUCTORS fail it too. The control passes.
#[test]
fn a_bracket_goal_is_the_sorts_atom_in_both_orders() {
    let spec = "  sort Pair\n    sort T = ?\n    sort U = ?\n  end\n";
    let op = "  operation Pair(x: Int64) -> Bool = x > 0\n";
    let uses = "  import anthill.prelude.String\n  fact Pair[U = String, T = Int64]\n  \
                rule inOrder(1) :- Pair[T = Int64, U = String]\n  \
                rule reversed(1) :- Pair[U = String, T = Int64]\n  \
                rule open(1) :- Pair[T = Int64, U = ?u]\n";
    for (order, decls) in [
        ("the spec first", format!("{spec}{op}")),
        ("the operation first", format!("{op}{spec}")),
        ("CONTROL, the spec alone", spec.to_string()),
        (
            "an eponymous entity's sort",
            "  sort Pair\n    sort T = ?\n    sort U = ?\n    entity Pair(n: Int64)\n  end\n".to_string(),
        ),
    ] {
        let mut kb = load_kb_with(&program(&decls, uses));
        for rule in ["inOrder", "reversed", "open"] {
            assert_eq!(
                query_unary(&mut kb, &format!("test.x7exey.{rule}")).len(),
                1,
                "{order}: `{rule}` is answered by the fact",
            );
        }
    }
}

/// A BARE `Positive` in a data context is the OPERATION (§4.4: the context's own reading
/// first), in both orders: it eta-lifts to a function value, and reflect's `kind` calls it
/// `Operation`. Its type written as data takes the bracket, `Positive[]`, which `kind`
/// calls a `Sort`. The CONTROLS are each half alone: the spec alone's bare name is its
/// type, which `kind` calls a `Sort` and which does not apply; the predicate alone's is the
/// operation.
///
/// BACKED OUT: NO FACE, FACE FOR CONSTRUCTORS, BARE IS THE TYPE — the bare name is the
/// type, and `apply(Positive, 3)` is refused; KIND — `kind(Positive)` is `Sort` in the
/// spec-first order. The controls pass either way, by design.
#[test]
fn a_bare_name_in_a_data_context_is_the_operation_in_both_orders() {
    const APPLY: &str = "  operation apply(p: (Int64) -> Bool, x: Int64) -> Bool = p(x)\n  \
                         operation viaBare() -> Bool = apply(Positive, 3)\n";
    const KIND_BARE: &str = "  import anthill.reflect.{kind}\n  rule kindBare(?k) :- kind(Positive, ?k)\n";
    const KIND_TYPE: &str = "  rule kindType(?k) :- kind(Positive[], ?k)\n";
    let kind = |src: &str, rule: &str| -> Vec<String> {
        query_unary(&mut load_kb_with(src), &format!("test.x7exey.{rule}"))
            .into_iter()
            .map(|(v, _)| match v {
                Value::Str(s) => s,
                other => panic!("`kind` answers a string, got {other:?}"),
            })
            .collect()
    };
    let applied = |src: &str| interp_for(src).call("test.x7exey.viaBare", &[]);
    for (order, decls) in [
        ("the spec first", format!("{SPEC}{PREDICATE}")),
        ("the predicate first", format!("{PREDICATE}{SPEC}")),
    ] {
        let src = program(&decls, &format!("{APPLY}{KIND_BARE}{KIND_TYPE}"));
        let got = applied(&src);
        assert!(
            matches!(got, Ok(Value::Bool(true))),
            "{order}: bare `Positive` is the operation's function value; got {got:?}",
        );
        assert_eq!(kind(&src, "kindBare"), ["Operation"], "{order}: the plain symbol");
        assert_eq!(kind(&src, "kindType"), ["Sort"], "{order}: the face");
    }
    // CONTROLS.
    let spec = program(SPEC, &format!("{KIND_BARE}{KIND_TYPE}"));
    assert_eq!(kind(&spec, "kindBare"), ["Sort"], "the spec alone: its bare name is the type");
    assert_eq!(kind(&spec, "kindType"), ["Sort"], "the spec alone: `Positive[]` is that type");
    let errs = load_errors_of(&program(SPEC, APPLY));
    assert!(
        errs.len() == 1 && errs[0].contains("expected Int64 -> Bool, got Type (Positive)"),
        "the spec alone: its bare name is the type, which does not apply: {errs:#?}",
    );
    let predicate = program(PREDICATE, &format!("{APPLY}{KIND_BARE}"));
    let got = applied(&predicate);
    assert!(matches!(got, Ok(Value::Bool(true))), "the predicate alone: {got:?}");
    assert_eq!(kind(&predicate, "kindBare"), ["Operation"], "the predicate alone");
}

/// The type, held as data, is the face: `fact held(Positive[])` is found by the bracket and
/// not by the bare name, which is the operation, and it PRINTS with the bracket — the
/// printed fact, loaded in its place, is that fact again.
///
/// BACKED OUT: NO FACE, FACE FOR CONSTRUCTORS — one term, printed `Positive`; BARE IS THE
/// TYPE — `held(Positive)` finds the fact.
#[test]
fn the_type_as_data_is_the_face_and_prints_with_the_bracket() {
    use anthill_core::persistence::print;
    let uses = "  fact held(Positive[])\n  rule byBracket(1) :- held(Positive[])\n  \
                rule byBare(1) :- held(Positive)\n";
    for (order, decls) in [
        ("the spec first", format!("{SPEC}{PREDICATE}")),
        ("the predicate first", format!("{PREDICATE}{SPEC}")),
    ] {
        let mut kb = load_kb_with(&program(&decls, uses));
        assert_eq!(query_unary(&mut kb, "test.x7exey.byBracket").len(), 1, "{order}: the bracket");
        assert_eq!(query_unary(&mut kb, "test.x7exey.byBare").len(), 0, "{order}: the bare name");
        let held = kb.try_resolve_symbol("test.x7exey.held").expect("held resolves");
        let rid = kb.rules_by_functor(held)[0];
        let printed = print::print_fact(&kb, kb.rule_head(rid), None);
        assert!(printed.contains("Positive[]"), "{order}: printed with the bracket: {printed}");
        let reloaded = format!("  {}\n  rule byBracket(1) :- held(Positive[])\n  rule byBare(1) :- held(Positive)\n", printed.trim());
        let mut again = load_kb_with(&program(&decls, &reloaded));
        assert_eq!(query_unary(&mut again, "test.x7exey.byBracket").len(), 1, "{order}: `{printed}` reloads");
        assert_eq!(query_unary(&mut again, "test.x7exey.byBare").len(), 0, "{order}: as the type");
    }
}

/// eval's APPLIED arm, reached by an occurrence made from a TERM, which carries no mark of
/// the bracket it was written with: here the term a fact STORED for `Positive[T = Int64]`,
/// evaluated as an expression (`materialize_from_handle`). It is headed by the face, and
/// builds the type.
///
/// BACKED OUT: NO FACE, FACE FOR CONSTRUCTORS — the stored term is `Positive(T: Int64)`,
/// not a type.
#[test]
fn an_unmarked_bracket_builds_the_type_in_eval() {
    let uses = "  fact held(Positive[T = Int64])\n";
    for (order, decls) in [
        ("the spec first", format!("{SPEC}{PREDICATE}")),
        ("the predicate first", format!("{PREDICATE}{SPEC}")),
    ] {
        let mut interp = interp_for(&program(&decls, uses));
        let kb = interp.kb();
        let positive = kb.try_resolve_symbol("test.x7exey.Positive").expect("Positive resolves");
        let held = kb.try_resolve_symbol("test.x7exey.held").expect("held resolves");
        let Term::Fn { pos_args, .. } = kb.get_term(kb.rule_head(kb.rules_by_functor(held)[0])) else {
            panic!("{order}: `held(…)` is an application");
        };
        let stored = pos_args[0];
        match interp.run_with_requirements(stored, Default::default()) {
            Ok(ty) => assert!(
                matches!(ty.head(interp.kb()), ViewHead::Functor { functor, .. }
                    if functor.is_type_face() && functor.plain() == positive),
                "{order}: the type, named by the face: {ty:?}",
            ),
            Err(e) => panic!("{order}: expected the type, got {e:?}"),
        }
    }
}

/// A sort-named operation written as a BINDING of a bracket is its type, in every body, as
/// the clause holding the bracket reads it: a rule body's `held(Box[V = Positive])` finds
/// `fact held(Box[V = Positive])`, a goal `:- Box[V = Positive]` finds `fact Box[V =
/// Positive]`, and an operation body's `Box[V = Positive]` binds the face. The two body
/// walks gave the face to a constructor only, so the binding was the operation there and
/// the plain sort in the clause. The CONTROL is the spec alone, whose binding is the plain
/// sort everywhere.
///
/// BACKED OUT: BINDING FACE — the rule body's rules answer nothing; FRAME — the operation
/// body's binding is the operation's function value, refused; NO FACE and FACE FOR
/// CONSTRUCTORS fail it too.
#[test]
fn a_bracket_binding_is_the_type_in_every_body_in_both_orders() {
    let uses = "  import anthill.prelude.Type\n  sort Box\n    sort V = ?\n  end\n  \
                fact held(Box[V = Positive])\n  rule viaData(1) :- held(Box[V = Positive])\n  \
                fact Box[V = Positive]\n  rule viaGoal(1) :- Box[V = Positive]\n  \
                operation theBox() -> Type = Box[V = Positive]\n";
    for (order, decls, face) in [
        ("the spec first", format!("{SPEC}{PREDICATE}"), true),
        ("the predicate first", format!("{PREDICATE}{SPEC}"), true),
        ("CONTROL, the spec alone", SPEC.to_string(), false),
    ] {
        let src = program(&decls, uses);
        let mut kb = load_kb_with(&src);
        for rule in ["viaData", "viaGoal"] {
            assert_eq!(query_unary(&mut kb, &format!("test.x7exey.{rule}")).len(), 1, "{order}: {rule}");
        }
        let mut interp = interp_for(&src);
        let positive = interp.kb().try_resolve_symbol("test.x7exey.Positive").expect("resolves");
        let Ok(the_box) = interp.call("test.x7exey.theBox", &[]) else {
            panic!("{order}: `theBox` returns the type");
        };
        let Some((_, named)) = type_application(interp.kb(), &the_box) else {
            panic!("{order}: `Box[V = …]` is an application: {the_box:?}");
        };
        let bound = named[0].1.head(interp.kb());
        assert!(
            matches!(bound, ViewHead::Ident(s) | ViewHead::Functor { functor: s, pos_arity: 0, named_arity: 0 }
                if s.plain() == positive && s.is_type_face() == face),
            "{order}: the binding is the type — {}: {bound:?}",
            if face { "the face" } else { "the sort" },
        );
    }
}

/// A bracket's OPERATION slot binds the operation, never the type face: an operation's
/// `requires Combiner[T = A, combine = tagCombine]` dispatches to `tagCombine` although a
/// sort of that name is beside it, and an operation body's `Combiner[…, combine =
/// tagCombine]` reads the binding as the operation — which a type value cannot hold, so it
/// is refused exactly as it is for an operation with no sort beside it, the CONTROL. (A
/// clause's bracket refuses an operation slot as no type parameter of the sort, in both.)
///
/// The instance claim is the third producer: `fact Combiner[T = Tag, combine = tagCombine]`
/// is found by a rule-body goal that writes the same bracket, the clause converter and the
/// rule-body walk reading the slot alike.
///
/// BACKED OUT: SLOT and LEAF — the operation body's binding is the face, and loads clean;
/// RULE SLOT — the goal finds no fact, the walk and the clause converter reading the slot
/// apart. FACE FOR CONSTRUCTORS and BARE IS THE TYPE fail it too.
#[test]
fn an_operation_slot_binds_the_operation_in_both_orders() {
    let uses = |the_sort: &str, entry: &str| {
        format!(
            "  import anthill.prelude.Type\n  sort Combiner\n    sort T = ?\n    operation \
             combine(x: T, y: T) -> T\n  end\n  sort Tag\n    entity tag(n: Int64)\n  end\n\
             {the_sort}  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 99)\n  namespace \
             Tag\n    provides Combiner[T = Tag, combine = tagCombine]\n  end\n{entry}"
        )
    };
    let requires = "  operation f[A](a: A) -> A requires Combiner[T = A, combine = tagCombine] = \
                    Combiner.combine(a, a)\n  operation go() -> Int64 =\n    match f(tag(n: 1))\n      \
                    case tag(v) -> v\n";
    let type_value = "  operation theCombiner() -> Type = Combiner[T = Tag, combine = tagCombine]\n";
    let claim = "  fact Combiner[T = Tag, combine = tagCombine]\n  \
                 rule viaGoal(1) :- Combiner[T = Tag, combine = tagCombine]\n";
    let the_sort = "  sort tagCombine\n    entity tc\n  end\n";
    let op_first = |entry: &str| uses("", &format!("{the_sort}{entry}"));
    // The refusals without their `line:col: ` prefix, which the declarations move.
    let refusal = |src: &str| -> Vec<String> {
        load_errors_of(src)
            .into_iter()
            .map(|e| e.split_once(": ").map_or(e.clone(), |(_, rest)| rest.to_owned()))
            .collect()
    };
    let control = refusal(&program(SPEC, &uses("", type_value)));
    assert!(
        control.len() == 1 && control[0].contains("bare reference to the 2-parameter operation"),
        "CONTROL: an operation in a type value is refused as a function value: {control:#?}",
    );
    let answered = |src: &str| query_unary(&mut load_kb_with(src), "test.x7exey.viaGoal").len();
    for (order, sort_first, op_after, claims) in [
        ("the sort first", uses(the_sort, requires), uses(the_sort, type_value), uses(the_sort, claim)),
        ("the operation first", op_first(requires), op_first(type_value), op_first(claim)),
    ] {
        assert_eq!(run_int64(&program(SPEC, &sort_first), "test.x7exey.go"), Ok(99), "{order}");
        assert_eq!(refusal(&program(SPEC, &op_after)), control, "{order}: the operation body");
        assert_eq!(answered(&program(SPEC, &claims)), 1, "{order}: the goal finds the fact");
    }
    assert_eq!(run_int64(&program(SPEC, &uses("", requires)), "test.x7exey.go"), Ok(99), "CONTROL");
    assert_eq!(answered(&program(SPEC, &uses("", claim))), 1, "CONTROL: the goal finds the fact");
}

/// A type face is never the operation of its name: two facts of a sort-named operation's
/// BRACKET at two arities load, as they do for a sort alone, where the face was asked the
/// operation's questions and refused as "an operation written at more than one arity".
///
/// BACKED OUT: FACE KINDS — both orders are refused; GOAL FACE, NO FACE and FACE FOR
/// CONSTRUCTORS fail it too. The control passes.
#[test]
fn bracket_facts_of_two_arities_load_in_both_orders() {
    let uses = "  fact Positive[T = Int64]\n  fact Positive[T = Int64, sign = amountSign]\n  \
                rule both(1) :- Positive[T = Int64]\n";
    for (order, decls) in [
        ("the spec first", format!("{SPEC}{PREDICATE}")),
        ("the predicate first", format!("{PREDICATE}{SPEC}")),
        ("CONTROL, the spec alone", SPEC.to_string()),
    ] {
        let mut kb = load_kb_with(&program(&decls, uses));
        assert_eq!(query_unary(&mut kb, "test.x7exey.both").len(), 1, "{order}");
    }
}

/// A LATER load may not give a SEALED sort an operation of its name (kernel-language.md
/// §8.3): the pair names its type by a face, which the sealed load's terms do not carry.
/// Measured with `operation Cell(…)` in `anthill.prelude` after the standard library's seal,
/// an ordinary cell program was refused, `Cell[V = Int64]` "not `Modifiable`". The other
/// order is accepted, and the sealed operation's precondition still reads as its call; the
/// CONTROLS are the two sources in ONE load (the pair is admitted, WI-751), and two loads
/// with nothing sealed.
///
/// BACKED OUT: SEALED — the later operation loads clean. FACE FOR CONSTRUCTORS and BARE IS
/// THE TYPE fail the other order (the sealed operation's call read as the sort); the
/// controls pass either way.
#[test]
fn a_later_load_may_not_give_a_sealed_sort_an_operation_of_its_name() {
    let src = |decl: &str| format!("namespace test.x7exey\n  import anthill.prelude.{{Int64, Bool}}\n{decl}end\n");
    let (spec, predicate) = (src(SPEC), src(PREDICATE));
    let mut kb = load_kb_with(&spec);
    load::seal_declarations(&mut kb);
    let errs = rendered_load_errors(
        load_in_a_later_call(&mut kb, &predicate, LoadOptions::default()).err().unwrap_or_default(),
    );
    assert!(
        errs.len() == 1 && errs[0].contains("is declared beside the sort of that name a sealed load"),
        "a later operation beside the sealed sort: {errs:#?}",
    );
    // The other order: a later sort beside the sealed operation, whose terms name it only
    // as the operation — `g`'s precondition is its call, before and after.
    let mut kb = load_kb_with(&src(&format!("{PREDICATE}{USES_PREDICATE}")));
    load::seal_declarations(&mut kb);
    let later = src(&format!("{SPEC}  operation goBad() -> Int64 = g(0 - 1)\n"));
    let errs = rendered_load_errors(
        load_in_a_later_call(&mut kb, &later, LoadOptions::default()).err().unwrap_or_default(),
    );
    assert!(
        errs.len() == 1 && errs[0].contains("unsatisfied precondition"),
        "a later sort beside the sealed operation loads, and `g(-1)` is still refused: {errs:#?}",
    );
    // CONTROLS.
    assert_eq!(load_errors_of_files(&[&spec, &predicate]), Vec::<String>::new(), "in one load");
    let mut kb = load_kb_with(&spec);
    let unsealed = load_in_a_later_call(&mut kb, &predicate, LoadOptions::default());
    assert!(unsealed.is_ok(), "nothing sealed: {:?}", unsealed.err().map(rendered_load_errors));
}

/// A type ALIAS that shares its name with an operation is the pair too, and its face stands
/// for what the alias does: `-> Money` over `sort Money = Int64` beside `operation Money(c:
/// Int64) -> Money` is `Int64`, in both orders. The alias readers are asked for the
/// declaration, which a face masks to. The CONTROL is the alias alone.
///
/// BACKED OUT: ALIAS — both orders are refused, "expected Money, got Int64"; TYPE SLOT —
/// `-> Money` lowers as a value place; FACE FOR CONSTRUCTORS and BARE IS THE TYPE — the
/// call `Money(4)` is refused as a sort applied. The control passes either way.
#[test]
fn an_alias_beside_an_operation_stands_for_its_type_in_both_orders() {
    let alias = "  sort Money = Int64\n";
    let op = "  operation Money(c: Int64) -> Money = c\n";
    let uses = "  operation go() -> Int64 = Money(4)\n";
    for (order, decls) in [("the alias first", format!("{alias}{op}")), ("the operation first", format!("{op}{alias}"))] {
        assert_eq!(run_int64(&program(&decls, uses), "test.x7exey.go"), Ok(4), "{order}");
    }
    let control = "  operation mk(c: Int64) -> Money = c\n  operation go() -> Int64 = mk(4)\n";
    assert_eq!(run_int64(&program(alias, control), "test.x7exey.go"), Ok(4), "CONTROL, the alias alone");
}
