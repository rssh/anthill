//! WI-974 — A NAME IS READ BY THE ROLES IT PLAYS, NOT BY THE KEYWORD WRITTEN FIRST.
//!
//! One written name can play several roles, and the loader admits several such sets on
//! purpose — `KindSet`'s doc lists them, with what measured each. The set was an ordered
//! list whose HEAD, the keyword written first, was compared against one kind at ~65
//! sites. Each asked "was it WRITTEN with this keyword" where "does it play this role" was
//! meant, so two programs that differ only in the order of two declarations — or in which
//! §6.3 spelling they use — loaded or ran differently. The roles are now a `KindSet`, and
//! the written keyword is a display-only `KindLabel` that cannot be compared with a kind.
//!
//! Where a name plays a type role AND another, the site reads it by POSITION, as
//! kernel-language §4.4 does: BARE, a sort that is no constructor is the type
//! (`KnowledgeBase::is_type_value_head`); APPLIED, a name that is an operation is the
//! operation (`KnowledgeBase::names_only_a_type`); at a provision's binding, the SLOT
//! decides (`is_type_param_binding` of the key).
//!
//! Every row here is ONE PROGRAM WRITTEN TWICE, and asserts the two give one verdict.
//!
//! WHAT FAILS WITH THE CHANGE BACKED OUT — every row (measured, 2026-10-21, the sources
//! at the parent commit and this file in a binary of its own), each on one half only:
//!   * `a_const_beside_a_namespace_reads_alike_in_both_orders` — namespace first, the
//!     field of the const (`origin.X`, the namespace declaring `Y`) was refused: "type
//!     mismatch in X.name: expected resolved name, got unresolved".
//!   * `a_simp_right_hand_side_constructs_in_both_spellings` — the long spelling (`sort Rec
//!     { entity Rec(n: Int64) }`) died in eval, `Rec` built as a TYPE ("has no type
//!     parameter named 'n'"); the short spelling constructed. The gap
//!     `wi_rm247_data_sort_equation_test`'s header recorded as NOT COVERED.
//!   * `a_bracket_is_checked_on_a_sort_written_after_its_namespace` — namespace first, a
//!     fact's `Box[W = Int64]` loaded clean: the bracket check found no owner.
//!   * `a_value_precondition_over_a_sort_named_operation_is_checked_in_both_orders` — sort
//!     first, `requires both(x)` was read as a spec requirement and never proved:
//!     `f(-1)` loaded clean.
//!   * `an_operation_slot_bound_to_a_sort_named_operation_dispatches_in_both_orders` —
//!     sort first, `combine = tagCombine` was not seen as an operation binding: "backs no
//!     operation 'combine'".
//!   * `a_sort_named_operation_is_a_type_in_a_type_slot_in_both_orders` — both orders: the
//!     loader lowered `Both` in a type slot as a VALUE place (by `has_kind(Operation)`,
//!     not by the written keyword — the one fix here that is not order), so the
//!     operation's own `-> Both` drew "expected Both, got Both … please report it", and
//!     `Modify[Both]` was refused for a reason that depended on order.
//!   * `a_bracket_requirement_on_a_sort_named_operation_is_refused_in_both_orders` — spec
//!     first, `requires Both[T = Int64]` loaded and was read as the requirement written;
//!     operation first it was read as a call of the operation. A stored clause keeps no
//!     bracket for a sort with no constructor, so no reader can tell the two: the bracket
//!     is now refused where it is written, in both orders — the one row where a verdict
//!     that held in one order was given up for a loud one in both.
//!   * `an_operations_own_parameter_projects_beside_a_same_named_sort_in_both_orders` —
//!     sort first, `F[U]`'s `U.Elem` was refused ("no `requires` bound … declares a
//!     member"); operation first it was self-licensed, as the operation alone is.
//!
//! PASS EITHER WAY, by design — the halves of each twin that were already right, which
//! is what makes the failing halves a difference of ORDER and nothing else, and the two
//! CONTROLS (the operation alone, the sort alone).
//!
//! The C++ generator's sum band is driven in `anthill-cpp-gen`:
//! `a_sum_written_after_its_namespace_is_emitted`.
//!
//! NO ROW DRIVES THE REST, and none fails if one of them is backed out alone:
//!   * the VALUE-PLACE readers — `Param`, `CallbackParam`, `CallbackResult`, `OpResult`,
//!     `Field`, `LocalLet` (`flow_derive`, `region`, `is_result_binder`, `effects`,
//!     `unify::callback_binder_position`, the loader's field and callback-place tests, the
//!     provenance builtin, `binder_out_of_scope`, `modify_place_type`). Each asks
//!     `KindSet::is_place`, which reads a name that is a type as well — `operation
//!     foo[T](T: Int64)`'s `T`, `{Sort, Param}`, the one such set — as the type, the
//!     reading the written keyword gave it there (the type parameter is declared first).
//!     Every other value place plays one role, where the head of a one-element list and
//!     membership are the same answer.
//!   * reachable, not driven: the other `Const` readers (eval's `force_const`, `const_map`,
//!     the data-slot folds, host const sources) — namespace first; the other `Operation`
//!     readers (const purity — a bare sort-named operation is the type there too —,
//!     `operation_map`, the two contract-target splits, the backed spec op) and the
//!     eta-lift hint; the `Sort` readers in `apply` (HK carrier),
//!     `unify` (a carrier's own member) and `provision_binding_at_param`; eval's BARE sort
//!     arm, reached only by a KB loaded without the typer; `body_specialize`'s nullary
//!     constructor (an eponymous one); the rigid projection's chain for a parameter of a
//!     sort that is also an operation; `modify_place_type`'s arms, which the loader fix
//!     above now keeps a sort-named operation from reaching; and the C++ generator's
//!     const and trait bands.

use anthill_core::eval::Value;

use crate::common::{load_errors_of, query_unary, run_int64, try_load_kb_with};

const BOTH_ORDERS: [&str; 2] = ["first", "second"];

/// `a` then `b` for `"first"`, `b` then `a` for `"second"`.
fn ordered(order: &str, a: &str, b: &str) -> String {
    match order {
        "first" => format!("{a}{b}"),
        _ => format!("{b}{a}"),
    }
}

/// The answers of `rel`, or the refusal.
fn answers(src: &str, rel: &str) -> Result<Vec<i64>, Vec<String>> {
    let mut kb = try_load_kb_with(src)?;
    Ok(query_unary(&mut kb, rel)
        .into_iter()
        .map(|(v, definite)| {
            assert!(definite, "a conditional answer, {v:?}");
            match v {
                Value::Int(n) => n,
                other => panic!("expected an Int64, got {other:?}"),
            }
        })
        .collect())
}

/// RXT6S's pair: `const origin` and `namespace origin`, one symbol `{Const, Namespace}`.
/// The whole name is read first, so `origin.X` is the namespace's `X` where it declares
/// one; where it does not, it is the field `X` of the const's value.
#[test]
fn a_const_beside_a_namespace_reads_alike_in_both_orders() {
    let the_const = "  const origin: Q = Q.q(7)\n";
    for (row, member, expected) in [
        ("whole", "    const X: Int64 = 3\n", 3),
        ("field", "    const Y: Int64 = 3\n", 7),
    ] {
        let the_namespace = format!("  namespace origin\n{member}  end\n");
        for order in BOTH_ORDERS {
            let decls = ordered(order, the_const, &the_namespace);
            let src = format!(
                "namespace test.wi974c\n  import anthill.prelude.{{Int64}}\n  sort Q\n    \
                 entity q(X: Int64)\n  end\n{decls}  operation go() -> Int64 = origin.X\n  \
                 rule r(?x) :- ?x <=> go()\nend\n"
            );
            assert_eq!(
                answers(&src, "test.wi974c.r"),
                Ok(vec![expected]),
                "{row}, the const written {order}",
            );
        }
    }
}

/// §6.3's two spellings of one declaration, `{Entity, Sort}` and `{Sort, Entity}`: a
/// `@[simp]` equation leaves the constructor's application where the call stood, and
/// eval constructs it in both.
#[test]
fn a_simp_right_hand_side_constructs_in_both_spellings() {
    for (spelling, decl) in [
        ("entity Rec(…)", "  entity Rec(n: Int64)\n"),
        ("sort Rec { entity Rec(…) }", "  sort Rec\n    entity Rec(n: Int64)\n  end\n"),
    ] {
        for rhs in ["Rec(n: ?v)", "Rec(?v)"] {
            let src = format!(
                "namespace test.wi974s\n  import anthill.prelude.Int64\n{decl}  operation \
                 mkrec(v: Int64) -> Rec\n  rule mkrec(?v) <=> {rhs} @[simp]\n  operation \
                 nof(r: Rec) -> Int64 = r.n\n  operation go() -> Int64 = nof(mkrec(4))\nend\n"
            );
            assert_eq!(run_int64(&src, "test.wi974s.go"), Ok(4), "{spelling}, `<=> {rhs}`");
        }
    }
}

/// 059 R2's pair, `{Namespace, Sort}` in either order: a bracket written in a clause is
/// checked against the sort's parameters whichever came first.
#[test]
fn a_bracket_is_checked_on_a_sort_written_after_its_namespace() {
    let the_sort = "  sort Box\n    sort V = ?\n    entity mk(x: V)\n  end\n";
    let the_namespace = "  namespace Box\n  end\n";
    for order in BOTH_ORDERS {
        let decls = ordered(order, the_sort, the_namespace);
        let program = |clause: &str| {
            format!("namespace test.wi974b\n  import anthill.prelude.{{Int64}}\n{decls}{clause}end\n")
        };
        for clause in [
            "  fact held(t: Box[W = Int64])\n",
            "  rule holds(?t) :- ?t <=> Box[W = Int64]\n",
        ] {
            let errs = load_errors_of(&program(clause));
            assert!(
                errs.iter().any(|e| e.contains("has no type parameter named 'W'")),
                "the sort written {order}, {clause:?}: expected the bracket refused, got {errs:?}",
            );
        }
        // CONTROL: the parameter the sort declares is accepted in both orders.
        assert_eq!(
            load_errors_of(&program("  fact held(t: Box[V = Int64])\n")),
            Vec::<String>::new(),
            "the sort written {order}: `V` is its parameter",
        );
    }
}

/// WI-751's pair, `{Sort, Operation}` in either order: a `requires` clause headed by the
/// name is APPLIED, so it is the operation's — a value precondition, proved at the call —
/// and not a spec requirement. The CONTROL is the operation alone.
#[test]
fn a_value_precondition_over_a_sort_named_operation_is_checked_in_both_orders() {
    let the_sort = "  sort both\n    entity mk(n: Int64)\n  end\n";
    let the_op = "  operation both(x: Int64) -> Bool = x > 0\n";
    for (order, decls) in [
        ("the sort first", format!("{the_sort}{the_op}")),
        ("the operation first", format!("{the_op}{the_sort}")),
        ("CONTROL, the operation alone", the_op.to_string()),
    ] {
        let src = format!(
            "namespace test.wi974p\n  import anthill.prelude.{{Int64, Bool}}\n{decls}  operation \
             f(x: Int64) -> Int64 requires both(x) = x\n  operation go() -> Int64 = f(0 - 1)\nend\n"
        );
        let errs = load_errors_of(&src);
        assert!(
            errs.iter().any(|e| e.contains("unsatisfied precondition")),
            "{order}: `f(-1)` breaks `requires both(x)`, and must be refused; got {errs:?}",
        );
    }
}

/// `{Sort, Operation}` again, at an OPERATION slot of a provision: `combine = tagCombine`
/// binds the operation whichever of the two was written first — the slot says so, not the
/// value's kinds.
#[test]
fn an_operation_slot_bound_to_a_sort_named_operation_dispatches_in_both_orders() {
    let the_sort = "  sort tagCombine\n    entity tc\n  end\n";
    let the_op = "  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 99)\n";
    for order in BOTH_ORDERS {
        let decls = ordered(order, the_sort, the_op);
        let src = format!(
            "namespace test.wi974d\n  import anthill.prelude.Int64\n  import \
             test.wi974d.Combiner.{{combine}}\n  sort Combiner\n    sort T = ?\n    operation \
             combine(x: T, y: T) -> T\n  end\n  sort Tag\n    entity tag(n: Int64)\n  end\n\
             {decls}  namespace Tag\n    provides Combiner[T = Tag, combine = tagCombine]\n  \
             end\n  operation go() -> Int64 =\n    match combine(tag(n: 1), tag(n: 2))\n      \
             case tag(v) -> v\nend\n"
        );
        assert_eq!(run_int64(&src, "test.wi974d.go"), Ok(99), "the sort written {order}");
    }
}

/// `{Sort, Operation}` once more, BARE in a type slot: the name is the type (§4.4), so
/// `Modify[Both]` is refused as a TYPE target exactly as `Modify[Cell]` is, and the
/// operation's own `-> Both` is the sort. The CONTROL is the sort alone.
#[test]
fn a_sort_named_operation_is_a_type_in_a_type_slot_in_both_orders() {
    let the_sort = "  sort Both\n    provides Modifiable[T = Self]\n    entity counter\n  end\n";
    let the_op = "  operation Both() -> Both = Both.counter()\n";
    for (order, decls) in [
        ("the sort first", format!("{the_sort}{the_op}")),
        ("the operation first", format!("{the_op}{the_sort}")),
        ("CONTROL, the sort alone", the_sort.to_string()),
    ] {
        let src = format!(
            "namespace test.wi974m\n  import anthill.prelude.{{Int64, Unit, Modify, Modifiable}}\n\
             {decls}  operation write() -> Unit effects Modify[Both] = ()\nend\n"
        );
        let errs = load_errors_of(&src);
        assert!(
            errs.len() == 1
                && errs[0].contains("declares effect `Modify[T = Both]` whose target is a TYPE"),
            "{order}: expected the one refusal of a TYPE target; got {errs:#?}",
        );
    }
}

/// `{Sort, Operation}` in a `requires` clause WRITTEN WITH A BRACKET: the stored clause
/// keeps no bracket for a sort with no constructor, so every reader would take it as the
/// operation's call. It is refused where the bracket is still visible, in both orders. The
/// CONTROL is the spec alone, which loads.
#[test]
fn a_bracket_requirement_on_a_sort_named_operation_is_refused_in_both_orders() {
    let the_spec = "  sort Both\n    sort T = ?\n  end\n";
    let the_op = "  operation Both(x: Int64) -> Bool = x > 0\n";
    let program = |decls: &str| {
        format!(
            "namespace test.wi974r\n  import anthill.prelude.{{Int64, Bool}}\n{decls}  operation \
             f(x: Int64) -> Int64 requires Both[T = Int64] = x\nend\n"
        )
    };
    for order in BOTH_ORDERS {
        let errs = load_errors_of(&program(&ordered(order, the_spec, the_op)));
        assert!(
            errs.len() == 1 && errs[0].contains("names a sort that is also an OPERATION"),
            "the spec written {order}: expected the one refusal of the bracket; got {errs:#?}",
        );
    }
    assert_eq!(load_errors_of(&program(the_spec)), Vec::<String>::new(), "CONTROL, the spec alone");
}

/// `{Sort, Operation}` and an operation's OWN type parameter: `F[U]`'s `U.Elem` with no
/// `requires` on `U` is self-licensed (WI-383) beside a same-named sort as it is alone,
/// whichever is written first. The two share one scope, and the operation's bracket — not
/// the scope — says `U` is its own. The CONTROL is the operation alone, whose one refusal —
/// a body-less operation in a namespace has no definition — every order must match.
#[test]
fn an_operations_own_parameter_projects_beside_a_same_named_sort_in_both_orders() {
    let the_op = "  operation F[U](x: U) -> U.Elem\n";
    let the_sort = "  sort F\n    entity mk(n: Int64)\n  end\n";
    // The refusals without their `line:col: ` prefix, which the orders move.
    let verdict = |decls: &str| -> Vec<String> {
        load_errors_of(&format!(
            "namespace test.wi974j\n  import anthill.prelude.{{Int64}}\n{decls}end\n"
        ))
        .into_iter()
        .map(|e| e.split_once(": ").map_or(e.clone(), |(_, rest)| rest.to_owned()))
        .collect()
    };
    let control = verdict(the_op);
    assert!(
        control.len() == 1 && control[0].contains("has no definition"),
        "CONTROL, the operation alone: {control:#?}",
    );
    for (what, decls) in [
        ("the operation first", format!("{the_op}{the_sort}")),
        ("the sort first", format!("{the_sort}{the_op}")),
    ] {
        assert_eq!(verdict(&decls), control, "{what}");
    }
}
