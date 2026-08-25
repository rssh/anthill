//! WI-20260822-AKKWF — A SURFACE-FORM MARKER IS ONE BECAUSE THE CONVERTER MINTED IT,
//! NOT BECAUSE OF ITS NAME. WI-20260822-AK2AJ's defect, one coordinate over and much
//! louder.
//!
//! `Loader::visit_load` (`kb/load.rs`, the expression walker `convert_expr_term`
//! drives) recognises the converter's surface-form markers — `if_expr`, `match_expr`,
//! `match_branch`, `let_expr`, `lambda_expr`, `proof_stmt`, the five `pattern_*` forms
//! — and then indexes `pos_args` by POSITION, a layout only the desugar produces. It
//! dispatched on `local_name(functor)` ALONE. Every one of those names is an ordinary
//! identifier a user may write, and none is reserved, so the trap WI-948 named ("a
//! name, not a verdict") was open at eleven of its twelve arms at once — and here it does not
//! misreport, it ABORTS THE PROCESS. A panic is not a diagnostic: no other error in
//! the file is reported either.
//!
//! MEASURED before the gate, each as `operation f() -> Int64 = <expr>`: FOURTEEN
//! written calls crashed the loader — `if_expr(1)`, `match_expr()`, `match_branch(1)`,
//! `let_expr(1)`, `lambda_expr(1)`, `proof_stmt()`, `pattern_var()`,
//! `pattern_literal()`, `pattern_constructor()`, `pattern_constructor(1)`,
//! `dot_apply()`, `dot_apply(1, 2)`, `pattern_tuple()`, `pattern_tuple(1, 2)` — and
//! `pattern_wildcard()` did not crash but was HIJACKED: nullary, so nothing indexed out
//! of range and the call was silently read as a `Pattern` ("expected Int64, got
//! Pattern"), a wrong value rather than a crash. (The ticket's own table named ten of
//! these; `pattern_constructor`, `dot_apply` and `pattern_tuple` are three arms it did
//! not reach. A feature's population is the arm list, not the ticket's list.)
//!
//! THE REPAIR IS AK2AJ's, APPLIED TO THE FAMILY, with the pairing hoisted to ONE gate:
//! `visit_load` matches on `Option<&str>` — `Some(name)` only when
//! `SimpleTermStore::is_minted` says the converter built the node — so a new marker arm
//! cannot be added without provenance, and a written call falls to the ordinary
//! conversion that gives it its own accurate diagnostic. The nine builders that did not
//! mint now do, through `convert::alloc_marker_term`, which fuses the mint to the
//! allocation and carries the per-READER census that new producer set owes.
//!
//! # ONE NAME IS DELIBERATELY NOT GATED, AND THAT IS THE FINDING THIS FILE PINS
//!
//! `dot_apply` is minted (WI-618) but is ALSO a spelling the author may write: it is
//! the surface of a sort-scoped dot rule (kernel-language.md §"a `[simp]` **dot rule**
//! … `rule dr: dot_apply(?receiver, member, ?x) = … [simp]`"). Gating it on provenance
//! does not close a trap, it DELETES THE SPELLING — measured both ways, and
//! [`the_spelled_dot_form_is_not_provenance_gated`] is this file's guard for it. Both
//! of its readers take a SHAPE guard instead (arity ≥ 2 with an `Ident` at the name
//! slot), which is what keeps `pos_args[1]` in range without answering a second
//! question.
//!
//! # THE BACK-OUTS — one per edit, each RUN, counts as the runs printed
//!
//! Backed out by MUTATING each guard, never by deleting code around it.
//!
//! * **THE READER GATE** — in `visit_load`, `is_minted(parse_id).then(|| name.as_str())`
//!   → `Some(name.as_str())`, restoring the name-only dispatch with every mint left in
//!   place. **2 of 8 here**, each for its own reason and neither for "it stopped
//!   loading": [`a_written_marker_call_is_read_as_an_ordinary_call`] PANICS the loader
//!   on its first row ("index out of bounds: the len is 1 but the index is 1", in
//!   `kb/load.rs`), and [`a_written_pattern_wildcard_is_no_longer_read_as_a_pattern`]
//!   gets the hijack back ("expected Int64, got Pattern"). The other six pass — the
//!   mints are untouched, so all five real forms still elaborate and the control and
//!   the dot-form row never depended on the gate.
//!
//!   ACROSS THE WHOLE `wi_tests` BINARY IT IS **7 of 3416**, and the other five are
//!   named rather than absorbed: `wi605_bare_arrow_lambda_test` (four) and
//!   `wi618_bare_arrow_logic_test` (one). That is not collateral — the shared binding
//!   SUBSUMES the arrow arm's own `is_minted` pairing, which WI-618 added and those
//!   five pin, so backing the gate out backs that pairing out too. The arrow family
//!   already had standing coverage; the eleven other arms had none, which is why the
//!   two rows above exist.
//! * **THE FACTORY MINT** — drop `self.terms.mark_minted(tid)` in
//!   `alloc_marker_term_with_named`, which every marker build now routes through, so it
//!   backs out all of them at once. **THIS ONE IS NOT ATTRIBUTABLE,
//!   AND THAT IS ITS FINDING**: the STDLIB stops loading (its own `match` arms report
//!   "expected resolved name, got unresolved" and a `pattern_constructor` unknown
//!   functor), so every fixture that imports the prelude falls with it — 6 of 8 here
//!   and **2398 of 3416 in the whole `wi_tests` binary**. That says the marker mints
//!   are load-bearing for the library itself; it says nothing about which row covers
//!   which producer, so the per-producer question is answered by the three below
//!   instead of credited to this one.
//! * **ONE NAMED-ARG PRODUCER AT A TIME** — in `alloc_marker_term_with_named`, wrap the
//!   mark in `if !(functor_name == "<name>" && !named_args.is_empty())`. Each is
//!   **1 of 8**, and each the right one: `proof_stmt` →
//!   [`an_in_body_proof_still_elaborates`], `pattern_var` (the typed binder) →
//!   [`a_let_and_a_typed_binder_still_evaluate`], `pattern_constructor` (named
//!   sub-patterns) → [`a_named_sub_pattern_still_binds_its_field`].
//!
//!   Stated separately because those five named-arg shapes are precisely what the
//!   whole-factory mutation above cannot attribute: without these three runs they would
//!   ride on a back-out whose only observable effect is that the stdlib died.
//! * **THE `dot_apply` SHAPE GUARD** — replace it with the provenance gate the other
//!   arms take (`Some("dot_apply")`). **1 of 3416** in the whole `wi_tests` binary:
//!   [`the_spelled_dot_form_is_not_provenance_gated`], and NOTHING ELSE. That number is
//!   the reason this file carries that row — the mistake it guards against is invisible
//!   to every other test in the crate.
//!
//! Apart from the stdlib collapse in the second, no row fails under two back-outs,
//! which is what says the edits answer separate questions.
//!
//! WI-20260822-AK2AJ's `wi_ak2aj_written_typed_var_test` is this file's sibling — the
//! same repair on `typed_var`, whose reader lives in `convert_term` rather than here.

use anthill_core::eval::value::Value;

fn errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

/// `operation f() -> Int64 = <expr>` in a namespace importing `Int64`. The op-body
/// position is what routes through `convert_expr_term`, the walker that owns the
/// marker arms.
fn op_body(expr: &str) -> String {
    // WI-20260825-5W3RJ — the reflect `Expr` constructors are IMPORTED here, and the
    // import is load-bearing for this file's SECOND class of row. A marker name used to
    // resolve bare from any namespace through the desugaring vocab's reserved-name rung;
    // that rung is gone (the converter names its target itself), so without this line
    // `match_expr(1)` would report "unknown functor" like the first class and the file
    // would stop distinguishing the two readings it exists to distinguish.
    //
    // The first class is deliberately NOT imported: `match_branch`, `proof_stmt` and the
    // `pattern_*` forms are parse-level markers with no reflect declaration to import,
    // so they still denote nothing — which is the reading those rows assert.
    format!(
        "namespace akkwf.written\n  import anthill.prelude.{{Int64}}\n  \
         import anthill.reflect.Expr.{{match_expr, if_expr, let_expr, lambda_expr, dot_apply}}\n  \
         operation f() -> Int64 = {expr}\nend\n"
    )
}

fn expect_int(v: Value) -> i64 {
    v.as_int()
        .unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

/// THE TICKET'S TABLE. Every written call named like a marker LOADS — reaching this
/// assertion at all is half the claim, since each of these aborted the process before
/// — and reports an ordinary diagnostic about the call the author actually wrote.
///
/// Each row names a DISTINGUISHING token, not a family: the diagnostic must say the
/// call was read as an ordinary APPLICATION. The rows split by what the name denotes,
/// and both halves say "the marker arm did not fire":
///
/// * a name that denotes NOTHING gets `<name>.apply … unknown functor` — byte for byte
///   what an undefined functor gets, which is the claim
///   ([`control_an_undefined_call_reports_the_same_way`] holds the other end of it);
/// * a name that denotes an `anthill.reflect.Expr` entity gets an `(entity-field)`
///   mismatch on the author's own argument — read as a CONSTRUCTOR call, which is what
///   that name means in scope.
#[test]
fn a_written_marker_call_is_read_as_an_ordinary_call() {
    // (expr, the token that says "read as an ordinary application")
    const ROWS: &[(&str, &str)] = &[
        // — the name denotes nothing: the undefined-functor diagnostic —
        ("match_branch(1)", "match_branch.apply"),
        ("proof_stmt()", "proof_stmt.apply"),
        ("pattern_var()", "pattern_var.apply"),
        ("pattern_wildcard()", "pattern_wildcard.apply"),
        ("pattern_literal()", "pattern_literal.apply"),
        ("pattern_constructor()", "pattern_constructor.apply"),
        ("pattern_constructor(1)", "pattern_constructor.apply"),
        ("pattern_tuple()", "pattern_tuple.apply"),
        ("pattern_tuple(1, 2)", "pattern_tuple.apply"),
        // — the name denotes a reflect `Expr` entity: an ordinary constructor call —
        ("match_expr(1)", "match_expr.scrutinee (entity-field)"),
        ("if_expr(1)", "if_expr.cond (entity-field)"),
        ("let_expr(1)", "let_expr.pattern (entity-field)"),
        ("lambda_expr(1)", "lambda_expr.param (entity-field)"),
        ("dot_apply(1, 2)", "dot_apply.receiver (entity-field)"),
    ];
    for (expr, token) in ROWS {
        let got = errs(&op_body(expr));
        assert!(
            got.iter().any(|e| e.contains(token)),
            "`{expr}` must report an ordinary diagnostic containing `{token}`; got {got:#?}"
        );
        assert!(
            got.iter()
                .all(|e| !e.contains("unknown functor")
                    || e.contains(expr.split('(').next().unwrap())),
            "and every unknown-functor diagnostic must name the author's own call; got {got:#?}"
        );
    }
}

/// THE `pattern_wildcard()` ROW, SEPARATELY, because its failure mode was the odd one
/// out: nullary, so it never indexed out of range and the loader HIJACKED it instead —
/// silently read as a `Pattern`, reporting "expected Int64, got Pattern" about a value
/// the source does not contain. The claim is a NEGATIVE, so it is asserted as one: no
/// diagnostic may say the expression is a `Pattern`.
///
/// `!contains` is the whole point. The positive half above ("unknown functor") would
/// be equally true of a loader that reported BOTH.
#[test]
fn a_written_pattern_wildcard_is_no_longer_read_as_a_pattern() {
    let got = errs(&op_body("pattern_wildcard()"));
    assert!(
        got.iter().all(|e| !e.contains("got Pattern")),
        "the hijack is gone: nothing may read `pattern_wildcard()` as a `Pattern`; got {got:#?}"
    );
    assert!(
        got.iter().any(|e| e.contains("pattern_wildcard.apply")),
        "and the call is reported as the ordinary application it is; got {got:#?}"
    );
}

/// THE CONTROL FOR THE TABLE, IN ITS OWN FIXTURE AND ITS OWN LOAD — an ordinary
/// undefined functor. It PASSES UNDER EVERY BACK-OUT BY DESIGN, and that is what
/// it is for: without it, "`pattern_var()` says unknown functor" would be equally true
/// of a loader that had started saying that about everything.
///
/// Its own fixture because a load error fails the whole file: sharing a namespace with
/// an arm would make the control's verdict depend on the arm's.
#[test]
fn control_an_undefined_call_reports_the_same_way() {
    let got = errs(&op_body("no_such_thing(1)"));
    assert!(
        got.iter()
            .any(|e| e.contains("no_such_thing.apply") && e.contains("unknown functor")),
        "CONTROL: an ordinary undefined call reports exactly what the table's first \
         half asserts; got {got:#?}"
    );
}

/// THE OTHER DIRECTION, and the failure mode this repair can introduce: pairing an arm
/// whose builder forgot to mint would silently switch the REAL form off. So the real
/// forms are DRIVEN, not merely loaded — `interp.call` returns the value, which "it
/// loads clean" cannot distinguish from a body that elaborated to nothing.
///
/// One operation exercises seven producers at once: `if_expr`, `match_expr`,
/// `match_branch`, and four of the pattern shapes — `pattern_literal` (`case 1`),
/// `pattern_constructor` (`case box(v)`), `pattern_tuple` (`case (a, b)`) and
/// `pattern_wildcard` (`case _`) — with `pattern_var` bound inside three of them.
#[test]
fn the_real_forms_still_evaluate() {
    const SRC: &str = r#"
namespace akkwf.real
  import anthill.prelude.{Int64, Bool}
  sort Box
    entity box(value: Int64)
  end
  operation classify(n: Int64) -> Int64 =
    match n
      case 1 -> 100
      case _ -> 200
  operation unbox(b: Box) -> Int64 =
    match b
      case box(v) -> v
  operation first(p: (Int64, Int64)) -> Int64 =
    match p
      case (a, _) -> a
  operation pick(b: Bool) -> Int64 =
    if b then unbox(box(value: 7)) + first((5, 4)) else classify(2)
  operation main() -> Int64 = pick(true) + classify(1)
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    assert_eq!(
        expect_int(interp.call("akkwf.real.main", &[]).expect("call main")),
        112,
        "`if`/`match`/literal-, constructor-, tuple- and wildcard-patterns all still \
         elaborate AND evaluate: pick(true) = unbox(7) + first((5,4)) = 12, plus \
         classify(1) = 100"
    );
}

/// `let_expr` AND `lambda_expr` AND THE TYPED BINDER, driven — the `let` and the bare
/// lambda binder are hand-marked and pre-existing (WI-618); `lambda (x: Int64) -> …`
/// is the `typed_binder` arm's `pattern_var`, a hand-marked site this ticket added and
/// the one the `alloc_marker_term` back-out cannot reach.
#[test]
fn a_let_and_a_typed_binder_still_evaluate() {
    const SRC: &str = r#"
namespace akkwf.letlam
  import anthill.prelude.{Int64}
  operation main() -> Int64 =
    let f = lambda (x: Int64) -> x + 1
    let k = 6
    f(k)
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    assert_eq!(
        expect_int(interp.call("akkwf.letlam.main", &[]).expect("call main")),
        7,
        "`let` and a TYPE-ANNOTATED lambda binder both still elaborate and evaluate"
    );
}

/// `pattern_constructor` WITH NAMED SUB-PATTERNS — the second hand-marked site this
/// ticket added, and a shape the positional back-out does not reach. WI-445 is the
/// reason it must be driven rather than loaded: named sub-patterns used to be dropped
/// silently at load, so a `case box(value: v) -> v` that merely LOADS proves nothing
/// about whether `v` was bound.
#[test]
fn a_named_sub_pattern_still_binds_its_field() {
    const SRC: &str = r#"
namespace akkwf.named
  import anthill.prelude.{Int64}
  sort Box
    entity box(value: Int64)
  end
  operation unbox(b: Box) -> Int64 =
    match b
      case box(value: v) -> v
  operation main() -> Int64 = unbox(box(value: 41))
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    assert_eq!(
        expect_int(interp.call("akkwf.named.main", &[]).expect("call main")),
        41,
        "the named sub-pattern still binds `v` — the value, not a fresh var"
    );
}

/// `proof_stmt`, THE THIRD HAND-MARKED SITE. An in-body proof has no value of its own
/// (its type is the continuation's), so the driving assertion is the OCCURRENCE: the
/// body must be an `Expr::Proof` naming the rule the author cited. Without the mint the
/// marker arm never fires and the body is an unknown-functor application instead — so
/// this row reads the shape rather than a number, and says so.
#[test]
fn an_in_body_proof_still_elaborates() {
    use anthill_core::kb::node_occurrence::Expr;
    const SRC: &str = r#"
namespace akkwf.proof
  import anthill.prelude.{Int64}
  sort Box
    entity box(value: Int64)
    rule trivial(?x) :- true
    operation f(b: Box) -> Int64 =
      proof trivial by derivation end
      3
  end
end
"#;
    let kb = crate::common::load_kb_with(SRC);
    let f = kb
        .try_resolve_symbol("akkwf.proof.Box.f")
        .expect("f symbol");
    let body = kb.op_body_node(f).expect("op body node for f");
    match body.as_expr() {
        Some(Expr::Proof {
            target, strategy, ..
        }) => {
            assert_eq!(
                kb.local_name_of(*target),
                "trivial",
                "the cited rule survives"
            );
            assert_eq!(
                strategy.map(|s| kb.local_name_of(s)),
                Some("derivation"),
                "and so does the strategy"
            );
        }
        other => panic!("expected Expr::Proof — the marker arm must still fire; got {other:?}"),
    }
}

/// THE ONE NAME THAT IS NOT PROVENANCE-GATED. `dot_apply(?receiver, member, ?x)` is a
/// spelling the spec gives the author, and it works in an operation BODY as well as in
/// the rule head — so the fix must NOT gate this arm on the mint.
///
/// The fixture is `wi279_dot_dispatch_test::dot_rule_override_enables_dispatch`'s, with
/// the call site written APPLICATIVELY: `special` is not an operation on `Box`, so the
/// body type-checks only if the written `dot_apply` reached the dot rule. MEASURED with
/// this arm gated on `is_minted` instead: refused with "special.name: expected resolved
/// name, got unresolved", while the `?b.special(7)` surface in a sibling fixture kept
/// loading — i.e. the gate would have deleted the spelling and left no test red but
/// this one.
#[test]
fn the_spelled_dot_form_is_not_provenance_gated() {
    const SRC: &str = r#"
namespace akkwf.dotrule
  import anthill.prelude.{Int64}
  sort Box
    entity box(value: Int64)
    operation regular(b: Box, x: Int64) -> Int64 = x
    rule dr: dot_apply(?e, special, ?x) <=> regular(?e, ?x) [simp]
    operation use_spelled(b: Box) -> Int64 = dot_apply(?b, special, 7)
    operation main() -> Int64 = use_spelled(box(value: 4))
  end
end
"#;
    // DRIVEN, not just loaded: `regular` returns its SECOND argument, so 7 is the value
    // only the rewritten call can produce. "It loads clean" would be equally true of a
    // body that type-checked for some other reason, and this row is the only guard in
    // the crate against the mistake it names — so it must not be the weak kind.
    let mut interp = crate::common::interp_for(SRC);
    assert_eq!(
        expect_int(
            interp
                .call("akkwf.dotrule.Box.main", &[])
                .expect("call main")
        ),
        7,
        "a WRITTEN `dot_apply(?b, special, 7)` must still reach the dot rule and REWRITE \
         to `regular(?b, 7)` — no `special` operation exists, so nothing else answers 7"
    );
}
