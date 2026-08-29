//! WI-20260828-N2FHM — a field dot on an `Iterable.find` callback parameter type-checked
//! CLEAN and died at run time with `Internal("unhandled Expr variant in eval:
//! Discriminant(10)")` — `Expr::DotApply`, the un-desugared dot.
//!
//! WHY THE DOT NEVER RESOLVED. `Iterable.find(c: C, pred: (x: Element) -> Bool …)` types
//! its callback binder from `Element`, a param of the SPEC. The typer knew TWO ways to
//! ground a callback param before it hints a lambda — the WI-485 elimination of a path
//! PROJECTION over a sibling (`Stream.find`'s `pred: (x: s.T)`), and WI-821's pinning of a
//! callee TYPE PARAM from a sibling argument — and this is a THIRD: `Element` relates to
//! the receiver only through the carrier's PROVISION (`List provides Stream provides
//! Iterable[C = …, Element = T, E = {}]`). So the binder was hinted with the bare sort ref
//! `anthill.prelude.Iterable.Element`, `flag` is no member of that, and dot dispatch
//! produced `DotDispatchNoMatch` — which `MatchAfterScrutinee` then DROPPED, leaving the
//! un-rewritten `DotApply` in the stored body for eval to die on.
//!
//! THE FIX, in two halves, both in the hint path: `bind_spec_params_for_hint` runs the
//! same carrier-param classification + provision binder `check_apply` runs after the
//! arguments are typed, off the WI-793 `known` map instead of the typed results; and
//! `spec_carrier_param_candidates` joins `projected` / `tp_pinning` as a third STAGING
//! trigger, so a receiver no no-typing reader can answer for (a call, a literal) is typed
//! first. Half one alone fixes the var-ref receiver; both are needed for a computed one.
//!
//! PLUS A BACKSTOP, because the swallow is a defect of its own and outlives this ticket:
//! `surviving_dot_apply` refuses a STORED operation body that still holds an
//! `Expr::DotApply`. It closes the boundary the ticket names — an unresolved dot must not
//! reach the evaluator — for every producer, not only this one. The swallow itself is
//! WI-20260829-1SSXM; see `surviving_dot_apply` for what propagating the scrutinee's own
//! error costs and why it is a ticket rather than a line in this one.
//!
//! CONTROLS AND WHAT EACH SEPARATES — each passes with every back-out below:
//!   * `control_filter_elems_dot` — `List.filterElems`, which projects `xs.T` off its own
//!     receiver. Same list, same element sort, same field dot, same lambda position. It is
//!     what attributes the defect to the COMBINATOR rather than to lambdas or to dots.
//!   * `control_stream_find_dot` — `Stream.find`, the PROJECTION spelling of the same
//!     search, reached through an explicit `iterator`.
//!   * `control_dot_spelling_find` — `rs.find(λ)`; the `DotApply` frame pre-types its
//!     receiver (WI-443), so the dot spelling always had the type the named one lacked.
//!   * `control_destructuring_callback` — the workaround that shipped in
//!     `examples/guardians/lib/gate.anthill`: match the binder instead of dotting it,
//!     which needs no type to bind.
//!
//! BACKING THE CHANGE OUT — three axes, each measured on this tree, each naming exactly
//! the rows it turns red:
//!   * BOTH HINT HALVES (neutralize `bind_spec_params_for_hint`'s call in
//!     `apply_arg_hints` AND `spec_carrier` in `known_arg_types_and_staged`) ⟹
//!     `find_dot_on_a_var_ref_receiver`, `find_dot_on_a_computed_receiver` and
//!     `find_callback_dot_selects_by_the_field_it_reads` all fail to LOAD, with
//!     `<unresolved receiver>.flag … no such member (dot dispatch)`.
//!   * THE STAGING HALF ALONE (`spec_carrier` only) ⟹ the two COMPUTED-receiver rows fail
//!     and `find_dot_on_a_var_ref_receiver` PASSES — the binder half covers a receiver the
//!     WI-485 env reader can already answer for, and only staging reaches a call.
//!   * THE BACKSTOP ALONE (drop the `surviving_dot_apply` error push) ⟹ NOTHING FAILS
//!     ANY MORE, and that is the point rather than a hole. It read "only
//!     `an_unresolvable_dot_never_reaches_the_evaluator` fails, by LOADING CLEAN" until
//!     WI-20260829-1SSXM repaired the SWALLOW this ticket only fenced off:
//!     `MatchAfterScrutinee` now propagates the scrutinee's own `Err`, so that program's
//!     `DotDispatchNoMatch` — naming `nosuchfield` AND the receiver sort `Row`, the two
//!     things the case asserts — is reported before the stored tree is ever walked.
//!     MEASURED on this tree: with the push neutralized, `wi_tests` is 3773/3773. The
//!     backstop is now unreachable from every program in the corpus, which is what an
//!     invariant looks like once it holds; it stays because it is the boundary
//!     ("an unresolved dot must not reach the evaluator") and not the repair, and
//!     nothing else guards that boundary for a producer we have not found yet. Since
//!     that leaves it live but unexercised BY A PROGRAM, its walk is now driven directly
//!     by `typing::wi_1ssxm_surviving_dot_backstop_tests` over synthetic occurrences —
//!     which is where a regression in it would surface, not here.
//! The four controls pass under all three, by design.

const DECLS: &str = r#"
namespace dotfind
  import anthill.prelude.{List, Bool, Option, String, Int64, Iterable, Stream}
  import anthill.prelude.Iterable.{find}
  import anthill.prelude.List.{filterElems, length}

  sort Row
    entity row(name: String, flag: Bool)
  end

  operation rows() -> List[T = Row] =
    [row(name: "a", flag: false), row(name: "b", flag: true), row(name: "c", flag: true)]
end
"#;

/// The consumer file: `DECLS` plus `ops`, so every case shares one declaration set.
fn program(ops: &str) -> String {
    format!(
        "\nnamespace dotfind\n  import anthill.prelude.{{List, Bool, Option, String, Int64, Iterable, Stream}}\n  import anthill.prelude.Iterable.{{find}}\n  import anthill.prelude.List.{{filterElems, length}}\n  import dotfind.{{Row, rows}}\n  import dotfind.Row.{{row}}\n{ops}\nend\n"
    )
}

/// NO `answer(ops, op) -> Value` HELPER, and the omission is the point: a `Value` is only
/// readable against the KB that produced it (`scalar_int` / `scalar_bool` go through
/// `v.head(kb)`, which resolves a per-KB `TermId`). A helper that returns the value and
/// drops its interpreter invites the caller to read it against a SECOND KB built from
/// different sources — where the intern order differs, so the lookup lands on an unrelated
/// term and the assertion either reads `None` or, worse, a coincidentally-valid literal it
/// did not compute. `control_filter_elems_dot` was written that way and caught by
/// /code-review. Every case below keeps ONE live interpreter and reads `interp.kb()` off it.
fn as_bool(v: &anthill_core::eval::Value, interp_kb: &anthill_core::kb::KnowledgeBase) -> bool {
    crate::common::scalar_bool(interp_kb, v)
        .unwrap_or_else(|| panic!("expected a Bool value, got {v:?}"))
}

/// Load `DECLS` + `ops` and return the load errors (empty when it loads).
fn load_errors(ops: &str) -> Vec<String> {
    match crate::common::try_load_kb_with_files(&[DECLS, &program(ops)]) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

/// Run `op` and assert it answers `want` — the DRIVING assertion for a Bool case.
fn assert_bool(ops: &str, op: &str, want: bool) {
    let mut interp = crate::common::interp_for_files(&[DECLS, &program(ops)]);
    let v = interp
        .call(op, &[])
        .unwrap_or_else(|e| panic!("{op} must run; got {e:?}"));
    assert_eq!(
        as_bool(&v, interp.kb()),
        want,
        "{op} must answer {want}, got {v:?}"
    );
}

// ── DRIVING CASES ────────────────────────────────────────────────────────────

/// DRIVES THE FIX (binder half). The receiver is a VAR-REF, so the WI-485 env reader
/// supplies its type without staging — but nothing related `Element` to it until
/// `bind_spec_params_for_hint`. RED with that call neutralized: the load fails with
/// `type mismatch in anthill.prelude.Iterable.Element.flag … no such member (dot dispatch)`.
#[test]
fn find_dot_on_a_var_ref_receiver() {
    assert_bool(
        "  operation via_find_ref(rs: List[T = Row]) -> Bool =\n    \
           match find(rs, lambda r -> r.flag)\n      \
             case some(_) -> true\n      \
             case none() -> false\n\
         \n  operation drive_ref() -> Bool = via_find_ref(rows())",
        "dotfind.drive_ref",
        true,
    );
}

/// DRIVES THE FIX (both halves). The receiver is a CALL, which no no-typing reader can
/// answer for, so it must be STAGED before the hint is built. This is the guardians shape
/// (`find(layer_symbols(l), lambda ls -> …)`) with nothing borrowed from that example.
/// RED with `spec_carrier` dropped from the staging trigger, even with the binder in.
#[test]
fn find_dot_on_a_computed_receiver() {
    assert_bool(
        "  operation via_find_call() -> Bool =\n    \
           match find(rows(), lambda r -> r.flag)\n      \
             case some(_) -> true\n      \
             case none() -> false",
        "dotfind.via_find_call",
        true,
    );
}

/// DRIVES THE FIX, and it is the one case that shows the dot RESOLVED rather than merely
/// tolerated: the callback reads a field, and the answer is the field's value on the
/// matching row — `false` would be what a `find` that matched the FIRST row returns, and
/// the empty-list reading cannot produce a name at all.
#[test]
fn find_callback_dot_selects_by_the_field_it_reads() {
    let mut interp = crate::common::interp_for_files(&[
        DECLS,
        &program(
            "  operation first_flagged_name() -> String =\n    \
               match find(rows(), lambda r -> r.flag)\n      \
                 case some(f) -> f.name\n      \
                 case none() -> \"<none>\"",
        ),
    ]);
    let v = interp
        .call("dotfind.first_flagged_name", &[])
        .expect("first_flagged_name must run");
    assert_eq!(
        crate::common::scalar_str(interp.kb(), &v).as_deref(),
        Some("b"),
        "the callback's `r.flag` must select row b (the first with flag: true)",
    );
}

/// An unresolvable dot inside a match SCRUTINEE. Before `surviving_dot_apply` this
/// program loaded CLEAN and died at eval with `Internal("unhandled Expr variant in
/// eval")` — not a `Raised` payload, so no handler sees it and the caller cannot catch
/// it. Now it is a load error naming the member.
///
/// WHAT REPORTS IT HAS CHANGED HANDS, and the assertions below are deliberately blind to
/// which. This drove the BACKSTOP when it was written: `MatchAfterScrutinee` dropped the
/// scrutinee's `Err` and put the un-rewritten node back into the stored tree, so the only
/// thing left to catch was the surviving `DotApply`. WI-20260829-1SSXM repaired that
/// swallow, so the same refusal now arrives from the frame itself and the backstop is
/// never reached (measured: neutralizing its push leaves `wi_tests` 3773/3773). What the
/// case pins is the BOUNDARY, which outlives either mechanism — an unresolved dot must
/// not reach the evaluator, by whichever route says so.
#[test]
fn an_unresolvable_dot_never_reaches_the_evaluator() {
    let errs = load_errors(
        "  operation scrutinee_error(rs: List[T = Row]) -> Bool =\n    \
           match find(rs, lambda r -> r.nosuchfield)\n      \
             case some(_) -> true\n      \
             case none() -> false",
    );
    assert!(
        errs.iter().any(|e| e.contains("nosuchfield")),
        "an unresolvable dot must be a LOAD error, not a surviving DotApply; got {errs:?}",
    );
    // AND IT NAMES THE RECEIVER'S SORT. The backstop reads the stamp the `DotApply` frame
    // left on the receiver (WI-732); without that it reports `receiver_sort: None`, which
    // renders as "<unresolved receiver>" / "the receiver's type is unresolved" — false
    // here, since `r` types as `Row`, and it would send the author after an inference
    // problem instead of their typo. Found by /code-review.
    assert!(
        errs.iter().any(|e| e.contains("Row")),
        "the refusal must name the receiver's sort `Row`, not report it unresolved; got {errs:?}",
    );
}

// ── CONTROLS — every one passes with the change backed out ───────────────────

/// CONTROL — `List.filterElems` projects `xs.T` off its own receiver (WI-485), so its
/// callback binder was always grounded. Same list, same element sort, same field dot,
/// same lambda position: this is what attributes the defect to the COMBINATOR.
#[test]
fn control_filter_elems_dot() {
    let mut interp = crate::common::interp_for_files(&[
        DECLS,
        &program(
            "  operation via_filter() -> Int64 =\n    \
               length(filterElems(rows(), lambda r -> r.flag))",
        ),
    ]);
    let v = interp
        .call("dotfind.via_filter", &[])
        .expect("via_filter must run");
    assert_eq!(
        crate::common::scalar_int(interp.kb(), &v),
        Some(2),
        "two of three rows carry flag: true",
    );
}

/// CONTROL — the PROJECTION spelling of the same search. `Stream.find`'s
/// `pred: (x: s.T)` names a path projection over its own receiver, which WI-485 already
/// eliminates at hint time. Green either way.
#[test]
fn control_stream_find_dot() {
    assert_bool(
        "  operation via_stream_find(rs: List[T = Row]) -> Bool =\n    \
           match Stream.find(Iterable.iterator(rs), lambda r -> r.flag)\n      \
             case some(_) -> true\n      \
             case none() -> false\n\
         \n  operation drive_stream() -> Bool = via_stream_find(rows())",
        "dotfind.drive_stream",
        true,
    );
}

/// CONTROL — the DOT spelling of `find`. The `DotApply` frame pre-types its receiver
/// (WI-443) and only then synthesizes the call, so this spelling always had the receiver
/// type the named one lacked. Green either way; it is why the gap was reachable only
/// through the qualified/unqualified form.
#[test]
fn control_dot_spelling_find() {
    assert_bool(
        "  operation via_dot(rs: List[T = Row]) -> Bool =\n    \
           match rs.find(lambda r -> r.flag)\n      \
             case some(_) -> true\n      \
             case none() -> false\n\
         \n  operation drive_dot() -> Bool = via_dot(rows())",
        "dotfind.drive_dot",
        true,
    );
}

/// CONTROL — the workaround that shipped in `examples/guardians/lib/gate.anthill`:
/// DESTRUCTURE the callback binder instead of dotting it. A pattern needs no type to
/// bind, so `find` itself was never unusable — only the dot was. Green either way.
#[test]
fn control_destructuring_callback() {
    assert_bool(
        "  operation via_match(rs: List[T = Row]) -> Bool =\n    \
           match find(rs, lambda r -> match r case row(_, f) -> f)\n      \
             case some(_) -> true\n      \
             case none() -> false\n\
         \n  operation drive_match() -> Bool = via_match(rows())",
        "dotfind.drive_match",
        true,
    );
}
