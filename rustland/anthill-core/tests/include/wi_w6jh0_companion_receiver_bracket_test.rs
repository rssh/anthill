//! WI-20260829-W6JH0 — A COMPANION RECEIVER'S TYPE-ARG BRACKET IS THE CALL'S RESULT TYPE.
//!
//! Proposal 035 form (3) — `Map[K = String, V = Int64].empty()` — parsed and then meant
//! NOTHING. `collect_field_access_segments` flattens the callee to the segments
//! `Map.empty` because the runtime call path wants the sort's NAME, and the bindings were
//! erased there, so nothing downstream ever saw `K`/`V`. The bracket did not constrain the
//! call, and it did not even reject a parameter name the sort does not have.
//!
//! WHAT 035 SAYS IT MEANS, and why (a) rather than (b): "Form (3) is the Scala-companion
//! analog: `Map[K = String, V = Int64]` is an instantiation term that names the sort *with*
//! type bindings, and **method dispatch on it produces values typed at those bindings**",
//! and it is listed beside form (1)'s `let m: Map[…] = Map.empty()` annotation and form
//! (2)'s inference as three spellings of one thing — with form (3) named as the REQUIRED
//! disambiguator when nothing else constrains the call. Refusing the bracket would have
//! deleted that third spelling.
//!
//! THE TICKET'S OWN PROPOSED MECHANISM WOULD NOT HAVE WORKED, and that is the finding
//! worth keeping. It asked to "unify the receiver's bindings against the sort's params for
//! the call". That is ALREADY what the callee bracket does — `call_bracket_scopes` includes
//! the parent sort's params, so `Map.empty[K = Bool, V = Bool]()` reaches
//! `seed_op_type_args` and binds them — and it changes nothing, because `empty() -> Map`
//! returns the sort BARE and WI-1082 deliberately leaves a constructor's self-sort return
//! untied ("NO SELF PARAMETER, NO TIE"). MEASURED: that spelling still accepts a `String`
//! key, before this change and after it — [`the_callee_bracket_still_does_not_reach_the_result`]
//! pins it. The binding has nowhere to land, so the receiver has to name the RESULT.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT. THREE AXES, THREE BACK-OUTS — measured
//! separately, because a single "turn it all off" run credits one mechanism for another's
//! rows. Each is a MUTATION (the reader still runs, its answer is discarded), never a
//! deletion, so what is measured is the capability and not whether the tree still builds.
//!
//! **(A) the whole feature off** — the typer arm never fires and `build_recv_type` answers
//! `None`: **8 of 14 red, 6 green.** Red: the contradictory bracket in an operation body
//! and in a rule body, the undeclared parameter name (both callee kinds), the two-bracket
//! spelling, `form_one_and_form_three_agree`, the named-argument agreement, and the
//! contradicting partial bracket. Green by design: the four controls below, plus the two
//! rows that measure a LATER axis (B and C) rather than this one.
//!
//! **(B) the unread-bracket sweep off** — `check_unconsumed_recv_types` not called:
//! **exactly 1 red**, [`an_unread_receiver_bracket_is_refused_rather_than_dropped`], and
//! nothing else moves. That isolation is the point: the sweep is a separate mechanism from
//! the typing, and it is what makes "every written bracket is read or reported" hold for
//! this channel the way WI-839 made it hold for `type_args`.
//!
//! **(C) the merge off — the FIRST CUT of this change** — the receiver's type returned
//! verbatim as the result and the `unify_types` verdict discarded: **3 red**.
//! [`a_true_partial_receiver_bracket_keeps_the_inferred_slots`] and
//! [`a_contradicting_partial_receiver_bracket_is_refused`] are its own controls, and
//! [`the_receiver_bracket_reads_the_same_with_named_arguments`] reddens here too — on its
//! COUNT rather than its agreement (both spellings answer 2 under (C), and agreeing on a
//! wrong answer is still agreeing). It is the finding-1 control under (A), where the two
//! spellings genuinely disagree, and both facts are why it asserts the two lists are equal
//! AND pins the length.
//!
//! THE CONTROLS, green under all three: [`a_correct_receiver_bracket_still_loads`],
//! [`the_bare_companion_call_is_unchanged`] (form (2)),
//! [`a_receiver_bracket_on_a_non_constructor_callee_is_left_alone`] (the gate), and
//! [`the_callee_bracket_still_does_not_reach_the_result`] (the stated boundary).
//!
//! `map_builtins_test::form_3_instantiation_receiver_parses_and_runs` is the other control
//! and passes either way: it EVALUATES a form-(3) call, so it holds the change to the
//! promise that a correctly-written form (3) still runs.
//!
//! WHAT IS DELIBERATELY NOT FIXED: the CALLEE bracket
//! (`Map.empty[K = Bool, V = Bool]()`) still does not reach the result type. It is the
//! same missing tie, reached from the other spelling, and closing it means reopening
//! WI-1082's decision — a change to every companion call that returns its own sort, rather
//! than to the programs that write a receiver bracket. That is its own ticket; this one is
//! gated on a written receiver bracket, which was inert, so nothing else can move.

use crate::common::try_load_kb_with;

fn load_errors(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(es) => es.to_vec(),
    }
}

fn prog(body: &str) -> String {
    format!(
        r#"
namespace test.w6jh0
  import anthill.prelude.{{Map, Int64, String, Bool}}
  import anthill.prelude.Map.{{put, get, size}}
  operation build() -> Int64 = {body}
end
"#
    )
}

/// THE TICKET'S HEADLINE ROW. `K = Bool, V = Bool` is written and then a `String` key and
/// an `Int64` value are put. The two errors are byte-for-byte the ones form (1) gives for
/// the same claim — see [`form_one_and_form_three_agree`].
#[test]
fn a_contradictory_receiver_bracket_is_a_located_error() {
    let errs = load_errors(&prog(
        r#"size(put(Map[K = Bool, V = Bool].empty(), "a", 1))"#,
    ));
    assert_eq!(errs.len(), 2, "{errs:#?}");
    assert!(errs[0].contains("put.key") && errs[0].contains("expected Bool, got String"));
    assert!(errs[1].contains("put.value") && errs[1].contains("expected Bool, got Int64"));
}

/// THE SAME CLAIM IN BOTH SPELLINGS MUST READ THE SAME. This is the whole of the design:
/// form (3) is form (1) written at the receiver, so it is not enough that it errors — it
/// has to error IDENTICALLY. A divergence here means the two forms have drifted into two
/// meanings, which is what 035 lists them together to prevent.
#[test]
fn form_one_and_form_three_agree() {
    let form3 = load_errors(&prog(
        r#"size(put(Map[K = Bool, V = Bool].empty(), "a", 1))"#,
    ));
    let form1 = load_errors(&prog(
        "let m: Map[K = Bool, V = Bool] = Map.empty()\n      size(put(m, \"a\", 1))",
    ));
    let strip = |v: Vec<String>| -> Vec<String> {
        v.into_iter()
            .map(|e| e.split_once(": ").map(|(_, m)| m.to_string()).unwrap_or(e))
            .collect()
    };
    assert_eq!(strip(form3), strip(form1), "form (3) must read as form (1)");
}

/// The bracket is now CHECKED, which it was not at all: `Bogus` is not one of `Map`'s
/// parameters. The message is the shared one every written type gets
/// (`type_expr_to_child_inner`'s WI-709 check), reached by lowering the receiver rather
/// than by a second rule of this ticket's own.
#[test]
fn an_undeclared_receiver_parameter_name_is_refused() {
    let errs = load_errors(&prog(r#"size(put(Map[Bogus = Int64].empty(), "a", 1))"#));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(
        errs[0].contains("has no type parameter named 'Bogus'"),
        "{errs:#?}"
    );
}

/// THE TICKET'S EXPLICIT QUESTION — "what happens when the receiver's bindings and the
/// callee's bracket bind the SAME name", which WI-20260829-BAD3V's spelling admits.
///
/// They do not compete, because they answer different questions: the callee bracket binds
/// the callee's (and its parent sort's) type params in the CALL's substitution, which is
/// what it has always done; the receiver names the RESULT. So where they disagree, the
/// receiver is the one that reaches the value — here `K = Bool` wins over the callee's
/// `K = String` and the `String` key is refused. Deterministic, and not a tie to break.
/// Making a disagreement itself LOUD would require the callee bracket to reach the result,
/// which is the half this ticket leaves alone.
#[test]
fn the_two_bracket_spelling_honours_the_receiver() {
    // Agreeing brackets: nothing to report.
    assert_eq!(
        load_errors(&prog(
            "size(put(Map[K = Bool, V = Bool].empty[K = Bool, V = Bool](), true, true))"
        )),
        Vec::<String>::new()
    );
    // Disagreeing: the RECEIVER decides, so the arguments are checked against `Bool`.
    let errs = load_errors(&prog(
        r#"size(put(Map[K = Bool, V = Bool].empty[K = String, V = Int64](), "a", 1))"#,
    ));
    assert_eq!(errs.len(), 2, "{errs:#?}");
    assert!(errs[0].contains("expected Bool, got String"), "{errs:#?}");
}

/// THE SECOND PRODUCER. A rule body is lowered by a DIFFERENT walk than an operation body
/// (`build_body_atom_occurrence`, not the `ApplyOrConstructor` frame), and it built an
/// `Expr::Apply` of its own — so the receiver's claim vanished there while being honoured
/// one lowering over. Both read the channel now.
#[test]
fn a_contradictory_receiver_bracket_in_a_rule_body() {
    let src = r#"
namespace test.w6jh0rb
  import anthill.prelude.{Map, Int64, String, Bool}
  import anthill.prelude.Map.{put, get, size}
  import anthill.prelude.List.{nil}
  rule r(?n) :- ?n = size(put(Map[K = Bool, V = Bool].empty(), "a", 1))
end
"#;
    let errs = load_errors(src);
    assert_eq!(errs.len(), 2, "{errs:#?}");
    assert!(errs[0].contains("expected Bool, got String"), "{errs:#?}");
}

/// CONTROL — a form (3) that says something TRUE still loads. Green either way, and it is
/// what keeps the change from being "reject the bracket", which is the answer proposal 035
/// forecloses.
#[test]
fn a_correct_receiver_bracket_still_loads() {
    assert_eq!(
        load_errors(&prog(
            r#"size(put(Map[K = String, V = Int64].empty(), "a", 1))"#
        )),
        Vec::<String>::new()
    );
    // And one whose bindings are true of DIFFERENT argument types.
    assert_eq!(
        load_errors(&prog(
            "size(put(Map[K = Bool, V = Bool].empty(), true, true))"
        )),
        Vec::<String>::new()
    );
}

/// CONTROL — form (2), no bracket at all, still infers from the immediate use. Green
/// either way; it is the row that says the result-typing is GATED on a written receiver
/// and does not fire on the ordinary companion call.
#[test]
fn the_bare_companion_call_is_unchanged() {
    assert_eq!(
        load_errors(&prog(r#"size(put(Map.empty(), "a", 1))"#)),
        Vec::<String>::new()
    );
}

/// CONTROL, AND THE GATE. `size` returns `Int64`, not a `Map`, so the receiver's bindings
/// say nothing this arm can honour and the result is left alone — reading `Map[…]` as the
/// type of an `Int64` would be inventing a claim. Green either way.
///
/// SPLIT FROM [`an_undeclared_parameter_is_refused_on_a_non_constructor_callee_too`] so
/// each row's back-out status is its own: this one passes with the change backed out and
/// that one does not, and a single test asserting both would have reported only the
/// stronger half.
#[test]
fn a_receiver_bracket_on_a_non_constructor_callee_is_left_alone() {
    assert_eq!(
        load_errors(&prog(
            r#"Map[K = Bool, V = Bool].size(put(Map.empty(), "a", 1))"#
        )),
        Vec::<String>::new()
    );
}

/// The two halves are INDEPENDENT: only the result-typing is gated on the callee's return,
/// while the name check follows from lowering the receiver at all. So a bracket on a
/// non-constructor callee is still checked, and this row is RED on back-out where its
/// sibling above is green.
#[test]
fn an_undeclared_parameter_is_refused_on_a_non_constructor_callee_too() {
    let errs = load_errors(&prog(
        r#"Map[Bogus = Bool].size(put(Map.empty(), "a", 1))"#,
    ));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains("has no type parameter named 'Bogus'"));
}

/// CONTROL, AND THE STATED BOUNDARY. The CALLEE bracket binds the sort's params in the
/// call's substitution and still does not reach the result, so this contradiction loads
/// clean — before this change and after it. It is the same missing tie as the ticket's
/// row, reached from the other spelling; closing it means reopening WI-1082's "NO SELF
/// PARAMETER, NO TIE" for every companion call that returns its own sort, which is a
/// separate decision. Pinned here so the next reader finds the boundary measured rather
/// than assumed.
#[test]
fn the_callee_bracket_still_does_not_reach_the_result() {
    assert_eq!(
        load_errors(&prog(
            r#"size(put(Map.empty[K = Bool, V = Bool](), "a", 1))"#
        )),
        Vec::<String>::new()
    );
}

// ── /code-review (high), four findings, all measured and all fixed ───────────────

/// FINDING 1 — ONE CLAIM MUST NOT GET TWO VERDICTS FROM ARGUMENT SPELLING.
/// `reorder_named_args_in_apply` rewrites a NAMED-argument call into positional form and
/// rebinds the occurrence, and it ran BEFORE the receiver type is read while rebuilding the
/// `Expr::Apply` with the field defaulted — so a form-(3) bracket was inert on any call
/// written with named arguments. It used `..` in its pattern, so the compiler's census
/// could not flag it.
///
/// The two rows must AGREE; asserting only that the named one errors would pass on a
/// future change that broke both.
#[test]
fn the_receiver_bracket_reads_the_same_with_named_arguments() {
    let positional = load_errors(&prog(
        r#"size(put(Map[K = Bool, V = Bool].put(Map.empty(), "a", 1), "b", 2))"#,
    ));
    let named = load_errors(&prog(
        r#"size(put(Map[K = Bool, V = Bool].put(m: Map.empty(), key: "a", value: 1), "b", 2))"#,
    ));
    assert_eq!(positional.len(), 1, "{positional:#?}");
    assert_eq!(named, positional, "spelling the args by name must not change the verdict");

    // CONTROL — with no receiver bracket the two spellings already agreed, so the
    // divergence above was the dropped `recv_type` and not the named path itself.
    let ctl_pos = load_errors(&prog(r#"size(put(Map.put(Map.empty(), "a", 1), "b", true))"#));
    let ctl_named = load_errors(&prog(
        r#"size(put(Map.put(m: Map.empty(), key: "a", value: 1), "b", true))"#,
    ));
    assert_eq!(ctl_pos.len(), 1, "{ctl_pos:#?}");
    assert_eq!(ctl_named, ctl_pos);
}

/// FINDING 2 — A TRUE CLAIM MUST NEVER REMOVE A CHECK. The first cut took the receiver's
/// type VERBATIM as the result, which discards every slot it does not write. For a callee
/// whose declared return is parameterized (`put(m, key, value) -> Map[K = K, V = V]`, the
/// WI-1082 self-tie) those slots hold what the ARGUMENTS just determined, so writing a
/// PARTIAL bracket that is perfectly true deleted the inferred `V` and silenced a real
/// error one call out. The receiver is unified INTO the declared return now.
#[test]
fn a_true_partial_receiver_bracket_keeps_the_inferred_slots() {
    // The fault the partial bracket must not hide: `true` where `V = Int64`.
    let bare = load_errors(&prog(r#"size(put(Map.put(Map.empty(), "a", 1), "b", true))"#));
    assert_eq!(bare.len(), 1, "{bare:#?}");
    assert!(bare[0].contains("put.value"), "{bare:#?}");

    // Writing `K = String` — TRUE, and silent about `V` — must not change that verdict.
    let partial = load_errors(&prog(
        r#"size(put(Map[K = String].put(Map.empty(), "a", 1), "b", true))"#,
    ));
    assert_eq!(partial, bare, "a true partial bracket must not remove a check");
}

/// FINDING 2, OTHER POLARITY — a receiver that CONTRADICTS what the call determined is a
/// fault the author wrote, and discarding the failed unify made it load clean. Reported at
/// the receiver, because that is where the wrong claim is.
#[test]
fn a_contradicting_partial_receiver_bracket_is_refused() {
    let errs = load_errors(&prog(
        r#"size(put(Map[V = Bool].put(Map.empty(), "a", 1), "b", true))"#,
    ));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains("op-return"), "{errs:#?}");
    assert!(errs[0].contains("expected Map[V = Bool]"), "{errs:#?}");
}

/// FINDINGS 3 AND 4 — ONE MECHANISM. The channel had no "read or reported" sweep, so every
/// position that does not read it dropped the bracket in silence: an ENTITY-CONSTRUCTOR
/// callee (which builds an `Expr::Constructor`, with nowhere to put it), a fact head, and a
/// `[simp]` rule head. The `type_args` twin is a loud refusal in all three. The gate on the
/// entity arm is therefore a REAL gate, not the dead one its first comment claimed.
///
/// Every form-(3) call in the corpus is on an operation (`Map[…].empty()`), so nothing
/// that loaded before is newly refused — [`a_correct_receiver_bracket_still_loads`] and
/// `map_builtins_test`'s evaluating row are the controls for that.
#[test]
fn an_unread_receiver_bracket_is_refused_rather_than_dropped() {
    // Entity constructor callee.
    for body in [
        r#"size(put(Map.empty(), "a", Option[Bogus = Int64].some(1)))"#,
        r#"size(put(Map.empty(), "a", List[Bogus = Int64].cons(1, nil())))"#,
    ] {
        let errs = load_errors(&format!(
            r#"
namespace test.w6jh0u
  import anthill.prelude.{{Map, Option, List, Int64, String, Bool}}
  import anthill.prelude.Map.{{put, size}}
  -- WI-909: one `body` writes a BARE `nil()` beside the bracketed
  -- `List[Bogus = Int64].cons(...)` it is really testing. Without this import that bare
  -- name is a second error and the row's `errs.len() == 1` reads 2 -- the refusal it
  -- asserts is still there, joined by an unrelated one.
  import anthill.prelude.List.{{nil}}
  operation build() -> Int64 = {body}
end
"#
        ));
        assert_eq!(errs.len(), 1, "{errs:#?}");
        assert!(errs[0].contains("not read here"), "{errs:#?}");
    }

    // Fact head — a position with no call to type at all.
    let errs = load_errors(
        r#"
namespace test.w6jh0f
  import anthill.prelude.{Map, Int64, String, Bool}
  import anthill.prelude.Map.{put, size}
  sort P
    import anthill.prelude.Int64
    entity P(n: Int64)
  end
  fact P(n: size(put(Map[Bogus = Bool].empty(), "a", 1)))
end
"#,
    );
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains("not read here"), "{errs:#?}");
}
