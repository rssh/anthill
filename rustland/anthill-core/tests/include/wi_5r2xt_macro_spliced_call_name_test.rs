//! WI-20260820-5R2XT — A MACRO-SPLICED CALL NAMES THE SURFACE CALL, NOT ONLY THE RUNNER.
//!
//! THE SYMPTOM. `p.join(q, λ)` over two relations that share a column reported
//! `type mismatch in join_run.return (op-return): …`. `join_run` is the RUNTIME back-end
//! the `conjoin_of` macro splices; the author wrote `join`. WI-20260819-33H3P repaired the
//! LOCATION of that diagnostic and left the name, which is this ticket.
//!
//! THE CHANNEL WAS ALREADY THERE AND WAS ALREADY WRONG. `OccurrenceOrigin::Synthesized
//! { from }` is documented as "a back-pointer to the originating source occurrence", and
//! every pass maintains it. MEASURED, walking it from the spliced call:
//!   join_run → join_run → join_run → VarRef(p)   [Source]
//! It ends at `p` — an ARGUMENT of the call, not what originated it. A macro BUILDS its
//! result and so picks that result's `from` itself (`make_apply(name, args, from)`), and it
//! can only pick among the occurrences it was handed: the redex's arguments.
//! `splice_query_runner` picks its first relation operand, whose real job there is to be
//! the SPAN anchor — `synthesized_expr` takes the span from `from`, which is what invited
//! a provenance field to be used as a location field.
//!
//! Meanwhile the TEMPLATE the macro was expanded from chained correctly, because
//! `instantiate_rhs` builds it `from` the redex:
//!   conjoin_of → join → .join   [Source]
//!
//! THE FIX splices those two: `try_expand_macro` re-parents the macro's result onto the
//! template. Macro-agnostic — no macro has to know to do it and none can forget — and the
//! SPAN is deliberately not moved with it, so 33H3P's answer to "where" stands unchanged.
//! `NodeOccurrence::surface_call_name` then walks to the first `Source` ancestor and reads
//! its head, which is the first READER that channel has ever had. That it had none is why
//! it could be wrong for this long.
//!
//! WHAT THE READER SEES: `join (expanded to join_run).return`. Not `join` alone — when the
//! failure is in the runner's own signature rather than in the operands, the internal name
//! is the only thing that leads anyone to it.
//!
//! WHICH LOWERINGS QUALIFY. Only those stamped `macro_expand_pass` — the discriminator
//! `make_apply`'s doc has named since WI-722. The typer synthesizes plenty of nodes that
//! are NOT macro expansions and stamps them `simp_pass`, and admitting those was measured
//! WRONG on both faces (found by review, not by an arm): an ordinary `bx.getIt(1)` rendered
//! `getIt (expanded to getIt)` — a `DotApply`'s member symbol is not the operation symbol
//! it resolves to, though both render as the same short name — and `r.(a, b)` would have
//! reported `TupleLiteral`, a constructor, as the operation the author called.
//!
//! BACK-OUTS, one per moving part, each mutating the site rather than deleting it:
//!  * DON'T RE-PARENT (`try_expand_macro` returns the macro's result unchanged): the three
//!    naming arms fail, each reading the runner's bare name (`join_run`, `myRun`). Controls
//!    pass.
//!  * DON'T READ (`surface: None` at the `check_apply_iter` sites): the same three fail the
//!    same way. Controls pass.
//!  * COMPARE SYMBOLS instead of rendered names: `..._a_runner_sharing_the_surface_short_-
//!    name_…` fails with `merge2 (expanded to merge2)`. That arm is the one that drives
//!    this half alone.
//!  * DROP THE MACRO GATE: no arm here fails on its own — see below — and the unit test
//!    `node_occurrence::tests::the_surface_name_needs_a_macro_link_not_merely_a_-
//!    synthesized_one` is what pins it.
//!
//! ONE ARM MEASURES A CONJUNCTION, AND SAYING SO IS THE POINT.
//! `..._a_dot_call_at_the_same_sites_…` fails only when the macro gate AND the same-name
//! suppression are BOTH backed out; either alone suppresses that particular noise, by a
//! different route. Its first draft claimed it failed under either — MEASURED FALSE, both
//! ways. The two halves are not redundant, they just overlap here: the gate is what stops a
//! non-operation head (`TupleLiteral`) being named, where the names differ so suppression
//! cannot help; the suppression is what stops a genuine macro whose runner shares the
//! surface short name. Each has its own arm above for the case the other cannot cover.
//!
//! WHAT IS NOT COVERED, and it is a limit of the CHANNEL rather than a missing test.
//! `where` has no arm here because a `where` refusal cannot reach this context at all:
//! `where_run` declares `-> Relation[T = r.T, E = r.E]`, which writes no reducible type
//! constructor, so the `op_return_ctors` gate that guards this reduction is false for it by
//! construction. `where`'s own refusals travel the WI-757 macro-rejection channel, which
//! names the macro explicitly and separately (`compile-time macro `…guarded_of``) and is
//! pinned by `wi757_macro_diagnostic_test`. The ticket asked for a `where` arm; there is no
//! reachable one to write.
//!
//! PASSES EITHER WAY BY DESIGN: the five arms of `wi_33h3p_dot_call_receiver_span_test`
//! (they assert the LOCATION, which this ticket does not move — they needed no edit) and
//! `typing_test::operation_return_type_mismatch_names_the_operation`, whose `greet` is an
//! ordinary un-lowered call and now also asserts `surface.is_none()`.

use crate::common::try_load_kb_with;

fn one_error(src: &str) -> String {
    match try_load_kb_with(src) {
        Ok(_) => panic!("expected the column collision to fail the load"),
        Err(e) => match &e[..] {
            [only] => only.clone(),
            _ => panic!("expected exactly one error, got: {e:?}"),
        },
    }
}

/// Two relations that share a `name` column, so a merge refuses them (§4.5), plus a
/// third whose columns are DISJOINT from `person_row`'s — the control's operand.
const DOMAIN: &str = r#"
namespace test.wi5r2xt
  import anthill.prelude.{String, Int64, Bool, List, Relation, Concat}
  import anthill.prelude.Relation.{join}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(id: Int64, name: String, age: Int64)
    entity pet(owner: Int64, name: String)
  end
  fact person(id: 1, name: "alice", age: 30)
  fact pet(owner: 1, name: "cat")

  rule person_row(?id, ?name, ?age) :- person(id: ?id, name: ?name, age: ?age)
  rule pet_row(?owner, ?name) :- pet(owner: ?owner, name: ?name)
  rule pet_disjoint(?owner, ?petname) :- pet(owner: ?owner, name: ?petname)
"#;

fn program(body: &str) -> String {
    format!(
        "{DOMAIN}\n  operation drive() -> Bool effects Error =\n    let p = person_row\n    \
         let q = pet_row\n{body}    true\nend\n",
    )
}

/// The stdlib `join`, written as a DOT call — the spelling the ticket was reported against.
#[test]
fn wi5r2xt_a_spliced_join_names_the_join_the_author_wrote() {
    let src = program("    let j = p.join(q, lambda (c, d) -> eq(c.id, d.owner))\n");
    let err = one_error(&src);
    assert!(
        err.contains("in join (expanded to join_run).return"),
        "expected the surface `join` beside the spliced runner, got: {err}",
    );
}

/// The SAME call written WITHOUT the dot. The name is read off the redex the `[simp]` rule
/// fired on, so both spellings answer `join` — a name recovered from the dot surface alone
/// would pass the arm above and fail this one.
#[test]
fn wi5r2xt_the_name_comes_from_the_redex_not_from_the_dot_spelling() {
    let src = program("    let j = join(p, q, lambda (c, d) -> eq(c.id, d.owner))\n");
    let err = one_error(&src);
    assert!(
        err.contains("in join (expanded to join_run).return"),
        "expected the surface `join` for the written spelling too, got: {err}",
    );
}

/// GENERALITY — the arm that makes this not a fix for `join`. A macro declared HERE,
/// splicing a runner declared HERE, through the same `[simp]` + `make_apply` route the
/// stdlib uses. Nothing in the typer, the expander or the reader names `join`, `join_run`
/// or `conjoin_of`, and this fixture would keep failing if any of them did.
///
/// `myRun` / `mySurface` are declared with no body: the diagnostic under test is raised
/// while TYPING the call, before any body would be reached.
#[test]
fn wi5r2xt_a_user_defined_macro_names_its_own_surface_operation() {
    let src = r#"
namespace test.wi5r2xt.own
  import anthill.prelude.{String, Int64, Bool, List, Relation, Concat}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{NodeOccurrence, make_apply}

  sort Person
    entity person(id: Int64, name: String, age: Int64)
    entity pet(owner: Int64, name: String)
  end
  fact person(id: 1, name: "alice", age: 30)
  fact pet(owner: 1, name: "cat")
  rule person_row(?id, ?name, ?age) :- person(id: ?id, name: ?name, age: ?age)
  rule pet_row(?owner, ?name) :- pet(owner: ?owner, name: ?name)

  operation myRun[L, R](r1: Relation[T = L], r2: Relation[T = R])
    -> Relation[T = Concat[A = L, B = R]]

  operation mySurface[L, R](r1: Relation[T = L], r2: Relation[T = R])
    -> Relation[T = Concat[A = L, B = R]]

  operation myMacro(a: NodeOccurrence, b: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi5r2xt.own.myRun", cons(a, cons(b, nil())), a)

  rule mySurface(?a, ?b) <=> myMacro(?a, ?b) [simp]

  operation drive() -> Bool effects Error =
    let p = person_row
    let q = pet_row
    let j = mySurface(p, q)
    true
end
"#;
    let err = one_error(src);
    assert!(
        err.contains("in mySurface (expanded to myRun).return"),
        "expected the user-defined surface/runner pair, got: {err}",
    );
    // Named EXACTLY, not by the substring `join`: the refusal's own detail text says
    // "disjoint field names", so a bare `!contains("join")` reads as a failure here and
    // measures the wrong thing.
    for stdlib_name in ["join_run", "conjoin_of"] {
        assert!(
            !err.contains(stdlib_name),
            "the generality arm must not reach anything named `{stdlib_name}`, got: {err}",
        );
    }
}

/// CONTROL — AN UN-LOWERED CALL GAINS NOTHING. `person_row.takeN(…)` is an ordinary
/// operation call: nothing rewrote it, so there is no surface name beside the callee and
/// the rendering must stay a bare `drive.return`.
///
/// Without this arm the change would be indistinguishable from "always append
/// `(expanded to …)`", which would pass every arm above.
#[test]
fn wi5r2xt_control_an_ordinary_call_carries_no_expansion_clause() {
    let src = format!(
        "{DOMAIN}\n  operation drive() -> String effects Error =\n    \
         person_row.takeN(9)\nend\n",
    );
    let err = one_error(&src);
    assert!(
        !err.contains("expanded to"),
        "an un-lowered call must carry no expansion clause, got: {err}",
    );
}

/// CONTROL — A MACRO WHOSE RUNNER SHARES THE SURFACE OP'S SHORT NAME renders the bare
/// name, not `merge2 (expanded to merge2)`. This is a REAL macro expansion, so the
/// macro-expand gate admits it; only the same-name suppression can quiet it, which makes
/// this the arm that drives that half ALONE.
///
/// MEASURED: comparing the two SYMBOLS instead of what is RENDERED makes this arm fail —
/// the surface and the runner are genuinely different symbols in different namespaces, and
/// `entity_name` renders both through `local_name_of`.
#[test]
fn wi5r2xt_control_a_runner_sharing_the_surface_short_name_renders_it_once() {
    let src = r#"
namespace test.wi5r2xt.back
  import anthill.prelude.{Int64, Bool, List, Relation, Concat}
  operation merge2[L, R](r1: Relation[T = L], r2: Relation[T = R])
    -> Relation[T = Concat[A = L, B = R]]
end

namespace test.wi5r2xt.front
  import anthill.prelude.{String, Int64, Bool, List, Relation, Concat}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{NodeOccurrence, make_apply}

  sort Person
    entity person(id: Int64, name: String, age: Int64)
    entity pet(owner: Int64, name: String)
  end
  fact person(id: 1, name: "alice", age: 30)
  fact pet(owner: 1, name: "cat")
  rule person_row(?id, ?name, ?age) :- person(id: ?id, name: ?name, age: ?age)
  rule pet_row(?owner, ?name) :- pet(owner: ?owner, name: ?name)

  operation merge2[L, R](r1: Relation[T = L], r2: Relation[T = R])
    -> Relation[T = Concat[A = L, B = R]]

  operation myMacro(a: NodeOccurrence, b: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi5r2xt.back.merge2", cons(a, cons(b, nil())), a)

  rule merge2(?a, ?b) <=> myMacro(?a, ?b) [simp]

  operation drive() -> Bool effects Error =
    let p = person_row
    let q = pet_row
    let j = merge2(p, q)
    true
end
"#;
    let err = one_error(src);
    assert!(
        err.contains("in merge2.return"),
        "expected the short name once, got: {err}",
    );
    assert!(
        !err.contains("expanded to"),
        "a runner sharing the surface short name must render it once, got: {err}",
    );
}

/// CONTROL — A DOT CALL AT THESE VERY SITES GAINS NOTHING, which the `takeN` control above
/// does NOT cover: that one fails through `check_operation_bodies` (a `surface: None` site
/// by construction), so it would pass no matter what the three wired sites did.
///
/// This one fails INSIDE `check_apply_iter`'s return-projection elimination — the same code
/// path the `join` arms take — on an ordinary dot call that no macro touched. It is a
/// REGRESSION TEST, not a hypothetical: the first cut of this ticket suppressed the clause
/// by comparing SYMBOLS, and a `DotApply`'s member symbol is not the operation symbol it
/// resolves to, so this rendered `getIt (expanded to getIt).return`. Found by review. The
/// fix has two halves and this arm fails only when BOTH are backed out — the macro-expand
/// gate on the provenance walk, and the same-name suppression comparing what is RENDERED.
/// Either alone suppresses this particular noise; the draft of this comment claimed either
/// alone would fail it, and that was measured false in both directions. See the module
/// header for which arm drives which half.
#[test]
fn wi5r2xt_control_a_dot_call_at_the_same_sites_carries_no_expansion_clause() {
    let src = r#"
namespace test.wi5r2xt.dot
  import anthill.prelude.{Int64, Bool}
  sort Box[T]
    entity box(v: T)
    operation getIt(b: Box, k: b.Missing) -> Int64
  end
  operation drive() -> Int64 effects Error =
    let bx = box(v: 1)
    bx.getIt(1)
end
"#;
    let err = one_error(src);
    assert!(
        err.contains("in getIt.return"),
        "expected the bare callee for an un-expanded dot call, got: {err}",
    );
    assert!(
        !err.contains("expanded to"),
        "a dot call is lowered but not MACRO-expanded, so it must carry no expansion \
         clause, got: {err}",
    );
}

/// CONTROL — the arms above must be shown to fail on the COLLISION, not on the join. The
/// same `join`, over operands whose columns are disjoint, loads.
#[test]
fn wi5r2xt_control_a_join_of_disjoint_relations_loads() {
    let src = format!(
        "{DOMAIN}\n  operation drive() -> Bool effects Error =\n    \
         let p = person_row\n    let q = pet_disjoint\n    \
         let j = p.join(q, lambda (c, d) -> eq(c.id, d.owner))\n    true\nend\n",
    );
    if let Err(e) = try_load_kb_with(&src) {
        panic!("a disjoint join must load, got: {e:?}");
    }
}
