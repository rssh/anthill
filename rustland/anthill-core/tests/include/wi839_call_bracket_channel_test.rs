//! WI-839 (proposal 058 §2.2 / §9 phase 0) — every CALL-SITE BRACKET is read or
//! reported.
//!
//! `f[T = X](args)` has parsed since WI-271 into a `type_args` ParseAux channel.
//! MEASURED on the parent commit, it was honoured in exactly TWO places — a call in an
//! OPERATION BODY (`build_call_type_args` → `Expr::Apply.type_args` → the typer's
//! `seed_op_type_args`) and a rule HEAD's `[T]` type-variable introducer (WI-582) — and
//! SILENTLY DROPPED in six spellings, every one of which loaded clean and meant nothing:
//!
//!   1. an op-body call whose callee declares no OP-LEVEL type params
//!      (`plain[Bogus = Int64](n)`) — `typing.rs`'s `op.type_params.is_empty()` guard;
//!   2. the same on a callee whose params are its enclosing SORT's (`Box.mk[Bogus = …]`);
//!   3. an over-applied POSITIONAL (`plain[Int64](n)`, `idy[Int64, String](n)`) — a
//!      `continue` in the same loop;
//!   4. an op-body call on a callee that is NOT AN OPERATION — a FUNCTION VALUE or an
//!      APPLIED RULE citation (WI-714) — which `seed_op_type_args` never reaches;
//!   5. an op-body ENTITY-CONSTRUCTOR call — `Expr::Constructor` has no type-args slot;
//!   6. a rule-body goal, a `fact` head, a `constraint`, and an operation's `requires` /
//!      `ensures` contract expression — lowerings that read the channel nowhere.
//!
//! Two more, inside the bracket rather than around it, and both found by /code-review
//! after the first cut: the same key written TWICE resolved both copies to one parameter
//! and discarded the second, and a positional after a named binding re-targeted the slot
//! that binding had taken instead of over-applying.
//!
//! WHY IT IS PHASE 0 of the arc: proposal 058's whole SELECT surface reuses this
//! channel, so the spelling is ALREADY ACCEPTED and ALREADY INERT — a program written
//! against it would load silently wrong until the typer leg lands. It is independently
//! a "loud error over silent skip" violation.
//!
//! TWO OWNERS, split by what each can decide:
//!   * the LOADER refuses a bracket no lowering READ — a whole-parse-store sweep
//!     (`check_unconsumed_call_type_args`) against the set the two honouring readers
//!     record. Deliberately NOT a check at each dropping lowering: cases 5 and 6 are
//!     four different walkers, and "enumerate the droppers" is the WI-805 mistake — a
//!     producer list that feels exhaustive and is not. It earned its keep immediately:
//!     the contract-expression position in case 6 was found BY the sweep, having
//!     appeared in nobody's list.
//!   * the TYPER refuses a bracket that WAS read but lands nowhere. Two rungs, and the
//!     split matters: a callee that is not an operation is refused ABOVE
//!     `check_apply_iter`'s early returns (there is no parameter list, whatever the
//!     key says), and a binding that misses / repeats / over-applies against a real
//!     parameter list is refused by `resolve_call_type_arg_targets`. Placing the first
//!     rung at the top rather than per-path is the same lesson again — guarding only
//!     the function-value path left the applied rule citation loading clean.
//!
//! SELECTION IN RULE BODIES IS DEFERRED, NOT IGNORED (§4.2): the refusal is the
//! deliberate answer, and a rule body needing a chosen witness routes through an
//! operation.
//!
//! THE CONTROL THIS FILE EXISTS TO KEEP: the refusal keys on the ParseAux `type_args`
//! CHANNEL, never on "a bracket in a rule body". A rule-body TYPE APPLICATION
//! (`:- Modifiable[T = ?t]`, `is_modifiable(Cell[V = Int64])`) is a DIFFERENT producer,
//! is legitimately checked by WI-710, and must keep loading — with its own
//! `InvalidTypeArgument` still firing on an undeclared param.

use crate::common::try_load_kb_with;

/// The refusal shape, asserted on the MESSAGE. A count-only assertion would pass on an
/// implementation that rejected these programs for an unrelated reason — and for the
/// rule-body cases the wrong implementation is a specific, tempting one (reading
/// `type_args` as a sort application, which says "no type parameter named 'type_args'").
fn assert_refused_with(src: &str, needle: &str, why: &str) {
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("must NOT load: {why}"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "{why}; expected a diagnostic containing {needle:?}, got: {errs:?}",
    );
}

fn assert_loads(src: &str, why: &str) {
    try_load_kb_with(src).unwrap_or_else(|errs| panic!("{why}; got: {errs:?}"));
}

/// The §9 phase-0 acceptance, verbatim: `plain[Bogus = Int64](n)` fails to load, reusing
/// the EXISTING `NoSuchTypeParam` message. Case 1 — a callee with no op-level params.
#[test]
fn a_bogus_key_on_a_callee_with_no_type_params_is_loud() {
    assert_refused_with(
        r#"
namespace test.wi839.no_params
  import anthill.prelude.{Int64}
  sort Driver
    operation plain(n: Int64) -> Int64 = n
    operation main(n: Int64) -> Int64 = plain[Bogus = Int64](n)
  end
end
"#,
        "unknown type-param 'Bogus'",
        "a bracket key matching no declared type param is loud even on a param-less callee",
    );
}

/// THE control for the above, and the reason the fix is a DELETED guard rather than a
/// new check: a callee that DOES declare type params already gave exactly this message
/// (§2.2 row 1). Both spellings must now read the same, or the "reuse the existing
/// diagnostic" half of the acceptance is unmet.
#[test]
fn a_bogus_key_on_a_callee_with_type_params_keeps_the_same_message() {
    assert_refused_with(
        r#"
namespace test.wi839.has_params
  import anthill.prelude.{Int64}
  sort Driver
    operation idy[T](n: T) -> T = n
    operation main(n: Int64) -> Int64 = idy[Bogus = Int64](n)
  end
end
"#,
        "unknown type-param 'Bogus'",
        "the already-loud case must keep its message unchanged",
    );
}

/// Case 2 — §2.2 row 6. The callee's type params are its enclosing SORT's, not its own,
/// so `op.type_params` is empty and the old guard swallowed the whole list. (Binding a
/// SORT-level param from a call bracket is 058 §9 phase 2 and still does not work; what
/// changes here is only that writing a key that binds nothing is heard.)
#[test]
fn a_bogus_key_on_a_sort_level_parametric_callee_is_loud() {
    assert_refused_with(
        r#"
namespace test.wi839.sort_level
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    entity box(v: T)
    operation mk(v: T) -> Box[T = T] = box(v: v)
  end
  sort Driver
    operation main() -> Box[T = Int64] = Box.mk[Bogus = Int64](5)
  end
end
"#,
        "unknown type-param 'Bogus'",
        "a sort-level-parametric callee's bracket key is checked against the OP's params",
    );
}

/// Case 3 — an over-applied POSITIONAL. It gets its own diagnostic because an unmatched
/// positional has no key to name. Both flavours: nothing to bind at all, and one too
/// many.
#[test]
fn an_over_applied_positional_bracket_is_loud() {
    assert_refused_with(
        r#"
namespace test.wi839.pos_none
  import anthill.prelude.{Int64}
  sort Driver
    operation plain(n: Int64) -> Int64 = n
    operation main(n: Int64) -> Int64 = plain[Int64](n)
  end
end
"#,
        "expected at most 0 positional type argument(s), got 1",
        "a positional binding on a param-less callee binds nothing",
    );
    assert_refused_with(
        r#"
namespace test.wi839.pos_excess
  import anthill.prelude.{Int64, String}
  sort Driver
    operation idy[T](n: T) -> T = n
    operation main(n: Int64) -> Int64 = idy[Int64, String](n)
  end
end
"#,
        "expected at most 1 positional type argument(s), got 2",
        "a second positional on a one-param callee binds nothing",
    );
}

/// THE control for the positional check, and it is not hypothetical: the stdlib-facing
/// `fresh_var[Term](name)` spelling (`anthill-todo/anthill/main.anthill`) is a POSITIONAL
/// call-site bracket that MATCHES. A check that refused positionals as such would break
/// it.
#[test]
fn a_positional_bracket_that_matches_still_loads() {
    assert_loads(
        r#"
namespace test.wi839.pos_ok
  import anthill.prelude.{Int64, String}
  import anthill.reflect.{fresh_var, Term}
  sort Driver
    operation main() -> Term = fresh_var[Term]("id")
  end
end
"#,
        "a positional binding that lands on a declared param is the working spelling",
    );
}

/// Case 4 — a callee that is NOT AN OPERATION has no type-parameter list at all, and
/// `seed_op_type_args` runs only on the operation path. Refused above `check_apply_iter`'s
/// early returns, so all three classes are one case: a function VALUE, an APPLIED RULE
/// citation (WI-714), and a bare-functor constructor invocation.
///
/// The applied-rule spelling is here because guarding only the function-value path left
/// it loading clean — /code-review measured it. That is the SAME "enumerate the sites"
/// failure the loader half avoids by sweeping, recommitted on the typer side; the fix
/// moved the check above every early return rather than adding a third one.
///
/// The diagnostic is deliberately NOT `NoSuchTypeParam`: that would imply some other key
/// would have been accepted, and would render a local binder through `qualified_name_of`
/// as though it were an operation.
#[test]
fn a_bracket_on_a_non_operation_callee_is_loud() {
    let needle = "expected an operation, which declares the type parameters";
    assert_refused_with(
        r#"
namespace test.wi839.fn_value
  import anthill.prelude.{Int64}
  sort Driver
    operation apply1(f: (x: Int64) -> Int64, n: Int64) -> Int64 = f[Bogus = Int64](n)
  end
end
"#,
        needle,
        "an arrow-typed variable has no type-parameter list to bind",
    );
    assert_refused_with(
        r#"
namespace test.wi839.rule_ref
  import anthill.prelude.{Int64, Relation}
  import anthill.prelude.PartialEq.{eq}
  rule p(?x) :- eq(?x, 1)
  sort Driver
    operation main() -> Relation = p[Bogus = Int64](1)
  end
end
"#,
        needle,
        "an applied rule citation is not an operation — WI-714's path skipped both checks",
    );
    assert_refused_with(
        r#"
namespace test.wi839.rule_ref_pos
  import anthill.prelude.{Int64, Relation}
  import anthill.prelude.PartialEq.{eq}
  rule p(?x) :- eq(?x, 1)
  sort Driver
    operation main() -> Relation = p[Int64, Int64, Int64](1)
  end
end
"#,
        needle,
        "three positionals on a rule citation bind nothing either",
    );
}

/// THE control for the above: the same rule citation WITHOUT a bracket still loads, so
/// the check added above `check_apply_iter`'s early returns did not break the WI-714
/// applied-citation path it now sits in front of.
#[test]
fn an_applied_rule_citation_without_a_bracket_still_loads() {
    assert_loads(
        r#"
namespace test.wi839.rule_ref_ok
  import anthill.prelude.{Int64, Relation}
  import anthill.prelude.PartialEq.{eq}
  rule p(?x) :- eq(?x, 1)
  sort Driver
    operation main() -> Relation = p(1)
  end
end
"#,
        "an applied rule citation is an ordinary Relation value",
    );
}

/// One bracket must not bind one parameter TWICE. Both keys resolve to the same var, so
/// the second unification contradicts the first and its verdict is discarded — `A =
/// String` written and meaning nothing. The guard WI-805 / WI-808 / WI-809 already put on
/// tuple labels, entity fields and named ARGUMENT lists; the type-argument list had none,
/// including in this ticket's first cut.
#[test]
fn one_type_parameter_bound_twice_in_a_bracket_is_loud() {
    assert_refused_with(
        r#"
namespace test.wi839.dup_key
  import anthill.prelude.{Int64, String, Bool}
  sort Driver
    operation two[A, B](a: A, b: B) -> Bool = true
    operation main(n: Int64, s: String) -> Bool = two[A = Int64, A = String](n, s)
  end
end
"#,
        "type-param 'A' bound twice in one bracket",
        "a repeated key discards the second binding",
    );
}

/// A POSITIONAL must take a slot no NAMED key already claimed. Counting positionals
/// against `declared.len()` instead of against the slots left FREE let `idy[T = Int64,
/// String]` re-target the one slot `T` already held: not over-applied by the count,
/// contradictory in effect, and silent.
#[test]
fn a_positional_after_a_named_binding_over_applies() {
    assert_refused_with(
        r#"
namespace test.wi839.named_then_pos
  import anthill.prelude.{Int64, String}
  import anthill.prelude.Option.{none}
  sort Driver
    operation idy[T](n: T) -> T = n
    operation main(n: Int64) -> Int64 = idy[T = Int64, String](n)
  end
end
"#,
        "expected at most 0 positional type argument(s), got 1",
        "the named key took the only slot, so the positional has none left",
    );
}

/// A callee with a parameter literally named `type_args` collides with the converter's
/// own channel key — they share one named-arg namespace, and the synthesized pair is
/// appended AFTER the user's. A first-match read found the user's value, missed the
/// bracket, and so REFUSED a correct program once the sweep existed. `read_parse_aux` now
/// scans for the entry whose value IS a matching `ParseAux`, which a user argument never
/// is. (WI-809's duplicate-label guard cannot see this: it runs before the synthesized
/// pair is appended.)
#[test]
fn a_parameter_named_type_args_does_not_shadow_the_channel() {
    assert_loads(
        r#"
namespace test.wi839.key_collision
  import anthill.prelude.{Int64}
  sort Driver
    operation f[T](type_args: T) -> T = type_args
    operation main(n: Int64) -> Int64 = f[T = Int64](type_args: n)
  end
end
"#,
        "a user parameter may be named `type_args` without disabling the bracket",
    );
}

/// Case 5 — an ENTITY-CONSTRUCTOR call in an op body. `Expr::Constructor` has no
/// type-args slot, so the loader read the channel and threw the result away. This is the
/// producer NOT named in the ticket's "all three" — found by measuring, which is why the
/// loader half sweeps consumption instead of enumerating droppers.
#[test]
fn a_bracket_on_an_entity_constructor_call_is_loud() {
    assert_refused_with(
        r#"
namespace test.wi839.ctor
  import anthill.prelude.{Int64}
  sort Thing
    entity boxed(n: Int64)
  end
  sort Driver
    operation main() -> Thing = boxed[Bogus = Int64](n: 1)
  end
end
"#,
        "call-site type arguments `boxed[…](…)` are not supported here",
        "an entity constructor has no type-args slot, so the bracket vanished",
    );
}

/// THE control for case 5: the same constructor call WITHOUT a bracket keeps loading, so
/// the refusal is about the channel, not about constructor calls.
#[test]
fn an_entity_constructor_call_without_a_bracket_still_loads() {
    assert_loads(
        r#"
namespace test.wi839.ctor_ok
  import anthill.prelude.{Int64}
  sort Thing
    entity boxed(n: Int64)
  end
  sort Driver
    operation main() -> Thing = boxed(n: 1)
  end
end
"#,
        "an ordinary constructor call is untouched",
    );
}

/// Case 6, the §9 phase-0 acceptance's second half: a rule body containing `f[T = X](…)`
/// fails to load with a not-supported-here diagnostic. Three positions, because they are
/// three different lowerings — a nested call, a TOP-LEVEL body atom, and an entity
/// constructor in a body (which routes through the term converter, not the occurrence
/// builder).
#[test]
fn a_rule_body_bracket_is_refused_as_not_supported_here() {
    assert_refused_with(
        r#"
namespace test.wi839.body_nested
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.PartialEq.{eq}
  operation plainp(n: Int64) -> Bool = true
  rule ok(?b) :- eq(?b, plainp[Bogus = Int64](1))
end
"#,
        "call-site type arguments `plainp[…](…)` are not supported here",
        "a nested rule-body call's bracket is dropped",
    );
    assert_refused_with(
        r#"
namespace test.wi839.body_atom
  import anthill.prelude.{Int64, Bool}
  operation plainp(n: Int64) -> Bool = true
  rule r(?t) :- plainp[Bogus = Int64](?t)
end
"#,
        "call-site type arguments `plainp[…](…)` are not supported here",
        "a top-level rule-body atom's bracket is dropped",
    );
    assert_refused_with(
        r#"
namespace test.wi839.body_ctor
  import anthill.prelude.{Int64}
  sort Thing
    entity boxed(n: Int64)
  end
  rule ok(?x) :- boxed[Bogus = Int64](n: ?x)
end
"#,
        "call-site type arguments `boxed[…](…)` are not supported here",
        "a rule-body constructor's bracket is dropped",
    );
}

/// The same channel in a `fact` head and in a `constraint` — the term-converter path,
/// which reads the channel nowhere at all.
#[test]
fn a_fact_head_and_a_constraint_bracket_are_refused_too() {
    assert_refused_with(
        r#"
namespace test.wi839.fact_head
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.PartialEq.{eq}
  operation plainp(n: Int64) -> Bool = true
  rule ok(?b) :- eq(?b, true)
  fact ok(plainp[Bogus = Int64](1))
end
"#,
        "call-site type arguments `plainp[…](…)` are not supported here",
        "a fact head's bracket is dropped",
    );
    assert_refused_with(
        r#"
namespace test.wi839.constraint
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.PartialEq.{eq}
  operation plainp(n: Int64) -> Bool = true
  rule p(?x) :- eq(?x, 1)
  constraint c
    :- p(?x), eq(?x, plainp[Bogus = Int64](1))
end
"#,
        "call-site type arguments `plainp[…](…)` are not supported here",
        "a constraint body's bracket is dropped",
    );
}

/// An operation's `requires` / `ensures` CONTRACT expression is the position the sweep
/// caught that no producer list had named — it is lowered by the term converter, so the
/// bracket never reached `build_call_type_args`. It refuses, and the message must name
/// the contract position: the author IS inside an operation, so "route the call through
/// an operation" would be advice they cannot take. That message defect is what a
/// substring-only assertion here would have missed.
#[test]
fn a_contract_expression_bracket_is_refused_and_the_message_names_that_position() {
    let src = r#"
namespace test.wi839.contract
  import anthill.prelude.{Int64, Bool}
  sort Driver
    operation idy[T](n: T) -> Bool = true
    operation main(n: Int64) -> Int64 ensures idy[T = Int64](n) = n
  end
end
"#;
    assert_refused_with(
        src,
        "`requires` / `ensures` contract expression",
        "a contract expression has no channel for the bracket, and must be named as such",
    );
    // The bracket, not the call: the same contract without it loads.
    assert_loads(
        r#"
namespace test.wi839.contract_ok
  import anthill.prelude.{Int64, Bool}
  sort Driver
    operation idy[T](n: T) -> Bool = true
    operation main(n: Int64) -> Int64 ensures idy(n) = n
  end
end
"#,
        "an ordinary contract expression is untouched",
    );
}

/// A rule HEAD carrying a CONCRETE binding (`rule r[A = Int64](…)`) is refused — the head
/// channel admits only the bare WI-582 introducer — and gets its OWN message. The shared
/// wording was actively wrong here: it named the rule-head introducer as a place the
/// bracket IS honoured, which is exactly where the author wrote it, and then told them to
/// route the call through an operation, which a rule head cannot do.
#[test]
fn a_rule_head_with_a_concrete_binding_is_refused_with_head_specific_advice() {
    assert_refused_with(
        r#"
namespace test.wi839.head_binding
  import anthill.prelude.{Int64}
  import anthill.prelude.PartialEq.{eq}
  rule r[A = Int64](?x) :- eq(?x, 1)
end
"#,
        "a rule head's bracket declares type-variable INTRODUCERS only",
        "a rule head binding a concrete type argument must be told what heads accept",
    );
}

/// THE CONTROL the ticket names, and the reason the refusal keys on the ParseAux
/// CHANNEL rather than on "a bracket appearing in a rule body": a rule-body TYPE
/// APPLICATION is a DIFFERENT producer (`convert_instantiation_term`, marked
/// `is_type_application`), is checked by WI-710, and must keep loading — as a goal, as a
/// value argument, and with variable arguments.
#[test]
fn a_rule_body_type_application_still_loads() {
    assert_loads(
        r#"
namespace test.wi839.type_app
  import anthill.prelude.{Cell, List, Int64, Bool, Modifiable}
  import anthill.reflect.{is_modifiable}
  import anthill.prelude.PartialEq.{eq}
  rule modifiable_elem(?t) :- Modifiable[T = ?t]
  rule any_list(?t, ?b) :- eq(?b, is_modifiable(List[T = ?t]))
  rule cell_body(?b) :- eq(?b, is_modifiable(Cell[V = Int64]))
end
"#,
        "a rule-body type application is WI-710's producer and is unaffected",
    );
}

/// …and its check still FIRES. Without this the control above is satisfiable by a fix
/// that disabled WI-710 in rule bodies altogether.
#[test]
fn an_undeclared_param_in_a_rule_body_type_application_stays_loud() {
    assert_refused_with(
        r#"
namespace test.wi839.type_app_bad
  import anthill.prelude.{Cell, Int64, Bool}
  import anthill.reflect.{is_modifiable}
  import anthill.prelude.PartialEq.{eq}
  rule bad(?x) :- eq(?x, is_modifiable(Cell[W = Int64]))
end
"#,
        "has no type parameter named 'W'",
        "WI-710's own diagnostic must still fire on a rule-body type application",
    );
}

/// THE OTHER honouring reader, and the second thing the sweep must not break: a rule
/// HEAD's `[T]` type-variable INTRODUCER (WI-582) rides on this very channel. It is
/// consumed, so it loads.
#[test]
fn a_rule_head_type_variable_introducer_still_loads() {
    assert_loads(
        r#"
namespace test.wi839.introducer
  import anthill.prelude.{Int64, Bool, Eq}

  sort Summable
    sort T = ?
    requires Eq[T]
  end

  fact Summable[T = Int64]

  sort Lib
    sort A = ?
    operation {
      keep(x: A, y: A) -> A
    }
    rule {
      keep_id: keep[T](?x: T, ?y) <=> ?x :- Summable[T] [simp]
    }
  end
end
"#,
        "a rule-head `[T]` introducer is a READ of the channel, not a drop",
    );
}
