//! WI-618: a bare `pattern -> body` (the keyword-less lambda typo, WI-605)
//! in a rule (head or body) / fact / constraint / contract term position
//! used to load with ZERO diagnostics — the pratt-minted arrow term rode as
//! inert data with unresolved-name leaves, so the clause silently never
//! meant what was written. A blanket error is wrong in these positions
//! (arrow-as-TYPE is legitimate — types are terms), so the diagnostic
//! (`LoadError::BareArrowInLogicPosition`) fires only on the typo shape:
//! a pratt-minted arrow (provenance via `SimpleTermStore::is_minted`, never
//! a user-written `arrow(a, b)` call) whose subtree contains a
//! binder-looking (lowercase or `_`-led) leaf name that fails to resolve in
//! scope. A real arrow type's leaves — sorts, type params, param/`result`
//! places, rule type-vars, lambda binders — resolve or are scoped by the
//! walk, and its logical variables are `?`-vars, not bare names.

/// The marker phrase shared by both bare-arrow diagnostics (WI-605's
/// op-body `arrow_expr_hint` and WI-618's `bare_arrow_logic_msg` both end
/// in `load::LAMBDA_KEYWORD_HINT`).
use crate::common::LAMBDA_HINT as HINT;

fn load_errors(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

/// The WI-618 rule-body repro: a keyword-less `(x, acc) -> …` on the RHS of a
/// body unify. Must produce exactly the one targeted diagnostic naming the
/// unresolved binder — not silence, not a cascade.
#[test]
fn bare_arrow_in_rule_body_is_flagged() {
    let errs = load_errors(
        r#"
namespace test.wi618.rulebody
  import anthill.prelude.{List, nil, cons, Int64}

  rule build_list(?y)
    :- ?y <=> ((x, acc) -> cons(head: x, tail: acc))
end
"#,
    );
    assert_eq!(
        errs.len(),
        1,
        "the rule-body bare arrow must produce exactly one targeted error; got: {errs:?}",
    );
    assert!(
        errs[0].contains(HINT) && errs[0].contains("rule body"),
        "expected the lambda-keyword hint in rule-body position; got: {errs:?}",
    );
}

/// The effectful ternary form (`x -> body @ e`, minted `arrow_effect/3`) in a
/// rule body gets the same diagnostic.
#[test]
fn bare_arrow_effect_in_rule_body_is_flagged() {
    let errs = load_errors(
        r#"
namespace test.wi618.roweffect
  import anthill.prelude.{Int64}

  rule build_fn(?y)
    :- ?y <=> ((x) -> x @ pure)
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains(HINT) && e.contains("rule body")),
        "expected the lambda-keyword hint for the arrow_effect form; got: {errs:?}",
    );
}

/// A typo arrow NESTED inside a constructor argument of a body goal is still
/// found (the walk recurses through positional and named args).
#[test]
fn nested_bare_arrow_in_rule_body_is_flagged() {
    let errs = load_errors(
        r#"
namespace test.wi618.nested
  import anthill.prelude.{List, nil, cons, Int64}

  rule build_list(?y)
    :- ?y <=> cons(head: (x) -> x, tail: nil)
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains(HINT) && e.contains("rule body")),
        "expected the lambda-keyword hint for a nested arrow; got: {errs:?}",
    );
}

/// The WI-618 contract repro: `ensures all_match(result, (x) -> x > 0)`.
#[test]
fn bare_arrow_in_ensures_is_flagged() {
    let errs = load_errors(
        r#"
namespace test.wi618.ensures
  import anthill.prelude.{List, Int64}

  operation all_pos(xs: List[T=Int64]) -> List[T=Int64]
    ensures all_match(result, (x) -> x > 0)
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains(HINT) && e.contains("ensures")),
        "expected the lambda-keyword hint in ensures position; got: {errs:?}",
    );
}

/// The same typo in a `requires` clause.
#[test]
fn bare_arrow_in_requires_is_flagged() {
    let errs = load_errors(
        r#"
namespace test.wi618.requires
  import anthill.prelude.{List, Int64}

  operation head_pos(xs: List[T=Int64]) -> Int64
    requires all_match(xs, (x) -> x > 0)
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains(HINT) && e.contains("requires")),
        "expected the lambda-keyword hint in requires position; got: {errs:?}",
    );
}

/// The same typo in a constraint goal.
#[test]
fn bare_arrow_in_constraint_is_flagged() {
    let errs = load_errors(
        r#"
namespace test.wi618.constraint
  import anthill.prelude.{Int64}

  sort Box
    entity item(value: Int64)
  end

  constraint arrow_typo: item(value: (x) -> x)
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains(HINT) && e.contains("constraint")),
        "expected the lambda-keyword hint in constraint position; got: {errs:?}",
    );
}

/// Legitimate arrow-as-TYPE terms in the same positions still load: over
/// resolved sorts in a rule body and in an `ensures` clause, over a RESOLVED
/// lowercase name (`nil` — exercising the resolve_in_scope suppression, not
/// just the uppercase case gate), over qualified names (whose dotted
/// segments are not scope-resolvable leaves), over logical `?`-variables,
/// and the effectful form over the empty effect row `{}`.
#[test]
fn arrow_types_over_resolved_leaves_still_load() {
    let errs = load_errors(
        r#"
namespace test.wi618.legit
  import anthill.prelude.{List, nil, Int64, String}

  rule arrow_type_data(?t)
    :- ?t <=> (Int64 -> Int64)

  rule arrow_type_lowercase_resolved(?t)
    :- ?t <=> (nil -> Int64)

  rule arrow_type_qualified(?t)
    :- ?t <=> (anthill.prelude.Int64 -> anthill.prelude.Int64)

  rule arrow_type_vars(?a, ?b, ?t)
    :- ?t <=> (?a -> ?b)

  rule effectful_arrow_type(?t)
    :- ?t <=> (Int64 -> Int64 @ {})

  operation describe(f: (a: Int64) -> Int64) -> String
    ensures mentions(result, Int64 -> Int64)
end
"#,
    );
    assert!(
        errs.is_empty(),
        "arrow types over resolved sorts / ?-vars must load clean; got: {errs:?}",
    );
}

/// An UNBOUNDED `[t]` introducer under a body arrow gets only the accurate
/// WI-582 "no bounding guard" diagnostic — not an additional, wrong-advice
/// lambda hint (`t` is a declared type-var, not a lambda binder).
#[test]
fn unbounded_rule_type_var_gets_only_wi582_diagnostic() {
    let errs = load_errors(
        r#"
namespace test.wi618.unbounded
  import anthill.prelude.{Int64}

  rule same_ty[t](?y)
    :- ?y <=> (t -> t)
end
"#,
    );
    assert!(
        !errs.iter().any(|e| e.contains(HINT)),
        "an unbounded rule tvar must not get the lambda hint; got: {errs:?}",
    );
}

/// A `_`-led binder is binder-looking too: `'_'.is_lowercase()` is false, so
/// a naive lowercase gate would let `(_x, _acc) -> …` (the unused-param
/// convention) slip back into silence.
#[test]
fn underscore_led_binder_is_flagged() {
    let errs = load_errors(
        r#"
namespace test.wi618.underscore
  import anthill.prelude.{Int64}

  rule build(?y)
    :- ?y <=> ((_x, _acc) -> _x)
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains(HINT) && e.contains("rule body")),
        "`_`-led binders must witness the typo; got: {errs:?}",
    );
}

/// An AMBIGUOUS binder name is a witness too: rule-body idents ride as inert
/// data (no `AmbiguousSymbol` fires for them), so treating `Ambiguous` as
/// resolved would keep the typo fully silent whenever the binder name
/// collides ambiguously across wildcard imports.
#[test]
fn ambiguous_binder_name_is_flagged() {
    let liba = r#"
namespace test.wi618.amba
  import anthill.prelude.{Int64}
  operation foo(a: Int64) -> Int64 = a
end
"#;
    let libb = r#"
namespace test.wi618.ambb
  import anthill.prelude.{Int64}
  operation foo(a: Int64) -> Int64 = a
end
"#;
    let main = r#"
namespace test.wi618.amb
  import test.wi618.amba.*
  import test.wi618.ambb.*
  import anthill.prelude.{Int64}

  rule build(?y)
    :- ?y <=> ((foo) -> foo)
end
"#;
    let errs = crate::common::try_load_kb_with_files(&[liba, libb, main])
        .err()
        .unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains(HINT)),
        "an ambiguous binder name must still witness the typo; got: {errs:?}",
    );
}

/// Facts are rules with empty bodies — a fact argument is the same logic
/// position, and the canonical place where arrow-as-type data legitimately
/// lives, so it gets the same leaf-discriminated diagnostic.
#[test]
fn bare_arrow_in_fact_argument_is_flagged() {
    let errs = load_errors(
        r#"
namespace test.wi618.fact
  import anthill.prelude.{Int64}

  sort Box
    entity item(value: Int64)
  end

  fact item(value: (x) -> x)
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains(HINT) && e.contains("a fact")),
        "expected the lambda-keyword hint in fact position; got: {errs:?}",
    );
}

/// A rule HEAD argument is checked like the body: a typo arrow head pattern
/// could only ever match the literal inert arrow shape, never a function
/// value, so the rule would be silently unfirable.
#[test]
fn bare_arrow_in_rule_head_is_flagged() {
    let errs = load_errors(
        r#"
namespace test.wi618.head
  import anthill.prelude.{Int64}

  rule holds((x) -> x)
    :- ?y <=> 1
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains(HINT) && e.contains("rule head")),
        "expected the lambda-keyword hint in rule-head position; got: {errs:?}",
    );
}

/// A lowercase WI-582 rule type-variable (`[t]` introducer) under a body
/// arrow is NOT a witness: it is legitimately bound by the head, living in
/// `rule_tvar_bounds` rather than the symbol table — the walk exempts it.
#[test]
fn lowercase_rule_type_var_arrow_still_loads() {
    let errs = load_errors(
        r#"
namespace test.wi618.tvar
  import anthill.prelude.{Int64, Eq}

  rule same_ty[t](?y)
    :- Eq[t], ?y <=> (t -> t)
end
"#,
    );
    assert!(
        errs.is_empty(),
        "a bounded lowercase rule type-var under an arrow must load; got: {errs:?}",
    );
}

/// A KEYWORD lambda passed as a call argument in a rule body, whose own
/// binder appears under an inner arrow-type term: the binder is scoped by
/// the walk, so the legitimate `lambda t -> (t -> t)` is not misread as a
/// typo (the advice would be self-contradictory — the keyword is present).
#[test]
fn lambda_binder_under_inner_arrow_still_loads() {
    let errs = load_errors(
        r#"
namespace test.wi618.lambdabind
  import anthill.prelude.{Int64}

  rule type_fn(?g)
    :- ?g <=> mk2(lambda t -> (t -> t))
end
"#,
    );
    assert!(
        !errs.iter().any(|e| e.contains(HINT)),
        "a keyword lambda's binder under an inner arrow is not a typo; got: {errs:?}",
    );
}

/// WI-605-side pin: an operation the user NAMED `arrow` does not change the
/// verdict on a minted `->` in an op body — the user typed the operator, and
/// silently reading `1 -> 2` as a call to that operation (the old
/// heuristic's behavior) hid the typo.
#[test]
fn arrow_operation_in_scope_does_not_legitimize_minted_arrow() {
    let errs = load_errors(
        r#"
namespace test.wi618.arrowop
  import anthill.prelude.{Int64}

  operation arrow(a: Int64, b: Int64) -> Int64 = a + b
  operation f() -> Int64 = 1 -> 2
end
"#,
    );
    assert_eq!(
        errs.len(),
        1,
        "a minted `->` in an op body errs even with an `arrow` op in scope; got: {errs:?}",
    );
    assert!(errs[0].contains(HINT), "expected the lambda-keyword hint; got: {errs:?}");
}

/// Provenance payoff on the WI-605 side: a WRITTEN 2-arg call `arrow(1, 2)`
/// to an undefined name matches the old heuristic's shape exactly, but is not
/// pratt-minted — it must keep the normal unresolved diagnostics, never the
/// lambda hint (the user typed no `->`).
#[test]
fn written_two_arg_arrow_call_gets_normal_diagnostics() {
    let errs = load_errors(
        r#"
namespace test.wi618.writtencall
  import anthill.prelude.{Int64}

  operation use_it() -> Int64 = arrow(1, 2)
end
"#,
    );
    assert!(
        !errs.is_empty(),
        "an undefined `arrow(1, 2)` call must still error",
    );
    assert!(
        !errs.iter().any(|e| e.contains(HINT)),
        "a written call is not the mis-parsed `->` — no lambda hint; got: {errs:?}",
    );
}

/// Provenance removes WI-605's deliberate false negative: a value binder
/// named `arrow` in scope used to suppress the op-body hint (the heuristic
/// could not tell the minted `->` from an application of that binder). The
/// minted term IS the `->`, so the typo now gets the targeted hint even with
/// an `arrow`-named param present.
#[test]
fn value_binder_named_arrow_no_longer_suppresses_hint() {
    let errs = load_errors(
        r#"
namespace test.wi618.binder
  import anthill.prelude.{Int64}

  operation weird(arrow: Int64) -> Int64 =
    (x) -> x + arrow
end
"#,
    );
    assert_eq!(
        errs.len(),
        1,
        "the bare arrow must get exactly the one targeted error despite the \
         `arrow`-named param; got: {errs:?}",
    );
    assert!(errs[0].contains(HINT), "expected the lambda-keyword hint; got: {errs:?}");
}
