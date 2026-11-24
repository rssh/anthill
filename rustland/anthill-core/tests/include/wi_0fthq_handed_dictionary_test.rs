//! WI-20261113-0FTHQ — proposal 074 stage 9: A CALL USES THE DICTIONARY ITS OPERATION IS HANDED
//! (`docs/proposals/074-typeclass-instance-is-a-dictionary.md` §2, "Which dictionary a call
//! uses"; T13; kernel-language §8.2, §5.4).
//!
//! A call of a spec's operation uses the first of: the provider its bracket names; a dictionary
//! the operation is handed at the call's spec and types — a parameter, a lambda's binder, a
//! clause; the provider chosen at load. Before the stage a parameter typed at the spec was read
//! only at its own members (`x: Additive` at `x.T`): over `t: Tag[T = Leaf]` the call at `Leaf`
//! was decided at load at `Leaf`'s own provision and `t` was not used (T13 answered 1), and over
//! `t: Tag[T = X]` a call at `X` was refused, "missing `requires Tag[T = …]`". A call two handed
//! dictionaries answer is refused at load. A bracket may name any provider, one with
//! constructors included (decided with the user 2026-11-24): it outranks the handed dictionary.
//!
//! CONTROLS — the back-out ledger at the end of this file.

use anthill_core::eval::Interpreter;

use crate::common::{interp_for, load_errors_of, show_value};

fn call(interp: &mut Interpreter, op: &str) -> String {
    match interp.call(op, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(v) => show_value(interp.kb(), &v),
        Err(e) => panic!("`{op}`: {e:?}"),
    }
}

/// T13's declarations: `Tag` over `T`, `Leaf`'s own provision answering 1, a second provider
/// `Alt` answering 2, and a dictionary of each.
const TAG: &str = "
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Leaf
    entity leaf(k: Int64)
    provides Tag[T = Leaf]
    operation tag(x: Leaf) -> Int64 = 1
  end
  sort Alt
    provides Tag[T = Leaf]
    operation tag(x: Leaf) -> Int64 = 2
  end
  operation alt() -> Tag[T = Leaf] = Dictionary.instance[Tag[T = Leaf], Tag = Alt]()
  operation own() -> Tag[T = Leaf] = Dictionary.instance[Tag[T = Leaf], Tag = Leaf]()
";

/// `Meters` with two providers of `Additive`, the default adding and `MetersTen` answering 10.
const METERS: &str = "
  sort Meters
    entity m(v: Int64)
  end
  sort MetersAdd
    default provides Additive[T = Meters]
    operation add(a: Meters, b: Meters) -> Meters = match a case m(x) -> match b case m(y) -> m(v: x + y)
    operation neg(a: Meters) -> Meters = a
    operation zero() -> Meters = m(v: 0)
  end
  sort MetersTen
    provides Additive[T = Meters]
    operation add(a: Meters, b: Meters) -> Meters = m(v: 10)
    operation neg(a: Meters) -> Meters = a
    operation zero() -> Meters = m(v: 0)
  end
  operation ten() -> Additive[T = Meters] = Dictionary.instance[Additive[T = Meters], Additive = MetersTen]()
  operation sum2[X](a: X, b: X) -> X requires Additive[T = X] = a + b
";

/// A spec whose chain reaches another through a conversion, as `Ord provides WeakOrd[T = T]`
/// does: `Strict provides Cmp[T = T]`, two providers of `Strict` at `Big`.
const STRICT: &str = "
  sort Cmp
    sort T = ?
    operation cmp(a: T, b: T) -> Int64
  end
  sort Strict
    sort T = ?
    provides Cmp[T = T]
  end
  sort Big
    entity big(n: Int64)
  end
  sort BigOrd
    default provides Strict[T = Big]
    operation cmp(a: Big, b: Big) -> Int64 = -1
  end
  sort BigRev
    provides Strict[T = Big]
    operation cmp(a: Big, b: Big) -> Int64 = 1
  end
  operation rev() -> Strict[T = Big] = Dictionary.instance[Strict[T = Big], Strict = BigRev]()
";

fn program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace p074s9.{ns}\n  import anthill.prelude.{{Int64, Additive}}\n  import anthill.realization.runtime.Dictionary\n{decls}{body}\nend\n"
    )
}

fn answers(ns: &str, decls: &str, body: &str, ops: &[(&str, &str)]) {
    let mut interp = interp_for(&program(ns, decls, body));
    for (op, want) in ops {
        assert_eq!(call(&mut interp, &format!("p074s9.{ns}.{op}")), *want, "{op}");
    }
}

/// The refusal of a call two handed dictionaries answer, naming both.
fn refused_tie(ns: &str, decls: &str, body: &str, spec: &str, first: &str, second: &str) {
    let errors = load_errors_of(&program(ns, decls, body));
    assert!(
        errors.iter().any(|e| e.contains(&format!("two providers of `{spec}` the operation is handed answer"))
            && e.contains(first)
            && e.contains(second)),
        "{ns}: expected the tie naming {first} and {second}, got {errors:?}"
    );
}

// ── The handed dictionary answers ──────────────────────────────────────────────────────────

/// T13: handed `Alt`'s dictionary, `viaParam` answers `Alt`'s 2 where `Leaf`'s own provision
/// answered 1; handed `Leaf`'s, 1; with nothing handed the call takes the provider chosen at
/// load, `Leaf`'s.
#[test]
fn t13_a_call_uses_the_dictionary_its_operation_is_handed() {
    let body = "  operation viaParam(t: Tag[T = Leaf]) -> Int64 = Tag.tag(leaf(k: 0))
  operation handedAlt() -> Int64 = viaParam(alt())
  operation handedOwn() -> Int64 = viaParam(own())
  operation unhanded() -> Int64 = Tag.tag(leaf(k: 0))";
    answers("t13", TAG, body, &[("handedAlt", "2"), ("handedOwn", "1"), ("unhanded", "1")]);
}

/// At the parameter's member, `x: t.T`, which `t`'s type fixes at `Leaf`, and at its own
/// members, `t: Tag` with `x: t.T` (as before the stage).
#[test]
fn a_call_at_the_parameters_member_uses_it() {
    let body = "  operation viaMember(t: Tag[T = Leaf], x: t.T) -> Int64 = Tag.tag(x)
  operation viaOpen(t: Tag, x: t.T) -> Int64 = Tag.tag(x)
  operation member() -> Int64 = viaMember(alt(), leaf(k: 0))
  operation open() -> Int64 = viaOpen(alt(), leaf(k: 0))";
    answers("member", TAG, body, &[("member", "2"), ("open", "2")]);
}

/// At the operation's own type parameter: `f[X](t: Tag[T = X], x: X)` reads `t` at `X`.
/// Refused before the stage, "missing `requires Tag[T = …]`".
#[test]
fn a_call_at_the_operations_type_parameter_uses_it() {
    let body = "  operation f[X](t: Tag[T = X], x: X) -> Int64 = Tag.tag(x)
  operation go() -> Int64 = f(alt(), leaf(k: 0))";
    answers("rigid", TAG, body, &[("go", "2")]);
}

/// A bracket outranks the handed dictionary, in either direction, and names a provider with
/// constructors where nothing is handed too (refused before the stage, "a call may not select
/// one").
#[test]
fn a_bracket_outranks_the_handed_dictionary() {
    let body = "  operation viaLeaf(t: Tag[T = Leaf]) -> Int64 = Tag.tag[Tag = Leaf](leaf(k: 0))
  operation viaAlt(t: Tag[T = Leaf]) -> Int64 = Tag.tag[Tag = Alt](leaf(k: 0))
  operation leafOverAlt() -> Int64 = viaLeaf(alt())
  operation altOverLeaf() -> Int64 = viaAlt(own())
  operation bare() -> Int64 = Tag.tag[Tag = Leaf](leaf(k: 0))";
    answers("bracket", TAG, body, &[("leafOverAlt", "1"), ("altOverLeaf", "2"), ("bare", "1")]);
}

/// What a handed dictionary covers: a callee's clause (`sum2`'s `requires Additive[T = X]` at
/// `Meters`) and the operation's own `+`, each answered by `MetersTen`'s 10 where the default
/// adds; unhanded, the default answers 5.
#[test]
fn a_handed_dictionary_answers_a_callees_requirement() {
    let body = "  operation viaCallee(d: Additive[T = Meters], a: Meters, b: Meters) -> Meters = sum2(a, b)
  operation viaOp(d: Additive[T = Meters], a: Meters, b: Meters) -> Meters = a + b
  operation callee() -> Meters = viaCallee(ten(), m(v: 2), m(v: 3))
  operation op() -> Meters = viaOp(ten(), m(v: 2), m(v: 3))
  operation unhanded() -> Meters = m(v: 2) + m(v: 3)";
    answers(
        "callee",
        METERS,
        body,
        &[("callee", "m(v: 10)"), ("op", "m(v: 10)"), ("unhanded", "m(v: 5)")],
    );
}

/// Through its chain: `o: Strict[T = Big]` answers `Cmp.cmp` through `Strict provides Cmp[T =
/// T]`, at the call and at a callee's `requires Cmp[T = X]` — `BigRev`'s 1. Refused before the
/// stage, "ambiguous dispatch": two providers of `Cmp`, and nothing handed read.
#[test]
fn a_handed_dictionary_answers_through_its_chain() {
    let body = "  operation cmpO(o: Strict[T = Big]) -> Int64 = Cmp.cmp(big(n: 1), big(n: 2))
  operation cmp2[X](a: X, b: X) -> Int64 requires Cmp[T = X] = Cmp.cmp(a, b)
  operation viaCallee(o: Strict[T = Big]) -> Int64 = cmp2(big(n: 1), big(n: 2))
  operation direct() -> Int64 = cmpO(rev())
  operation callee() -> Int64 = viaCallee(rev())";
    answers("chain", STRICT, body, &[("direct", "1"), ("callee", "1")]);
}

// ── A call two handed dictionaries answer is refused ───────────────────────────────────────

#[test]
fn two_parameters_at_one_type_are_refused() {
    let body = "  operation two(a: Tag[T = Leaf], b: Tag[T = Leaf]) -> Int64 = Tag.tag(leaf(k: 0))";
    refused_tie("two", TAG, body, "Tag", "the parameter `a`", "the parameter `b`");
}

#[test]
fn a_parameter_beside_a_clause_is_refused() {
    let body = "  operation pc[X](a: Tag[T = X], x: X) -> Int64 requires Tag[T = X] = Tag.tag(x)";
    refused_tie("clause", TAG, body, "Tag", "the parameter `a`", "the clause `requires");
}

#[test]
fn a_lambdas_binder_beside_the_operations_parameter_is_refused() {
    let body = "  operation withLam(t: Tag[T = Leaf]) -> Int64 =
    let g = lambda (u: Tag[T = Leaf]) -> Tag.tag(leaf(k: 0))
    g(t)";
    refused_tie("lambda", TAG, body, "Tag", "the parameter `t`", "the lambda's parameter `u`");
}

/// `o: Strict[T = Big]` beside `w: Cmp[T = Big]`: both answer `Cmp.cmp`, one through its chain.
#[test]
fn a_dictionary_beside_one_its_chain_reaches_is_refused() {
    let body = "  operation both(o: Strict[T = Big], w: Cmp[T = Big]) -> Int64 = Cmp.cmp(big(n: 1), big(n: 2))";
    refused_tie("chainpair", STRICT, body, "Cmp", "the parameter `o`", "the parameter `w`");
}

#[test]
fn two_parameters_at_a_callees_requirement_are_refused() {
    let body = "  operation two(d: Additive[T = Meters], e: Additive[T = Meters], a: Meters, b: Meters) -> Meters = sum2(a, b)";
    refused_tie("calleetwo", METERS, body, "Additive", "the parameter `d`", "the parameter `e`");
}

// ── The back-out ledger (measured 2026-11-24, one optimized build, a temporary switch per part
// read at run time, over the whole of `anthill-core` — 11618 rows; the control, no switch, every
// row passed) ───────────────────────────────────────────────────────────────────────────────
//
// | part backed out | rows that fail |
// |---|---|
// | the entry at the types a parameter's type writes (`param_written_entry`) | 10: every row here but `a_bracket_outranks_the_handed_dictionary` |
// | the operation's own type parameter read in it, `<op>.X` | `a_call_at_the_operations_type_parameter_uses_it`, `a_parameter_beside_a_clause_is_refused` |
// | the tie at a call, for a sort with a parameter (`handed_dictionaries_at_call`) | `two_parameters_at_one_type_are_refused`, `a_parameter_beside_a_clause_is_refused`, `a_lambdas_binder_beside_the_operations_parameter_is_refused`, `a_dictionary_beside_one_its_chain_reaches_is_refused` |
// | the tie at a callee's requirement (`handed_dictionaries_for_dep`) | `two_parameters_at_a_callees_requirement_are_refused` |
// | a parameter's carried named slot counted as handed | `wi1094_named_slot_inference_test::a_nested_frame_supply_does_not_outrank_the_argument` |
// | one parameter one entry, in the advice of a call that names no instance (`sole_chain_entry_over_spec`) | `wi_2kv4y_unfixed_carrier_test::a_value_of_the_callees_own_spec_does_not_say_it_either` |
// | §4.4 check 3 restored, as WI-20260911-TX0G6 had it (a written witness with constructors refused everywhere, without CXR5B's narrowing) | 13: `a_bracket_outranks_the_handed_dictionary`; the eight rows this stage rewrote from check 3's refusals (`wi841…selecting_a_concrete_provider_names_it`, `wi870…a_concrete_provider_is_named_in_the_key_and_in_a_slot`, `wi_b6qya…a_named_requirement_slot_is_bound_and_selects`, `wi_cxr5b…a_bracket_where_a_value_decides_names_its_provider`, `wi_hzvqa` ×2, `wi_tx0g6…a_concrete_witness_is_selected_in_both_spellings`); and, the stand-in being the unnarrowed check, CXR5B's own rows (`wi_cxr5b` ×3, `wi843…a_tie_among_concrete_providers_where_no_value_decides_offers_the_bracket`, `wi_q2c01…a_provider_with_constructors_may_be_named`), which pass on the tree before the stage |
//
// Measured on the term carrier, before `/code-review` made the written-types entry
// carrier-neutral (it read a fixed binding off `Value::Term` alone: under
// `ANTHILL_TEST_NODE_CARRIER=1`, MEASURED on the CLI, T13 answered 1, `viaCallee` `m(v: 5)`, and
// two parameters at one type loaded); the parts are the same functions, and every row here
// passes on both carriers since.
//
// PASS EITHER WAY BY DESIGN: `a_bracket_outranks_the_handed_dictionary` under every part but the
// last — a bracket is read before any handed dictionary. Inside the rows, the unhanded calls
// (`unhanded`, `handedOwn`) answer what the provider chosen at load answers, as before the stage.
