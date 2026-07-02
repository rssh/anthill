//! WI-278 — method-call (dot) syntax, end to end.
//!
//! The structural pieces (the `DotApply` occurrence, the converter's
//! value-receiver routing, the typer-phase dispatch, requirement threading)
//! land in the dependency cluster WI-279/280/281/282. This file pins the
//! *headline* WI-278 acceptance the cluster did not, on its own, exercise: a
//! real combinator chain `xs.map(f).filter(p)` that
//!
//!   1. dispatches `map`/`filter` with NO import of the operation. POST-WI-588
//!      (finiteness Phase B): on a `List` these now resolve to
//!      `FiniteCollection.map`/`filter` (List provides FiniteCollection at
//!      provision-graph depth 1, beating `Iterable` at depth 2), producing the
//!      FINITE carriers `FiniteMappedStream` / `FiniteFilteredStream`. (Before
//!      Phase B they resolved to the lazy `Iterable.map` → `mapped`/`filtered`;
//!      the lazy carriers are still reached on a genuinely-infinite bare Stream.)
//!   2. INFERS the method's type parameters (`map`'s `Dst` from the callback,
//!      the receiver's element type from the receiver) — proposal 043 §6.6;
//!   3. EVALUATES: the dispatched chain runs through the real finite
//!      `fmapped` / `ffiltered` carriers and produces the right elements.
//!
//! Regression context: the chain originally type-failed not in the dot path
//! but in the effect-row algebra — the lazy combinators' result row
//! `{E, EffP}` unions List's iterable `E` (bound *bare*) with the callback's
//! `EffP` (bound to a *wrapped* `effects_rows(empty_row)`), and
//! `decompose_effect_row` hard-rejected the wrapped tail mid-walk. The fix
//! unwraps a nested `EffectsRows` wrapper during decomposition.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::parse;

/// Load full stdlib + Rust host bindings + `extra`; return load (typer) errors.
fn load_errs(extra: &str) -> Vec<LoadError> {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).err().unwrap_or_default()
}

fn fmt(errs: &[LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

// ── (1)+(2) Type-check: the headline chain dispatches and infers ────────

#[test]
fn headline_map_filter_chain_type_checks() {
    // `xs.map(f).filter(p)`: on a `List`, `.map`/`.filter` dispatch to the FINITE
    // ops (WI-588 coherence: List provides FiniteCollection at depth 1, beating
    // Iterable), and the WI-599 thin design returns a `FiniteCollection`. So the
    // chain is consumed by `.size()` (a FiniteCollection consumer) — this pins that
    // the whole chain type-checked and stays finite. Inline lambdas in dot-arg
    // position resolve their params (distinct from the WI-605 op-body-arg gap).
    let src = r#"
namespace wi278.chain
  import anthill.prelude.{List, Int64, Bool}

  operation run(xs: List[T = Int64]) -> Int64 =
    xs.map(lambda x -> x + 1).filter(lambda x -> x > 0).size()
end
"#;
    let errs = load_errs(src);
    assert!(errs.is_empty(), "headline chain should type-check:\n{}", fmt(&errs));
}

#[test]
fn map_infers_dst_from_callback() {
    // `map`'s `Dst` is inferred from the callback's result type, not the receiver's
    // element type: a `(Int64) -> Bool` callback makes the mapped element `Bool`.
    // WI-599: `.map` on a List returns a `FiniteCollection[Element = Bool]`;
    // `collect` materializes it as a `List[T = Bool]`, so the declared
    // `List[T = Bool]` return only type-checks if `Dst` was inferred as `Bool`.
    let src = r#"
namespace wi278.infer
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.FiniteCollection.{collect}

  operation run(xs: List[T = Int64]) -> List[T = Bool] =
    collect(xs.map(lambda x -> x > 0))
end
"#;
    let errs = load_errs(src);
    assert!(errs.is_empty(), "map should infer Dst = Bool from the callback:\n{}", fmt(&errs));
}

#[test]
fn map_wrong_inferred_element_is_rejected() {
    // Soundness twin of the previous test: a `(Int64) -> Bool` callback yields
    // `Stream[Bool, _]`, which must NOT satisfy a declared `Stream[Int64, {}]`
    // return — the inferred `Dst` is checked, not rubber-stamped.
    let src = r#"
namespace wi278.infer_neg
  import anthill.prelude.{List, Int64, Bool, Stream}

  operation run(xs: List[T = Int64]) -> Stream[Int64, {}] =
    xs.map(lambda x -> x > 0)
end
"#;
    let errs = load_errs(src);
    assert!(!errs.is_empty(),
        "a Stream[Bool] map result must not satisfy a Stream[Int64] return");
    // Pin the REASON: it must be the return-type element mismatch (Bool vs
    // Int64), not some unrelated parse/import/effect failure — otherwise the
    // test would rubber-stamp any error and miss a real inference regression.
    let text = fmt(&errs);
    assert!(text.contains("run.return") && text.contains("Bool"),
        "expected a return-type element mismatch naming Bool; got:\n{text}");
}

// ── (3) Eval: the dispatched chain runs through the lazy carriers ────────

const EVAL_SRC: &str = r#"
namespace wi278.eval
  import anthill.prelude.{List, Int64, Stream, Bool}
  import anthill.prelude.List.{nil, cons}
  -- WI-588: `.map`/`.filter` on a List now produce FINITE carriers
  -- (FiniteMappedStream/FiniteFilteredStream), so the chain is a FiniteStream.
  -- Consume it via FiniteCollection's `collect`/`foldLeft` (effect = the sort
  -- param `E`, grounded by the provision) rather than Stream's (effect = the
  -- projection `s.E`, which does not ground through the 2-hop transitive provision
  -- FiniteFilteredStream → FiniteStream → Stream).
  import anthill.prelude.FiniteCollection.{foldLeft}

  operation inc(n: Int64) -> Int64 = n + 1
  operation is_big(n: Int64) -> Bool = n > 2
  operation addp(a: Int64, b: Int64) -> Int64 = a + b
  -- positional encode via foldLeft: [a,b,c] -> a*100+b*10+c (left-to-right shift),
  -- so the SAME 345 acceptance is preserved while consuming the chain with the
  -- finite eager `foldLeft` (whose sort-param effect grounds through the dot
  -- chain's abstract FiniteStream result; the body-less `collect` primitive does
  -- not dispatch on an abstract spec value — a narrow follow-up gap).
  operation shift(acc: Int64, x: Int64) -> Int64 = acc * 10 + x

  -- [1,2,3,4] -.map(inc)-> [2,3,4,5] -.filter(>2)-> [3,4,5].
  -- Receiver is a list literal (a value); both methods dispatch by sort,
  -- no import of map/filter. foldLeft forces the finite chain → [3,4,5] → 345.
  operation chain_literal() -> Int64 =
    foldLeft([1, 2, 3, 4].map(inc).filter(is_big), 0, shift)

  -- Same chain on a param receiver; folded → 3+4+5 = 12.
  operation chain_param_sum(xs: List[T = Int64]) -> Int64 =
    foldLeft(xs.map(inc).filter(is_big), 0, addp)

  operation mk_list() -> List[T = Int64] = [1, 2, 3, 4]

  -- Receiver is a let-bound local (WI-280 value receiver) → [3,4,5] → 345.
  operation chain_let() -> Int64 =
    let xs = [1, 2, 3, 4]
    foldLeft(xs.map(inc).filter(is_big), 0, shift)

  -- Predicate rejects everything: [1,2] -.map(inc)-> [2,3] -.filter(>9)-> [].
  -- Forces the finite filter's drop-everything self-recursion to terminate at the
  -- empty stream → fold of [] → 0.
  operation chain_empty() -> Int64 =
    foldLeft([1, 2].map(inc).filter(is_huge), 0, shift)

  operation is_huge(n: Int64) -> Bool = n > 9
end
"#;

#[test]
fn dot_chain_evaluates_on_literal_receiver() {
    let mut interp = crate::common::interp_for(EVAL_SRC);
    let got = interp.call("wi278.eval.chain_literal", &[])
        .unwrap_or_else(|e| panic!("call chain_literal: {e:?}"));
    assert_eq!(expect_int(got), 345);
}

#[test]
fn dot_chain_evaluates_on_param_receiver() {
    // Build the `[1,2,3,4]` argument inside anthill (a sibling op), then feed it
    // to `chain_param_sum` so the receiver reaches dispatch as an operation
    // PARAM value — the WI-280 bare-identifier value-receiver path.
    let mut interp = crate::common::interp_for(EVAL_SRC);
    let arg = interp.call("wi278.eval.mk_list", &[]).expect("build arg list");
    let got = interp.call("wi278.eval.chain_param_sum", &[arg])
        .unwrap_or_else(|e| panic!("call chain_param_sum: {e:?}"));
    assert_eq!(expect_int(got), 12);
}

#[test]
fn dot_chain_evaluates_on_let_receiver() {
    let mut interp = crate::common::interp_for(EVAL_SRC);
    let got = interp.call("wi278.eval.chain_let", &[])
        .unwrap_or_else(|e| panic!("call chain_let: {e:?}"));
    assert_eq!(expect_int(got), 345);
}

#[test]
fn dot_chain_evaluates_to_empty_when_all_filtered() {
    let mut interp = crate::common::interp_for(EVAL_SRC);
    let got = interp.call("wi278.eval.chain_empty", &[])
        .unwrap_or_else(|e| panic!("call chain_empty: {e:?}"));
    assert_eq!(expect_int(got), 0);
}
