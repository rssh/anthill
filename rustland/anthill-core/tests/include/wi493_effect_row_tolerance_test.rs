//! WI-493 — ONE shared bare-vs-wrapped effect-row tolerance.
//!
//! A row tail can be bound to EITHER a bare `EffectExpression` (the canonical
//! `bind_row_tail` shape, and a `provides … E = {}` fact's binding) OR a WRAPPED
//! `effects_rows(…)` (a written / provided `E` row bound whole onto the tail var
//! across unify / subtype / provider admissibility). A two-combinator chain
//! `xs.map(f).filter(p)` mixes both: `filter`'s source-effect param binds to
//! `map`'s whole provided `{ES, EF}` row (wrapped), unioned with a bare tail —
//! so `decompose_effect_row` walks a `merge(open(bare), open(wrapped))`.
//!
//! WI-278 first patched this inline in `decompose_effect_row`. WI-493 (user
//! decision: consolidate, don't chase every producer) routes EVERY row-tail
//! walker — `decompose_effect_row` (top-level + mid-walk), `row_inner_value` (the
//! multi-tail arm), and `effects_rows_to_flat_list` — through ONE shared
//! `effects_rows_inner` unwrap, so a new row consumer cannot drift into
//! mis-decomposing a wrapped tail. This test pins the end-to-end chain (the
//! scenario the tolerance exists for) type-checking AND evaluating.

use anthill_core::eval::Value;

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

const SRC: &str = r#"
namespace wi493.chain
  import anthill.prelude.{List, Int64, Stream, Bool}
  import anthill.prelude.Stream.foldLeft

  operation inc(n: Int64) -> Int64 = n + 1
  operation is_big(n: Int64) -> Bool = n > 2
  operation addp(a: Int64, b: Int64) -> Int64 = a + b

  operation mk_list() -> List[T = Int64] = [1, 2, 3, 4]

  -- map THEN filter: the mapped stream's whole `{ES, EF}` row binds (wrapped)
  -- into the filtered stream's source-effect param, unioned with filter's own
  -- (bare) tail — the bare-vs-wrapped mixed row WI-493 consolidates the unwrap of.
  -- [1,2,3,4] -map(+1)-> [2,3,4,5] -filter(>2)-> [3,4,5] -sum-> 12.
  operation map_then_filter_sum(xs: List[T = Int64]) -> Int64 =
    foldLeft(xs.map(inc).filter(is_big), 0, addp)
end
"#;

/// The chain type-checks (load-clean, no leaked `undeclared effect: {merge[…]}`)
/// AND evaluates — proving the consolidated tolerance decomposes the mixed
/// bare/wrapped row correctly.
#[test]
fn map_then_filter_chain_type_checks_and_evaluates() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp.call("wi493.chain.mk_list", &[]).expect("build list");
    let got = interp
        .call("wi493.chain.map_then_filter_sum", &[xs])
        .unwrap_or_else(|e| panic!("call map_then_filter_sum: {e:?}"));
    assert_eq!(expect_int(got), 12);
}
