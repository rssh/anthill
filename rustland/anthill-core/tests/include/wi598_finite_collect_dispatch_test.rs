//! WI-598 (finiteness, proposal library/003): a body-less `FiniteCollection`
//! primitive (`collect`) must DISPATCH on a value whose STATIC type is an
//! abstract spec that PROVIDES + DEFINES it.
//!
//! WHEN THIS WAS WRITTEN, `xs.map(f)` / `xs.filter(p)` returned the abstract
//! `FiniteStream` — the finite combinators' declared return. `FiniteStream provides
//! FiniteCollection` AND defines its own `collect` (the well-founded drain). A
//! DIRECT `collect(xs.map(f))` raised `FiniteCollection.collect.dispatch: no impl
//! matches per-call bindings` — so a finite dot-chain could only be consumed via
//! the DEFAULTED ops (`size` / `foldLeft`, whose bodies call `collect` on the
//! spec's own `C` param through WI-365 self-typing). This pins the DIRECT form.
//!
//! WI-590 changed what those chains RETURN — the concrete `mapped`/`filtered`
//! carrier, whose `collect` comes from a finiteness witness — so these rows no
//! longer reach through an abstract-spec receiver. They still pin the DIRECT form
//! end to end, which is the acceptance; the abstract-`FiniteStream` receiver the
//! deferral was written for now arrives from a declared `FiniteStream` return
//! (`anthill.realization.Dictionary.ops`) rather than from `map`/`filter`.

use anthill_core::eval::{Interpreter, Value};

fn run_int(interp: &mut Interpreter, op: &str) -> i64 {
    match interp
        .call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
    {
        Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// Direct `collect` on the finite dot-chain's result (an abstract `FiniteStream`
/// when written, the concrete combinator carrier since WI-590)
/// type-checks and EVALs: `collect(map([1,2,3,4], inc))` materializes `[2,3,4,5]`
/// (length 4), `collect(filter([1,2,3,4], is_big))` materializes `[3,4]` (2).
#[test]
fn collect_on_finite_map_chain_eval() {
    let src = r#"
namespace test.wi598.list
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.FiniteCollection.{map, filter, collect}

  operation inc(n: Int64) -> Int64 = n + 1
  operation is_big(n: Int64) -> Bool = n > 2

  operation map_collect_len() -> Int64 = List.length(collect(map([1, 2, 3, 4], inc)))
  operation filter_collect_len() -> Int64 = List.length(collect(filter([1, 2, 3, 4], is_big)))
  operation chain_collect_len() -> Int64 =
    List.length(collect(map(filter([1, 2, 3, 4], is_big), inc)))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi598.list.map_collect_len"), 4);
    assert_eq!(
        run_int(&mut interp, "test.wi598.list.filter_collect_len"),
        2
    );
    assert_eq!(run_int(&mut interp, "test.wi598.list.chain_collect_len"), 2);
}

/// The NATURAL dot-chain form the ticket motivates: `xs.map(f).collect()`. The
/// `.collect()` member dispatches by short name on the chain's receiver and must
/// land on `FiniteCollection.collect` (whose access effect is
/// the sort-param `E`, which grounds), NOT `Stream.collect` (whose `s.E`
/// projection effect does not ground through the 2-hop transitive provision) —
/// so the fully-dotted pipeline stays consumable end to end.
#[test]
fn dot_collect_on_finite_chain_eval() {
    let src = r#"
namespace test.wi598.dot
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.FiniteCollection.{map, filter, collect}

  operation inc(n: Int64) -> Int64 = n + 1
  operation is_big(n: Int64) -> Bool = n > 2

  -- prefix `collect` over a dot-built chain
  operation prefix_over_dot() -> Int64 = List.length(collect([1, 2, 3, 4].map(inc)))
  -- fully-dotted: `.map(inc).collect()`
  operation fully_dotted() -> Int64 = List.length([1, 2, 3, 4].map(inc).collect())
  -- fully-dotted with a filter hop: [1,2,3,4] -filter(>2)-> [3,4] -> len 2
  operation dotted_filter() -> Int64 = List.length([1, 2, 3, 4].filter(is_big).collect())
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi598.dot.prefix_over_dot"), 4);
    assert_eq!(run_int(&mut interp, "test.wi598.dot.fully_dotted"), 4);
    assert_eq!(run_int(&mut interp, "test.wi598.dot.dotted_filter"), 2);
}
