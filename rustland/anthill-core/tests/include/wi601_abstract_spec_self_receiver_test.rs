//! WI-601 (finiteness, typer ALTITUDE follow-up to WI-598): unify the
//! abstract-spec-carrier deferral across BOTH dispatch shapes.
//!
//! WI-598 taught the CARRIER-PARAM path (`FiniteCollection.collect(c)`) to defer
//! when the receiver's carrier sort is itself an abstract spec
//! (`carrier_is_abstract_spec`). The SELF-RECEIVER path (`receiver_carrier`)
//! still classified such a carrier `Concrete` by the narrow `base == spec_sort`
//! test — so a body-less BARE-`Stream` self-receiver op (`headOption` / `tail` /
//! the qualified `Stream.splitFirst`) called on a `FiniteStream`-typed value
//! concrete-dispatched into `FiniteStream provides Stream → Stream requires
//! EffectsRuntime[E]`, unsatisfiable at the abstract access row `E` → a spurious
//! `DispatchNoMatch` / `MissingRequiresForSpecOp` on the enclosing op.
//!
//! WI-601 funnels both shapes through the one `carrier_is_abstract_spec` notion:
//! `receiver_carrier` now returns `Abstract` for an abstract-interface carrier
//! distinct from the op's spec, so the self-receiver path defers to eval's
//! value-directed dispatch exactly as the carrier-param path does. Concrete
//! carriers (`List`/`Map` — they have constructors, so `carrier_is_abstract_spec`
//! is false) stay `Concrete` and dispatch as before (the whole suite screens it).

use anthill_core::eval::{Interpreter, Value};

fn run_int(interp: &mut Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// The fix, end to end. `interp_for` fully LOADS (parses + types) the source, so
/// the three GENERIC consumers over an ABSTRACT `FiniteStream` (element `T` and
/// access row `E` both abstract) — each calling a body-less bare-`Stream`
/// self-receiver op NOT reachable as a concrete impl on `FiniteStream` — must
/// TYPECHECK. Before WI-601 each raised `MissingRequiresForSpecOp` on the
/// abstract `E` (the self-receiver path pinned `FiniteStream` as a concrete
/// carrier and demanded a `requires Stream[…]`); WI-601 defers instead.
///
/// - `g_headOption` / `g_tail`: at WI-601 time `headOption` / `tail` were
///   law-only (no body); WI-818 gave them default bodies over `splitFirst`.
///   The load-time deferral these consumers pin is unchanged — the receiver is
///   an abstract `FiniteStream` either way. Loading them IS the assertion
///   (`g_tail` now also declares the guarded `Error[EmptyStream]` that
///   WI-818's `tail` row carries).
/// - `g_split`: the QUALIFIED `Stream.splitFirst` (`spec_sort = Stream`, forced
///   over the `FiniteStream` override) — the SAME deferral, but `splitFirst` has
///   a concrete body on the runtime carrier, so it also EVALS: `ev_head` passes a
///   concrete `FiniteStream` (a plain `List`, which provides FiniteStream) and
///   value-directed dispatch peels the first element `1`. This is the "defers to
///   eval value-directed dispatch" half of the acceptance. (Pre-WI-599 the witness
///   was `map([..], inc)`, which then built a FiniteStream-providing carrier; the
///   thin `FiniteCollection.map` now returns a `FiniteCollection`, so a bare List
///   is the FiniteStream witness.)
#[test]
fn bare_stream_op_on_abstract_finite_stream_defers_and_evals() {
    let src = r#"
namespace test.wi601
  import anthill.prelude.{FiniteStream, Stream, Option, Pair, List, Int64, EmptyStream}
  import anthill.prelude.Stream.{headOption, tail}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  -- GENERIC consumers over an abstract FiniteStream — the fix's load-time core.
  -- `headOption` / `tail` are body-less bare-Stream ops NOT overridden by
  -- FiniteStream; the receiver `fs` is a FiniteStream (an abstract spec that
  -- provides Stream). Both defer to value-directed dispatch instead of erroring.
  operation g_headOption[T](fs: FiniteStream[T = T]) -> Option[T] effects fs.E =
    headOption(fs)
  -- WI-818: `tail` now declares the guarded `Error[EmptyStream]` (tail of an
  -- empty stream is partial), and the guard is not statically refutable on an
  -- abstract receiver — so this generic consumer declares the label.
  operation g_tail[T](fs: FiniteStream[T = T]) -> Stream[T = T, E = fs.E]
    effects { fs.E, Error[EmptyStream] } =
    tail(fs)

  -- The evaluable witness: the QUALIFIED bare-Stream `splitFirst` (spec_sort =
  -- Stream), forced over the FiniteStream override, on an abstract FiniteStream.
  -- Same deferral as above, but `splitFirst` has a concrete body on the runtime
  -- carrier, so this arm EVALS.
  operation g_split[T](fs: FiniteStream[T = T])
    -> Option[Pair[A = T, B = Stream[T = T, E = fs.E]]] effects fs.E =
    Stream.splitFirst(fs)

  -- eval caller: pass a CONCRETE FiniteStream (a plain List provides FiniteStream);
  -- value-directed dispatch resolves splitFirst on it; first elem = 1.
  operation ev_head() -> Int64 =
    match g_split([1, 2, 3, 4])
      case some(pair(h, rest)) -> h
      case none() -> 0
end
"#;
    // interp_for panics if load/typecheck fails — so reaching eval proves all
    // three generic consumers (headOption, tail, Stream.splitFirst) typechecked.
    let mut interp = crate::common::interp_for(src);
    // The deferral routes to eval's value-directed dispatch: splitFirst peels
    // the first List element = 1.
    assert_eq!(run_int(&mut interp, "test.wi601.ev_head"), 1);
}
