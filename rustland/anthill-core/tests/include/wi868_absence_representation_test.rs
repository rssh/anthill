//! WI-868 — the two representations of "this slot has no evidence" stay SEPARATE,
//! and this file is the measurement the decision rests on.
//!
//! WI-857 left two: (a) `ResolvedRequiresNode::Unavailable` → an empty bundle over an
//! `anthill.reflect.NoProvider` marker, which `resolve_op_target_checked` refuses to
//! dispatch through; (b) `Interpreter::stand_in_requirement`, the host-entry stand-in,
//! whose sub-slots are markers but whose OWN functor is the parent sort. The ticket
//! proposed that moving the refusal to AFTER the WI-350/WI-822 value-directed rescue
//! would let ONE representation serve both, and asked for the builtin case to be
//! measured rather than assumed.
//!
//! It was, three ways — see [`Interpreter::stand_in_requirement`] for the decision and
//! the other two arms. THE ROW BELOW IS THE THIRD: with the refusal off the dispatch
//! path, a body that reads a marker slot to call a BUILTIN-backed spec op gets the
//! HOST's structural verdict for a requirement that has no provider at all, silently.

use anthill_core::eval::Value;

/// The shape that reaches a marker slot at all — and reaching one is HARDER than the
/// ticket assumes, which is itself part of the account.
///
/// TWO LOAD-TIME GATES refuse the obvious spellings, MEASURED:
///
///  * a CONCRETE carrier at the call site (`Holder.via(wrap(v: 5))` where `Holder
///    requires PartialEq[T]`) is refused by WI-1102's use-site discharge —
///    "`Wrap` provides no `anthill.prelude.PartialEq` — declare `provides …`";
///  * a provider whose spec's chain it does not cover (`WTop provides Top` where `Top
///    requires PartialEq`) is refused by `check_provider_requires` (WI-343/WI-356) —
///    "'WTop' provides 'Top', which requires 'PartialEq', but 'WTop' does not provide
///    'PartialEq'".
///
/// So the fixture needs the WI-865 template's RED HERRING — `provides PartialEq[T =
/// Int64]`, a provision at a binding this call never uses — to satisfy the
/// base-level existence check while leaving the goal the dictionary actually has,
/// `PartialEq[T = Wrap[E = Int64]]`, with no provider. That is the gap through which a
/// marker slot is minted, and it is where the refusal below is the only thing standing
/// between the program and a host answer.
const BUILTIN_READ: &str = r#"
namespace wi868.builtin
  import anthill.prelude.{Int64, Bool, PartialEq}

  enum Wrap
    import anthill.prelude.{Int64}
    sort E = ?
    entity wrap(v: E)
  end

  sort Top
    sort T = ?
    requires PartialEq[T = T]
    operation t(x: T) -> Int64
  end

  sort WTop
    sort E = ?
    provides Top[T = Wrap[E = E]]
    provides PartialEq[T = Int64]
    operation t(x: Wrap[E = E]) -> Int64 = 7
  end

  sort Holder
    sort T = ?
    requires Top[T]
    operation via(a: T, b: T) -> Bool = PartialEq.eq(a, b)
  end

  sort Driver
    operation same(n: Int64) -> Int64 = if Holder.via(wrap(v: 5), wrap(v: 5)) then 1 else 0
    operation diff(n: Int64) -> Int64 = if Holder.via(wrap(v: 5), wrap(v: 6)) then 1 else 0
  end
end
"#;

/// THE MEASUREMENT THE TICKET ASKED FOR. A builtin-backed spec op read through a
/// marker slot is REFUSED, naming the spec and the repair — and it has to be refused
/// HERE, at `resolve_op_target_checked`, because there is nothing downstream to refuse
/// it: the value-directed rescue is what runs next, and for a builtin the fall-through
/// IS the host default.
///
/// MEASURED with the refusal removed from `dispatch_via_sort_ops_table` (the ticket's
/// proposed move):
///
/// ```text
///   Driver.same  ->  Ok(Int(1))
///   Driver.diff  ->  Ok(Int(0))
/// ```
///
/// A full structural verdict for `PartialEq[Wrap[E = Int64]]`, which NOTHING provides.
/// BOTH POLARITIES, deliberately: `eq(x, x)` alone proves little, because reflexivity
/// can be answered before dispatch — `diff` is the row that shows the host's `eq`
/// actually compared two distinct values and decided.
///
/// The two rows below are the same program under the refusal that ships. They are the
/// CONTROL for the numbers above, and the tripwire for a future attempt at the merge.
#[test]
fn wi868_a_builtin_read_through_a_marker_slot_is_refused() {
    for entry in ["same", "diff"] {
        // A FRESH interpreter per row — a trapped call poisons later calls.
        let mut interp = crate::common::interp_for(BUILTIN_READ);
        let err = match interp.call(&format!("wi868.builtin.Driver.{entry}"), &[Value::Int(0)]) {
            Err(e) => format!("{e}"),
            Ok(v) => panic!(
                "`Driver.{entry}` must not answer: nothing provides `PartialEq` at this \
                 dictionary's bindings, so a value here is the HOST deciding \
                 structurally for a requirement the program never satisfied. Got {v:?}",
            ),
        };
        assert!(
            err.contains("anthill.prelude.PartialEq.eq") && err.contains("pins no provider"),
            "the refusal must name the op it would not dispatch and say why; got: {err}",
        );
        assert!(
            err.contains("Declare a provider"),
            "…and the repair, which is WI-865's payload doing its work; got: {err}",
        );
    }
}
