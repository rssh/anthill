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
//! the other two arms. THE ROWS BELOW ARE THE THIRD: with the refusal off the dispatch
//! path, a body that reads a marker slot to call a BUILTIN-backed spec op gets the
//! HOST's structural verdict for a requirement that has no provider at all, silently.
//!
//! WI-20260925-4ZZKZ CLOSED THE LOAD-TIME ROUTE to such a slot: the resolver no longer
//! records a spec half absent, and the provision that let one arise is refused at load
//! (`a_marker_slot_is_no_longer_minted_at_load`). The refusal at the read is still the
//! only thing between a builtin and the host default for the markers that remain — the
//! RUN-time producers, of which the host-entry stand-in is the one a program reaches
//! without a rule body (`a_builtin_read_through_a_host_entry_marker_is_refused`).

use anthill_core::eval::Value;

/// The shape that reached a load-time marker slot, before WI-20260925-4ZZKZ — and
/// reaching one was HARDER than WI-868 assumed, which is itself part of the account.
///
/// TWO LOAD-TIME GATES refused the obvious spellings, MEASURED then:
///
///  * a CONCRETE carrier at the call site (`Holder.via(wrap(v: 5))` where `Holder
///    requires PartialEq[T]`) is refused by WI-1102's use-site discharge;
///  * a provider whose spec's chain it does not cover (`WTop provides Top` where `Top
///    requires PartialEq`) is refused by `check_provider_requires` (WI-343/WI-356).
///
/// So the fixture needed the WI-865 template's RED HERRING — `provides PartialEq[T =
/// Int64]`, a provision at a binding this call never uses — to satisfy the check's
/// base-level fallback while leaving `PartialEq[T = Wrap[E = Int64]]` with no provider.
/// That fallback is gone: the check resolves `PartialEq[T = Wrap[E = WTop.E]]` itself.
const BUILTIN_READ: &str = r#"
namespace wi868.builtin
  import anthill.prelude.{Int64, Bool, PartialEq}

  -- `opaque`'s FUNCTION field keeps `Wrap` out of WI-20260918-CKD4J's derivation, which
  -- would otherwise give it `provides PartialEq[Wrap] :- PartialEq[E]` and so a provider
  -- at `Wrap[E = Int64]` — the absence this fixture is built on. A function has no
  -- equality, so no row is derived and `PartialEq[Wrap[E = Int64]]` stays unprovided.
  enum Wrap
    import anthill.prelude.{Int64, Function}
    sort E = ?
    entity wrap(v: E)
    entity opaque(f: Function[A = Int64, B = Int64])
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

end
"#;

/// THE GAP IS CLOSED: the program that minted a marker slot at load is refused there.
///
/// CONTROL (MEASURED): restore `check_provider_requires`' base-level fallback and this
/// loads clean (the red herring answers it) — the premise the row below used to rest on.
/// The host-entry row passes either way by design: it is the channel that remains.
#[test]
fn a_marker_slot_is_no_longer_minted_at_load() {
    let errs = crate::common::try_load_kb_with(BUILTIN_READ)
        .err()
        .expect("`WTop provides Top` needs `PartialEq[Wrap[E]]`, which nothing provides");
    assert!(
        errs.iter().any(|e| e.contains(
            "'wi868.builtin.WTop' provides 'wi868.builtin.Top', which requires \
             'anthill.prelude.PartialEq'"
        )),
        "the refusal names the provision and the requirement: {errs:?}",
    );
}

/// The same program made SOUND — `Wrap` gets its own `PartialEq`, and `WTop`'s provision
/// is conditioned on its element's — so it loads, and the only marker left is the one a
/// HOST ENTRY installs: `Holder.via` entered directly, with no dictionary supplied.
const BUILTIN_READ_SOUND: &str = r#"
namespace wi868.sound
  import anthill.prelude.{Int64, Bool, PartialEq}

  enum Wrap
    import anthill.prelude.{Int64, Bool, PartialEq}
    sort E = ?
    entity wrap(v: E)
    provides PartialEq[T = Wrap] :- PartialEq[E]
    operation eq(a: Wrap, b: Wrap) -> Bool = true
  end

  sort Top
    sort T = ?
    requires PartialEq[T = T]
    operation t(x: T) -> Int64
  end

  sort WTop
    sort E = ?
    provides Top[T = Wrap[E = E]] :- PartialEq[E]
    operation t(x: Wrap[E = E]) -> Int64 = 7
  end

  sort Holder
    sort T = ?
    requires Top[T]
    operation via(a: T, b: T) -> Bool = PartialEq.eq(a, b)
  end
end
"#;

/// THE MEASUREMENT THE TICKET ASKED FOR. A builtin-backed spec op read through a
/// marker slot is REFUSED, naming the op and the entry — and it has to be refused HERE,
/// at `resolve_op_target_checked`, because there is nothing downstream to refuse it: the
/// value-directed rescue is what runs next, and for a builtin the fall-through IS the
/// host default.
///
/// CONTROL (MEASURED, WI-20260925-4ZZKZ): make `marker_refusal` accept every marker and
/// this row fails on its first pair — `Holder.via(5, 5)` answers `Bool(true)`, the host's
/// structural verdict for a `PartialEq` nothing supplied. (WI-868 measured the same
/// silence on the load-time marker this file used to reach, both polarities.) BOTH
/// POLARITIES are driven, deliberately: `eq(x, x)` alone proves little, because
/// reflexivity can be answered before dispatch — the distinct pair is the row that shows
/// the host's `eq` actually compared two values and decided. The values are passed bare,
/// as the host would: the slot is read before either is inspected.
#[test]
fn a_builtin_read_through_a_host_entry_marker_is_refused() {
    for (v1, v2) in [(5, 5), (5, 6)] {
        // A FRESH interpreter per row — a trapped call poisons later calls.
        let mut interp = crate::common::interp_for(BUILTIN_READ_SOUND);
        let err = match interp.call("wi868.sound.Holder.via", &[Value::Int(v1), Value::Int(v2)])
        {
            Err(e) => format!("{e}"),
            Ok(v) => panic!(
                "`Holder.via({v1}, {v2})` must not answer: the host supplied no `Top` \
                 dictionary, so a value here is decided by nothing the program provided. \
                 Got {v:?}",
            ),
        };
        assert!(
            err.contains("anthill.prelude.PartialEq.eq") && err.contains("pins no provider"),
            "the refusal must name the op it would not dispatch and say why; got: {err}",
        );
        assert!(
            err.contains("host entry point"),
            "…and blame the entry, which is WI-865's payload doing its work; got: {err}",
        );
    }
}
