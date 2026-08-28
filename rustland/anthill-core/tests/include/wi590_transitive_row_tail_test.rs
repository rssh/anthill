//! WI-590 — a carrier parameter inside an EFFECT ROW is spelled as the row's `Var` tail, not
//! as a `Ref` to the parameter symbol, and the provider-view substitution only read the
//! second spelling.
//!
//! `substitute_carrier_params` grounds a provision binding by walking it to its leaves and
//! replacing each carrier parameter with the receiver's type-arg, identifying a leaf via
//! `typaram_ref_vid` — which reads `Ref(symbol)`. That is how a parameter appears in a
//! TYPE-ARGUMENT slot. Inside a row it appears as the bare `Var(Global(vid))` the row's tail
//! carries (`{ES}` lowers to `open[tail = Var]`, the tail anonymous — its name is `_`). So a
//! row-valued binding substituted NOTHING, stayed non-ground, and the spec's row leaked `?_`.
//!
//! WHERE IT BITES: a TWO-HOP provision. One hop writes the row directly and grounds through
//! the ordinary path; two hops compose the views, and the composed row is expressed in the
//! CARRIER's own parameter vars — correctly, as it turns out. Measured while composing:
//! the composed `Element` came out as the carrier's own `T` (so composition itself works)
//! and only the row's tails went unresolved. `recv_bindings` is keyed by exactly those
//! VarIds, so matching the tail's vid against it is both exact and name-free.
//!
//! CONTROL: `control_one_hop_direct_provision` uses the same sorts with a single hop and
//! passes with the change backed out. Backing out means deleting the `Term::Var(Var::Global)`
//! arm from `substitute_carrier_params`; MEASURED, both `two_hop_*` cases then fail with
//! `undeclared effect: ?_` and the control stays green.

fn source(drive: &str) -> String {
    format!(
        r#"
namespace wi590row
  import anthill.prelude.{{Int64}}

  -- The OUTER spec, carrier-param.
  sort Iter
    sort C = ?
    sort Element = ?
    effects E = ?
    operation iter(c: C) -> Element effects E
  end

  -- The INTERMEDIATE: provides Iter, and is itself provided by the carrier below.
  sort Str
    import wi590row.Iter
    sort T = ?
    effects E = ?
    operation split(s: Str) -> T effects E
    provides Iter[C = Str, Element = T, E = E]
    operation iter(s: Str) -> T effects E = split(s)
  end

  -- The CARRIER. Its provided row is a UNION of its own two row params, so the composed
  -- Iter row reaches the substitution as a compound whose leaves are row tails.
  sort Wrap
    import wi590row.{{Str}}
    sort T = ?
    effects ES = ?
    effects EF = ?
    entity wrap(v: T)
    provides Str[T = T, E = {{ES, EF}}]
    operation split(w: Wrap) -> T effects {{ES, EF}} =
      match w
        case wrap(v) -> v
  end

  operation consume(x: Int64) -> Int64 = x
{drive}
end
"#
    )
}

fn expect_loads(name: &str, src: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{name} must load clean; got {} error(s):\n{}", errs.len(), errs.join("\n"));
    }
}

/// DRIVES THE FIX — two hops (`Wrap` -> `Str` -> `Iter`), so `Iter.E` is reached only by
/// composing the two provisions, and the composed row's leaves are the carrier's row-tail
/// vars. RED when backed out.
#[test]
fn two_hop_provision_grounds_a_row_valued_binding() {
    expect_loads(
        "two-hop, ascribed",
        &source("  operation a(w: Wrap[T = Int64, ES = {}, EF = {}]) -> Int64 effects {} =\n    Iter.iter(w)"),
    );
}

/// DRIVES THE FIX — the same call with its result flowing into another, so nothing at the
/// use site can pin the row either. RED when backed out.
#[test]
fn two_hop_provision_grounds_an_unascribed_result() {
    expect_loads(
        "two-hop, result consumed",
        &source("  operation b(w: Wrap[T = Int64, ES = {}, EF = {}]) -> Int64 effects {} =\n    consume(Iter.iter(w))"),
    );
}

/// CONTROL — ONE hop: the intermediate's own op on the same receiver. The provision is read
/// directly rather than composed, so it never needed the row-tail spelling. Green either way.
#[test]
fn control_one_hop_direct_provision() {
    expect_loads(
        "one-hop control",
        &source("  operation c(w: Wrap[T = Int64, ES = {}, EF = {}]) -> Int64 effects {} =\n    Str.split(w)"),
    );
}
