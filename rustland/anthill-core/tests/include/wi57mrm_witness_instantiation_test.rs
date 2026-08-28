//! WI-20260828-57MRM — a WITNESS provision's head is a TEMPLATE over the witness sort's own
//! binder, and dispatching through it must INSTANTIATE that template against the receiver.
//!
//! A witness keys its carrier as an APPLICATION and writes the head's other bindings in its
//! OWN variables:
//!
//! ```text
//! fact Box[C = Wrap[Source = S, T = T, ES = ES, EF = EF], Element = T, E = {ES, EF}]
//! ```
//!
//! `Element` and `E` are the WITNESS's `T`/`ES`/`EF`, not `Wrap`'s. The grounding path read
//! each binding leaf-by-leaf and resolved it against the CARRIER by short name
//! (`typaram_ref_vid`), which is the wrong namespace — so a binding grounded only when
//! witness and carrier happened to spell the parameter identically, and never when the leaf
//! was a row variable. The fix matches the fact's CARRIER BINDING against the receiver's type
//! to obtain σ over the witness's parameters, then applies σ to the rest of the head.
//!
//! ONE PARAMETER, TWO SPELLINGS — this is what defeated the leaf-by-leaf read, and why σ is
//! keyed on the witness's VarId. In a type-argument slot a witness parameter is a
//! `Ref(symbol)` (`Wrap[ES = ES]`); inside an effect ROW the same parameter is the bare
//! `Var(Global(vid))` a row tail carries (`{ES, EF}` lowers to
//! `merge[open[tail = Var], open[tail = Var]]`, both tails anonymous). MEASURED on this
//! fixture: the witness sort's parameters are `ES → Var(Global 120)`, `EF → Var(Global 121)`
//! and those are exactly the two row tails, so the identity was present all along — only the
//! reader was looking it up the wrong way.
//!
//! WHICH TESTS MEASURE WHAT. Back out by making `witness_instantiation` return an empty
//! `Vec`. Then `compound_row_*` and `renamed_param_*` go RED with
//! `undeclared effect: ?_`; every `control_*` stays green. The controls are not decoration:
//! `control_name_coincident_row_derived` is the case that used to work BY ACCIDENT, and it
//! must keep working — a fix that regressed it would be trading one silent gap for another.

/// The fixture: a carrier-param spec `Box` with one PRIMITIVE op (`get`, which the witness
/// supplies) and one DERIVED op (`getAgain`, default-bodied — its row can only come from the
/// witness FACT). `Wrap` is the parameterized carrier; `WrapBox` the witness.
///
/// `witness_params` / `carrier_extra` / `row` vary the two axes that decide the outcome:
/// whether the witness spells its parameters like the carrier, and whether the fact's row is
/// a single variable or a UNION.
fn source(carrier_extra: &str, witness_names: [&str; 3], row: &str, call: &str, ret_row: &str) -> String {
    let [s, t, e] = witness_names;
    let ef = if carrier_extra.is_empty() { String::new() } else { format!(", EF = {e}F") };
    let ef_decl = if carrier_extra.is_empty() { String::new() } else { format!("    effects {e}F = ?\n") };
    let recv = if carrier_extra.is_empty() {
        "Wrap[Source = Int64, T = Int64, ES = {}]"
    } else {
        "Wrap[Source = Int64, T = Int64, ES = {}, EF = {}]"
    };
    format!(
        r#"
namespace w57
  import anthill.prelude.{{Int64}}

  sort Box
    sort C = ?
    sort Element = ?
    effects E = ?
    operation get(c: C) -> Element effects E
    operation getAgain(c: C) -> Element effects E = get(c)
    operation echo(c: C, x: Element) -> Element effects E = x
  end

  sort Wrap
    sort Source = ?
    sort T = ?
    effects ES = ?
{carrier_extra}    entity wrap(src: Source, v: T)
  end

  sort WrapBox
    import w57.{{Box, Wrap}}
    import w57.Wrap.{{wrap}}
    sort {s} = ?
    sort {t} = ?
    effects {e} = ?
{ef_decl}    fact Box[C = Wrap[Source = {s}, T = {t}, ES = {e}{ef}], Element = {t}, E = {row}]
    operation get(w: Wrap[Source = {s}, T = {t}, ES = {e}{ef}]) -> {t} effects {row} =
      match w
        case wrap(_, v) -> v
  end

  operation drive(w: {recv}) -> Int64 effects {ret_row} =
    Box.{call}(w)
end
"#
    )
}

fn expect_loads(name: &str, src: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{name} must load clean; got {} error(s):\n{}", errs.len(), errs.join("\n"));
    }
}

const COINCIDENT: [&str; 3] = ["S", "T", "ES"];
const RENAMED: [&str; 3] = ["WS", "WT", "WE"];

/// DRIVES THE FIX. A UNION row (`E = {ES, EF}`) on a DERIVED op. The row's leaves are
/// anonymous row variables, which no by-name lookup against the carrier can resolve, so this
/// leaked its effect row regardless of how the parameters were spelled. RED when backed out.
#[test]
fn compound_row_derived_op_grounds_its_effect_row() {
    expect_loads(
        "compound row, derived op",
        &source("    effects EF = ?\n", COINCIDENT, "{ES, ESF}", "getAgain", "{}"),
    );
}

/// DRIVES THE FIX. A single-variable row, but the witness spells its parameters DIFFERENTLY
/// from the carrier — so the by-name lookup finds nothing and the row leaks. RED when backed
/// out. Together with the test above this pins BOTH manifestations of the one root cause:
/// the head is read in the wrong namespace, and a name coincidence was hiding it.
#[test]
fn renamed_witness_params_derived_op_grounds_its_effect_row() {
    expect_loads(
        "renamed witness params, derived op",
        &source("", RENAMED, "WE", "getAgain", "{}"),
    );
}

/// CONTROL — the case that USED TO WORK BY ACCIDENT and must keep working: a single-variable
/// row whose witness parameter happens to share the carrier's short name. Green either way;
/// it is here because a fix that re-expressed the head wrongly would break exactly this.
#[test]
fn control_name_coincident_row_derived() {
    expect_loads(
        "name-coincident row, derived op",
        &source("", COINCIDENT, "ES", "getAgain", "{}"),
    );
}

/// CONTROL — the PRIMITIVE the witness itself supplies. Its row comes from that op's own
/// declaration, never from the fact, so it grounds with or without the change. Green either
/// way; it separates "the witness dispatches at all" from "the fact's head is readable".
#[test]
fn control_witness_supplied_primitive_still_dispatches() {
    expect_loads(
        "witness-supplied primitive, compound row",
        &source("    effects EF = ?\n", COINCIDENT, "{ES, ESF}", "get", "{}"),
    );
}

/// CONTROL — the same primitive with RENAMED witness parameters. Green either way, for the
/// same reason; it shows the renaming itself is not what breaks the two driving cases.
#[test]
fn control_renamed_witness_supplied_primitive() {
    expect_loads(
        "witness-supplied primitive, renamed params",
        &source("", RENAMED, "WE", "get", "{}"),
    );
}

/// NEGATIVE — the instantiated head must still be READ, not merely rewritten. `Element` is
/// the witness's `T`, pinned to `Int64` by the receiver, so passing a `String` in the
/// `Element` slot must be REFUSED.
///
/// This is the case an earlier revision of the fix got wrong, and it is worth naming: once
/// the binding is instantiated it is the receiver's own type-arg (`Int64`), which is
/// ref-shaped but is NOT a parameter of the CARRIER — so the carrier-keyed classification
/// that follows answered `None` and DROPPED it. `Element` then stayed unbound and a `String`
/// was accepted. Caught by review, not by the effect-row tests above: every one of those
/// pins `Element` through its declared return, so only the row was ever driven.
#[test]
fn refuses_a_wrong_element_type_through_an_instantiated_witness() {
    let src = r#"
namespace w57neg
  import anthill.prelude.{Int64, String}

  sort Box
    sort C = ?
    sort Element = ?
    effects E = ?
    operation get(c: C) -> Element effects E
    operation echo(c: C, x: Element) -> Element effects E = x
  end

  sort Wrap
    sort Source = ?
    sort T = ?
    effects ES = ?
    entity wrap(src: Source, v: T)
  end

  sort WrapBox
    import w57neg.{Box, Wrap}
    import w57neg.Wrap.{wrap}
    sort WS = ?
    sort WT = ?
    effects WE = ?
    fact Box[C = Wrap[Source = WS, T = WT, ES = WE], Element = WT, E = WE]
    operation get(w: Wrap[Source = WS, T = WT, ES = WE]) -> WT effects WE =
      match w
        case wrap(_, v) -> v
  end

  operation bad(w: Wrap[Source = Int64, T = Int64, ES = {}], s: String) -> String effects {} =
    Box.echo(w, s)
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        !errs.is_empty(),
        "a String must NOT be accepted where the witness pins Element = Int64"
    );
}

/// A WITNESS PARAMETER IS MATCHED BY SYMBOL IDENTITY, NEVER BY NAME — and this is the test
/// that separates the two, because everything else in this file passes under either rule.
///
/// Building σ means asking, of each value written in the fact's carrier slots, "is this one of
/// the WITNESS's own parameters, and which?". The obvious resolver, `type_param_vid_in_sort`,
/// answers it by taking the written symbol's LOCAL NAME and looking that name up in the
/// witness's scope — so identity is discarded and only spelling survives. Any symbol spelled
/// like a witness parameter is then adopted as one.
///
/// Here the sort `lnm.B` and the witness's parameter `B` share a name and nothing else. The
/// head writes the SORT in the carrier's `A` slot and the PARAMETER in its `B` slot. Under a
/// name join the `A` slot also resolves to the parameter, σ binds `B` to `lnm.B`, and
/// `Element = B` comes out as `lnm.B` — so `drive`, which correctly returns `Int64`, is
/// REFUSED with `expected Int64, got B`. Under identity the `A` slot resolves to nothing (it
/// is not a witness parameter), `B` binds from its own slot, and the program loads.
///
/// MEASURED both ways on this fixture. It is also the general hazard behind a PERMUTED head
/// (`Alg[T = X.S, S = X.T]`), where a name join pairs `X.S` with the witness's `S` and
/// silently inverts the permutation; that shape is harder to write in one fixture, and this
/// one exercises the same resolver.
#[test]
fn witness_params_match_by_symbol_identity_not_by_name() {
    let src = r#"
namespace lnm
  import anthill.prelude.{Int64}

  -- A SORT whose name collides with the witness parameter below, and nothing more.
  sort B
    entity b_val
  end

  sort Box
    sort C = ?
    sort Element = ?
    operation get(c: C) -> Element
    operation getAgain(c: C) -> Element = get(c)
  end

  sort Wrap
    sort A = ?
    sort B = ?
    entity wrap(a: A, b: B)
  end

  sort WrapBox
    import lnm.{Box, Wrap}
    import lnm.Wrap.{wrap}
    sort B = ?
    -- `A` gets the SORT `lnm.B`; `B` gets the PARAMETER `B`. Only identity tells them apart.
    provides Box[C = Wrap[A = lnm.B, B = B], Element = B]
    operation get(w: Wrap[A = lnm.B, B = B]) -> B = match w
      case wrap(_, b) -> b
  end

  operation drive(w: Wrap[A = lnm.B, B = Int64]) -> Int64 =
    Box.getAgain(w)
end
"#;
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!(
            "a witness parameter must be matched by SYMBOL, not by name — a sort merely spelled \
             like one must not be adopted as it; got {} error(s):\n{}",
            errs.len(),
            errs.join("\n")
        );
    }
}
