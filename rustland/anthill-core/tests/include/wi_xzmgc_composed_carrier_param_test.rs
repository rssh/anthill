//! WI-20260829-XZMGC — THE CARRIER PARAMETER OF A COMPOSED PROVISION VIEW IS THE ACTUAL,
//! NOT THE INTERMEDIATE.
//!
//! `Stream provides Iterable[C = Stream, Element = T, E = E]` binds `C` to STREAM ITSELF,
//! and `compose_provision_views` substitutes values that are type-param refs OF THE
//! INTERMEDIATE (`Stream.T ↦ List.T`, `Stream.E ↦ {}`) and keeps everything else verbatim
//! — its own doc names this exact case ("a value not referencing an intermediate param
//! (the carrier application `C ↦ Stream`) is kept verbatim"). So the composed view for
//! `List` said the carrier of a `List` is a `Stream`. It is not: `C` is the value
//! `Iterable.iterator(c: C)` receives, and `iterator` on a `List` receives the LIST.
//!
//! THE DEFECT HAS TWO HALVES AND ONLY ONE WAS FILED. WI-20260829-GNPG7 measured the
//! refusing half — `ti(c: Iterable[C = List[T = Row], …])` rejecting a `List[T = Row]` —
//! and split it out as this ticket. The accepting half is the same artifact read the other
//! way and nothing had named it: `ti(c: Iterable[C = Stream])` ACCEPTED that same `List`,
//! because the view literally said the carrier was a `Stream`. That row is
//! [`a_list_is_no_longer_admissible_at_a_spec_view_naming_stream`], and it is the more
//! dangerous of the two — a refusal that never comes is invisible.
//!
//! WHERE THE FIX IS, AND WHY NOT IN THE COMPOSER. `compose_provision_views` is UNCHANGED.
//! Its three non-subtype consumers were censused, and not one of them reads the composed
//! `C`:
//!
//!   * `bind_spec_params_from_carrier` (WI-357/714, self-receiver grounding) — the value
//!     `Stream` is a bare ref, so it takes the `ref_shape` arm, and `typaram_ref_vid(…,
//!     carrier)` asks whether it names a type parameter OF THE CARRIER. `Stream` is not one
//!     of `List`'s, so `concrete` is `None` and the param is skipped. It would be skipped
//!     for `List` too — the binding is DROPPED either way.
//!   * `carrier_param_receiver` → `bind_spec_params_from_carrier_param` (WI-424/593) —
//!     SKIPS the carrier param by VarId, explicitly and by design: `C` is bound by ordinary
//!     argument unification against the receiver, not by the provision.
//!   * `bare_spec_arg_provision_projection` (WI-20260828-BH1JZ) — skips it by VarId too and
//!     substitutes THE RECEIVER'S OWN TYPE, and its comment is a measurement of this very
//!     artifact: without it, `mapped(xs, inc)` over a `List` inferred `MappedStream[Source =
//!     Stream, …]` and the finiteness witness asked whether the SPEC `Stream` is a
//!     `FiniteCollection`. Its conclusion — "the spec's CARRIER parameter is the receiver's
//!     own type, by definition, and must not be read off the provision" — is the rule this
//!     ticket applies at the fourth consumer.
//!
//! So the composer's verbatim behaviour is invisible to all three and changing it would
//! have been a mutability cascade (it would need `kb.alloc`) through paths that do not read
//! the value. The SUBTYPE relation is the one reader that COMPARES `C`, and it already has
//! its own entry point — `subtype_provider_view`, which GNPG7 added for exactly this
//! reason. It now EXCLUDES the carrier param from a COMPOSED view and reports that it did;
//! each of its two callers supplies the actual it has.
//!
//! WHY THE ACTUAL AND NOT A BARE `Ref(carrier)`, which is what `subtype_provider_view`
//! could have emitted with no caller change: MEASURED, the bare form opens a hole the
//! DIRECT case does not have. See [`a_wrong_carrier_argument_still_refuses`].
//!
//! TWO BACK-OUTS WERE RUN, because the change has two axes — whether the carrier param is
//! taken out of the composed view at all, and WHAT replaces it — and one back-out cannot
//! separate them. Both were measured by MUTATING the shipped code, not deleting it.
//!
//! (A) NEUTRALIZE THE EXCLUSION (`carrier_vid` forced to `None` in `subtype_provider_view`,
//! so nothing is dropped and neither caller's override fires) — the pre-ticket tree:
//!
//!   * [`a_two_hop_carrier_conforms_to_a_spec_view_naming_it`] — RED.
//!   * [`a_list_is_no_longer_admissible_at_a_spec_view_naming_stream`] — RED.
//!   * [`a_bare_two_hop_carrier_conforms_to_a_spec_view_naming_it`] — RED.
//!   * [`a_wrong_carrier_argument_still_refuses`] — GREEN. It refuses for the OLD reason,
//!     the composed view naming `Stream`, so it says nothing about this axis.
//!   * [`a_direct_provider_is_untouched`] — GREEN.
//!   * [`the_composed_non_carrier_params_are_unaffected`] — GREEN.
//!   * Also RED: `typer_capability_matrix_test::a_spec_typed_parameter_and_its_carrier` and
//!     `wi_gnpg7_…::the_carrier_param_of_a_composed_view_names_the_carrier`.
//!
//! (A2) WIDEN THE GATE — the axis (A) cannot measure, because a gate that is too WIDE
//! still drops the carrier param and so leaves every row in (A) green. Two earlier cuts of
//! this ticket were exactly that, each caught by a /code-review pass the other could not
//! have caught:
//!
//!   * CUT 1 — the PARAMETER gate alone (drop whenever `spec_carrier_param` names the
//!     param). RED: [`a_composed_element_parameter_is_not_dropped_as_the_carrier`] AND
//!     [`a_self_providing_element_sort_is_not_read_as_the_carrier`]. Everything else green.
//!   * CUT 2 — parameter gate plus "the value's sort self-provides the spec at this param".
//!     RED: [`a_self_providing_element_sort_is_not_read_as_the_carrier`] ONLY. Cut 1's
//!     fixture stays GREEN through this defect, because its `P` is `Int64` and `Int64`
//!     provides no `Spec` — which is why the second review pass was needed and why both
//!     fixtures are kept.
//!
//! The two together are the ladder: absent gate, wide gate, exact gate. A single fixture
//! could not have told the middle rung from the top.
//!
//! (B) KEEP THE EXCLUSION, SUPPLY THE BARE `Ref(actual_base)` instead of the actual — the
//! design `subtype_provider_view` could have implemented alone, with no caller change:
//!
//!   * [`a_wrong_carrier_argument_still_refuses`] — RED, and it is the ONLY row that moves.
//!     `List[T = Row]` is ACCEPTED at `Iterable[C = List[T = Bool]]`, because a bare
//!     `C ↦ List` against a parameterized expected is the (sort_ref, parameterized) arm on
//!     one base and compatible both directions.
//!   * Every other row here — GREEN. Which is exactly why that one test exists: it is the
//!     only thing in the corpus that tells the two designs apart, and without it (B) would
//!     have looked like the simpler equal.
//!
//! [`a_direct_provider_is_untouched`] is GREEN UNDER BOTH, by design. A direct provision
//! names its own carrier truthfully and never reaches the composed branch. It is the
//! control that makes the rows above attributable to composition rather than to the carrier
//! parameter having been given a new meaning everywhere.

use crate::common::{expect_loaded, try_load_kb_with};

/// The two-hop carrier is `List`, reaching `Iterable` through `Stream`
/// (`List provides Stream[T, {}]`, `Stream provides Iterable[C = Stream, …]`).
fn program(param: &str, arg_ty: &str) -> String {
    format!(
        r#"
namespace test.xzmgc
  import anthill.prelude.{{Int64, Bool, List, Iterable, Stream, MutableStack}}
  sort Row
    import anthill.prelude.{{Int64, Bool}}
    entity row(a: Int64, flag: Bool)
  end
  operation ti(c: {param}) -> Int64 = 1
  operation drive(rs: {arg_ty}) -> Int64 = ti(rs)
end
"#
    )
}

/// A BARE actual (`nil()` has type `List`, no bindings) reaches
/// `bare_provider_binding_precise`, not `parameterized_compatible_view` — the second of the
/// two subtype sites, and a separate call site with its own override.
fn bare_program(param: &str) -> String {
    format!(
        r#"
namespace test.xzmgc_bare
  import anthill.prelude.{{Int64, List, Iterable, Stream}}
  import anthill.prelude.List.{{nil}}
  operation ti(c: {param}) -> Int64 = 1
  operation drive() -> Int64 = ti(nil())
end
"#
    )
}

fn load_errors(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(es) => es.iter().map(|e| e.to_string()).collect(),
    }
}

/// THE TICKET'S ACCEPTANCE ROW, plus the two spellings either side of it. All three name
/// the carrier the composed chain could not: `C` is `List`, so a `List[T = Row]` is what
/// `Iterable.iterator` receives.
///
/// The three spellings are not one row three times — they separate what the OVERRIDE
/// supplies from what the rest of the view does. The bare `C = List` needs only the base to
/// match; `C = List[T = Row]` needs the actual's own `T` to reach the comparison; the full
/// view adds `Element`/`E`, which come from the composed view and were already green
/// (WI-20260829-GNPG7) — so if that row alone regressed, the cause would be the exclusion
/// having taken too much.
#[test]
fn a_two_hop_carrier_conforms_to_a_spec_view_naming_it() {
    for param in [
        "Iterable[C = List]",
        "Iterable[C = List[T = Row]]",
        "Iterable[C = List[T = Row], Element = Row, E = {}]",
    ] {
        expect_loaded(try_load_kb_with(&program(param, "List[T = Row]")));
    }
}

/// THE OTHER HALF, and the one nothing had named: a `List` was ADMITTED at a spec view
/// claiming its carrier is a `Stream`, because the composed view said exactly that. Same
/// artifact, opposite sign, and a silent accept rather than a visible refusal.
///
/// Asserted at BOTH subtype sites. They are separate call sites with separate overrides,
/// and a fix to one says nothing about the other — the pairing GNPG7's own two tests
/// established for this relation.
#[test]
fn a_list_is_no_longer_admissible_at_a_spec_view_naming_stream() {
    let parameterized = load_errors(&program("Iterable[C = Stream]", "List[T = Row]"));
    assert!(
        parameterized
            .iter()
            .any(|e| e.contains("expected Iterable[C = Stream]")),
        "a List's Iterable carrier is the LIST, so a view naming Stream must refuse it \
         (parameterized actual): {parameterized:?}"
    );

    let bare = load_errors(&bare_program("Iterable[C = Stream]"));
    assert!(
        bare.iter()
            .any(|e| e.contains("expected Iterable[C = Stream]")),
        "the same, at the BARE-actual site (`bare_provider_binding_precise`): {bare:?}"
    );

    // CONTROL — the same fixture with the carrier named correctly loads, so the rows above
    // are about WHICH carrier is named and not about the view carrying a `C` at all.
    expect_loaded(try_load_kb_with(&program("Iterable[C = List]", "List[T = Row]")));
    expect_loaded(try_load_kb_with(&bare_program("Iterable[C = List]")));
}

/// THE STRENGTH CONTROL, and the row that decides HOW the carrier param is supplied.
///
/// `subtype_provider_view` could have emitted a bare `Ref(carrier)` itself and left both
/// callers alone. It does not, because that is measurably weaker than the direct case:
/// `C = List` against an expected `C = List[T = Bool]` is the (sort_ref, parameterized) arm
/// on ONE base, which is compatible in both directions — so a `List[T = Row]` would have
/// been accepted at `Iterable[C = List[T = Bool]]`. The callers supply the ACTUAL instead
/// (`List[T = Row]`), which is what the DIRECT case has always compared.
///
/// So the two rows below are the same question at one hop and at two, and they must answer
/// alike. The `MutableStack` row is green under every variant; the `List` row is what the
/// bare-`Ref` alternative turns red.
#[test]
fn a_wrong_carrier_argument_still_refuses() {
    let two_hop = load_errors(&program("Iterable[C = List[T = Bool]]", "List[T = Row]"));
    assert!(
        two_hop
            .iter()
            .any(|e| e.contains("expected Iterable[C = List[T = Bool]]")),
        "two hops: the actual's own T must reach the carrier comparison: {two_hop:?}"
    );

    let one_hop = load_errors(&program(
        "Iterable[C = MutableStack[T = Bool]]",
        "MutableStack[T = Row]",
    ));
    assert!(
        one_hop
            .iter()
            .any(|e| e.contains("expected Iterable[C = MutableStack[T = Bool]]")),
        "one hop, the pre-existing behaviour the row above now matches: {one_hop:?}"
    );
}

/// THE BARE-ACTUAL SITE. `nil()` is a bare `List` — no bindings — so its own type IS the
/// bare sort, and that is what the override supplies there.
///
/// `Iterable[C = List[T = Int64]]` loading is the (sort_ref, parameterized) arm doing what
/// it does everywhere: a bare actual carries nothing to contradict a written argument. The
/// CONTROL beside it is the same argument against `List` written DIRECTLY — it loads too,
/// so admitting it through the `Iterable` view is that arm's established reading and not a
/// hole this ticket opened.
#[test]
fn a_bare_two_hop_carrier_conforms_to_a_spec_view_naming_it() {
    for param in ["Iterable[C = List]", "Iterable[C = List[T = Int64]]"] {
        expect_loaded(try_load_kb_with(&bare_program(param)));
    }
    // CONTROL: the same shape with no spec view in it at all.
    for param in ["List", "List[T = Int64]"] {
        expect_loaded(try_load_kb_with(&bare_program(param)));
    }
}

/// THE CONTROL FOR EVERY ROW ABOVE. `MutableStack` declares `provides Iterable[C =
/// MutableStack[T], Element = T, E = {}]` ITSELF (mutable_stack.anthill), so
/// `subtype_provider_view` returns on its direct branch, the carrier param is never
/// excluded and no override runs. GREEN EITHER WAY across this ticket's change — which is
/// the point: it says the composed path was changed and the direct one was not, so the
/// movement in the `List` rows is attributable to composition rather than to the carrier
/// param having been given a new meaning everywhere.
#[test]
fn a_direct_provider_is_untouched() {
    for param in [
        "Iterable[Element = Row]",
        "Iterable[C = MutableStack]",
        "Iterable[C = MutableStack[T = Row]]",
        "Iterable[C = MutableStack[T = Row], Element = Row, E = {}]",
    ] {
        expect_loaded(try_load_kb_with(&program(param, "MutableStack[T = Row]")));
    }
}

/// THE PARAMETER GATE ALONE IS NOT ENOUGH, and this is the row that says so. Found by
/// /code-review on the first cut, then DRIVEN.
///
/// `spec_carrier_param` answers "the first declared type parameter some declared operation
/// TAKES" — and that reads an ACCEPTED ARGUMENT as the carrier, deliberately and by the
/// language's own rule (kernel-language.md, WI-1077: `Set.insert(s: Set, x: T)` files at
/// `T`). So for a spec whose operation is `touch(c: Spec, x: P)` the predicate answers `P`,
/// the ELEMENT. `P`'s composed binding is an ordinary one and CORRECT; the first cut
/// dropped it anyway and substituted the actual's whole type, so `Carrier[T = Int64]` was
/// compared against `Int64` and a program that LOADS on the pre-ticket tree was refused.
///
/// The exclusion therefore also asks whether the VALUE is the intermediate's own
/// self-naming (`composed_self_reference`): `Int64` provides no `Spec`, so `P` is kept.
/// `Q` — a parameter no operation takes, and so never a carrier-param candidate — is the
/// row that says the fixture reaches the composed path at all.
///
/// WHAT FAILS WITHOUT THE VALUE GATE: the first two rows. The third passes either way,
/// which is why it is here — it is the control that the chain composes.
#[test]
fn a_composed_element_parameter_is_not_dropped_as_the_carrier() {
    let program = |want: &str| {
        format!(
            r#"
namespace test.xzmgc_elem
  import anthill.prelude.{{Int64}}
  sort Spec
    sort P = ?
    sort Q = ?
    operation touch(c: Spec, x: P) -> Q
  end
  sort Mid
    sort A = ?
    provides Spec[P = A, Q = Int64]
    operation touch(c: Mid, x: A) -> Int64 = 1
  end
  sort Carrier
    sort T = ?
    entity carrier(v: T)
    provides Mid[A = T]
    operation touch(c: Carrier, x: T) -> Int64 = 2
  end
  operation ti(c: Spec[{want}]) -> Int64 = 1
  operation drive(x: Carrier[T = Int64]) -> Int64 = ti(x)
end
"#
        )
    };
    for want in ["P = Int64, Q = Int64", "P = Int64", "Q = Int64"] {
        expect_loaded(try_load_kb_with(&program(want)));
    }
}

/// THE SECOND CUT'S GATE WAS STILL TOO WEAK, and this is the fixture that shows it. Found
/// by the SECOND /code-review pass, then DRIVEN.
///
/// That cut asked "does the value's sort itself provide the spec, binding this parameter to
/// itself?" — which is true of the intermediate's `C = Self`, and equally true of ANY
/// self-providing sort (`Int64 provides Combiner[T = Int64]` is the ordinary shape). So a
/// mis-identified ELEMENT parameter whose value is such a sort was dropped again, and the
/// test above could not see it: its `P` is `Int64`, which provides no `Spec`.
///
/// HERE `Elem` DOES PROVIDE `Spec`, and both signs flipped on the composed path:
///
///     Spec[P = Elem]     <- Carrier (2 hops)   loads on main    REFUSED on the 2nd cut
///     Spec[P = Carrier]  <- Carrier (2 hops)   refused on main  ACCEPTED on the 2nd cut
///     Spec[P = Elem]     <- Mid     (1 hop)    loads            loads
///     Spec[P = Carrier]  <- Mid     (1 hop)    refused          refused
///
/// The one-hop rows are the CONTROL and they are why this is a defect rather than a
/// preference: the composed path was contradicting the direct path about the same two
/// programs — which is the defect this whole ticket removes, relocated onto element
/// parameters.
///
/// The gate is now IDENTITY against the chain's own self-naming sort, resolved once by
/// `transitive_carrier_for_param` — the walk that already answers "who owns this spec's
/// implementation on this chain". No sort on `Carrier`'s chain binds `P` to itself, so
/// nothing is dropped and all four rows agree again.
#[test]
fn a_self_providing_element_sort_is_not_read_as_the_carrier() {
    let program = |want: &str, arg: &str| {
        format!(
            r#"
namespace test.xzmgc_selfelem
  import anthill.prelude.{{Int64}}
  sort Spec
    sort P = ?
    operation touch(c: Spec, x: P) -> Int64
  end
  sort Elem
    import anthill.prelude.{{Int64}}
    entity el(v: Int64)
    provides Spec[P = Elem]
    operation touch(c: Elem, x: Elem) -> Int64 = 0
  end
  sort Mid
    import anthill.prelude.{{Int64}}
    sort Z = ?
    provides Spec[P = Elem]
    operation touch(c: Mid, x: Elem) -> Int64 = 1
  end
  sort Carrier
    import anthill.prelude.{{Int64}}
    entity carrier(v: Int64)
    provides Mid
    operation touch(c: Carrier, x: Elem) -> Int64 = 2
  end
  operation ti(c: Spec[{want}]) -> Int64 = 1
  operation drive(x: {arg}) -> Int64 = ti(x)
end
"#
        )
    };
    // TWO HOPS — the composed path, and the pair that moved.
    expect_loaded(try_load_kb_with(&program("P = Elem", "Carrier")));
    let wrong = load_errors(&program("P = Carrier", "Carrier"));
    assert!(
        wrong
            .iter()
            .any(|e| e.contains("expected Spec[P = Carrier]")),
        "the actual's own type must NOT be substituted for a composed element param: \
         {wrong:?}"
    );

    // ONE HOP — the direct control the rows above must agree with. Green under every
    // variant of this ticket: a direct provision never reaches the composed branch.
    expect_loaded(try_load_kb_with(&program("P = Elem", "Mid")));
    let wrong_direct = load_errors(&program("P = Carrier", "Mid"));
    assert!(
        wrong_direct
            .iter()
            .any(|e| e.contains("expected Spec[P = Carrier]")),
        "the one-hop control: {wrong_direct:?}"
    );
}

/// AN ENTITY ACTUAL GETS THE SORT ITS PROVISION IS FILED AT, and the two subtype branches
/// agree about that. Also found by /code-review, which read the first cut's comment as
/// promising the entity itself.
///
/// `Iterable.C` declares no variance, so the check is INVARIANT and one value cannot
/// satisfy both spellings — MEASURED, supplying the entity instead of its sort swaps the
/// two rows below rather than adding one. The DIRECT branch is what decides which way:
/// a carrier that provides `Iterable` ITSELF binds `C` to that carrier, so a `boxed`
/// argument is admissible at `Iterable[C = Box]` and not at `Iterable[C = Box.boxed]` —
/// on a fixture with no composition in it. The composed branch answers the same, which is
/// the property this test pins.
///
/// ONLY THE BARE SITE HAS AN ANSWER HERE. `parameterized_compatible_view` has no
/// entity→parent climb, so a PARAMETERIZED entity actual finds no provider view and every
/// carrier spelling refuses — measured, and identically with this ticket backed out. That
/// gap is the missing climb, is pre-existing, and is not what this row is about.
#[test]
fn an_entity_actual_is_admissible_at_its_providing_sort() {
    let program = |want: &str| {
        format!(
            r#"
namespace test.xzmgc_entity
  import anthill.prelude.{{Int64, Iterable, Stream}}
  sort Box
    import anthill.prelude.{{Int64, Stream}}
    sort T = ?
    entity boxed(v: Int64)
    provides Stream[T = T, E = {{}}]
    operation splitFirst(s: Box) -> Int64 = 1
  end
  operation ti(c: {want}) -> Int64 = 1
  operation drive(b: Box.boxed) -> Int64 = ti(b)
end
"#
        )
    };
    expect_loaded(try_load_kb_with(&program("Iterable[C = Box]")));

    // And the carrier is CHECKED, not merely present: the intermediate's own name — the
    // value the composed view used to carry — is refused.
    let errs = load_errors(&program("Iterable[C = Stream]"));
    assert!(
        errs.iter()
            .any(|e| e.contains("expected Iterable[C = Stream]")),
        "an entity of a two-hop provider must not be admissible at the INTERMEDIATE: \
         {errs:?}"
    );
}

/// THE NON-CARRIER PARAMS ARE STILL COMPOSED. WI-20260829-GNPG7 made these load and this
/// ticket must not have taken them back: the exclusion is one parameter wide, and an
/// over-wide one would show here first — `Element` and `E` are exactly what the composed
/// view still has to supply.
#[test]
fn the_composed_non_carrier_params_are_unaffected() {
    for param in [
        "Iterable",
        "Iterable[Element = Row]",
        "Iterable[Element = Row, E = {}]",
    ] {
        expect_loaded(try_load_kb_with(&program(param, "List[T = Row]")));
    }
}
