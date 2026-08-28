//! WI-590 — a spec op dispatched on a receiver whose capability comes from the
//! ENCLOSING SORT's `requires`, not from the receiver's own carrier.
//!
//! The carrier-param grounding path reads a spec's params off the RECEIVER's carrier: its
//! `provides` fact (WI-424/492), the spec that carrier itself `requires` (WI-608), or its own
//! type-args when carrier and spec coincide (WI-609). All three need a carrier SORT to read
//! from. A receiver typed by an abstract sort PARAMETER has none — inside a sort body the
//! param is rigidified to a Skolem — so every spec param except the carrier used to leak
//! `?_`, surfacing as an `undeclared effect` on the op's row or an ungrounded element in its
//! return.
//!
//! The information is one level out: the enclosing sort's own `requires Spec[C = P, …]` IS
//! the statement "P provides Spec, with these params". That is the shape a WITNESS sort needs
//! in order to consume its own subject, which is what WI-590's finite-combinator
//! consolidation rests on, and the wiring `carrier_provision_short_bindings`' doc named as
//! missing ("a free op licensing `c` through an ambient `requires FiniteCollection[C = C2,
//! …]` is NOT handled here … What is missing is the wiring, not the information").
//!
//! NOT COVERED HERE — the CONSTRUCTION side. The same information is missing when a value
//! flows into an entity FIELD typed on a spec the enclosing sort merely requires
//! (`carrier_provision_short_bindings`, whose doc names that face too). That half is NOT
//! implemented: the only fixture that would drive it also type-checks with the change backed
//! out (its declared return pins the params the construction leaves free), so it would have
//! measured nothing. It lands with the stdlib work that actually needs it.
//!
//! CONTROLS. `control_*` are the two shapes that ALREADY worked — the receiver typed as a
//! view of the very spec the `requires` names. They must pass with the change backed out;
//! the three `enclosing_requires_*` cases must FAIL with it backed out. Backing out means
//! making `enclosing_requires_licensing_clause` return `None`; MEASURED, the three go red —
//! with `undeclared effect: ?_`, an ungrounded element, and a `missing requires … on
//! enclosing sort` refusal respectively — and both controls stay green. The `refuses_*`
//! cases pass EITHER WAY by design: they pin the gates that keep the licence from widening,
//! and a back-out only removes licences.

fn expect_loads(name: &str, src: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{name} must load clean; got {} error(s):\n{}", errs.len(), errs.join("\n"));
    }
}

/// The RECEIVER IS THE BARE PARAM. `collect(s)` on `s : S`, where the enclosing sort says
/// `requires FiniteCollection[C = S, Element = Src, E = ES]`. Without the change the element
/// grounds (the declared return names it) but the effect row does not, and `drain`'s declared
/// `effects ES` is rejected against an `undeclared effect: ?_`.
#[test]
fn enclosing_requires_grounds_a_bare_param_receiver() {
    expect_loads(
        "bare-param receiver",
        r#"
namespace wi590.encl.a
  import anthill.prelude.{FiniteCollection, List}
  sort W
    import anthill.prelude.{FiniteCollection, List}
    import anthill.prelude.FiniteCollection.{collect}
    sort S = ?
    sort Src = ?
    effects ES = ?
    requires FiniteCollection[C = S, Element = Src, E = ES]
    operation drain(s: S) -> List[T = Src] effects ES = collect(s)
  end
end
"#,
    );
}

/// The RECEIVER IS A VIEW OVER THE PARAM, and over a DIFFERENT spec than the one being
/// called: `s : Iterable[C = S, …]` (what destructuring a spec-typed field yields) with
/// `requires FiniteCollection[C = S, …]`. `Iterable` neither provides nor requires
/// `FiniteCollection`, so the carrier-keyed search finds nothing; the clause that licenses
/// the call is the enclosing sort's, keyed by `S`. Without the change this is REFUSED
/// outright with `missing requires FiniteCollection[…] on enclosing sort` — the licensing
/// half of the fix, separate from the binding half the other cases exercise.
#[test]
fn enclosing_requires_licenses_a_view_over_the_param() {
    expect_loads(
        "view-over-param receiver",
        r#"
namespace wi590.encl.b
  import anthill.prelude.{FiniteCollection, Iterable, List}
  sort W
    import anthill.prelude.{FiniteCollection, Iterable, List}
    import anthill.prelude.FiniteCollection.{collect}
    sort S = ?
    sort Src = ?
    effects ES = ?
    requires FiniteCollection[C = S, Element = Src, E = ES]
    operation drain(s: Iterable[C = S, Element = Src, E = ES]) -> List[T = Src] effects ES = collect(s)
  end
end
"#,
    );
}

/// The ELEMENT, not just the effect row: `Iterable.iterator(s)` on a bare `Source` param
/// yields a `Stream` whose element must come from the enclosing `requires`. Without the
/// change the peeled element is a fresh `?A` and the declared `Pair[A = Src]` return is
/// rejected — the failure the lazy combinators hit when their source field became a
/// parameter rather than a `Stream`.
#[test]
fn enclosing_requires_grounds_the_produced_element() {
    expect_loads(
        "iterator peel on a bare param",
        r#"
namespace wi590.encl.d
  import anthill.prelude.{Iterable, Stream, Option, Pair}
  sort W
    import anthill.prelude.{Iterable, Stream, Option, Pair}
    sort Source = ?
    sort Src = ?
    effects ES = ?
    requires Iterable[C = Source, Element = Src, E = ES]
    operation peel(s: Source) -> Option[Pair[A = Src, B = Stream[T = Src, E = ES]]] effects ES =
      Stream.splitFirst(Iterable.iterator(s))
  end
end
"#,
    );
}

/// CONTROL — the shape that already worked: the receiver is a view of the SAME spec the
/// `requires` names (`s : FiniteCollection[C = S, …]`, `requires FiniteCollection[…]`), which
/// WI-608/WI-609 already ground. Passes with the change backed out; it is here so a
/// regression in the shared path is not mistaken for the new one.
#[test]
fn control_same_spec_view_receiver_still_grounds() {
    expect_loads(
        "control: same-spec view",
        r#"
namespace wi590.encl.c
  import anthill.prelude.{FiniteCollection, List}
  sort W
    import anthill.prelude.{FiniteCollection, List}
    import anthill.prelude.FiniteCollection.{collect}
    sort S = ?
    sort Src = ?
    effects ES = ?
    requires FiniteCollection[C = S, Element = Src, E = ES]
    operation drain(s: FiniteCollection[C = S, Element = Src, E = ES]) -> List[T = Src] effects ES = collect(s)
  end
end
"#,
    );
}

/// CONTROL — the other already-working shape: an `Iterable`-viewed receiver calling an
/// `Iterable` op, which the WI-608 requires-view path grounds. Also passes backed out.
#[test]
fn control_same_spec_view_peel_still_grounds() {
    expect_loads(
        "control: same-spec view peel",
        r#"
namespace wi590.encl.f
  import anthill.prelude.{Iterable, Stream, Option, Pair}
  sort W
    import anthill.prelude.{Iterable, Stream, Option, Pair}
    sort Source = ?
    sort Src = ?
    effects ES = ?
    requires Iterable[C = Source, Element = Src, E = ES]
    operation peel(s: Iterable[C = Source, Element = Src, E = ES]) -> Option[Pair[A = Src, B = Stream[T = Src, E = ES]]] effects ES =
      Stream.splitFirst(Iterable.iterator(s))
  end
end
"#,
    );
}

/// NEGATIVE — the clause must be about the RECEIVER'S param, not merely name the spec. `W`
/// requires `FiniteCollection` over `S`, and `drain` is called on a `Q` that nothing says
/// anything about. Licensing this would let a clause lend its `Element`/`E` to an unrelated
/// param; the call must still be refused.
#[test]
fn refuses_a_receiver_typed_by_a_different_param() {
    let errs = crate::common::try_load_kb_with(
        r#"
namespace wi590.encl.neg1
  import anthill.prelude.{FiniteCollection, List}
  sort W
    import anthill.prelude.{FiniteCollection, List}
    import anthill.prelude.FiniteCollection.{collect}
    sort S = ?
    sort Q = ?
    sort Src = ?
    effects ES = ?
    requires FiniteCollection[C = S, Element = Src, E = ES]
    operation drain(q: Q) -> List[T = Src] effects ES = collect(q)
  end
end
"#,
    )
    .err()
    .unwrap_or_default();
    assert!(
        !errs.is_empty(),
        "a receiver typed by a param the `requires` does not name must NOT be licensed"
    );
}

/// NEGATIVE — a NON-SPEC application over the required param is not a view of it.
/// `Option[T = S]` is an ordinary parameterized type whose first type argument happens to be
/// `S`; reading that argument as a carrier would license an `Option` receiver as though it
/// were the `S` itself. `Option` has constructors, so it is not an abstract spec — the gate
/// that separates it from a genuine `Iterable[C = S, …]` view.
#[test]
fn refuses_a_non_spec_application_over_the_required_param() {
    let errs = crate::common::try_load_kb_with(
        r#"
namespace wi590.encl.neg2
  import anthill.prelude.{FiniteCollection, Option, List}
  sort W
    import anthill.prelude.{FiniteCollection, Option, List}
    import anthill.prelude.FiniteCollection.{collect}
    sort S = ?
    sort Src = ?
    effects ES = ?
    requires FiniteCollection[C = S, Element = Src, E = ES]
    operation drain(o: Option[T = S]) -> List[T = Src] effects ES = collect(o)
  end
end
"#,
    )
    .err()
    .unwrap_or_default();
    assert!(
        !errs.is_empty(),
        "a non-spec application over the required param must NOT be read as a carrier view"
    );
}

/// NEGATIVE, AND IT PASSES EITHER WAY — say so rather than let it read as a measurement.
/// Only the CARRIER slot counts as the receiver. `Bag.put(c: C, x: Elem)` has a
/// second parameter typed by a spec type-param, and `W`'s clause binds `Elem = Src`. If any
/// spec-param-typed parameter could be the receiver, `put(q, x)` would match on parameter 1,
/// license a call nothing licenses. MEASURED: this fixture is refused BOTH with the gate and
/// with it backed out to the earlier scan-every-parameter form, because the carrier param is
/// already pinned by argument unification against `q` and the binder will not overwrite it —
/// so the wrong licence never becomes a wrong type, only a diagnostic deferred by one step.
/// Kept as a regression guard on that reasoning, NOT as evidence the gate is load-bearing.
/// The other two `refuses_*` cases ARE measured: each goes red with its own gate backed out.
#[test]
fn refuses_a_non_carrier_parameter_as_the_receiver() {
    let errs = crate::common::try_load_kb_with(
        r#"
namespace wi590.encl.neg3
  sort Bag
    sort C = ?
    sort Elem = ?
    operation put(c: C, x: Elem) -> C
  end
  sort W
    import wi590.encl.neg3.Bag
    sort S = ?
    sort Q = ?
    sort Src = ?
    requires Bag[C = S, Elem = Src]
    operation bad(q: Q, x: Src) -> S = Bag.put(q, x)
  end
end
"#,
    )
    .err()
    .unwrap_or_default();
    assert!(
        !errs.is_empty(),
        "a non-carrier spec-param-typed parameter must NOT be treated as the receiver"
    );
}
