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
//! consolidation rests on.
//!
//! THE CONSTRUCTION SIDE came with WI-20261005-KSSA4, the standard library work that needed
//! it: a value built into an entity whose sort requires a spec of the field's parameter
//! reads the same clause (`bind_sort_params_from_sort_requires_at_construction`). Its rows
//! are the `ambient_requires_*` ones of `wi_mdwew_bare_spec_arg_provision_test` and
//! `wi599_carrier_arg_provision_test`'s.
//!
//! WHAT FAILS WHEN IT IS BACKED OUT. Backing out means making
//! `enclosing_requires_licensing_clause` return `None`: the two `enclosing_requires_*` cases
//! go red, and the `refuses_*` cases pass EITHER WAY by design — they pin the gates that
//! keep the licence from widening, and a back-out only removes licences. RE-MEASURED
//! 2026-10-05 (WI-20261005-KSSA4): the two go red on the STANDARD LIBRARY's own errors —
//! `iterator.return: cannot project 'Element' off an abstract receiver with no concrete
//! sort`, twice. The library's lazy carriers hold their source as a value of their own
//! `Source` and read it through the sort's clause (`Iterable.iterator(src)` in
//! `MappedStream.splitFirst`), which this reader is what licenses; so with it backed out
//! every row that loads the library fails, anywhere, and these two no longer isolate it.
//!
//! A RECEIVER TYPED AS A VIEW OVER THE PARAM (`s: Iterable[C = S, …]`) was a third licensed
//! case and the file's two controls. A value typed at a spec over a parameter is not a
//! value of a sort that provides it (WI-20261005-KSSA4), so the three are one refusal row,
//! [`a_receiver_typed_as_a_view_over_the_param_is_refused`], which passes with or without
//! the licence.

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

/// A RECEIVER TYPED AS A VIEW OVER THE PARAM IS NOT A VALUE OF THE PARAM. `s: Iterable[C =
/// S, …]` and `s: FiniteCollection[C = S, …]` type `s` at a spec, and a value typed at a
/// spec over a parameter is not a value of a sort that provides it (WI-20261005-KSSA4): the
/// enclosing clause is about `S`, and `s` is not an `S`. These three were the licensing row
/// and the two controls of this file — each read the view's carrier argument as the
/// receiver's own type. The receiver is written `s: S`, as the two rows above write it.
#[test]
fn a_receiver_typed_as_a_view_over_the_param_is_refused() {
    let program = |ns: &str, spec: &str, param: &str, body: &str, ret: &str| {
        format!(
            r#"
namespace wi590.encl.{ns}
  import anthill.prelude.{{FiniteCollection, Iterable, List, Stream, Option, Pair}}
  sort W
    import anthill.prelude.{{FiniteCollection, Iterable, List, Stream, Option, Pair}}
    import anthill.prelude.FiniteCollection.{{collect}}
    sort S = ?
    sort Src = ?
    effects ES = ?
    requires {spec}[C = S, Element = Src, E = ES]
    operation use(s: {param}[C = S, Element = Src, E = ES]) -> {ret} effects ES = {body}
  end
end
"#
        )
    };
    let list = "List[T = Src]";
    let peeled = "Option[Pair[A = Src, B = Stream[T = Src, E = ES]]]";
    for (ns, spec, param, body, ret, callee) in [
        // a view of ANOTHER spec than the one the clause names
        ("b", "FiniteCollection", "Iterable", "collect(s)", list, "FiniteCollection"),
        // a view of the SAME spec
        ("c", "FiniteCollection", "FiniteCollection", "collect(s)", list, "FiniteCollection"),
        ("f", "Iterable", "Iterable", "Stream.splitFirst(Iterable.iterator(s))", peeled, "Iterable"),
    ] {
        let errs = crate::common::try_load_kb_with(&program(ns, spec, param, body, ret))
            .err()
            .unwrap_or_default();
        assert!(
            errs.iter().any(|e| e.contains(&format!("expected anthill.prelude.{callee}.C, got {param}["))
                && e.contains("a value typed at it is not a value of a sort that provides it")),
            "`s: {param}[C = S, …]` is not an `S`, so `{body}` must refuse it where the \
             carrier is expected; got: {errs:#?}"
        );
    }
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
