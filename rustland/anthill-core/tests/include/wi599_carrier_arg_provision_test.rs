//! WI-599 — typer: generalize WI-594's bare-receiver access-effect threading to a
//! CARRIER-PARAM-spec constructor field.
//!
//! WI-594 threads a bare spec receiver `s : Stream` into a field typed with that
//! SAME spec (`source: Stream[Src, ES]`) via the receiver's self-projection. The
//! THIN finite `map` the user preferred for WI-588 wraps the bare CARRIER value
//! directly — `FiniteCollection.map(c, f) = mapped(c, f)` — where `c` has the
//! carrier-param type `C` (a sort that merely PROVIDES the spec) and the combinator's
//! `source` field is typed with a spec (`Iterable[C = Source, …]` in the stdlib since
//! WI-590; the fixture below writes the same shape over its own `Coll`). The
//! carrier param `C`/`C2` is NOT the spec base, so WI-594's self-projection does not
//! fire and the field's source carrier + access effect leak as `??_`.
//!
//! `carrier_arg_provision_projection` rebuilds the argument's type from the carrier's
//! provision, keyed by the field's binding symbols so every param (carrier, element AND
//! effect) threads. That provision can be written on THREE declarations and each has its
//! own reader: the enclosing spec's own params for a spec METHOD
//! (`carrier_provision_short_bindings`, the first test below — the shape the stdlib thin
//! `FiniteCollection.map`/`filter` use); the ENCLOSING SORT's ambient `requires`
//! (`enclosing_requires_provision_bindings`, WI-20260828-MDWEW, whose rows live in
//! `wi_mdwew_bare_spec_arg_provision_test`); and the OPERATION's own
//! (`op_requires_provision_bindings`, WI-20260829-70XVH, at the bottom of this file).

/// A spec method `wrapmap(c: C, f)` wraps its bare carrier param `c` into a
/// combinator `Mapped` whose `source` field is typed with the enclosing spec
/// (`Coll[C = SrcC, Element = Src, E = ES]`). The element threads through the
/// sibling `fn` field; WITHOUT the fix the source carrier `SrcC` and access effect
/// `ES` stay unbound and the declared return `Coll[C = Mapped[SrcC = C, ES = E, …]]`
/// is rejected. With the fix they thread from the enclosing spec's own params.
#[test]
fn spec_method_bare_carrier_threads_source_and_effect() {
    let src = r#"
namespace test.wi599
  import anthill.prelude.{List, Int64, Modify, EffectsRuntime}

  sort Coll
    import anthill.prelude.{List, Modify, EffectsRuntime}
    sort C = ?
    sort Element = ?
    effects E = ?

    operation collect(c: C) -> List[T = Element] effects E

    operation wrapmap[Dst, EffP](c: C, f: (x: Element) -> Dst @ {EffP, -Modify[x]})
      -> Coll[C = Mapped[SrcC = C, Src = Element, T = Dst, ES = E, EF = EffP], Element = Dst, E = {E, EffP}] =
      mk(c, f)
  end

  sort Mapped
    import anthill.prelude.{List, EffectsRuntime}
    import anthill.prelude.List.{nil}
    sort SrcC = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    entity mk(source: Coll[C = SrcC, Element = Src, E = ES], fn: (Src) -> T @ {EF})
    provides Coll[C = Mapped, Element = T, E = {ES, EF}]
    operation collect(m: Mapped) -> List[T = T] effects {ES, EF} = nil
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.is_empty(),
        "a bare carrier value wrapped into a carrier-param-spec field should thread \
         the source carrier AND access effect from the carrier's provision and load \
         clean:\n{}",
        errs.join("\n")
    );
}

use crate::common::assert_refused_naming;

// ── WI-20260829-70XVH — the OPERATION's own `requires`, the third and last face ────────
//
// The two faces above read a SORT's declaration: the op is ON the field's spec
// (`carrier_provision_short_bindings`), or the ENCLOSING SORT requires it
// (`enclosing_requires_provision_bindings`). A FREE operation — one whose receiver is its
// own type parameter rather than its sort's carrier — carries the clause ITSELF, and may
// sit in no sort at all, or in the DATA sort it constructs, whose parameters say nothing
// about the source. WI-599 excluded that face on a reason WI-942 has since retired (an op's
// own parameters are in `TypingEnv::param_rigids` now, so a clause `Ref` resolves to the
// rigid the body is checked at).
//
// It is unread in TWO places, and the general free combinator the ticket wants needs both:
// the operation's BODY, typing the construction (`op_requires_provision_bindings`), and the
// CALL SITE, grounding the operation's own type parameters
// (`bind_op_type_params_from_op_requires`).
//
// THE BACK-OUTS, MEASURED — each run over every row in this file, with the row(s) that fell:
//   1. body face returns `None` at entry            → `free_op_requires_clause_threads_…`
//   2. call face returns at entry (it reports       → FOUR rows: `general_free_op_grounds_…`,
//      nothing, so the back-out is `return;`)          `a_clause_about_another_parameter_…`,
//                                                      `a_clause_whose_carrier_is_the_…` and
//                                                      `the_stdlib_combinators_are_general_…`
//                                                      — the stdlib widening DEPENDS on this
//                                                      pass, which is why it is one commit
//   3. the already-bound skip removed               → NOTHING (see that row's own note)
//   4. the body face's "about this argument" gate   → `free_op_clause_about_another_param_…`
//      widened to any clause naming the spec
//   5. the call face's carrier search widened to    → `a_clause_about_another_parameter_…`
//      the first typed argument
//   6. the carrier read narrowed back to the        → `a_clause_whose_carrier_is_the_…`
//      operation's OWN parameters
//   7. either stdlib signature restored to its      → `the_stdlib_combinators_are_general_…`
//      X13YV receiver-method form
// `spec_method_bare_carrier_threads_source_and_effect` (the WI-599 row) and
// `free_op_carrier_return_is_pinned_by_expected` pass under all of them, by design.

/// The BODY face, and the free-op twin of `ambient_requires` one file over. `Walk` is the
/// spec `Mapped`'s field is typed on; `freemap` is a FREE operation whose source is its own
/// type parameter `Sc` and which carries `requires Walk[C = …, Element = S, E = EffS]`.
///
/// `clause_carrier` is the parameter the clause is written ABOUT (the driving row writes the
/// argument's own `Sc`; the control writes the unrelated `Other`) and `ret` the declared
/// return, so one fixture serves the driving row and both controls.
fn free_op_requires(clause_carrier: &str, ret: &str) -> Vec<String> {
    let src = format!(
        r#"
namespace test.wi70xvh.body
  import anthill.prelude.{{Option, Modify}}

  sort Seq
    import anthill.prelude.Option
    sort Elem = ?
    effects Row = ?
    operation firstOf(s: Seq) -> Option[T = s.Elem] effects s.Row
    provides Walk[C = Seq, Element = Elem, E = Row]
    operation walk(s: Seq) -> Seq[Elem = s.Elem, Row = s.Row] = s
  end

  sort Walk
    sort C = ?
    sort Element = ?
    effects E = ?
    operation walk(c: C) -> Seq[Elem = Element, Row = E]
  end

  sort Mapped
    import anthill.prelude.{{Option, Function}}
    import anthill.prelude.Option.{{none}}
    sort Source = ?
    sort Src = ?
    sort T = ?
    effects ES = ?
    effects EF = ?
    requires Walk[C = Source, Element = Src, E = ES]
    entity mk(source: Walk[C = Source, Element = Src, E = ES], fn: (Src) -> T @ {{EF}})
    provides Seq[Elem = T, Row = {{ES, EF}}]
    operation firstOf(m: Mapped) -> Option[T = T] effects {{ES, EF}} = none
  end

  -- THE FREE OPERATION: no enclosing sort, and the source is its OWN type parameter.
  operation freemap[Sc, Other, S, Dst, EffS, EffP](c: Sc, o: Other, f: (x: S) -> Dst @ {{EffP, -Modify[x]}})
    -> {ret}
    requires Walk[C = {clause_carrier}, Element = S, E = EffS] =
    mk(c, f)
end
"#
    );
    crate::common::try_load_kb_with(&src)
        .err()
        .unwrap_or_default()
}

/// DRIVES the body face. The return goes through `Mapped`'s own provision, so `expected`
/// pins nothing (`free_op_carrier_return_is_pinned_by_expected` below is the record of what
/// happens when it does) and only the operation's own `requires Walk[C = Sc, …]` can supply
/// `Source` and `ES`.
///
/// MEASURED: with `op_requires_provision_bindings` returning `None` at entry, this test
/// ALONE goes red — `got Mapped[T = ?Dst, Source = ??_, Src = ?S, ES = ??_, …]`, the same
/// leak the two sort faces were built for, one declaration over.
#[test]
fn free_op_requires_clause_threads_the_field_specs_params() {
    let errs = free_op_requires("Sc", "Seq[Elem = Dst, Row = {EffS, EffP}]");
    assert!(
        errs.is_empty(),
        "a FREE operation's own `requires` is the third place \"this carrier provides that \
         spec\" can be written, and it must thread the field's params like the other two:\n{}",
        errs.join("\n")
    );
}

/// CONTROL — the clause must be ABOUT THIS ARGUMENT. Written about `Other`, it says nothing
/// about `c : Sc`, so nothing licenses the construction. Green with the face backed out too,
/// by design: it is the WIDENED gate — a face that took the first clause naming the field's
/// spec whatever it is about — that this catches. MEASURED: neutralize the
/// `substitute_body_rigids(cval) == arg_id` comparison and this test alone goes RED, by
/// loading a program nothing licenses.
#[test]
fn free_op_clause_about_another_param_does_not_license() {
    let errs = free_op_requires("Other", "Seq[Elem = Dst, Row = {EffS, EffP}]");
    // `Source = ??_` is the LICENCE WITHHELD: the field's carrier param was never bound, so
    // it rigidified unwritten.
    assert_refused_naming(
        &errs,
        &["Source = ??_"],
        "an op-level `requires` about a DIFFERENT type parameter must not license this \
         argument",
    );
}

/// CONTROL, and the record of why the driving row returns through a provision: with the
/// return spelled as the constructed carrier, `expected` seeds every param the field loops
/// left free, so this loads whether or not anything threaded. GREEN both with the face and
/// with it backed out — the same reading `ambient_requires_carrier_return_is_pinned_by_-
/// expected` records for the sort face, and the reason the stdlib's own general combinator
/// (whose return IS the carrier) is not evidence for this half.
#[test]
fn free_op_carrier_return_is_pinned_by_expected() {
    let errs = free_op_requires(
        "Sc",
        "Mapped[Source = Sc, Src = S, T = Dst, ES = EffS, EF = EffP]",
    );
    assert!(errs.is_empty(), "{}", errs.join("\n"));
}

// ── the CALL-SITE half: grounding the operation's OWN type parameters ─────────────────

/// The general free combinator the ticket exists for, over the real stdlib: any `Iterable`
/// source, the source KEPT in the return (`Source = Sc`, so a finiteness witness can still
/// read it), and the element and access effect named only by the clause.
///
/// `clause_carrier` is the parameter the clause is written about and `bracket` what the call
/// site writes, so one fixture serves the driving row and both controls. The second argument
/// is a `List[T = Bool]` and the first a `List[T = Int64]`: the two DISAGREE about the
/// element, which is what lets the control below separate "read the clause" from "read the
/// first argument".
fn general_free_op(clause_carrier: &str, bracket: &str) -> String {
    format!(
        r#"
namespace test.wi70xvh.call
  import anthill.prelude.{{List, Int64, Bool, Modify, Iterable, MappedStream, FiniteCollection}}
  import anthill.prelude.MappedStream.{{mapped}}
  import anthill.prelude.FiniteCollection.{{collect}}

  operation gmap[Sc, Other, S, Dst, EffS, EffP](s: Sc, o: Other, f: (x: S) -> Dst @ {{EffP, -Modify[x]}})
    -> MappedStream[Source = Sc, Src = S, T = Dst, ES = EffS, EF = EffP]
    requires Iterable[C = {clause_carrier}, Element = S, E = EffS] =
    mapped(s, f)

  -- The digit fold `acc * 10 + x`: it pins COUNT, ORDER and VALUE at once, where a sum
  -- would survive a dropped or reordered element.
  operation digits(xs: List[T = Int64]) -> Int64 =
    List.foldLeft(xs, 0, lambda (acc, x) -> acc * 10 + x)

  operation mapped_list() -> Int64 =
    digits(collect(gmap{bracket}([1, 2, 3, 4], [true, false], lambda (n: Int64) -> n * 2)))
end
"#
    )
}

/// DRIVES the call-site half, and drives it to a VALUE. `S` and `EffS` appear in no
/// argument the call supplies — `Sc` alone is determined — so before this the author had to
/// write `gmap[S = Int64, EffS = {}](…)`, repeating what `List provides Iterable[Element =
/// T, E = {}]` already says.
///
/// MEASURED: with `bind_op_type_params_from_op_requires` RETURNING AT ENTRY (it reports
/// nothing, so the back-out is a bare `return;`), FOUR rows go red at LOAD — this one,
/// `a_clause_about_another_parameter_names_that_parameters_element`,
/// `a_clause_whose_carrier_is_the_enclosing_sorts_parameter_still_grounds` and
/// `the_stdlib_combinators_are_general_over_any_iterable_source`. This one reports
/// `type mismatch in gmap.type_arg: expected a type for 'S', got unconstrained`.
#[test]
fn general_free_op_grounds_its_element_from_the_arguments_provision() {
    let mut interp = crate::common::interp_for(&general_free_op("Sc", ""));
    let got = interp
        .call("test.wi70xvh.call.mapped_list", &[])
        .expect("mapped_list");
    assert!(
        matches!(got, anthill_core::eval::Value::Int(2468)),
        "[1,2,3,4] doubled is [2,4,6,8], whose digit fold is 2468; got {got:?}"
    );
}

/// CONTROL — the clause decides WHICH argument answers, and the two arguments disagree.
/// Written about `Other`, the clause says the element comes from the `List[T = Bool]`, so
/// `S = Bool` and the `(n: Int64)` callback contradicts it. Reading the FIRST argument
/// instead — the reading a search that did not key on the clause would take — grounds
/// `S = Int64` and the program loads.
///
/// RED BOTH WAYS, and the two reds are different messages — which is the point, and why the
/// token asserted is the clause's own answer rather than "something failed". With the pass
/// backed out `S` is unconstrained (`gmap.type_arg`); with the search widened to the first
/// argument the program LOADS. Only reading the clause produces `expected Bool -> ?Dst`.
#[test]
fn a_clause_about_another_parameter_names_that_parameters_element() {
    let errs = crate::common::try_load_kb_with(&general_free_op("Other", ""))
        .err()
        .unwrap_or_default();
    // `expected Bool -> ?Dst` is the clause READ: `S` came from the `List[T = Bool]` the
    // clause names, so the `(n: Int64)` callback contradicts it. Reading the first argument
    // instead grounds `S = Int64` and the program loads with no message at all.
    assert_refused_naming(
        &errs,
        &["expected Bool -> ?Dst"],
        "the clause names WHICH argument's provision answers; reading the first argument \
         instead would accept an `Int64` callback over a `List[T = Bool]` source",
    );
}

/// CONTROL — a WRITTEN BRACKET outranks the clause. `seed_op_type_args` runs above this
/// pass and the pass fills only still-free parameters, so `gmap[S = Bool]` keeps `S = Bool`
/// and the `(n: Int64)` callback is refused.
///
/// IT PASSES UNDER EVERY BACK-OUT I COULD BUILD, and that is stated rather than dressed up:
/// TWO independent mechanisms hold it, so neutralizing either leaves the other. With the
/// call-site half off, nothing grounds and the bracket is still what `S` is; with the pass's
/// own `subst.resolve_as_value(target).is_some()` skip removed, `Substitution::bind_term`
/// refuses to overwrite an existing binding on its own (it flags a contradiction instead of
/// replacing), so the bracket survives that too — MEASURED, all seven rows green with the
/// skip removed. What this row pins is the user-visible rule, not which guard enforces it.
#[test]
fn a_written_bracket_outranks_the_clause() {
    let errs = crate::common::try_load_kb_with(&general_free_op("Sc", "[S = Bool]"))
        .err()
        .unwrap_or_default();
    // The same token, and here it is the BRACKET that put `Bool` there. Overwriting it from
    // the clause grounds `S = Int64` and the program loads.
    assert_refused_naming(
        &errs,
        &["expected Bool -> ?Dst"],
        "a written bracket is the author's answer and the clause must not overwrite it",
    );
}

/// FOUND BY `/code-review`, and it is the read that decides which ARGUMENT the clause is
/// about — a different question from which PARAMETER the clause may bind.
///
/// §5.3 says an op-level clause names parameters of its own scope and its enclosing sort's
/// as ONE list, and an operation on a parametric sort routinely takes its carrier through
/// the SORT's parameter: `wrap[El, …](x: C, …) requires Iterable[C = C, Element = El, …]`.
/// The first cut required the CARRIER to be one of the operation's own too, which made that
/// whole clause unreadable — `El` stayed `unconstrained` with nothing saying why, and the
/// function's own doc claimed the opposite ("each element naming a type parameter of the
/// operation is bound from it").
///
/// The BINDING side keeps the narrow test, and this row cannot show that: a sort parameter
/// is the sort INSTANCE's and not this call's. `free_op_clause_about_another_param_does_not_-
/// license` and the `own` gate's own doc carry that half.
///
/// DRIVES: the callback is UNANNOTATED, so nothing but the clause can say what `El` is —
/// annotate it and the row loads with the pass backed out, which is how the first cut's gap
/// hid. MEASURED: narrow the carrier read back to `clause_named_op_type_param` and this row
/// ALONE goes red, `expected a type for 'El', got unconstrained`.
#[test]
fn a_clause_whose_carrier_is_the_enclosing_sorts_parameter_still_grounds() {
    const SRC: &str = r#"
namespace test.wi70xvh.sortcarrier
  import anthill.prelude.{List, Int64, Iterable, MappedStream, Modify, FiniteCollection}

  sort Box
    import anthill.prelude.{List, Int64, Iterable, MappedStream, Modify}
    import anthill.prelude.MappedStream.{mapped}
    -- the carrier is the SORT's parameter; `El` is the OPERATION's.
    sort C = ?
    operation wrap[El, Dst, EffP](x: C, f: (y: El) -> Dst @ {EffP, -Modify[y]})
      -> MappedStream[Source = C, Src = El, T = Dst, ES = {}, EF = EffP]
      requires Iterable[C = C, Element = El, E = {}] =
      mapped(x, f)
  end

  operation digits(xs: List[T = Int64]) -> Int64 =
    List.foldLeft(xs, 0, lambda (acc, x) -> acc * 10 + x)

  operation drive() -> Int64 =
    digits(FiniteCollection.collect(Box.wrap([1, 2, 3, 4], lambda n -> n * 2)))
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    let got = interp
        .call("test.wi70xvh.sortcarrier.drive", &[])
        .expect("drive");
    assert!(
        matches!(got, anthill_core::eval::Value::Int(2468)),
        "the clause's carrier may name the enclosing SORT's parameter — that read says which \
         ARGUMENT the clause is about, not which parameter it may bind; got {got:?}"
    );
}

/// THE PAYOFF, over the real stdlib. `MappedStream.map` and `FilteredStream.filter` were
/// narrowed to their OWN carrier by WI-20260829-X13YV, on the measurement that the general
/// form's element did not ground; that is the narrowing this ticket exists to lift, and
/// `combinators.anthill` carries the note. Both now take ANY `Iterable` source, and a BARE
/// LIST — the shape the receiver-method spelling refused — is the row that says so.
///
/// The chained and mixed hops ride along because generalizing the INPUT must not move the
/// dot ladder: `.map` on a mapped stream still resolves to `MappedStream.map` (the ladder
/// reads the receiver's own sort first) and `.size()` still reads finiteness off `Source`.
/// Those three are X13YV's own rows re-asserted here against the widened signature; they
/// pass either way and are here so a regression names the widening rather than the chain.
///
/// MEASURED TWO WAYS, and the second is why the stdlib widening and the typer pass are one
/// commit: restore either signature to its X13YV receiver-method form
/// (`map[Dst, EffP](m: MappedStream, …)`) and this row fails to LOAD at all —
/// `type mismatch in map.m (op-arg): expected MappedStream, got List[T = Int64]`; and back
/// out `bind_op_type_params_from_op_requires` instead, leaving the widened signatures, and it
/// fails to load too — the widened `map` cannot ground its own `S` without that pass.
#[test]
fn the_stdlib_combinators_are_general_over_any_iterable_source() {
    const SRC: &str = r#"
namespace test.wi70xvh.stdlib
  import anthill.prelude.{List, Int64, Bool, MappedStream, FilteredStream, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size, collect}

  -- the digit fold `acc * 10 + x`: COUNT, ORDER and VALUE at once.
  operation digits(xs: List[T = Int64]) -> Int64 =
    List.foldLeft(xs, 0, lambda (acc, x) -> acc * 10 + x)

  -- A BARE LIST into each combinator: the general form, refused before this ticket.
  operation map_from_list() -> Int64 =
    digits(collect(MappedStream.map([1, 2, 3, 4], lambda n -> n * 2)))
  operation filter_from_list() -> Int64 =
    digits(collect(FilteredStream.filter([1, 2, 3, 4], lambda n -> n > 1)))

  -- X13YV's own chains, unchanged by the widening.
  operation chained_map() -> Int64 =
    digits([1, 2, 3, 4].map(lambda n -> n * 2).map(lambda n -> n + 1).collect())
  operation chained_filter() -> Int64 =
    digits([1, 2, 3, 4].filter(lambda n -> n > 1).filter(lambda n -> n < 4).collect())
  operation mixed() -> Int64 =
    digits([1, 2, 3, 4].map(lambda n -> n * 2).filter(lambda n -> n > 4).collect())
  operation chained_size() -> Int64 =
    [1, 2, 3, 4].map(lambda n -> n * 2).map(lambda n -> n + 1).size()
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    let run = |interp: &mut anthill_core::eval::Interpreter, op: &str| -> i64 {
        match interp
            .call(&format!("test.wi70xvh.stdlib.{op}"), &[])
            .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
        {
            anthill_core::eval::Value::Int(i) => i,
            other => panic!("call {op}: expected Int, got {other:?}"),
        }
    };
    assert_eq!(run(&mut interp, "map_from_list"), 2468, "[1,2,3,4] * 2");
    assert_eq!(run(&mut interp, "filter_from_list"), 234, "keep > 1");
    assert_eq!(run(&mut interp, "chained_map"), 3579, "* 2 then + 1");
    assert_eq!(run(&mut interp, "chained_filter"), 23, "> 1 then < 4");
    assert_eq!(run(&mut interp, "mixed"), 68, "* 2 then > 4");
    assert_eq!(run(&mut interp, "chained_size"), 4);
}
