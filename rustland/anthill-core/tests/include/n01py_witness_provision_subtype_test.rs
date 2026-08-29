//! WI-20260829-N01PY — a value whose provision comes from a WITNESS was refused at a
//! SPEC-TYPED PARAMETER, while the same value dispatched that spec's operations fine.
//!
//! THE TWO READERS OF ONE RELATION. `load_provides_clause` files
//! `SortProvidesInfo(sort_ref = <the ENCLOSING sort>, …)`, so a WITNESS — which names its
//! carrier only in the spec's carrier BINDING (`sort MappedStreamFinite provides
//! FiniteCollection[C = MappedStream[…]]`) — files under the WITNESS and not under the
//! carrier. DISPATCH does not ask the carrier-keyed question: it reads the spec-base
//! bucket and matches each provision's carrier binding, so it sees the witness. The
//! SUBTYPE relation asked `sort_provides`, which is carrier-keyed, and answered "no" for
//! a carrier that is fully spoken for. `provision_carriers_of_spec`'s doc had already
//! written that asymmetry down for the eq-derive reader; this is the same asymmetry at
//! the subtype reader, where its cost is a refused program.
//!
//! WHAT THE TICKET SAID AND WHAT IS MEASURED. WI-20260829-N01PY was filed as "a LAZY
//! STREAM cannot feed an EAGER consumer, so `xs.map(f).length()` and every shape like it
//! is refused", with three candidate repairs and the note that the choice was a design
//! question. Re-measured, two of the three are already delivered:
//!
//!   xs.map(f).size()      LOADS and evaluates   (c) — WI-590's finiteness witness
//!   xs.map(f).collect()   LOADS and evaluates   (b) — the materializing step
//!   length(xs.map(f))     REFUSED               — and correctly: `List.length` is
//!                                                 `List`'s own operation, and the
//!                                                 generic consumer is
//!                                                 `FiniteCollection.size`
//!
//! So the ticket's four tracked cells were calling a `List` operation on a value that is
//! not a `List`. What was NOT available is repair (a) — "an eager consumer accepting any
//! `FiniteCollection` rather than a concrete `List`" — and it was not a road not taken:
//! an operation an AUTHOR declares over the spec refused the very value `.size()`
//! dispatches on. [`an_author_declared_consumer_takes_a_mapped_stream`] is that row.
//!
//! WHAT FAILS WHEN THE FIX IS BACKED OUT — measured on the FULL WORKSPACE, by making
//! `witness_provides_admissibly` return `false` at its first statement (a MUTATION, not a
//! deletion: deleting the call sites would compile the function out and measure a
//! different tree). **6085 passed, 8 failed**, and all eight are in this file and the
//! capability matrix:
//!
//!   * [`a_witness_provided_carrier_is_admissible_at_a_spec_parameter`] and
//!     [`a_bare_witnessed_carrier_is_admissible_too`] — the minimal arms, one per
//!     bare-expected arm of `types_compatible_term_dispatch`;
//!   * [`an_author_declared_consumer_takes_a_mapped_stream`] and
//!     [`an_author_declared_consumer_takes_a_filtered_stream`] — the stdlib arms;
//!   * [`the_same_shape_over_a_finite_source_loads`] — an arm too, and it says so at its
//!     own site: it is what makes [`an_infinite_source_is_still_refused`] mean something;
//!   * [`a_self_carried_provision_beside_a_witness_does_not_recurse`] — an arm for the
//!     VALUE it asserts; separately, without the re-entrancy guard (and with the leg) the
//!     same program overflows the stack, which is the regression that row exists for;
//!   * [`a_denoted_effect_row_is_a_known_gap`] — its GROUND-ROW CONTROL needs the leg, so
//!     the pair moves as a unit even though the gap half is a refusal either way;
//!   * `typer_capability_matrix_test::an_author_declared_consumer_takes_a_finite_carrier`
//!     — its two `AUTHOR's consumer <- map/filter` cells and no others; that table's own
//!     doc records which of its rows are controls.
//!
//! NOTHING ELSE IN THE WORKSPACE MOVES, which is what says the leg only ever turns a
//! refusal into an accept: it is reached exactly when `sort_sym_compatible` and
//! `sort_provides_admissibly` have both already refused.
//!
//! AND THESE PASS EITHER WAY, BY DESIGN — they are here to pin the boundary, not to
//! measure the change: [`a_direct_provider_is_the_control`] and
//! [`the_same_consumer_over_a_list_is_the_control`] (the provision route the
//! carrier-keyed walk always saw — the second one needed its OWN program to earn that,
//! see [`STDLIB_CONTROL_SRC`]), [`a_non_provider_is_still_refused`],
//! [`an_unmet_witness_condition_is_still_refused`] and
//! [`an_infinite_source_is_still_refused`] (the conditional gate the leg must not waive),
//! and [`the_erased_iterable_map_return_is_still_refused`].
//!
//! ONE BOUNDARY IS STATED AND NOT TESTED, deliberately. The subtype relation has no call
//! site and no enclosing operation, so the leg resolves with an EMPTY
//! `available_requires`: a witness whose condition is met only by the CALLER's own
//! `requires` is still refused, where dispatch at the same point would find it in scope.
//! That is strictly narrower than dispatch and strictly wider than before the leg
//! existed. It is written here rather than pinned by a cell because a cell for it would
//! be red for a reason no one could separate from the arms above until the scope is
//! actually threaded — see [`witness_provides_admissibly`]'s own doc, which owns the
//! decision.

use crate::common::{interp_for, try_load_kb_with};

/// A user-defined spec with a DIRECT provider, a WITNESS provider whose provision is
/// keyed on `Wrap[S = S]` and GATED by `requires Cap[C = S, …]`, and a sort that provides
/// nothing at all.
///
/// THE WITNESS'S `Element` IS CONCRETE HERE ON PURPOSE, and the stdlib arm is what says
/// why that is not enough on its own: a witness head that binds a spec sibling to an IMPL
/// PARAM shared with the carrier binding (`FiniteCollection[C = MappedStream[T = T], …,
/// Element = T]`) exercises a matcher path this fixture does not, and the first cut of the
/// fix passed here while failing there.
fn fixture(use_expr: &str) -> String {
    format!(
        r#"
namespace n01py
  import anthill.prelude.{{Int64}}

  sort Cap
    sort C = ?
    sort Element = ?
    operation get(c: C) -> Element
    -- A CONCRETE-returning member, so the test's consumer can return a plain `Int64`.
    -- `sink(c: Cap) -> c.Element` would drag in a SECOND reader — the return
    -- PROJECTION, which does not consult a witness provision either ("type `Wrap` has no
    -- member `Element`") — and a fixture that trips it measures that reader, not this
    -- one. `get` stays declared so `Element` is a real spec parameter and
    -- `spec_carrier_param` still has two to choose between.
    operation tag(c: C) -> Int64
  end

  sort Direct
    import anthill.prelude.{{Int64}}
    import n01py.Cap
    entity direct(v: Int64)
    provides Cap[C = Direct, Element = Int64]
    operation get(d: Direct) -> Int64 = match d case direct(x) -> x
    operation tag(d: Direct) -> Int64 = match d case direct(x) -> x
  end

  -- A witnessed carrier with NO TYPE PARAMETERS, so the subtype comparison is
  -- `(sort_ref, sort_ref)` and not `(parameterized, sort_ref)` — a DIFFERENT arm.
  sort Plain
    import anthill.prelude.{{Int64}}
    entity plain(v: Int64)
  end

  sort PlainWitness
    import anthill.prelude.{{Int64}}
    import n01py.{{Cap, Plain}}
    import n01py.Plain.{{plain}}
    provides Cap[C = Plain, Element = Int64]
    operation get(p: Plain) -> Int64 = match p case plain(x) -> x
    operation tag(p: Plain) -> Int64 = match p case plain(x) -> x
  end

  -- Provides NOTHING: the witness's condition must not be dischargeable for it.
  sort Opaque
    import anthill.prelude.{{Int64}}
    entity opaque(v: Int64)
  end

  sort Wrap
    sort S = ?
    entity wrap(inner: S)
  end

  sort WrapWitness
    import anthill.prelude.{{Int64}}
    import n01py.{{Cap, Wrap}}
    import n01py.Wrap.{{wrap}}
    sort S = ?
    requires Cap[C = S, Element = Int64]
    provides Cap[C = Wrap[S = S], Element = Int64]
    operation get(w: Wrap[S = S]) -> Int64 =
      match w case wrap(i) -> Cap.get(i)
    operation tag(w: Wrap[S = S]) -> Int64 =
      match w case wrap(i) -> Cap.tag(i)
  end

  import n01py.Direct.{{direct}}
  import n01py.Opaque.{{opaque}}
  import n01py.Plain.{{plain}}
  import n01py.Wrap.{{wrap}}

  -- The consumer under test: an ordinary operation declared over the SPEC.
  operation sink(c: Cap) -> Int64 = Cap.tag(c)

  operation use() -> Int64 = {use_expr}
end
"#
    )
}

fn drive(use_expr: &str) -> i64 {
    let mut interp = interp_for(&fixture(use_expr));
    let v = interp
        .call("n01py.use", &[])
        .unwrap_or_else(|e| panic!("call n01py.use over `{use_expr}`: {e:?}"));
    v.as_int()
        .unwrap_or_else(|| panic!("expected an Int64 from `{use_expr}`, got {v:?}"))
}

fn errors_for(use_expr: &str) -> Vec<String> {
    try_load_kb_with(&fixture(use_expr))
        .err()
        .unwrap_or_else(|| panic!("`{use_expr}` was expected to be REFUSED, but it loaded clean"))
}

/// THE TICKET, in its minimal form. `Wrap[S = Direct]` conforms to the bare spec `Cap`
/// because `WrapWitness` says so — and not "it loads": the projection runs, so the value
/// really did travel through the spec-typed parameter and dispatch really did find the
/// witness's `get` on the other side.
#[test]
fn a_witness_provided_carrier_is_admissible_at_a_spec_parameter() {
    assert_eq!(
        drive("sink(wrap(inner: direct(v: 7)))"),
        7,
        "the witness provides `Cap` for `Wrap[S = Direct]`, so the value is admissible at \
         `sink(c: Cap)` and `Cap.get` reaches `WrapWitness.get`, which unwraps and \
         delegates to `Direct.get`",
    );
}

/// THE SIBLING ARM, and it is a row rather than a footnote because the first cut of the
/// fix MISSED IT. `Plain` has no type parameters, so `Plain` vs the bare `Cap` compares
/// at `(sort_ref, sort_ref)` while `Wrap[S = Direct]` compares at `(parameterized,
/// sort_ref)` — two arms of `types_compatible_term_dispatch`, and wiring the leg into one
/// left the other refusing. Nothing in the stdlib has this shape (`MappedStream` and
/// `FilteredStream` are both parameterized), so only a fixture could find it.
#[test]
fn a_bare_witnessed_carrier_is_admissible_too() {
    assert_eq!(drive("sink(plain(v: 7))"), 7);
}

/// CONTROL — PASSES EITHER WAY BY DESIGN. `Direct` files its provision under ITSELF, so
/// the carrier-keyed `sort_provides` always saw it. Its presence is what says the
/// spec-typed parameter was never broken at large: the axis that decides the verdict is
/// HOW THE PROVISION IS FILED, not that a spec type is in the parameter position.
#[test]
fn a_direct_provider_is_the_control() {
    assert_eq!(drive("sink(direct(v: 7))"), 7);
}

/// CONTROL — PASSES EITHER WAY BY DESIGN, and it is the one that keeps the fix sound. A
/// witness is a CONDITIONAL instance: `WrapWitness requires Cap[C = S, …]`, so a `Wrap`
/// over a carrier that provides nothing must stay refused. The leg defers to `resolve`
/// precisely so this verdict is the SAME one dispatch reaches rather than a second
/// opinion — accepting on the provision HEAD alone would make every `Wrap` a `Cap`.
#[test]
fn an_unmet_witness_condition_is_still_refused() {
    let errs = errors_for("sink(wrap(inner: opaque(v: 7)))");
    assert!(
        errs.iter()
            .any(|e| e.contains("expected Cap") && e.contains("Wrap[S = Opaque]")),
        "`Opaque` provides no `Cap`, so the witness's condition cannot be discharged and \
         `Wrap[S = Opaque]` must not conform; got: {errs:#?}",
    );
}

/// CONTROL — PASSES EITHER WAY BY DESIGN. A sort that provides the spec by NO route is
/// refused, which is what says the leg widened admissibility rather than deleting the
/// check.
#[test]
fn a_non_provider_is_still_refused() {
    let errs = errors_for("sink(opaque(v: 7))");
    assert!(
        errs.iter()
            .any(|e| e.contains("expected Cap") && e.contains("Opaque")),
        "got: {errs:#?}",
    );
}

/// THE LEG ASKS A QUESTION THAT CAN BECOME ITS OWN SUB-QUESTION, and before the guard
/// that was a STACK OVERFLOW — measured, on a program that was a clean type error without
/// the leg, which is what makes this a regression row and not a hypothetical.
///
/// THE SHAPE: `Sp` is a spec with two provisions — a witness for `A`, and one whose
/// carrier binding is `Sp` ITSELF. Asking "is `A` a `Sp`" resolves `Sp[C = A]`; matching
/// the second candidate compares `A` against `Sp` (`dispatch_values_match` →
/// `types_lesseq`), which is the question we started from. `resolve`'s own cycle stack
/// cannot see it: that stack is allocated per `resolve` call, so it does not span this
/// boundary. `KnowledgeBase::witness_admissibility_in_flight` does.
///
/// AND THE ANSWER IS THE RIGHT ONE, not merely a non-crash: `A` genuinely provides `Sp`
/// through its witness, so the value IS admissible and the projection runs. The
/// self-carried rival simply cannot answer, which is what re-entry returning `false`
/// says.
///
/// FOUND BY /code-review, which named the shape from the call graph; the fixture and the
/// overflow are the measurement of it.
#[test]
fn a_self_carried_provision_beside_a_witness_does_not_recurse() {
    let src = r#"
namespace n01pyrec
  import anthill.prelude.{Int64}
  sort Sp
    sort C = ?
    operation tag(c: C) -> Int64
  end
  sort A
    import anthill.prelude.{Int64}
    entity a(v: Int64)
  end
  sort AW
    import anthill.prelude.{Int64}
    import n01pyrec.{Sp, A}
    import n01pyrec.A.{a}
    provides Sp[C = A]
    operation tag(x: A) -> Int64 = match x case a(v) -> v
  end
  -- THE RIVAL whose carrier binding is the SPEC itself.
  sort SpW
    import anthill.prelude.{Int64}
    import n01pyrec.Sp
    provides Sp[C = Sp]
    operation tag(x: Sp) -> Int64 = 0
  end
  import n01pyrec.A.{a}
  operation sink(c: Sp) -> Int64 = Sp.tag(c)
  operation use() -> Int64 = sink(a(v: 7))
end
"#;
    let mut interp = interp_for(src);
    let v = interp
        .call("n01pyrec.use", &[])
        .unwrap_or_else(|e| panic!("call n01pyrec.use: {e:?}"));
    assert_eq!(
        v.as_int(),
        Some(7),
        "`A` provides `Sp` through `AW`; the self-carried `SpW` cannot answer for `A` and \
         must simply drop out, not drive the question into itself",
    );
}

/// A KNOWN GAP, PAIRED WITH ITS CONTROL — the one arm of the subtype relation this leg
/// does NOT reach, recorded rather than left to be rediscovered (found by /code-review).
///
/// `types_compatible` routes to `types_compatible_view_structural` whenever a side is not
/// a hash-consed term, and a DENOTED effect row (`EF = {Modify[k]}`) is such a side. That
/// arm's own comment promises provider admissibility stays carrier-symmetric, and with
/// the witness leg it no longer is: the two rows below are the same program but for the
/// effect row, and they disagree.
///
/// IT IS NOT A ONE-LINE OMISSION. `witness_provides_admissibly` asks through a
/// `SortGoal`, whose bindings are `TermId`s, and a denoted binding is precisely what has
/// none. Wiring the leg into that arm was tried and MEASURED INERT — `walk_view` hands
/// back a `Value::Node`, the branch never fires, the verdict does not move — so it was
/// removed rather than shipped as a path nothing can drive. WI-20260829-2NMXA owns the
/// increment.
///
/// THE CONTROL IS WHAT MAKES THIS A GAP AND NOT A DESIGN: strip the `Modify[k]` and the
/// identical program loads. FLIP BOTH ROWS TOGETHER when WI-20260829-2NMXA lands.
#[test]
fn a_denoted_effect_row_is_a_known_gap() {
    const DENOTED: &str = r#"
namespace n01pyden
  import anthill.prelude.{List, Int64, FiniteCollection, MappedStream, Cell, Modify}
  operation total(c: FiniteCollection) -> Int64 effects c.E = FiniteCollection.size(c)
  operation f(k: Cell[V = Int64],
              m: MappedStream[Source = List[T = Int64], Src = Int64, T = Int64,
                              ES = {}, EF = {Modify[k]}]) -> Int64 effects {Modify[k]} =
    total(m)
end
"#;
    const GROUND: &str = r#"
namespace n01pygr
  import anthill.prelude.{List, Int64, FiniteCollection, MappedStream}
  operation total(c: FiniteCollection) -> Int64 effects c.E = FiniteCollection.size(c)
  operation f(m: MappedStream[Source = List[T = Int64], Src = Int64, T = Int64,
                              ES = {}, EF = {}]) -> Int64 = total(m)
end
"#;
    let errs = try_load_kb_with(DENOTED).err().unwrap_or_else(|| {
        panic!(
            "THE GAP HAS CLOSED — the denoted-row spelling now loads. That is good news:              delete this test's `KnownGap` half, keep the control, and close              WI-20260829-2NMXA in the same commit."
        )
    });
    assert!(
        errs.iter()
            .any(|e| e.contains("expected FiniteCollection") && e.contains("MappedStream")),
        "still refused, but for a DIFFERENT reason than this cell records: {errs:#?}",
    );
    if let Err(errs) = try_load_kb_with(GROUND) {
        panic!(
            "THE CONTROL MUST LOAD — without it the row above is satisfied by any refusal              of a declared `MappedStream[…]` parameter and measures nothing: {errs:#?}"
        );
    }
}

// ── THE STDLIB ARM: what the ticket is actually about ────────────────────────

const STDLIB_SRC: &str = r#"
namespace n01pystl
  import anthill.prelude.{List, Int64, Bool, Iterable, FiniteCollection, Stream}
  import anthill.prelude.FiniteCollection.{size, collect}

  operation inc(n: Int64) -> Int64 = n + 1
  operation big(n: Int64) -> Bool = n > 2

  -- THE CONSUMER AN AUTHOR WRITES. Declared over the SPEC, not over `List` — repair (a)
  -- of the ticket's three, which before this fix could be written and could not be
  -- CALLED with anything a combinator produced.
  operation total(c: FiniteCollection) -> Int64 effects c.E = size(c)

  operation rows() -> List[T = Int64] = [1, 2, 3, 4]

  -- [1,2,3,4] -map(+1)-> [2,3,4,5], counted -> 4
  operation totalOfMapped() -> Int64 = total(rows().map(inc))
  -- [1,2,3,4] -filter(>2)-> [3,4], counted -> 2
  operation totalOfFiltered() -> Int64 = total(rows().filter(big))
end
"#;

/// THE CONTROL'S OWN PROGRAM, and it must not share [`STDLIB_SRC`] — which the first cut
/// did, and the BACK-OUT is what caught it: with `totalOfMapped` in the same file NOTHING
/// loads, so the "control" failed on the back-out too and would have measured the change
/// while asking a question the change cannot answer. A control that shares a fixture with
/// the arms is a second arm.
const STDLIB_CONTROL_SRC: &str = r#"
namespace n01pystlctl
  import anthill.prelude.{List, Int64, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}
  operation total(c: FiniteCollection) -> Int64 effects c.E = size(c)
  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation totalOfList() -> Int64 = total(rows())
end
"#;

fn drive_stdlib(op: &str) -> i64 {
    drive_stdlib_in(STDLIB_SRC, op)
}

fn drive_stdlib_in(src: &str, op: &str) -> i64 {
    let mut interp = interp_for(src);
    let v = interp
        .call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"));
    v.as_int()
        .unwrap_or_else(|| panic!("expected an Int64 from {op}, got {v:?}"))
}

/// THE SHAPE THE TICKET IS ABOUT. `xs.map(f)` is a `MappedStream`, whose
/// `FiniteCollection`-ness is `MappedStreamFinite`'s — a witness — so it dispatched
/// `.size()` and was refused at `total(c: FiniteCollection)`. The sum is asserted rather
/// than the load, so the witness's `collect` really did materialize the mapped source.
#[test]
fn an_author_declared_consumer_takes_a_mapped_stream() {
    assert_eq!(drive_stdlib("n01pystl.totalOfMapped"), 4);
}

/// The sibling carrier, through `FilteredStreamFinite`. It is a row and not a footnote
/// for the reason the capability matrix gives: one witness green says nothing about the
/// other, and the two are separate provisions.
#[test]
fn an_author_declared_consumer_takes_a_filtered_stream() {
    assert_eq!(drive_stdlib("n01pystl.totalOfFiltered"), 2);
}

/// CONTROL — PASSES EITHER WAY BY DESIGN, and it has its OWN program for the reason
/// [`STDLIB_CONTROL_SRC`] states. `List provides FiniteCollection` DIRECTLY, so the
/// carrier-keyed walk always saw it: the axis that decides the verdict is how the
/// provision is FILED, not that a spec type sits in the parameter position.
#[test]
fn the_same_consumer_over_a_list_is_the_control() {
    assert_eq!(drive_stdlib_in(STDLIB_CONTROL_SRC, "n01pystlctl.totalOfList"), 4);
}

/// CONTROL — PASSES EITHER WAY BY DESIGN, and it is the stdlib's soundness row.
/// `Iterable.map` DECLARES a bare `Stream` return, which ERASES the source sort and with
/// it the witness's finiteness gate (`iterable.anthill` says so at the operation, and
/// `wi492`'s `lazy_map_iterator_count` pins the erased reading). A maybe-infinite stream
/// must not reach an eager consumer, and it still does not — so the leg widened
/// admissibility for the carrier-preserving spelling ONLY.
#[test]
fn the_erased_iterable_map_return_is_still_refused() {
    let src = r#"
namespace n01pyerased
  import anthill.prelude.{List, Int64, Iterable, FiniteCollection}
  operation inc(n: Int64) -> Int64 = n + 1
  operation total(c: FiniteCollection) -> Int64 effects c.E = FiniteCollection.size(c)
  operation rows() -> List[T = Int64] = [1, 2, 3]
  operation bad() -> Int64 = total(Iterable.map(rows(), inc))
end
"#;
    let errs = try_load_kb_with(src)
        .err()
        .expect("a bare `Stream` is maybe-infinite and must not satisfy `FiniteCollection`");
    assert!(
        errs.iter()
            .any(|e| e.contains("expected FiniteCollection") && e.contains("Stream")),
        "got: {errs:#?}",
    );
}

/// CONTROL — PASSES EITHER WAY BY DESIGN. The witness's condition is `FiniteCollection[C
/// = S]` on the SOURCE, so a mapped stream whose `Source` is a carrier that is `Iterable`
/// and NOT `FiniteCollection` must not conform. This is the stdlib twin of
/// [`an_unmet_witness_condition_is_still_refused`], and it is what says WI-590's
/// finiteness gate is still doing its job at the new reader.
///
/// THE VALUE IS A PARAMETER, NOT A CONSTRUCTION, and that is measured rather than
/// stylistic: `mapped(nats(from: 0), inc)` leaks an effect row of its own
/// (`bad.effects: got undeclared effect: ??_`) and so does `mapped([1,2,3], inc)` — the
/// CONTROL — so a fixture built that way refuses both ways for a reason that has nothing
/// to do with finiteness. Declaring the type puts the argument check, which IS the leg
/// under test, in front of anything else.
#[test]
fn an_infinite_source_is_still_refused() {
    let src = r#"
namespace n01pyinf
  import anthill.prelude.{Int64, Option, Pair, Stream, Iterable, FiniteCollection, MappedStream}

  sort Nats
    import anthill.prelude.{Int64, Option, Pair, Stream}
    import anthill.prelude.Option.{some}
    import anthill.prelude.Pair.{pair}
    entity nats(from: Int64)
    provides Stream[T = Int64, E = {}]
    operation splitFirst(n: Nats) -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =
      match n case nats(f) -> some(pair(f, nats(from: f + 1)))
  end

  operation total(c: FiniteCollection) -> Int64 effects c.E = FiniteCollection.size(c)

  operation bad(m: MappedStream[Source = Nats, Src = Int64, T = Int64, ES = {}, EF = {}])
    -> Int64 = total(m)
end
"#;
    let errs = try_load_kb_with(src)
        .err()
        .expect("a mapped stream over an INFINITE source provides no FiniteCollection");
    assert!(
        errs.iter()
            .any(|e| e.contains("expected FiniteCollection") && e.contains("MappedStream")),
        "the witness's `requires FiniteCollection[C = S]` is unmet at `S = Nats`, so the \
         mapped stream must not conform; got: {errs:#?}",
    );
}

/// THE DISCRIMINATOR FOR THE ROW ABOVE — the SAME declared shape over a FINITE source,
/// which must LOAD. Without it, [`an_infinite_source_is_still_refused`] would be
/// satisfied by any refusal of a declared `MappedStream[…]` parameter — including one
/// that refuses every source — and would measure nothing about finiteness.
///
/// IT IS AN ARM, NOT A CONTROL, and the back-out says so: it goes from refused to
/// accepted with the leg. That is not a flaw in the pairing — the pair is "finite loads,
/// infinite does not", and only one half of it could ever have been true before.
#[test]
fn the_same_shape_over_a_finite_source_loads() {
    let src = r#"
namespace n01pyfin
  import anthill.prelude.{Int64, List, FiniteCollection, MappedStream}
  operation total(c: FiniteCollection) -> Int64 effects c.E = FiniteCollection.size(c)
  operation ok(m: MappedStream[Source = List[T = Int64], Src = Int64, T = Int64, ES = {}, EF = {}])
    -> Int64 = total(m)
end
"#;
    if let Err(errs) = try_load_kb_with(src) {
        panic!(
            "a mapped stream over a `List` IS finite (MappedStreamFinite's condition holds), \
             so it must conform to `FiniteCollection`; got: {errs:#?}"
        );
    }
}
