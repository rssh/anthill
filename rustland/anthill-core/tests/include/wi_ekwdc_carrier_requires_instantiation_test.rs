//! WI-20260828-EKWDC — a carrier's `requires` clause is instantiated AT THE RECEIVER,
//! not in the carrier's own declaration scope.
//!
//! A provision's sub-goals are built by substituting the impl-param bindings that
//! matching the PROVISION HEAD against the dispatch goal produced. A head names only
//! the parameters the spec is about, so every OTHER parameter of the carrier survives
//! into the sub-goal as a bare reference to the declaration's own parameter:
//!
//!     sort MappedStream
//!       sort Source = ?  sort Src = ?  sort T = ?  effects ES = ?  effects EF = ?
//!       requires Iterable[C = Source, Element = Src, E = ES]   -- names Source, Src, ES
//!       provides Stream[T = T, E = {ES, EF}]                   -- names T, ES, EF
//!
//! `Stream.splitFirst(mapped(xs, inc))` therefore asked for `Iterable[C =
//! MappedStream.Source, Element = MappedStream.Src, E = MappedStream.ES]` — a goal
//! about a PARAMETER — and was refused `no impl provides Iterable`, for a receiver
//! whose type is fully ground (`MappedStream[Source = List[T = Int64], Src = Int64,
//! …]`, which WI-20260828-BH1JZ delivered and its suite pins). The dispatch could not
//! see those arguments: [`SortGoal::carrier`] carried the receiver's SORT and nothing
//! else. It now carries the receiver's own type arguments as well, and they fill the
//! impl-param substitution wherever the head left it free.
//!
//! ADDITIVE, so it cannot move a dispatch the head already decided: only a parameter
//! the head match did NOT bind is filled. That is also what the `Elemental` control
//! below measures from the other side.
//!
//! THE POPULATION, censused rather than taken from the ticket, which named only the
//! `MappedStream` row: `grep -rn '^\s*requires ' stdlib/ examples/ --include=*.anthill`
//! is 28 clauses, and `MappedStream` and `FilteredStream` are the only two whose
//! `requires` names a parameter their `provides` head does not. The rest either name the
//! head's own parameters — `Ord requires Eq[T]`, and `MappedStreamFinite requires
//! FiniteCollection[C = S, …]` under `provides FiniteCollection[C = MappedStream[Source =
//! S, …]]`, whose head DOES write `S` inside the carrier binding — or belong to specs
//! with no carrier at all. Both members are driven here.
//!
//! WHAT FAILS WHEN IT IS BACKED OUT is stated per test. The `Pairer` pair is the sharp
//! one: ONE carrier, TWO receivers, and before this change both were refused with the
//! IDENTICAL message naming `Pairer.Src` — the fix is exactly what tells them apart.
//!
//! ── AND THE SAME RULE ACROSS A PROVIDER CHAIN ──────────────────────────────────────
//!
//! `collect_provides_candidates` accepts a candidate the carrier reaches only
//! TRANSITIVELY (WI-714: `Relation provides LogicalStream provides Stream`), so the sort
//! whose `requires` must be discharged can be one or more hops from the receiver's own.
//! There the receiver's ARGUMENTS are not the answer — `Chained[Out = Int64]` says
//! nothing about the intermediate's `Src`. What connects them is the CARRIER'S PROVISION,
//! `Chained provides Mid[Src = Heavy, Out = Out]`, composed per hop and instantiated at
//! the receiver's arguments. [`provision_path_subst`] is that walk; at zero hops it is the
//! identity, which is why one function serves both halves.
//!
//! The second fixture below is that chain. Its rows are the same experiment as the
//! `Pairer` pair, one hop out.

use anthill_core::eval::{Interpreter, Value};

/// Two carriers whose `provides` head does NOT name the parameter their `requires`
/// constrains (`Pairer`), and one whose head DOES (`Elemental`) — the axis, held
/// against its own control.
///
/// `Pairer` needs `Out` as well as `Src` for a reason the fixture cannot skip: a
/// provision writing only CONCRETE arguments (`provides Stream[T = Int64]`) binds no
/// spec parameter from the carrier, so the dispatch goal stays empty and resolves
/// `NoCandidates` — the permissive fall-through, which never reaches a provision's
/// sub-goals at all. MEASURED on three earlier drafts of this fixture, each of which
/// passed both with and without the change. `Out` is what makes the goal `Stream[T =
/// Int64]` and so makes the dispatch happen; `Src` is then the parameter the head does
/// not name.
const CARRIERS: &str = r#"
namespace wiekwdc.fix
  import anthill.prelude.{Int64, List, Option, Pair, Stream}

  sort Tagger
    import anthill.prelude.Int64
    sort T = ?
    operation tagOf(x: T) -> Int64
  end

  sort Heavy
    import anthill.prelude.Int64
    entity heavy(k: Int64)
    provides Tagger[T = Heavy]
    operation tagOf(h: Heavy) -> Int64 =
      match h
        case heavy(k) -> k
  end

  -- No `provides Tagger`: the sort that makes `Pairer`'s requirement FAIL.
  sort Light
    import anthill.prelude.Int64
    entity light(k: Int64)
  end

  sort Pairer
    import anthill.prelude.{Int64, List, Stream, Option, Pair}
    import anthill.prelude.Option.{some}
    import anthill.prelude.Pair.{pair}
    sort Src = ?
    sort Out = ?
    requires Tagger[T = Src]
    entity pairer(item: Src, out: Out)
    provides Stream[T = Out, E = {}]
    operation splitFirst(p: Pairer) -> Option[Pair[A = Out, B = Stream[T = Out, E = {}]]] =
      match p
        case pairer(_, o) -> some(pair(o, rest()))
    operation rest() -> List[T = Out] = []
  end

  sort Elemental
    import anthill.prelude.{Int64, List, Stream, Option, Pair}
    import anthill.prelude.Option.{some}
    import anthill.prelude.Pair.{pair}
    sort Src = ?
    requires Tagger[T = Src]
    entity elemental(item: Src)
    provides Stream[T = Src, E = {}]
    operation splitFirst(e: Elemental) -> Option[Pair[A = Src, B = Stream[T = Src, E = {}]]] =
      match e
        case elemental(i) -> some(pair(i, rest()))
    operation rest() -> List[T = Src] = []
  end
end
"#;

/// The carriers plus a consumer namespace holding `body`.
fn program(body: &str) -> String {
    format!(
        "{CARRIERS}\nnamespace wiekwdc.use\n  \
         import anthill.prelude.{{Int64, List, Option, Pair, Stream}}\n  \
         import anthill.prelude.Option.{{some, none}}\n  \
         import anthill.prelude.Pair.{{pair}}\n  \
         import wiekwdc.fix.{{Tagger, Heavy, Light, Pairer, Elemental}}\n  \
         import wiekwdc.fix.Heavy.{{heavy}}\n  \
         import wiekwdc.fix.Light.{{light}}\n  \
         import wiekwdc.fix.Pairer.{{pairer}}\n  \
         import wiekwdc.fix.Elemental.{{elemental}}\n{body}\nend\n"
    )
}

fn errors_of(body: &str) -> Vec<String> {
    crate::common::try_load_kb_with(&program(body))
        .err()
        .unwrap_or_default()
}

fn int_of(interp: &mut Interpreter, op: &str, args: &[Value]) -> i64 {
    interp
        .call(op, args)
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
        .as_int()
        .unwrap_or_else(|| panic!("call {op}: expected Int64"))
}

/// THE CAPABILITY, DRIVEN. `Pairer`'s `requires Tagger[T = Src]` is discharged at the
/// receiver's own `Src = Heavy`, and the dispatched `Pairer.splitFirst` runs.
///
/// BACKED OUT: FAILS at load with `expected Int64, got ?_` at the `match` — the
/// dispatch resolved nothing, so `splitFirst`'s result never got an element type. The
/// dispatch's own message is the one the next row asserts on, where no `match` stands
/// between it and the reader: `unresolved: Tagger[T = wiekwdc.fix.Pairer.Src]`, the
/// requirement asked about the DECLARATION's parameter.
#[test]
fn a_requirement_the_provision_head_does_not_name_is_discharged_at_the_receiver() {
    let body = "  operation w() -> Int64 =\n    \
                match Stream.splitFirst(pairer(heavy(7), 42))\n      \
                case some(pair(v, _)) -> v\n      case none() -> 0";
    let errs = errors_of(body);
    assert!(errs.is_empty(), "got: {errs:?}");
    let mut interp = crate::common::interp_for(&program(body));
    assert_eq!(
        int_of(&mut interp, "wiekwdc.use.w", &[]),
        42,
        "the dispatched `Pairer.splitFirst` must run and yield the carried `out`"
    );
}

/// AND IT IS STILL CHECKED — the same carrier over a `Src` that provides no `Tagger` is
/// refused, and the refusal NAMES THE RECEIVER'S OWN ARGUMENT. This is the row that
/// separates "instantiated" from "dropped": a fix that skipped the requirement instead
/// of instantiating it would turn this green.
///
/// BACKED OUT: still refused — but with `Tagger[T = wiekwdc.fix.Pairer.Src]`, the
/// IDENTICAL message the `heavy` row above gets. One carrier, two receivers, one
/// indistinguishable diagnostic; naming `Light` here is what says the goal is now about
/// the value. So the assert is on the TEXT, not on the mere presence of an error.
#[test]
fn and_the_requirement_is_still_refused_at_a_receiver_that_cannot_meet_it() {
    let body = "  operation w() -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =\n    \
                Stream.splitFirst(pairer(light(7), 42))";
    let errs = errors_of(body);
    assert!(
        errs.iter()
            .any(|e| e.contains("wiekwdc.fix.Tagger[T = wiekwdc.fix.Light]")),
        "the refusal must name the RECEIVER's own argument, not `Pairer.Src`; got: {errs:?}"
    );
}

/// THE CONTROL — a carrier whose `provides Stream[T = Src]` NAMES the very parameter its
/// `requires Tagger[T = Src]` constrains. The head match already binds `Src := Heavy`, so
/// there is nothing for the receiver's arguments to fill.
///
/// Passes either way BY DESIGN. It is what makes the two rows above experiments about
/// the head/`requires` MISMATCH rather than about whether a carrier-level `requires` ever
/// worked — and it is the additivity claim measured: this row's substitution is the head
/// match's, before and after.
#[test]
fn a_requirement_the_provision_head_does_name_already_worked() {
    let body = "  operation w() -> Int64 =\n    \
                match Stream.splitFirst(elemental(heavy(7)))\n      \
                case some(pair(v, _)) -> Heavy.tagOf(v)\n      case none() -> 0";
    let errs = errors_of(body);
    assert!(errs.is_empty(), "got: {errs:?}");
    let mut interp = crate::common::interp_for(&program(body));
    assert_eq!(int_of(&mut interp, "wiekwdc.use.w", &[]), 7);
}

/// THE HEADLINE, on the stdlib carriers the ticket came from, and DRIVEN rather than
/// merely loaded. Both members of the population are here: `MappedStream` (`requires
/// Iterable[C = Source, Element = Src, E = ES]` under `provides Stream[T = T, E = {ES,
/// EF}]`) and its sibling `FilteredStream`.
///
/// The VALUES separate a stream that ran its combinator from one that did not: `[1,2,3]`
/// mapped by `+1` splits to head 2 (an unmapped split gives 1), and filtered by `> 2`
/// splits to head 3 (an unfiltered split gives 1).
///
/// BACKED OUT: FAILS at load. Both calls report `expected Int64, got ?_` at the `match`
/// — the dispatch resolved nothing, so `splitFirst`'s result never got an element type.
/// Written without the `match`, the same call reports the ticket's own message:
/// `Stream.splitFirst.dispatch: … unresolved: Iterable[C = anthill.prelude.MappedStream
/// .Source, …]`.
#[test]
fn the_stdlib_lazy_stream_carriers_split_and_the_combinator_ran() {
    let src = r#"
namespace wiekwdc.stdlib
  import anthill.prelude.{List, Int64, Bool, Stream, Option, Pair, MappedStream, FilteredStream}
  import anthill.prelude.MappedStream.{mapped}
  import anthill.prelude.FilteredStream.{filtered}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  operation inc(x: Int64) -> Int64 = x + 1
  operation big(x: Int64) -> Bool = x > 2
  operation mk() -> List[T = Int64] = [1, 2, 3]

  operation firstMapped(xs: List[T = Int64]) -> Int64 =
    match Stream.splitFirst(mapped(xs, inc))
      case some(pair(h, _)) -> h
      case none() -> 0

  operation firstFiltered(xs: List[T = Int64]) -> Int64 =
    match Stream.splitFirst(filtered(xs, big))
      case some(pair(h, _)) -> h
      case none() -> 0
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(errs.is_empty(), "got: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    let xs = interp
        .call("wiekwdc.stdlib.mk", &[])
        .expect("build the source list");
    assert_eq!(
        int_of(&mut interp, "wiekwdc.stdlib.firstMapped", &[xs.clone()]),
        2,
        "the transform must have run: [1,2,3] mapped by +1 splits to 2, not 1"
    );
    assert_eq!(
        int_of(&mut interp, "wiekwdc.stdlib.firstFiltered", &[xs]),
        3,
        "the predicate must have run: [1,2,3] filtered by >2 splits to 3, not 1"
    );
}


// ── TWO HOPS: the same rule across a provider chain ────────────────────────────────

/// The chain fixture. `Mid` is the `LogicalStream` position — CONSTRUCTOR-LESS (a data
/// sort cannot be provided at all), body-less primitive, `requires` naming `Src` and
/// `provides Stream[T = Out]` naming `Out` and NOT `Src`. The carriers below reach
/// `Stream` only through it.
///
/// THE PROVISION MUST BIND `Src` CONCRETELY, and that is the language's rule rather than
/// the fixture's convenience: a parametric `Src` is refused at the provision site with
/// `'X' provides 'Mid', which requires 'Tagger', but 'X' does not provide 'Tagger'` — and
/// a forwarding `requires Tagger[T = Src]` on `X` does NOT satisfy it (the check asks
/// about `provides`). So a legal two-hop carrier pins the constrained parameter itself,
/// and `Heavy` vs `Light` in that slot is what the two rows differ in.
const CHAIN: &str = r#"
  sort Tagger
    import anthill.prelude.Int64
    sort T = ?
    operation tagOf(x: T) -> Int64
  end

  sort Heavy
    import anthill.prelude.Int64
    entity heavy(k: Int64)
    provides Tagger[T = Heavy]
    operation tagOf(h: Heavy) -> Int64 =
      match h
        case heavy(k) -> k
  end

  sort Light
    import anthill.prelude.Int64
    entity light(k: Int64)
  end

  sort Mid
    import anthill.prelude.{Int64, Stream, Option, Pair}
    sort Src = ?
    sort Out = ?
    requires Tagger[T = Src]
    provides Stream[T = Out, E = {}]
    operation splitFirst(m: Mid) -> Option[Pair[A = m.Out, B = Stream[T = m.Out, E = {}]]]
  end
"#;

/// The chain fixture plus one carrier and a consumer that splits `ctor`.
///
/// THE CARRIER MUST BE PARAMETERIZED, and the reason is the one the `Pairer` note above
/// records from the other side: a carrier with NO type parameters gives
/// `bind_spec_params_from_carrier` no receiver bindings, so it returns before pinning
/// `Stream.T`, the dispatch goal stays EMPTY and resolves `NoCandidates` — the permissive
/// fall-through, which never reaches a provision's sub-goals. MEASURED: the same two rows
/// over a parameter-less carrier are green with this change BACKED OUT.
fn chain_program(ns: &str, carrier: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  \
         import anthill.prelude.{{Int64, List, Option, Pair, Stream}}\n  \
         import anthill.prelude.Option.{{some, none}}\n  \
         import anthill.prelude.Pair.{{pair}}\n{CHAIN}{carrier}\n{body}\nend\n"
    )
}

fn chain_errors(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

/// THE CAPABILITY AT ONE HOP OUT. `Mid`'s `requires Tagger[T = Src]` is discharged at
/// `Heavy` — read off `Chained provides Mid[Src = Heavy, Out = Out]`, not off the
/// receiver's own arguments, which name no `Src` at all — and the call runs.
///
/// BACKED OUT (make [`provision_path_subst`]'s `for intermediate in …` loop not run,
/// keeping its identity arm so the four direct rows above stay green — measured): FAILS
/// with `expected Int64, got ?_` at the `match`, which is where the dispatch's own
/// message ends up when a `match` stands between it and the reader. The next row, which
/// has none, shows it: `unresolved: Tagger[T = Mid.Src]`, the INTERMEDIATE's declaration
/// parameter.
#[test]
fn a_requirement_one_provider_hop_away_is_discharged_through_the_provision() {
    let carrier = r#"
  sort Chained
    import anthill.prelude.{Int64, List, Stream, Option, Pair}
    import anthill.prelude.Option.{some}
    import anthill.prelude.Pair.{pair}
    sort Out = ?
    entity chained(item: Heavy, out: Out)
    provides Mid[Src = Heavy, Out = Out]
    operation splitFirst(c: Chained) -> Option[Pair[A = Out, B = Stream[T = Out, E = {}]]] =
      match c
        case chained(_, v) -> some(pair(v, tail()))
    operation tail() -> List[T = Out] = []
  end
"#;
    let src = chain_program(
        "wiekwdc2",
        carrier,
        "  operation w() -> Int64 =\n    \
         match Stream.splitFirst(chained(heavy(7), 42))\n      \
         case some(pair(v, _)) -> v\n      case none() -> 0",
    );
    let errs = chain_errors(&src);
    assert!(errs.is_empty(), "got: {errs:?}");
    let mut interp = crate::common::interp_for(&src);
    assert_eq!(
        int_of(&mut interp, "wiekwdc2.w", &[]),
        42,
        "the dispatched impl must run and yield the carried `out`"
    );
}

/// AND IT IS STILL CHECKED ACROSS THE HOP, at the value the PROVISION names. The twin of
/// the direct fixture's `Light` row, and it asserts on the TEXT for the same reason: an
/// error exists either way, and only its subject says whether the requirement was
/// instantiated or merely skipped.
///
/// BACKED OUT: still refused, but naming `Tagger[T = Mid.Src]` — the identical message
/// the `Heavy` row above got, so the two programs were indistinguishable.
///
/// THE ARMS DIFFER ON A SECOND AXIS AND CANNOT BE MADE NOT TO, which a review raised and
/// the measurement answers: `BareL`'s declaration ALSO reports `'BareL' provides 'Mid',
/// which requires 'Tagger', but 'BareL' does not provide 'Tagger'`, where the `Heavy` twin
/// loads clean. That is not a fixture flaw to design away — the provision-site check is
/// BINDING-PRECISE where the bindings are concrete (`provider_requires_subgoals`), so it
/// asks the very question the dispatch asks, and any arm whose requirement is
/// unsatisfiable trips both. Making a `Light` arm load clean at its declaration would mean
/// making its requirement satisfiable, at which point there is nothing left to refuse.
///
/// SO THE ASSERT NAMES THE DISPATCH, not merely the type. It requires BOTH the
/// `Stream.splitFirst.dispatch` marker and the instantiated `Tagger[T = Light]`, so the
/// coherence diagnostic cannot satisfy this row on its own — the failure mode a review
/// named, should that message ever grow bindings in its rendering.
#[test]
fn and_a_requirement_one_hop_away_is_still_refused_at_a_value_that_cannot_meet_it() {
    let carrier = r#"
  sort BareL
    import anthill.prelude.{Int64, List, Stream, Option, Pair}
    import anthill.prelude.Option.{some}
    import anthill.prelude.Pair.{pair}
    sort Out = ?
    entity bareL(item: Light, out: Out)
    provides Mid[Src = Light, Out = Out]
    operation splitFirst(b: BareL) -> Option[Pair[A = Out, B = Stream[T = Out, E = {}]]] =
      match b
        case bareL(_, v) -> some(pair(v, tail()))
    operation tail() -> List[T = Out] = []
  end
"#;
    // The Option-returning spelling, with no `match` between the dispatch and the
    // reader: a `match` over an unresolved result reports its OWN mismatch first and
    // hides the refusal this row is about.
    let errs = chain_errors(&chain_program(
        "wiekwdc3",
        carrier,
        "  operation w() -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =\n    \
         Stream.splitFirst(bareL(light(7), 42))",
    ));
    assert!(
        errs.iter().any(|e| {
            e.contains("Stream.splitFirst.dispatch")
                && e.contains("wiekwdc3.Tagger[T = wiekwdc3.Light]")
        }),
        "the DISPATCH's refusal must name the value the PROVISION binds, not `Mid.Src`; \
         got: {errs:?}"
    );
}

/// THE NEIGHBOURING GAP THIS DOES **NOT** CLOSE, pinned so its repair is visible rather
/// than discovered. An impl reached across a hop whose declared return is written as a
/// RECEIVER PROJECTION (`m.Out`, the `Relation.splitFirst` spelling) leaves that
/// projection un-eliminated — `expected Int64, got w.Out`. The rows above use the bare
/// `Out` spelling (`MappedStream.splitFirst`'s) and are clean, so the two are separable.
///
/// IT IS NOT THIS TICKET'S, and that is measured rather than asserted: the fixture here
/// carries NO `requires` ANYWHERE, so nothing [`carrier_arg_impl_subst`] does can run,
/// and it fails identically with the whole change backed out. It is the WI-376
/// `ExprCarried` elimination over a transitively-dispatched impl.
#[test]
fn a_receiver_projection_across_a_hop_is_a_separate_open_gap() {
    let src = format!(
        "namespace wiekwdc4\n  \
         import anthill.prelude.{{Int64, List, Option, Pair, Stream}}\n  \
         import anthill.prelude.Option.{{some, none}}\n  \
         import anthill.prelude.Pair.{{pair}}\n{}\n  \
         operation w() -> Int64 =\n    \
         match Stream.splitFirst(wrapper(42))\n      \
         case some(pair(v, _)) -> v\n      case none() -> 0\nend\n",
        r#"
  sort Plain
    import anthill.prelude.{Int64, Stream, Option, Pair}
    sort Out = ?
    provides Stream[T = Out, E = {}]
    operation splitFirst(m: Plain) -> Option[Pair[A = m.Out, B = Stream[T = m.Out, E = {}]]]
  end

  sort Wrapper
    import anthill.prelude.{Int64, List, Stream, Option, Pair}
    import anthill.prelude.Option.{some}
    import anthill.prelude.Pair.{pair}
    sort Out = ?
    entity wrapper(out: Out)
    provides Plain[Out = Out]
    operation splitFirst(w: Wrapper) -> Option[Pair[A = w.Out, B = Stream[T = w.Out, E = {}]]] =
      match w
        case wrapper(v) -> some(pair(v, tail()))
    operation tail() -> List[T = Out] = []
  end
"#
    );
    let errs = chain_errors(&src);
    assert!(
        errs.iter().any(|e| e.contains("got w.Out")),
        "a receiver projection across a provider hop is still un-eliminated; if this row \
         has gone green the gap is closed and the test should say so — got: {errs:?}"
    );
}


/// TWO ROUTES TO ONE PROVIDER SORT, and the walk must take the carrier's OWN.
///
/// `Two` reaches `Mid` twice — directly (`provides Mid[Src = Heavy]`, which resolves) and
/// through `J` (`provides J`, `J provides Mid[Src = Odd]`, which does not). Provides-facts
/// are enumerated in assertion order, so a plain DFS takes whichever comes first; here
/// that is the DETOUR, and the requirement would be discharged at what `J` wrote instead
/// of at what `Two` wrote. `collect_provides_candidates` states the preference one level
/// up — direct route first, transitive only as a fallback — so the walk has to hold it too.
///
/// BACKED OUT (drop the `edges.swap(0, i)` that hoists the direct edge): FAILS with
/// `unresolved: Tagger[T = Odd]` — measured, so the DFS really does reach `J` first on
/// this fixture rather than the row being a tautology.
///
/// THE FIXTURE DOES NOT LOAD CLEAN IN EITHER ARM, and that is the axis held CONSTANT
/// rather than a second one: `J provides Mid[Src = Odd]` is refused at its own
/// declaration, because the detour has to bind something no `Tagger` answers for the two
/// routes to be distinguishable at all — resolvability is the only difference a body-less
/// primitive can expose. That error is identical in both arms; the `Tagger[T = Odd]`
/// DISPATCH refusal is what appears and disappears.
#[test]
fn two_routes_to_one_provider_take_the_carriers_own() {
    let src = r#"
namespace wiekwdc5
  import anthill.prelude.{Int64, List, Option, Pair, Stream}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  sort Tagger
    import anthill.prelude.Int64
    sort T = ?
    operation tagOf(x: T) -> Int64
  end

  sort Heavy
    import anthill.prelude.Int64
    entity heavy(k: Int64)
    provides Tagger[T = Heavy]
    operation tagOf(h: Heavy) -> Int64 =
      match h
        case heavy(k) -> k
  end

  sort Odd
    import anthill.prelude.Int64
    entity odd(k: Int64)
  end

  sort Mid
    import anthill.prelude.{Int64, Stream, Option, Pair}
    sort Src = ?
    sort Out = ?
    requires Tagger[T = Src]
    provides Stream[T = Out, E = {}]
    operation splitFirst(m: Mid) -> Option[Pair[A = m.Out, B = Stream[T = m.Out, E = {}]]]
  end

  sort J
    import anthill.prelude.{Int64, Stream, Option, Pair}
    sort Out = ?
    provides Mid[Src = Odd, Out = Out]
  end

  sort Two
    import anthill.prelude.{Int64, List, Stream, Option, Pair}
    import anthill.prelude.Option.{some}
    import anthill.prelude.Pair.{pair}
    sort Out = ?
    entity two(out: Out)
    provides J[Out = Out]
    provides Mid[Src = Heavy, Out = Out]
    operation splitFirst(t: Two) -> Option[Pair[A = Out, B = Stream[T = Out, E = {}]]] =
      match t
        case two(v) -> some(pair(v, tail()))
    operation tail() -> List[T = Out] = []
  end

  operation w() -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =
    Stream.splitFirst(two(42))
end
"#;
    let errs = chain_errors(src);
    assert!(
        !errs.iter().any(|e| e.contains("Stream.splitFirst.dispatch")),
        "the dispatch must discharge `Mid`'s requirement at the DIRECT provision's \
         `Src = Heavy`, not at the detour's `Src = Odd`; got: {errs:?}"
    );
}
