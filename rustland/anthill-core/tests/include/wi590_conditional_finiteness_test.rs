//! WI-590 — the finiteness witness is CONDITIONAL, and that is the whole point of
//! folding the finite twin carriers away.
//!
//! Before WI-590 there were two carriers. `Iterable.map` built `mapped`, whose
//! `source` field was typed `Stream[Src, ES]`; `FiniteCollection.map` built a
//! separate `fmapped`, whose field was typed `FiniteCollection[…]`. Finiteness was
//! carried by WHICH CARRIER a value was, and a value could not cross between them.
//! What FORCED the duplication was erasure: `Stream[Src, ES]` does not record which
//! carrier the source was, so no rule could condition on it.
//!
//! There is now one carrier, and its source field keeps that sort
//! (`MappedStream.Source`). The witness sort `MappedStreamFinite` reads it:
//!
//!     requires FiniteCollection[C = S, Element = Src, E = ES]
//!     provides FiniteCollection[C = MappedStream[Source = S, …], Element = T, …]
//!
//! — "a mapped stream is a FiniteCollection exactly when its source is one". The
//! POSITIVE half is pinned all over the suite (`xs.map(f).size()` in
//! wi492/wi278/eval_test). The NEGATIVE half — that an infinite source does NOT get
//! the provision — is what this file drives, on the real stdlib rather than a
//! fixture, because it is the soundness property the design rests on: `collect` on a
//! mapped infinite stream must be a LOAD ERROR, not a diverging program.
//!
//! THE EXPERIMENT. Three rows over ONE fixture, differing in a single token — the
//! `Source` argument of the `MappedStream` the probe is handed. The probe NAMES that
//! carrier in its signature rather than building one, and that is deliberate twice
//! over.
//!
//! It keeps an UNRELATED inference gap out of the measurement. Building
//! `mapped(src, fn)` INLINE and handing it straight to a spec op does not type-check:
//! the construction's own sort params are grounded by nothing, so `FiniteCollection.
//! collect(mapped(xs, inc))` reports `undeclared effect ??_` and `Stream.splitFirst`
//! of the same expression reports `no impl matches per-call bindings`. It fails for a
//! `List` source exactly as for `Nats`, so it would have reddened every row here for a
//! reason that is not the witness. MEASURED, and the two ends bracket it: the same
//! construction under a declared return that names the carrier is CLEAN, and the same
//! witness consumer fed an already-typed carrier — what these rows do — is CLEAN. The
//! stdlib never writes the failing shape; `xs.map(f)` goes through
//! `FiniteCollection.map`, whose declared return pins every param.
//!
//! And it keeps `.map` out of it: `.map` on a `Nats` resolves `Iterable.map`, whose
//! declared return is a bare `Stream`, so the refusal would then be "a Stream has no
//! collect" — a NEIGHBOURING mechanism that survives the witness being deleted. Naming
//! the carrier puts the identical `MappedStream[Source = …]` in front of `collect`
//! every time and leaves the witness's `requires` as the only thing that can differ.
//!
//! CONTROLS, both RUN rather than reasoned about.
//!
//!   * IN THE FIXTURE, and this is the sharp one: drop the ONE line
//!     `provides FiniteCollection[C = Fin, …]` from `Fin` and nothing else.
//!     `mapped_over_a_hand_written_finite_source_is_collectable` goes red and the
//!     other three stay green. The gate reads the SOURCE's own provision.
//!   * IN THE STDLIB: comment out `MappedStreamFinite`'s `provides` clause. Both
//!     accepting rows go red and the REFUSAL stays green — which is why the refusal
//!     alone would not be evidence of anything. That back-out is coarse, and the
//!     measurement says so: without the provision `MappedStreamFinite.collect`'s own
//!     body stops typing, so the stdlib does not load at all and all five wi492 rows
//!     fall with it. It measures loadability as much as this capability; the fixture
//!     control above is the one that isolates the axis.

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// The load errors of stdlib + `extra`, empty on a clean load.
///
/// ONE `load_all` over both, deliberately: the whole-KB passes — op-body type
/// checking among them — belong to `load_all`, so a second incremental `load` of
/// `extra` on top of an already-loaded stdlib KB is not the loader's verdict on
/// this source, and a test reading it would assert over checks that never ran.
fn stdlib_plus_source_errors(extra: &str) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => Vec::new(),
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// An INFINITE source, and the probe over it. `Nats` provides `Stream` and so
/// provides `Iterable` transitively (WI-495) — a perfectly good `MappedStream`
/// source — but it never provides `FiniteCollection`, because counting it does not
/// terminate. `{SOURCE}` is the only text that differs between the two rows.
///
/// The probe takes the carrier AS ITS PARAMETER and does not build one. That is
/// deliberate: constructing `mapped(src, fn)` in a free operation would drag in the
/// construction-side row threading (the source's access row `ES` has to be read off
/// the argument's own provision, and in a free op with no enclosing `requires` it
/// leaks — measured, and it leaks for a `List` source just as it does for `Nats`, so
/// it would have made BOTH rows red for a reason that is not the witness). Naming
/// the carrier in the signature puts the same `MappedStream[Source = …]` in front of
/// `collect` either way and leaves the witness's `requires` as the only thing that
/// can differ.
const PROBE: &str = r#"
namespace wi590.conditional
  import anthill.prelude.{List, Int64, Stream, Option, Pair, MappedStream, FiniteCollection}
  import anthill.prelude.Option.{some}
  import anthill.prelude.Pair.{pair}

  sort Nats
    import anthill.prelude.{Int64, Stream, Option, Pair}
    import anthill.prelude.Option.{some}
    import anthill.prelude.Pair.{pair}
    entity nats(from: Int64)
    provides Stream[T = Int64, E = {}]
    operation splitFirst(n: Nats)
      -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =
      match n
        case nats(k) -> some(pair(k, nats(from: k + 1)))
  end

  -- `Nats`' FINITE twin, and the reason the gate's axis is legible. Same shape, same
  -- `provides Stream`; the ONE thing it adds is the FiniteCollection provision. Against
  -- `Nats` alone the contrast could be read as "a `List` is special"; against `Fin` it
  -- can only be read as the source's own finiteness.
  sort Fin
    import anthill.prelude.{Int64, List, Stream, Option, Pair, FiniteCollection}
    import anthill.prelude.Option.{some, none}
    import anthill.prelude.Pair.{pair}
    entity fin(xs: List[T = Int64])
    provides Stream[T = Int64, E = {}]
    provides FiniteCollection[C = Fin, Element = Int64, E = {}]
    operation splitFirst(f: Fin)
      -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =
      match f
        case fin(l) ->
          match List.splitFirst(l)
            case none() -> none
            case some(pair(h, t)) -> some(pair(h, fin(xs: t)))
    operation collect(f: Fin) -> List[T = Int64] =
      match f
        case fin(l) -> l
  end

  operation probe(
      m: MappedStream[Source = {SOURCE}, Src = Int64, T = Int64, ES = {}, EF = {}])
    -> List[T = Int64] =
    FiniteCollection.collect(m)
end
"#;

/// The FILTER witness's gate, in the same shape. `FilteredStreamFinite` carries the
/// identical `requires FiniteCollection[C = S, …]` over `FilteredStream[Source = S,
/// …]`, and the positive filter paths elsewhere (wi492, wi439, eval_test) all run
/// over a `List`, so weakening that clause would leave the workspace green. Two
/// witnesses, two gates, two experiments.
const FILTER_PROBE: &str = r#"
namespace wi590.conditional.filter
  import anthill.prelude.{List, Int64, Stream, Option, Pair, FilteredStream, FiniteCollection}
  import anthill.prelude.Option.{some}
  import anthill.prelude.Pair.{pair}

  sort FNats
    import anthill.prelude.{Int64, Stream, Option, Pair}
    import anthill.prelude.Option.{some}
    import anthill.prelude.Pair.{pair}
    entity fnats(from: Int64)
    provides Stream[T = Int64, E = {}]
    operation splitFirst(n: FNats)
      -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =
      match n
        case fnats(k) -> some(pair(k, fnats(from: k + 1)))
  end

  operation probe(
      f: FilteredStream[Source = {SOURCE}, T = Int64, ES = {}, EF = {}])
    -> List[T = Int64] =
    FiniteCollection.collect(f)
end
"#;

fn probe_over(source: &str) -> Vec<String> {
    stdlib_plus_source_errors(&PROBE.replace("{SOURCE}", source))
}

fn filter_probe_over(source: &str) -> Vec<String> {
    stdlib_plus_source_errors(&FILTER_PROBE.replace("{SOURCE}", source))
}

/// THE GATE. A `List` source is finite, so the witness's `requires` discharges and
/// the mapped stream is collectable.
///
/// This row is a load-verdict CONTROL, not the capability drive — it is what makes
/// the refusal below an experiment about finiteness rather than about the shape.
/// The capability itself runs in `the_witness_supplied_collect_evaluates`.
#[test]
fn mapped_over_a_finite_source_is_collectable() {
    let errs = probe_over("List[T = Int64]");
    assert!(
        errs.is_empty(),
        "a mapped stream over a finite source must get the witness's \
         FiniteCollection provision; got: {errs:?}"
    );
}

/// THE GATE with the `List` taken out of it: a hand-written FINITE source, whose
/// only difference from `Nats` is that it provides `FiniteCollection`. This is the
/// row that makes the pair an experiment about FINITENESS — the `List` row alone
/// leaves "a List is special" as a live reading, and the two hand-written carriers
/// close it.
#[test]
fn mapped_over_a_hand_written_finite_source_is_collectable() {
    let errs = probe_over("Fin");
    assert!(
        errs.is_empty(),
        "the witness reads the SOURCE's own FiniteCollection provision, not its \
         identity as a List; got: {errs:?}"
    );
}

/// THE GATE, other side — and the row this file exists for. The SAME carrier over an
/// infinite source is refused, because `requires FiniteCollection[C = Nats]` cannot
/// be discharged.
#[test]
fn mapped_over_an_infinite_source_is_not_collectable() {
    let errs = probe_over("Nats");
    assert!(
        !errs.is_empty(),
        "collecting a mapped stream over an INFINITE source must be a load error — \
         the witness gates finiteness on the source, and `Nats` provides only \
         Stream/Iterable; got a clean load"
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("collect") || e.contains("FiniteCollection")),
        "the refusal must name the finiteness primitive it could not supply; \
         got: {errs:?}"
    );
}

/// THE FILTER WITNESS'S GATE, both sides. Same experiment, other combinator — a
/// `List` source is collectable and an infinite one is not.
#[test]
fn filtered_over_a_finite_source_is_collectable() {
    let errs = filter_probe_over("List[T = Int64]");
    assert!(
        errs.is_empty(),
        "a filtered stream over a finite source must get FilteredStreamFinite's \
         provision; got: {errs:?}"
    );
}

#[test]
fn filtered_over_an_infinite_source_is_not_collectable() {
    let errs = filter_probe_over("FNats");
    assert!(
        !errs.is_empty(),
        "collecting a filtered stream over an INFINITE source must be a load error; \
         got a clean load"
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("collect") || e.contains("FiniteCollection")),
        "the refusal must name the finiteness primitive it could not supply; \
         got: {errs:?}"
    );
}

/// The provision DRIVEN, not merely accepted: the drain the witness supplies runs
/// and applies the transform. Its own source, so the two contrast rows above keep
/// differing in exactly one token, and it builds the carrier the way the stdlib does
/// — through `FiniteCollection.map` — rather than by hand.
///
/// `[1, 2, 3]` mapped by `+1` collects to `[2, 3, 4]` — length 3, sum 9. The SUM is
/// what separates a drain that mapped from one that did not: an unmapped `[1, 2, 3]`
/// has the same length and sums to 6.
#[test]
fn the_witness_supplied_collect_evaluates() {
    let src = r#"
namespace wi590.conditional.eval
  import anthill.prelude.{List, Int64, FiniteCollection}

  operation inc(x: Int64) -> Int64 = x + 1
  operation addp(a: Int64, b: Int64) -> Int64 = a + b

  operation mk() -> List[T = Int64] = [1, 2, 3]

  operation collected(xs: List[T = Int64]) -> List[T = Int64] =
    FiniteCollection.collect(FiniteCollection.map(xs, inc))

  operation collected_len(xs: List[T = Int64]) -> Int64 = List.length(collected(xs))
  operation collected_sum(xs: List[T = Int64]) -> Int64 =
    FiniteCollection.foldLeft(collected(xs), 0, addp)
end
"#;
    let mut interp = crate::common::interp_for(src);
    let xs = interp
        .call("wi590.conditional.eval.mk", &[])
        .expect("build the source list");
    assert_eq!(
        int_of(
            &mut interp,
            "wi590.conditional.eval.collected_len",
            &[xs.clone()]
        ),
        3
    );
    assert_eq!(
        int_of(&mut interp, "wi590.conditional.eval.collected_sum", &[xs]),
        9,
        "the witness's collect must apply the transform: [1,2,3] +1 sums to 9, not 6"
    );
}

fn int_of(interp: &mut Interpreter, op: &str, args: &[Value]) -> i64 {
    interp
        .call(op, args)
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
        .as_int()
        .unwrap_or_else(|| panic!("call {op}: expected Int64"))
}
