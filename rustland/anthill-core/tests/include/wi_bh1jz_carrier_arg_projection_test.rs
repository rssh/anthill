//! WI-20260828-BH1JZ — projecting a CARRIER ARGUMENT into a spec-typed constructor
//! field: through a TRANSITIVE provision, and from a receiver written with TYPE
//! ARGUMENTS.
//!
//! `bare_spec_arg_provision_projection` rebuilds a carrier argument's type as the
//! spec its field declares, reading the relating `provides`. It answered for exactly
//! one shape — a receiver spelled BARE whose sort provides the spec DIRECTLY — and
//! declined the two commonest departures from it:
//!
//!   * the provision is TRANSITIVE (`List provides Stream`, `Stream provides
//!     Iterable`, with no direct `List provides Iterable` fact);
//!   * the receiver is written with type ARGUMENTS (`xs: List[T = Int64]`) rather
//!     than bare or all-self-projections.
//!
//! THE MISS WAS SILENT, which is what made it expensive. The caller falls back to the
//! raw argument type, `unify_types` of `List[T = Int64]` against `Iterable[C = ?_,
//! Element = ?_, E = ?_]` answers TRUE while binding nothing useful, and the
//! constructed carrier's params — including the SIBLING arrow field's row — stay
//! free. It surfaced far from the cause, as `undeclared effect ??_` on the
//! constructing operation.
//!
//! TWO AXES, AND THEY ARE INDEPENDENT — measured as a 2x2 before anything was
//! changed, because the first fixture confounded them (the carrier that worked was
//! both direct AND unparameterized):
//!
//!            | direct provision | transitive provision
//!   bare     | clean            | LEAKED
//!   written  | LEAKED           | LEAKED
//!
//! Only the conjunction worked, so both had to move. Three edits: the direct view
//! falls back to [`transitive_provision_view`] (which already composes exactly this
//! and whose own doc names `List`-through-`Stream` as its case); the receiver test
//! accepts a written application, restricted to CONCRETE carriers; and a written type
//! argument overrides the receiver projection in σ.
//!
//! WHAT FAILS WHEN EACH IS BACKED OUT is stated per test below. The rows are ordered
//! so the two axes are separated before the stdlib row that needs both.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

fn errors_for(extra: &str) -> Vec<String> {
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

/// Four source carriers spanning the 2x2. `BareDirect` is the one shape that already
/// worked; the others each depart from it on ONE axis.
const CARRIERS: &str = r#"
  sort BareDirect
    import anthill.prelude.{Int64, List, Stream, Iterable}
    entity bareDirect(xs: List[T = Int64])
    provides Iterable[C = BareDirect, Element = Int64, E = {}]
    operation iterator(b: BareDirect) -> Stream[T = Int64, E = {}] =
      match b
        case bareDirect(l) -> l
  end

  sort BareTrans
    import anthill.prelude.{Int64, List, Stream, Option, Pair}
    import anthill.prelude.Option.{some, none}
    import anthill.prelude.Pair.{pair}
    entity bareTrans(xs: List[T = Int64])
    provides Stream[T = Int64, E = {}]
    operation splitFirst(b: BareTrans)
      -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =
      match b
        case bareTrans(l) -> Stream.splitFirst(l)
  end

  sort ParamDirect
    import anthill.prelude.{Int64, List, Stream, Iterable}
    sort T = ?
    entity paramDirect(xs: List[T = T])
    provides Iterable[C = ParamDirect[T = T], Element = T, E = {}]
    operation iterator(b: ParamDirect) -> Stream[T = b.T, E = {}] =
      match b
        case paramDirect(l) -> l
  end
"#;

fn load_body(ns: &str, body: &str) -> Vec<String> {
    errors_for(&format!(
        "namespace wibh1jz.{ns}\n  \
         import anthill.prelude.{{List, Int64, Stream, Iterable, MappedStream}}\n  \
         import anthill.prelude.MappedStream.{{mapped}}\n{CARRIERS}\n  \
         operation inc(x: Int64) -> Int64 = x + 1\n{body}\nend\n"
    ))
}

/// CONTROL — the one cell that already worked. Passes either way BY DESIGN; it is
/// what makes the two rows after it experiments about their own axis rather than
/// about whether this shape ever worked.
#[test]
fn bare_receiver_with_a_direct_provision_was_always_fine() {
    let errs = load_body(
        "bd",
        "  operation probe(b: BareDirect) -> Stream[T = Int64, E = {}] =\n    \
         Iterable.iterator(mapped(b, inc))",
    );
    assert!(errs.is_empty(), "the control cell must be green; got: {errs:?}");
}

/// AXIS 1 — TRANSITIVE provision, receiver still bare.
///
/// BACKED OUT (drop the `transitive_provision_view` fallback): FAILS with
/// `undeclared effect ??_`.
#[test]
fn a_transitive_provision_projects() {
    let errs = load_body(
        "bt",
        "  operation probe(b: BareTrans) -> Stream[T = Int64, E = {}] =\n    \
         Iterable.iterator(mapped(b, inc))",
    );
    assert!(
        errs.is_empty(),
        "a carrier whose spec rides through an intermediate must still project; \
         got: {errs:?}"
    );
}

/// AXIS 2 — receiver WRITTEN with type arguments, provision still direct.
///
/// BACKED OUT (drop the `sort_functor_of_view` widening, or the written-argument
/// override in σ): FAILS — without the widening as `undeclared effect ??_`, without
/// the σ override as `expected b.T -> ?_, got Int64 -> Int64`, the sibling arrow field
/// judged against the projection instead of the written argument.
#[test]
fn a_receiver_written_with_type_arguments_projects() {
    let errs = load_body(
        "pd",
        "  operation probe(b: ParamDirect[T = Int64]) -> Stream[T = Int64, E = {}] =\n    \
         Iterable.iterator(mapped(b, inc))",
    );
    assert!(
        errs.is_empty(),
        "a receiver written with type arguments must project as well as a bare one; \
         got: {errs:?}"
    );
}

/// BOTH AXES AT ONCE, on the stdlib carrier this ticket came from — and the headline
/// program: `List` is written with a type argument AND reaches `Iterable` through
/// `Stream`. FAILS when EITHER axis is backed out.
#[test]
fn the_stdlib_list_case_type_checks() {
    let errs = errors_for(
        r#"
        namespace wibh1jz.stdlib
          import anthill.prelude.{List, Int64, MappedStream, FiniteCollection}
          import anthill.prelude.MappedStream.{mapped}
          operation inc(x: Int64) -> Int64 = x + 1
          operation probe(xs: List[T = Int64]) -> List[T = Int64] =
            FiniteCollection.collect(mapped(xs, inc))
        end
    "#,
    );
    assert!(
        errs.is_empty(),
        "building a combinator by hand over a List and collecting it must type-check; \
         got: {errs:?}"
    );
}

/// THE CARRIER PARAMETER IS THE RECEIVER'S OWN TYPE, not what the provision writes
/// there. A self-referential provision spells it with the sort's own name (`Stream
/// provides Iterable[C = Stream, …]` — `C = Self`), and composing through a hop
/// substitutes the intermediate's PARAMS, not that self-reference, so it survives
/// literally.
///
/// BACKED OUT (read the carrier slot off the view like every other param): the
/// construction infers `MappedStream[Source = Stream, …]` and this row FAILS — the
/// finiteness witness, gated on `requires FiniteCollection[C = S]`, asks whether the
/// SPEC `Stream` is a FiniteCollection and answers no. Measured; it is why the
/// stdlib row above needs this edit as well as the two axes.
#[test]
fn the_carrier_param_binds_to_the_receiver_not_to_the_provisions_self_reference() {
    let errs = errors_for(
        r#"
        namespace wibh1jz.carrier
          import anthill.prelude.{List, Int64, Bool, MappedStream}
          import anthill.prelude.MappedStream.{mapped}
          operation inc(x: Int64) -> Int64 = x + 1
          operation probe(xs: List[T = Int64])
            -> MappedStream[Source = List[T = Int64], Src = Int64, T = Int64, ES = {}, EF = {}] =
            mapped(xs, inc)
        end
    "#,
    );
    assert!(
        errs.is_empty(),
        "`Source` must be the receiver's own `List[T = Int64]`; got: {errs:?}"
    );
}

/// THE SOUNDNESS GATE, RE-MEASURED HERE. This change grounds the very parameter the
/// finiteness witness reads, so it could in principle have made an INFINITE source
/// collectable. It does not: `ZNats` provides `Stream` (hence `Iterable`) and never
/// `FiniteCollection`, so the witness's `requires` is still undischarged.
///
/// Passes either way BY DESIGN — before the change this was refused for the WRONG
/// reason (nothing grounded at all). It is here because a soundness property must be
/// re-asserted by the change that touches its inputs, not inherited.
#[test]
fn an_infinite_source_is_still_refused() {
    let errs = errors_for(
        r#"
        namespace wibh1jz.sound
          import anthill.prelude.{List, Int64, Stream, Option, Pair, MappedStream, FiniteCollection}
          import anthill.prelude.MappedStream.{mapped}
          import anthill.prelude.Option.{some}
          import anthill.prelude.Pair.{pair}
          sort ZNats
            import anthill.prelude.{Int64, Stream, Option, Pair}
            import anthill.prelude.Option.{some}
            import anthill.prelude.Pair.{pair}
            entity znats(from: Int64)
            provides Stream[T = Int64, E = {}]
            operation splitFirst(n: ZNats)
              -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =
              match n
                case znats(k) -> some(pair(k, znats(from: k + 1)))
          end
          operation inc(x: Int64) -> Int64 = x + 1
          operation probe(n: ZNats) -> List[T = Int64] =
            FiniteCollection.collect(mapped(n, inc))
        end
    "#,
    );
    assert!(
        !errs.is_empty(),
        "a mapped stream over an INFINITE source must stay uncollectable — grounding \
         `Source` must not hand the witness a gate it cannot fail"
    );
}
