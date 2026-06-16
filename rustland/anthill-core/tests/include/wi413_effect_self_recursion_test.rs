//! WI-413 — effect-row threading through a CARRIER-IMPL SELF-RECURSION (the
//! effect dual of WI-357's element threading, one layer deeper than WI-365).
//!
//! A lazy stream carrier whose `splitFirst` impl SELF-RECURSES on a
//! RECONSTRUCTED carrier value (`splitFirst(recw(rest))`) — the shape `filter`
//! needs to SKIP a non-matching element — must thread the carrier's effect row
//! through that recursive call. Before WI-413 the recursive call's incurred
//! effect leaked as an unbound `??_`.
//!
//! ROOT CAUSE (fixed): the constructor-pattern destructure `case recw(src)` read
//! its field types through the SHALLOW `walk_type_value`, which resolves only a
//! top-level type-param var — a PARAMETERIZED field type (`source: Stream[T = T,
//! E = E]`, whose params sit NESTED in the `Fn`'s named_args) was left
//! unsubstituted. So `src` came out `Stream[T = ?_, E = ?_]` instead of threading
//! the carrier's element/effect; `rest`, the reconstructed `recw(rest)`, and the
//! recursive call's effect all followed it to `?_`. The fix deep-walks the
//! pattern field type (`walk_pattern_field_type_deep`).
//!
//! As with the whole combinator library (`collect` / `takeN` / `fold_*` / `find`
//! / `map`), the carrier op declares its OWN `[Elem, Eff]` type params bound from
//! the receiver `Rec[T = Elem, E = Eff]`: the destructure then threads the
//! element/effect in (deep-walk), and the recursive call's `Eff` binds from its
//! reconstructed argument by ordinary op-type-param unification — so the effect
//! closes to the declared row. (A BARE self-receiver `r: Rec` has no such
//! op-param machinery and is not supported — the same reason the eager
//! combinators are all written with explicit params.)
//!
//! The real-world payoff is the lazy `FilteredStream` carrier (combinators.anthill,
//! WI-410); its end-to-end typecheck+eval lives in `eval_test.rs`
//! (`wi413_lazy_filter_skips_via_self_recursion`). This file pins the minimal
//! repro so a regression points straight at the threading gap.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra sources → load-error strings (empty Vec on clean load).
fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// The minimal repro: a parametric carrier `Rec` that provides `Stream`, whose
/// own `splitFirst` impl self-recurses on a RECONSTRUCTED `recw(rest)`. With the
/// carrier op's own `[Elem, Eff]` params (the combinator-library convention), the
/// destructure threads the element/effect and the recursive call's effect closes
/// to the declared `Eff` — no leaked `??_`.
const REC: &str = r#"
namespace test.wi413.rec
  import anthill.prelude.{Stream, Option, Pair, EffectsRuntime}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  sort Rec
    sort T = ?
    effects E = ?
    entity recw(source: Stream[T = T, E = E])
    provides Stream[T = T, E = E]
    operation splitFirst[Elem, Eff](r: Rec[T = Elem, E = Eff]) -> Option[T = Pair[A = Elem, B = Rec[T = Elem, E = Eff]]] effects Eff =
      match r
        case recw(src) ->
          match Stream.splitFirst(src)
            case none() -> none
            case some(pair(h, rest)) -> splitFirst(recw(rest))
  end
end
"#;

/// The `Rec` carrier typechecks: the self-recursive `splitFirst(recw(rest))`
/// threads the carrier effect so no undeclared `??_` effect leaks.
#[test]
fn rec_self_recursion_threads_effect() {
    let errs = load_errors(&[REC]);
    assert!(
        errs.is_empty(),
        "the WI-413 Rec carrier must typecheck: the self-recursive \
         splitFirst(recw(rest)) must thread the carrier effect, not leak an \
         undeclared ??_; got: {errs:?}",
    );
}
