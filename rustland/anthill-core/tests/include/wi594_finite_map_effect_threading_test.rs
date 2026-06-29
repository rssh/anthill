//! WI-594 — typer bug: thread the access-EFFECT row (not just the element) when a
//! value flows into a carrier's spec-typed field.
//!
//! Surfaced by WI-588 (finiteness Phase B). The finite-preserving combinator
//! `FiniteStream.map(s, f) = fmapped(s, f)` wants to wrap a stream-typed value in
//! a carrier whose `source` field is the spec, exactly like the lazy
//! `MappedStream.map`. But when a BARE spec-typed receiver flows into such a field
//! (and the carrier's element comes from a SECOND field, the transform), the typer
//! threads the source ELEMENT into the field and LEAVES THE EFFECT ROW UNBOUND.
//! The provided spec row is then ungrounded, so the declared return is rejected.
//! WI-588 ships a `finiteIterator` indirection (an explicit `FiniteStream[Element,
//! E]` return type) to route the effect; when this bug is fixed, that indirection
//! can be removed and `FiniteStream.map`/`filter` can wrap the receiver directly.
//!
//! The asymmetry (element threads, effect doesn't) has three faces — construction
//! (here), dispatch grounding of an op-param effect, and the provision-return
//! check on a row-bearing return. This test pins the construction face on the
//! EXISTING lazy carrier `MappedStream` (no finite machinery), so it isolates the
//! kernel gap and shows it is general — the lazy combinators have it too; they
//! only avoid it because `Iterable.map` routes through `iterator(c) -> Stream[
//! Element, E]`, whose explicit type-args carry the effect. A single-field carrier
//! threads the effect fine; the gap needs the two-field map shape.
//!
//! IGNORED until WI-594 lands; removing `#[ignore]` is the acceptance flip.

/// A bare-receiver `map` over the existing `MappedStream`: `mapped(s, f)` wraps a
/// bare abstract `Stream` receiver `s` into the `mapped` carrier (`source` field
/// `Stream[Src, ES]`). The result element comes from the transform `f` (`Dst`);
/// the source element/effect come from `s`. Threading SHOULD give the carrier
/// `ES = s.E` (provided row `{s.E, EffP}`), matching the declared return. Today
/// the source ELEMENT threads (`Src = s.T`) but the source EFFECT does NOT (`ES`
/// stays unbound), so the row is ungrounded and the return is rejected — the same
/// gap that forces WI-588's `finiteIterator` indirection. WI-594 fixes it.
#[test]
fn bare_receiver_map_threads_source_effect() {
    let src = r#"
namespace test.wi594
  import anthill.prelude.{Int64, Stream, Modify}
  import anthill.prelude.MappedStream.{mapped}

  -- the obvious bare-receiver map, mirroring `FiniteStream.map`:
  operation bare_map[Dst, EffP](s: Stream, f: (x: s.T) -> Dst @ {EffP, -Modify[x]})
    -> Stream[T = Dst, E = {s.E, EffP}] =
    mapped(s, f)
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(errs.is_empty(),
        "a bare spec receiver wrapped into a carrier field should thread the source \
         effect row (not just the element) and load clean:\n{}",
        errs.join("\n"));
}
