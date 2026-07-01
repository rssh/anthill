//! WI-599 — typer: generalize WI-594's bare-receiver access-effect threading to a
//! CARRIER-PARAM-spec constructor field.
//!
//! WI-594 threads a bare spec receiver `s : Stream` into a field typed with that
//! SAME spec (`source: Stream[Src, ES]`) via the receiver's self-projection. The
//! THIN finite `map` the user preferred for WI-588 wraps the bare CARRIER value
//! directly — `FiniteCollection.map(c, f) = fmapped(c, f)` — where `c` has the
//! carrier-param type `C` (a sort that merely PROVIDES the spec) and the combinator's
//! `source` field is typed with the spec (`FiniteCollection[C = SrcC, …]`). The
//! carrier param `C`/`C2` is NOT the spec base, so WI-594's self-projection does not
//! fire and the field's source carrier + access effect leak as `??_`.
//!
//! `carrier_arg_provision_projection` rebuilds the argument's type from the carrier's
//! provision (the enclosing spec's own params for a spec METHOD; an ambient `requires`
//! for a free op), keyed by the field's binding symbols so every param (carrier,
//! element AND effect) threads. This pins the spec-METHOD face (the shape the stdlib
//! thin `FiniteCollection.map`/`filter` use).

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
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.is_empty(),
        "a bare carrier value wrapped into a carrier-param-spec field should thread \
         the source carrier AND access effect from the carrier's provision and load \
         clean:\n{}",
        errs.join("\n")
    );
}
