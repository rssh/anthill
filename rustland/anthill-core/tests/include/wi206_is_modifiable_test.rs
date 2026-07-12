//! WI-206 — the `anthill.reflect.is_modifiable(t: Type) -> Bool` reflect op:
//! whether `t` is a modifiable resource, i.e. whether a `Modifiable[T = S]` fact
//! names t's head sort (the marker proposal 037 Rule 8 demands before `Modify[t]`
//! may appear in an effect row). It lets user code introspect what the kernel
//! typer enforces — defensive code that mutates only a modifiable argument,
//! reflection-driven listings of the modifiable resources in scope.
//!
//! Two surfaces are pinned here:
//!   * from anthill source, with the sort passed BY REFERENCE (`is_modifiable(Cell)`,
//!     the `facts_of(kb(), WorkItem)` convention of WI-632). A bare SORT name had no
//!     value reading before this WI (only a free-standing ENTITY did), so the op also
//!     brought the sort-as-`Type` reading in the typer + eval;
//!   * at the value level, where the HEAD-SORT semantics shows: a parameterized
//!     `Cell[V = Int64]` is modifiable because its base `Cell` is. A literal
//!     `Modifiable[T = t]` KB query could NOT answer that — the fact's `T` is the
//!     bare `Ref(Cell)`, which does not unify with the parameterized type.
//!
//! Writing that parameterized type in SOURCE (`is_modifiable(Cell[V = Int64])`) is a
//! separate language surface — a type expression used as a value argument, missing
//! today for every `Type`-taking reflect op alike (`facts_of(kb(), List[T = Int64])`
//! fails identically) — filed as its own WI.

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;
use smallvec::SmallVec;

use crate::common::{interp_for, try_load_kb_with};

/// The stdlib asserts `fact Modifiable[T = Cell]` (cell.anthill) and
/// `fact Modifiable[T = KB]` (reflect.anthill), and nothing asserts one for
/// `Int64` — so the op answers true, true, false from anthill source.
#[test]
fn is_modifiable_answers_the_modifiable_facts() {
    let src = r#"
namespace test.wi206
  import anthill.prelude.{Cell, Int64, Bool}
  import anthill.reflect.{is_modifiable, KB}

  operation cell_is() -> Bool = is_modifiable(Cell)
  operation kb_is() -> Bool = is_modifiable(KB)
  operation int_is() -> Bool = is_modifiable(Int64)
end
"#;
    let mut interp = interp_for(src);

    for (op, want) in [("cell_is", true), ("kb_is", true), ("int_is", false)] {
        let got = interp
            .call(&format!("test.wi206.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e:?}"));
        assert!(
            matches!(got, Value::Bool(b) if b == want),
            "{op}: expected {want} — the `Modifiable[T = …]` facts name Cell and KB, \
             never Int64 — got {got:?}"
        );
    }
}

/// The HEAD SORT decides, so a PARAMETERIZED instance answers as its base does:
/// `Cell[V = Int64]` is modifiable on the strength of `fact Modifiable[T = Cell]`.
/// Built at the value level because the source surface for a parameterized type in
/// an argument slot does not exist yet (see the module header).
#[test]
fn parameterized_instance_is_modifiable_via_its_base_sort() {
    let mut interp = interp_for("namespace test.wi206b\nend\n");

    let cell_int = {
        let kb = interp.kb_mut();
        let cell = kb.try_resolve_symbol("anthill.prelude.Cell").expect("Cell");
        let int64 = kb.try_resolve_symbol("anthill.prelude.Int64").expect("Int64");
        let v = kb.intern("V");
        let int_ref = kb.alloc(Term::Ref(int64));
        Value::term(kb.alloc(Term::Fn {
            functor: cell,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(v, int_ref)]),
        }))
    };

    let got = interp
        .call("anthill.reflect.is_modifiable", &[cell_int])
        .expect("is_modifiable(Cell[V = Int64])");
    assert!(
        matches!(got, Value::Bool(true)),
        "a parameterized Cell[V = Int64] is modifiable because its base sort Cell is \
         — the op matches the head sort, which a literal `Modifiable[T = t]` query \
         could not (the fact's T is the bare `Ref(Cell)`) — got {got:?}"
    );
}

/// A PARAMETERIZED `Modifiable` fact makes its BASE modifiable, never its type
/// ARGUMENT: under `fact Modifiable[T = Box[V = Int64]]`, `Box` is modifiable and
/// `Int64` is not.
///
/// The op must therefore read the fact's `T` binding and take its head sort — NOT
/// reuse the typer's `region_sorts`, which deliberately over-approximates (it
/// collects every sort reachable anywhere in the head, because for effect-masking a
/// result type that merely MENTIONS a region-bearing sort must keep its `Modify`).
/// Sharing that reader would report `Int64` modifiable here, and `cell.anthill`
/// documents exactly this `Modifiable[T = Cell[V]]` shape — so the trap is live.
#[test]
fn a_parameterized_modifiable_fact_does_not_make_its_type_argument_modifiable() {
    let src = r#"
namespace test.wi206d
  import anthill.prelude.{Int64, Bool, Modifiable}
  import anthill.reflect.{is_modifiable}

  sort Box
    sort V = ?
  end

  fact Modifiable[T = Box[V = Int64]]

  operation box_is() -> Bool = is_modifiable(Box)
  operation int_is() -> Bool = is_modifiable(Int64)
end
"#;
    let mut interp = interp_for(src);

    let box_is = interp.call("test.wi206d.box_is", &[]).expect("box_is");
    assert!(
        matches!(box_is, Value::Bool(true)),
        "the fact's T binding is Box[V = Int64] — its head sort Box is modifiable, \
         got {box_is:?}"
    );

    let int_is = interp.call("test.wi206d.int_is", &[]).expect("int_is");
    assert!(
        matches!(int_is, Value::Bool(false)),
        "Int64 merely APPEARS inside the fact's T binding as a type argument — that \
         does not make it a modifiable resource, got {int_is:?}"
    );
}

/// The sort-as-`Type` reading is confined to a slot that ASKS for a `Type`. A sort
/// name in an ordinary value position stays the loud error it is today rather than
/// silently typing as a type value — the guard on the typer's new arm.
#[test]
fn a_sort_name_in_a_non_type_slot_is_still_an_error() {
    let src = r#"
namespace test.wi206c
  import anthill.prelude.{Cell, Int64}

  operation stray() -> Int64 = Cell
end
"#;
    let errs = match try_load_kb_with(src) {
        Err(errs) => errs,
        Ok(_) => panic!("a bare sort name in an Int64 slot must not load"),
    };
    assert!(
        errs.iter().any(|e| e.contains("Cell")),
        "expected a loud diagnostic naming Cell, got {errs:?}"
    );
}
