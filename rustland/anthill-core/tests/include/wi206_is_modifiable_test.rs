//! WI-206 — the `anthill.reflect.is_modifiable(t: Type) -> Bool` reflect op:
//! whether a `Modify` can fire on a place of type `t` (proposal 037 Rule 8). Since
//! 2026-10-16 it asks the predicate the kernel typer enforces the rule with
//! (`region::type_admits_modify`, WI-20260823-TR8CF), so reflection and the kernel
//! cannot disagree: a claimed sort, a provider of one, a type holding one. It lets
//! user code introspect what the kernel typer enforces — defensive code that mutates
//! only a modifiable argument, reflection-driven listings of the modifiable resources
//! in scope.
//!
//! Two surfaces are pinned here:
//!   * from anthill source, with the sort passed BY REFERENCE (`is_modifiable(Cell)`,
//!     the `facts_of(kb(), WorkItem)` convention of WI-632). A bare SORT name had no
//!     value reading before this WI (only a free-standing ENTITY did), so the op also
//!     brought the sort-as-`Type` reading in the typer + eval;
//!   * at the value level: a parameterized `Cell[V = Int64]` is modifiable because its
//!     claimed base `Cell` is — which a literal `Modifiable[T = t]` KB query could not
//!     answer, the claim's `T` being the bare `Cell` — and a value that is no type is
//!     refused.
//!
//! The parameterized type written in SOURCE (`is_modifiable(List[T = Cell])`) is
//! WI-707's surface, and the type-argument row below uses it.
//!
//! DEFINITE where the typer is conservative (`region::type_definitely_admits_modify`):
//! what the walk cannot read — a bare `List`'s element, a type variable — answers false,
//! where the typer refuses a `Modify` only on a type known to hold nothing.

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;
use smallvec::SmallVec;

use crate::common::{interp_for, try_load_kb_with};

/// The stdlib claims `provides Modifiable[T = Self]` in `Cell` and `KB`, and nothing
/// claims one for `Int64` — so the op answers true, true, false from anthill source.
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
        let int64 = kb
            .try_resolve_symbol("anthill.prelude.Int64")
            .expect("Int64");
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
        "a parameterized Cell[V = Int64] is modifiable because its claimed base Cell is, \
         which a literal `Modifiable[T = t]` query could not answer (the claim's T is \
         the bare `Cell`) — got {got:?}"
    );
}

/// A PARAMETERIZED `Modifiable` fact makes its BASE modifiable, never its type
/// ARGUMENT: under `fact Modifiable[T = Box[V = Int64]]`, `Box` is modifiable and
/// `Int64` is not.
///
/// The claim's `T` binding is read for its head sort. `region_sorts`, which the op now
/// shares with the typer, used to collect every sort reachable anywhere in a claim's
/// head and would have reported `Int64` modifiable here — the trap this row pinned while
/// the two readers were kept apart; it now pins that the shared set is exact
/// (WI-20260823-TR8CF).
#[test]
fn a_parameterized_modifiable_fact_does_not_make_its_type_argument_modifiable() {
    let src = r#"
namespace test.wi206d
  import anthill.prelude.{Int64, Bool, Modifiable}
  import anthill.reflect.{is_modifiable}

  sort Box
    sort V = ?
  end

  namespace Box
    provides Modifiable[T = Box[V = Int64]]
  end

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

/// A sort name in an ordinary value position does not load. THE INVARIANT IS
/// UNCHANGED; what the rejection is MADE OF changed under proposal 055 §2
/// (WI-20260824-WAHB6).
///
/// Denotation no longer depends on the slot: the loader classifies a bare `Cell` as a
/// `Type` value wherever it stands, so this is no longer an unresolved NAME — it is the
/// ordinary sort mismatch §2 specifies ("a stray sort name in a `String` slot today
/// errors as `UnresolvedName`, under this rule as `expected String, got Type` — still
/// loud, arguably clearer"). The test asserts the two tokens that separate the readings:
/// the destination sort and `Type`.
///
/// STILL OWED, and owned: §8 requires the diagnostic to NAME THE DENOTED SORT
/// (`expected Int64, got Type (Cell)`) so a forgotten-parentheses constructor stays
/// short to trace. That is WI-20260824-JM6ZW's item, with its own control; this row
/// deliberately does not assert `Cell` yet, because asserting it here would make this
/// test the measurement of a change it is not paired with.
///
/// BACK-OUT: with the classification removed, the load still fails — as an unresolved
/// name — so `contains("got Type")` is the half that inverts and `Err(..)` is the half
/// that holds either way.
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
        errs.iter()
            .any(|e| e.contains("expected Int64") && e.contains("got Type")),
        "expected the ordinary destination mismatch proposal 055 §2 specifies \
         (`expected Int64, got Type`), got {errs:?}"
    );
}

/// REFLECTION AND THE KERNEL AGREE: a sort that `provides` a claimed spec
/// (`NonMonotonicStore provides Store`) and a data sort holding a `Cell` in a field
/// (`Wrap`) are modifiable — the op says so, AND a `Modify` on a place of each loads —
/// while a sort holding none (`Plain`) is not, and a `Modify` on it is refused. A bare
/// generic sort (`List`, its element unbound) answers false: the op is definite.
/// `wrap_is` FAILS with the op reading only the HEAD sort (its reading before 2026-10-16);
/// `nonmono_is` with the `provides` closure of `region_sorts` backed out
/// (`NonMonotonicStore` carries no claim of its own — and that back-out refuses the
/// stdlib's own rows, so every load fails with it); `bare_list_is` with the op on the
/// typer's conservative reading (an unbound element counted as admitting); `plain_is`
/// passes either way, by design. MEASURED, 2026-10-16.
#[test]
fn is_modifiable_answers_what_the_typer_accepts() {
    let src = r#"
namespace test.wi206e
  import anthill.prelude.{Cell, Int64, Bool, Unit, List, Modify}
  import anthill.reflect.{is_modifiable}
  import anthill.persistence.{NonMonotonicStore}

  sort Wrap
    entity wrap(rep: Cell[V = Int64])
  end
  sort Plain
    entity plain(n: Int64)
  end

  operation nonmono_is() -> Bool = is_modifiable(NonMonotonicStore)
  operation wrap_is() -> Bool = is_modifiable(Wrap)
  operation plain_is() -> Bool = is_modifiable(Plain)
  operation bare_list_is() -> Bool = is_modifiable(List)
end
"#;
    let mut interp = interp_for(src);
    for (op, want) in [
        ("nonmono_is", true),
        ("wrap_is", true),
        ("plain_is", false),
        ("bare_list_is", false),
    ] {
        let got = interp
            .call(&format!("test.wi206e.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e:?}"));
        assert!(matches!(got, Value::Bool(b) if b == want), "{op}: expected {want}, got {got:?}");
    }
    // The kernel's side of the same question, on the same sorts.
    let kernel = r#"
namespace test.wi206k
  import anthill.prelude.{Cell, Int64, Unit, Modify}
  import anthill.persistence.{NonMonotonicStore}
  sort Wrap
    entity wrap(rep: Cell[V = Int64])
  end
  sort Plain
    entity plain(n: Int64)
  end
  operation on_nonmono(s: NonMonotonicStore) -> Unit effects Modify[s]
  operation on_wrap(w: Wrap) -> Unit effects Modify[w]
  operation on_plain(p: Plain) -> Unit effects Modify[p]
end
"#;
    let errs = crate::common::load_errors_of(kernel);
    assert!(
        errs.len() == 1 && errs[0].contains("on_plain") && errs[0].contains("not `Modifiable`"),
        "the kernel must accept `Modify` on `NonMonotonicStore` and `Wrap` and refuse it on \
         `Plain`, as the op answers; got: {errs:#?}"
    );
}

/// … AND A TYPE ARGUMENT, written in source (WI-707): `List[T = Cell]` holds cells, so a
/// `Modify` on a place of it is accepted and the op answers true; `List[T = Int64]` does
/// not. The `Cell` row FAILS with the op reading only the head sort (`List` carries no
/// claim, measured); the `Int64` row passes either way, by design.
#[test]
fn a_type_argument_that_is_modifiable_makes_the_type_modifiable() {
    let src = r#"
namespace test.wi206f
  import anthill.prelude.{Cell, Int64, Bool, List}
  import anthill.reflect.{is_modifiable}

  operation cells_is() -> Bool = is_modifiable(List[T = Cell[V = Int64]])
  operation ints_is() -> Bool = is_modifiable(List[T = Int64])
end
"#;
    let mut interp = interp_for(src);
    for (op, want) in [("cells_is", true), ("ints_is", false)] {
        let got = interp
            .call(&format!("test.wi206f.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e:?}"));
        assert!(matches!(got, Value::Bool(b) if b == want), "{op}: expected {want}, got {got:?}");
    }
}

/// A VALUE THAT IS NO TYPE IS REFUSED, NOT ANSWERED. `plain(n: 3)` is a data value — a
/// constructor applied to an `Int64` — and the op raises a type mismatch for it. FAILS
/// with the guard reduced to "has a functor" (the guard before the review): the value
/// passes and is answered rather than refused (MEASURED; under the conservative reading
/// it was answered TRUE, the walk counting its unreadable argument as admitting).
#[test]
fn a_data_value_is_refused_as_no_type() {
    let mut interp = interp_for(
        "namespace test.wi206g\n  import anthill.prelude.{Int64}\n  sort Plain\n    entity plain(n: Int64)\n  end\nend\n",
    );
    let value = {
        let kb = interp.kb_mut();
        let plain = kb.try_resolve_symbol("test.wi206g.Plain.plain").expect("plain");
        let n = kb.intern("n");
        let three = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(3)));
        Value::term(kb.alloc(Term::Fn {
            functor: plain,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(n, three)]),
        }))
    };
    let got = interp.call("anthill.reflect.is_modifiable", &[value]);
    assert!(got.is_err(), "a data value must be refused as no type; got {got:?}");
}
