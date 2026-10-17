//! WI-20260823-TR8CF — a `Modify` fires only on a place of a MODIFIABLE type
//! (proposal 037 Rule 8; kernel-language.md §5.6). `operation touch(pattern: String)
//! -> Unit effects Modify[pattern]` loaded clean, and an op's honest row then had to
//! repeat a `Modify` on an `Int64` at every caller.
//!
//! A type is modifiable when a `Modifiable` provision names it, when it `provides` a
//! sort that is, when a type argument or an entity field of it is, or when it is a type
//! parameter. Each test below states which back-out it fails under.

use std::collections::BTreeSet;

use crate::common::load_errors_of;

/// The ops a load refused for a `Modify` over a non-modifiable type, by local name —
/// and the load's ONLY errors: any other refusal fails the test, so an op the fixture
/// counts as accepted is shown to load clean, not merely to escape this one message.
fn refused_ops(src: &str) -> BTreeSet<String> {
    let errs = load_errors_of(src);
    let (ours, others): (Vec<&String>, Vec<&String>) =
        errs.iter().partition(|e| e.contains("which is not `Modifiable`"));
    assert!(others.is_empty(), "errors other than the Modifiable refusal: {others:#?}");
    ours.iter()
        .filter_map(|e| {
            let qn = e.split("operation `").nth(1)?.split('`').next()?;
            Some(qn.rsplit('.').next()?.to_string())
        })
        .collect()
}

fn names(ns: &[&str]) -> BTreeSet<String> {
    ns.iter().map(|n| n.to_string()).collect()
}

/// THE ACCEPTANCE ROW, and the refusal names `Modifiable` and the place's type. FAILS
/// with the check backed out (`check_modify_targets`'s place arm): it loaded clean.
#[test]
fn a_modify_on_a_string_parameter_is_refused_naming_modifiable() {
    let errs = load_errors_of(
        r#"
namespace tr8cf.string
  import anthill.prelude.{String, Unit, Modify}
  operation touch(pattern: String) -> Unit effects Modify[pattern] = ()
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains("touch")
            && e.contains("Modify[T = pattern]")
            && e.contains("`String`")
            && e.contains("which is not `Modifiable`")),
        "expected `Modify[pattern]` on a `String` refused naming `Modifiable`; got: {errs:#?}"
    );
}

/// ONE FIXTURE, BOTH VERDICTS: what is refused and what is not, together, so a predicate
/// that refused too much or too little cannot pass by a homogeneous fixture. The
/// accepted half covers each way a type is modifiable except `provides` (its own test
/// below): a `Modifiable` sort, a type argument, an entity field, a field path, a type
/// parameter, and `result` of a modifiable type. A function value admits only through
/// what it RETURNS: `on_fn_returning_cell` is accepted, while `on_fn_row` and
/// `on_fn_cell` return an `Int64` and are refused — they were admitted, by the
/// effect-row binding and by the `Cell` PARAMETER (review). `on_fn_cell` FAILS with the
/// `Function` arm of `region::admits_modify` backed out; that arm alone also refuses
/// `on_fn_row`, reading only `B`. An effect-row binding is no held value either:
/// `on_stream` FAILS with the effect-row arm backed out (MEASURED). FAILS with the check
/// backed out (the
/// refused set is empty), and with the type-parameter arm of `region::admits_modify`
/// backed out (`on_param` is refused — and so is the stdlib's `MutableCollection`, whose
/// `Modify[c]` has `c: C`, so every load fails with it). MEASURED, 2026-10-16.
#[test]
fn only_places_of_non_modifiable_types_are_refused() {
    let src = r#"
namespace tr8cf.mixed
  import anthill.prelude.{Int64, Bool, Unit, Cell, Modify, List, Function, Stream}
  sort Wrap
    entity wrap(rep: Cell[V = Int64])
  end
  operation on_int(n: Int64) -> Unit effects Modify[n] = ()
  operation on_ints(ns: List[T = Int64]) -> Unit effects Modify[ns] = ()
  operation on_fn(k: Function[A = Int64, B = Int64]) -> Unit effects Modify[k] = ()
  operation on_fn_row(k: Function[A = Int64, B = Int64, E = {}]) -> Unit effects Modify[k] = ()
  operation on_fn_cell(k: Function[A = Cell[V = Int64], B = Int64]) -> Unit effects Modify[k] = ()
  operation on_fn_returning_cell(k: Function[A = Int64, B = Cell[V = Int64]]) -> Unit effects Modify[k] = ()
  operation on_stream(s: Stream[T = Int64, E = {}]) -> Unit effects Modify[s] = ()
  operation on_int_result() -> Bool effects Modify[result] = true
  operation on_cell(c: Cell[V = Int64]) -> Unit effects Modify[c] = ()
  operation on_cells(l: List[T = Cell[V = Int64]]) -> Unit effects Modify[l] = ()
  operation on_wrap(w: Wrap) -> Unit effects Modify[w] = ()
  operation on_wrap_rep(w: Wrap) -> Unit effects Modify[w.rep] = ()
  operation on_param[T](x: T) -> Unit effects Modify[x] = ()
  operation on_cell_result() -> Cell[V = Int64] effects Modify[result] = Cell.new(0)
end
"#;
    assert_eq!(
        refused_ops(src),
        names(&["on_fn", "on_fn_cell", "on_fn_row", "on_int", "on_int_result", "on_ints", "on_stream"])
    );
}

/// A field path is judged by its LAST field's type: `h.c` is a `Cell`, `h.n` an
/// `Int64`. FAILS with the path walk backed out to the head's type: the head `Holder`
/// admits by its `Cell` field, so `on_int_field` is accepted too.
#[test]
fn a_field_path_is_judged_by_its_last_fields_type() {
    let src = r#"
namespace tr8cf.path
  import anthill.prelude.{Int64, Unit, Cell, Modify}
  sort Holder
    entity holder(c: Cell[V = Int64], n: Int64)
  end
  operation on_cell_field(h: Holder) -> Unit effects Modify[h.c] = ()
  operation on_int_field(h: Holder) -> Unit effects Modify[h.n] = ()
end
"#;
    assert_eq!(refused_ops(src), names(&["on_int_field"]));
}

/// AN ABSTRACT CARRIER SAYS SO ITSELF, AND A REFINEMENT INHERITS IT. `Pool` claims
/// `Modifiable`; `SubPool provides Pool` claims nothing and is modifiable through it;
/// `Other`, claiming nothing and providing nothing, is refused. Mirrors the stdlib's
/// `Store` / `NonMonotonicStore`. FAILS with the `provides` closure backed out of
/// `region::region_sorts`' fixpoint (`drain_sub` is refused — and so is the stdlib's own
/// `NonMonotonicStore`, so every load fails with it).
#[test]
fn an_abstract_carrier_claims_it_and_a_provider_of_one_inherits_it() {
    let src = r#"
namespace tr8cf.abstract
  import anthill.prelude.{Unit, Modify, Modifiable}
  sort Pool {
    provides Modifiable[T = Self]
    operation drain(p: Pool) -> Unit effects Modify[p]
  }
  sort SubPool {
    provides Pool
    operation drain_sub(p: SubPool) -> Unit effects Modify[p]
  }
  sort Other {
    operation drain_other(p: Other) -> Unit effects Modify[p]
  }
end
"#;
    assert_eq!(refused_ops(src), names(&["drain_other"]));
}

/// A PARAMETERIZED CLAIM MAKES ITS SORT MODIFIABLE, NOT ITS ARGUMENTS. Under `provides
/// Modifiable[T = Box[V = Int64]]`, `Box` is modifiable and `Int64` is not. FAILS with
/// `region_sorts` collecting every sort reachable in a claim's head (its reading before
/// the review): `Int64` joined the set and `touch` loaded, program-wide.
#[test]
fn a_parameterized_claim_makes_its_sort_modifiable_not_its_arguments() {
    let src = r#"
namespace tr8cf.claim
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}
  sort Box
    sort V = ?
    entity box(v: V)
  end
  namespace Box
    provides Modifiable[T = Box[V = Int64]]
  end
  operation touch(n: Int64) -> Unit effects Modify[n] = ()
  operation poke(b: Box[V = Int64]) -> Unit effects Modify[b] = ()
end
"#;
    assert_eq!(refused_ops(src), names(&["touch"]));
}

/// A GENERIC MODIFIER INSTANTIATED AT A NON-MODIFIABLE TYPE OWES NOTHING. `touch[T]`'s
/// `Modify[x]` re-keyed at `touch(n)`, `n: Int64`, names a place nothing can mutate, so it
/// is dropped (user, 2026-10-16): `caller` loads with no declaration — which the check
/// would refuse — while `caller_cell` still owes `Modify[c]`. `caller` FAILS with the
/// vacuous-label arm of `region::op_boundary_effects` backed out (an undeclared
/// `Modify[n]` it could not declare); `caller_cell` passes either way, by design.
#[test]
fn a_generic_modifier_instantiated_at_a_non_modifiable_type_owes_nothing() {
    let src = r#"
namespace tr8cf.generic
  import anthill.prelude.{Int64, Unit, Cell, Modify}
  operation touch[T](x: T) -> Unit effects Modify[x] = ()
  operation caller(n: Int64) -> Unit = touch(n)
  operation caller_cell(c: Cell[V = Int64]) -> Unit = touch(c)
end
"#;
    let errs = load_errors_of(src);
    assert!(
        !errs.iter().any(|e| e.contains("caller.") || e.contains("`tr8cf.generic.caller`")),
        "`caller` passes an `Int64`: nothing to declare; got: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("caller_cell") && e.contains("Modify[T = c]")),
        "`caller_cell` passes a `Cell` and owes `Modify[c]`; got: {errs:#?}"
    );
}

/// A WRITTEN ROW IS JUDGED AT ITS ORIGIN. `Modify[p]` in a type argument names the
/// operation's own parameter, and an `Int64` one is refused there — a caller projecting
/// `s.E` would otherwise inherit a label it cannot declare. FAILS with the place arm of
/// `check_written_row_bindings` backed out (it loaded).
#[test]
fn a_place_in_a_written_row_must_be_modifiable() {
    let src = r#"
namespace tr8cf.written
  import anthill.prelude.{Int64, Bool, Cell, Modify, EffectsRuntime}
  sort Strm
    sort T = ?
    effects E = ?
  end
  operation from_int(p: Int64) -> Strm[T = Int64, E = {Modify[p]}]
  operation from_cell(c: Cell[V = Int64]) -> Strm[T = Int64, E = {Modify[c]}]
end
"#;
    let errs = load_errors_of(src);
    let refused: Vec<&String> = errs.iter().filter(|e| e.contains("not `Modifiable`")).collect();
    assert!(
        refused.len() == 1 && refused[0].contains("Modify[T = p]") && refused[0].contains("`Int64`"),
        "expected `from_int`'s written `Modify[p]` refused and `from_cell`'s admitted; got: {errs:#?}"
    );
}

/// A FIELD PATH IS JUDGED BY THE FIELD IT REACHES: by position in a tuple (`_1`), by
/// EVERY constructor that declares it (any one that admits), and with the application's
/// bindings for a field typed by the sort's parameter. FAILS with the review's three gaps
/// restored to `declared_field_types` (`result._1` and `b.v` admitted, `s.x` refused by
/// its first constructor's `Int64`).
#[test]
fn a_field_path_reads_positions_constructors_and_bindings() {
    let src = r#"
namespace tr8cf.fields
  import anthill.prelude.{Int64, Unit, Cell, Modify, todo}
  sort Two
    entity p(x: Int64)
    entity q(x: Cell[V = Int64])
  end
  sort Box
    sort T = ?
    entity box(v: T)
  end
  -- A hole, not an allocating body: the subject is the declaration, and a body
  -- allocating the whole tuple would owe `Modify[result]`, which a field's label does
  -- not cover.
  operation on_first() -> (a: Int64, b: Cell[V = Int64]) effects Modify[result._1] = todo()
  operation on_second() -> (a: Int64, b: Cell[V = Int64]) effects Modify[result._2] = todo()
  operation on_either(s: Two) -> Unit effects Modify[s.x] = ()
  operation on_int_box(b: Box[T = Int64]) -> Unit effects Modify[b.v] = ()
  operation on_cell_box(b: Box[T = Cell[V = Int64]]) -> Unit effects Modify[b.v] = ()
end
"#;
    assert_eq!(refused_ops(src), names(&["on_first", "on_int_box"]));
}

/// RESULT MASKING READS THE SAME PREDICATE. A cell reachable only through the returned
/// sort's FIELD escapes through the result, so its `Modify[result]` is kept and owed —
/// WI-314's recorded narrow slice masked it, an unsound drop. FAILS with masking's own
/// structural walk restored in `region::result_type_admits_region` (`mk_bare` then loads
/// clean); `mk_declared` passes either way, by design.
#[test]
fn a_region_behind_a_returned_field_is_kept() {
    let src = r#"
namespace tr8cf.mask
  import anthill.prelude.{Int64, Cell, Modify}
  sort Pair
    entity pair(c: Cell[V = Int64])
  end
  operation mk_bare() -> Pair = pair(c: Cell.new(0))
  operation mk_declared() -> Pair effects Modify[result] = pair(c: Cell.new(0))
end
"#;
    let errs = load_errors_of(src);
    assert!(
        errs.iter().any(|e| e.contains("mk_bare") && e.contains("Modify[T = result]")),
        "`mk_bare` returns a fresh cell inside its result and owes `Modify[result]`; got: {errs:#?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("mk_declared")),
        "`mk_declared` declares it; got: {errs:#?}"
    );
}
