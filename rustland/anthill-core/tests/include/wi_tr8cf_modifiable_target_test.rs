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

/// The ops a load refused for a `Modify` over a non-modifiable type, by local name.
fn refused_ops(src: &str) -> BTreeSet<String> {
    load_errors_of(src)
        .iter()
        .filter(|e| e.contains("which is not `Modifiable`"))
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
/// parameter, and `result` of a modifiable type. FAILS with the check backed out (the
/// refused set is empty), and with the type-parameter arm of `region::admits_modify`
/// backed out (`on_param` is refused — and so is the stdlib's `MutableCollection`, whose
/// `Modify[c]` has `c: C`, so every load fails with it). MEASURED, 2026-10-16.
#[test]
fn only_places_of_non_modifiable_types_are_refused() {
    let src = r#"
namespace tr8cf.mixed
  import anthill.prelude.{Int64, Bool, Unit, Cell, Modify, List, Function}
  sort Wrap
    entity wrap(rep: Cell[V = Int64])
  end
  operation on_int(n: Int64) -> Unit effects Modify[n] = ()
  operation on_ints(ns: List[T = Int64]) -> Unit effects Modify[ns] = ()
  operation on_fn(k: Function[A = Int64, B = Int64]) -> Unit effects Modify[k] = ()
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
        names(&["on_fn", "on_int", "on_int_result", "on_ints"])
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
/// `region::is_region_sort` (`drain_sub` is refused — and so is the stdlib's own
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
