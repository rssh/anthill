//! WI-377: the loader's shared absent-aware effect-row fold
//! (`fold_effect_row_occ`) must NOT double-wrap a `-E` lacks-atom. The
//! pre-WI-377 `Arrow` arm wrapped EVERY effect child in `present(…)`, so on the
//! occurrence/Node fold path (taken when the row carries a value-in-type, e.g.
//! the denoted `Modify[a]`) a `-E` lacks-atom — already an `absent(E)` atom
//! from the `EffectAbsent` arm — became the malformed `present(absent(E))`.
//! That makes the lacks-atom surface as a spurious PRESENT effect
//! (`effect_row_present_values` drops bare `absent` atoms but keeps the label
//! of a `present(absent(E))`).
//!
//! Behavioural witness, on the same effect-propagation lever as WI-341/WI-360:
//! a `foreach` callback that BOTH modifies its element (`Modify[a]`, a denoted
//! effect that forces the occurrence/Node fold) AND carries a lacks-atom
//! (`-Branch`). With the op-level row declared as exactly `Modify[l]` (the
//! surfaced, re-keyed `Modify[a]`), the op must load CLEAN — the lacks-atom
//! contributes NOTHING to the present row. Under the pre-WI-377 double-wrap,
//! `present(absent(Branch))` surfaces a spurious undeclared effect and the load
//! fails. (Empirically confirmed: reverting `fold_effect_row_occ` to the
//! unconditional-`present` fold turns this test red.)

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Load stdlib + user source together (the path the effect check runs on) and
/// surface load errors as strings rather than panicking. Mirrors the WI-341
/// callback harness.
fn load_result(source: &str) -> Result<(), Vec<String>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    parsed.push(parse::parse(source).expect("parse user source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| format!("{}", e)).collect())
}

#[test]
fn lacks_atom_in_denoted_effect_row_is_not_double_wrapped() {
    // `{Modify[a], -Branch}`: `Modify[a]` (the arrow param `a` is a value) forces
    // the occurrence/Node fold; `-Branch` is the lacks-atom under test. The
    // callback's only PRESENT effect is `Modify[a]`, surfacing as `Modify[l]` at
    // the op boundary (WI-341), which is exactly what the op declares — so it must
    // load CLEAN. The pre-WI-377 fold wrapped `-Branch` into the malformed
    // `present(absent(Branch))`, surfacing a spurious undeclared effect.
    let src = r#"
namespace anthill.test.wi377
  import anthill.prelude.{List, Unit, Cell}

  operation each(l: List[T = Cell], f: (a: Cell) -> Unit @ {Modify[a], -Branch}) -> Unit effects Modify[l] =
    match l
      case nil() -> ()
      case cons(h, rest) -> f(h)
end
"#;
    let res = load_result(src);
    assert!(
        res.is_ok(),
        "a `-Branch` lacks-atom in a denoted effect row must lower to a bare \
         `absent(Branch)`, not the double-wrapped `present(absent(Branch))`; the \
         lacks-atom adds no present effect, so `each` must load clean with \
         `effects Modify[l]`. Got: {:#?}",
        res.err()
    );
}

#[test]
fn lacks_atom_without_declaration_still_surfaces_only_the_modify() {
    // Control / companion to WI-341's surfacing test: drop the `effects Modify[l]`
    // declaration. The callback still modifies its element, so `Modify[l]` must
    // surface and be reported undeclared — but the `-Branch` lacks-atom must add
    // NOTHING to surface (no spurious `absent`/`Branch` effect). Under the bug, an
    // extra undeclared effect from `present(absent(Branch))` would also appear.
    let src = r#"
namespace anthill.test.wi377nodecl
  import anthill.prelude.{List, Unit, Cell}

  operation each(l: List[T = Cell], f: (a: Cell) -> Unit @ {Modify[a], -Branch}) -> Unit =
    match l
      case nil() -> ()
      case cons(h, rest) -> f(h)
end
"#;
    let errs = load_result(src)
        .expect_err("a modifying callback must surface `Modify[l]` when undeclared");
    assert!(
        errs.iter().any(|e| e.contains("Modify[T = l]")),
        "expected the surfaced, re-keyed `Modify[l]` (rendered `Modify[T = l]`) — not \
         the un-re-keyed `Modify[T = a]`/`Modify[f.a]`; got: {errs:#?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("absent") || e.contains("Branch")),
        "the `-Branch` lacks-atom must NOT surface a spurious effect \
         (the pre-WI-377 `present(absent(Branch))` double-wrap would); got: {errs:#?}"
    );
}
