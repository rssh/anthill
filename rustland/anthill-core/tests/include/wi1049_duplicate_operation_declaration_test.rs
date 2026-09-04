//! WI-1049 — AN OPERATION NAME IS DECLARED AT MOST ONCE PER SCOPE.
//!
//! (Number note: `wi1049_effect_polymorphic_diagnostic_test` and the `WI-1049`
//! comments in `body_specialize.rs` / `typing.rs` are MIS-NUMBERED — that work is
//! the effect-polymorphic `[simp]` diagnostic, WI-1050's subject, committed
//! against this number by mistake. There has only ever been one WI-1049 and it is
//! this one. Nothing here relates to that work.)
//!
//! THE PROPERTY, not the refusal: a load must be a function of the program, not
//! of its spelling order. Two `operation` declarations of one name in one scope
//! break that. Both resolve to the SAME `Symbol` (`SymbolTable::define` merges —
//! "one name in one scope is still one symbol", WI-926), so the second does not
//! overload; it leaves a second `anthill.reflect.OperationInfo` fact carrying the
//! same name, and `op_info::lookup_operation_info` answers from whichever it
//! reaches FIRST. MEASURED before the fix, on `q_op(x: T, y: T) -> T` and
//! `q_op(x: T) -> T` in one sort: the load is CLEAN in both orders, and
//! `declared_arity` answers 2 when the 2-ary is written first and 1 when the
//! 1-ary is. Swapping two declarations the language says nothing about changed
//! the answer.
//!
//! Order-independence ALONE would not have been enough: a deterministic
//! `lookup_operation_info` (always-first, always-last) restores the property and
//! still leaves one written `operation` silently unreachable. The refusal gives
//! both — the same error in either order, and no silent loss.
//!
//! THE VERDICT IS HOW MANY `operation` ITEMS ONE LOAD PHASE CONVERTED for the
//! name, not the number of `OperationInfo` facts the ticket proposed — that
//! premise ("survives the same file being scanned twice") is measured FALSE, and
//! `re_presenting_the_same_files_is_not_a_duplicate` is where it is measured. The
//! log is cleared per load phase, which is the whole de-duplication: a re-load is
//! a new phase, while everything inside one phase is the program as presented.
//! `two_identical_files_are_two_declarations` is why it is not de-duplicated any
//! further than that.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT:
//!   * `duplicate_operation_declaration_is_refused` — loads clean today.
//!   * `the_refusal_is_the_same_in_either_declaration_order` — the WI-979 idiom:
//!     the two fixtures are identical BUT FOR THE ORDER, and that is the whole
//!     experiment. Backed out, both orders load and the suite's own
//!     `arity_is_order_dependent_without_the_refusal` records what they answer.
//!   * `the_refusal_names_the_sort_the_name_and_both_sites`.
//!   * `an_identical_repeat_is_refused_too` — and this one ALSO fails against the
//!     fact-count design, so it is what separates the two.
//!   * `two_identical_files_are_two_declarations` — also fails against the
//!     text-keyed cut this suite's history records, which is why it exists.
//!
//! WHAT PASSES EITHER WAY, BY DESIGN — the controls:
//!   * `prelude_and_full_stdlib_still_load_clean` — the bootstrap PRE-DEFINES
//!     operation symbols (`kb.symbols.define("eq", "anthill.prelude.PartialEq.eq",
//!     …)`, WI-718/WI-967) into the same scope the stdlib source then declares
//!     `operation eq` in. A name-state check in `scan_definitions` pass 1 would
//!     fire on every one of them; the bootstrap converts no `Item::Operation`, so
//!     it logs no declaration and cannot be seen from here. This test says so.
//!   * `re_presenting_the_same_files_is_not_a_duplicate` — passes either way only
//!     because the verdict was moved off the fact count; against a fact-count
//!     verdict it FAILS, together with the three `*_idempotent_across_loads`
//!     suites. Non-vacuous: it asserts the re-load really did re-emit.
//!   * `a_rule_naming_an_operation_is_not_a_second_declaration` — a rule whose
//!     head names an operation is a LAW about it (WI-818), or the `[simp]`
//!     defining equation that GIVES a body-less operation its meaning (WI-881).
//!     Never a redeclaration. Refusing it would break the eq-family
//!     definition-by-cases and every hand-written law.
//!   * `same_name_on_two_sorts_is_not_a_duplicate` — `List.map`/`Stream.map` are
//!     distinct symbols in distinct scopes, chosen by carrier (§8.7's ladder,
//!     WI-1048). The check keys on the SYMBOL, so this cannot be caught, and this
//!     test is the pin that it stays that way.

use anthill_core::kb::op_info;

/// The ticket's own measurement, minimised: one sort, one name, two signatures.
/// Body-less on purpose — a spec-op declaration is the smallest shape that emits
/// an `OperationInfo`, with no body/equation machinery in the way.
const TWO_ARY_FIRST: &str = r#"
    namespace wi1049dup.a
      sort Q
        sort T = ?
        operation q_op(x: T, y: T) -> T
        operation q_op(x: T) -> T
      end
    end
"#;

/// `TWO_ARY_FIRST` with the two declarations SWAPPED and nothing else changed.
const ONE_ARY_FIRST: &str = r#"
    namespace wi1049dup.a
      sort Q
        sort T = ?
        operation q_op(x: T) -> T
        operation q_op(x: T, y: T) -> T
      end
    end
"#;

fn load_errors(src: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(errs) => errs,
    }
}

/// The errors that are THIS refusal, not some unrelated load failure the fixture
/// might also provoke.
fn duplicate_errors(src: &str) -> Vec<String> {
    load_errors(src)
        .into_iter()
        .filter(|e| e.contains("declared more than once"))
        .collect()
}

#[test]
fn duplicate_operation_declaration_is_refused() {
    let errs = duplicate_errors(TWO_ARY_FIRST);
    assert_eq!(
        errs.len(),
        1,
        "expected exactly one duplicate-operation refusal, got {errs:#?}"
    );
}

#[test]
fn the_refusal_is_the_same_in_either_declaration_order() {
    // WI-979 idiom: the two sources differ ONLY in the order of the two
    // declarations, so an identical rendering is the whole experiment.
    let a = duplicate_errors(TWO_ARY_FIRST);
    let b = duplicate_errors(ONE_ARY_FIRST);
    assert_eq!(a.len(), 1, "2-ary-first: {a:#?}");
    assert_eq!(b.len(), 1, "1-ary-first: {b:#?}");
    // BYTE-identical, including the two sites: the fixtures have the same line
    // layout, so the only thing that moved is which signature sits on which line —
    // exactly the difference the language says nothing about.
    assert_eq!(a[0], b[0], "a={a:#?}\nb={b:#?}");
}

#[test]
fn the_refusal_names_the_sort_the_name_and_both_sites() {
    let errs = duplicate_errors(TWO_ARY_FIRST);
    let msg = &errs[0];
    assert!(msg.contains("q_op"), "names the operation: {msg}");
    assert!(msg.contains("wi1049dup.a.Q"), "names the sort: {msg}");
    // Both declarations are on their own line in the fixture, so two distinct
    // `line:col` sites must appear — the author has to be able to find BOTH.
    assert_eq!(
        msg.matches("`operation` at ").count(),
        2,
        "expected two declaration sites in: {msg}"
    );
}

/// The measurement this refusal exists for, kept as a live assertion: with the
/// refusal backed out both fixtures load, and the SAME sort answers a different
/// arity depending on which declaration was written first. Here it runs against
/// the refusal, so it asserts the KBs do not exist at all — which is the fix.
#[test]
fn arity_is_order_dependent_without_the_refusal() {
    for src in [TWO_ARY_FIRST, ONE_ARY_FIRST] {
        let Ok(kb) = crate::common::try_load_kb_with(src) else {
            continue;
        };
        let op = kb
            .try_resolve_symbol("wi1049dup.a.Q.q_op")
            .expect("q_op resolves");
        panic!(
            "the duplicate loaded; `declared_arity` = {:?} — this is the \
             order-dependent read WI-1049 refuses",
            op_info::declared_arity(&kb, op),
        );
    }
}

/// CONTROL — passes either way BY DESIGN, and it is the one that says the
/// bootstrap was not caught. The stdlib is where the pre-registration lives:
/// `PartialEq.eq` / `WeakOrd.compare` / `Additive.add` are each `symbols.define`d by
/// the prelude bootstrap AND declared by source in the same scope. A name-state
/// check in `scan_definitions` pass 1 refuses all of them; a fact-count check
/// sees exactly one `OperationInfo` apiece. Driven, not asserted from the load
/// verdict alone — `load_kb_with` panicking would only say "no error", while the
/// counts say WHY there is none.
#[test]
fn prelude_and_full_stdlib_still_load_clean() {
    let kb = crate::common::load_kb_with(
        "namespace wi1049dup.empty\n  sort Nothing0\n    entity n0\n  end\nend\n",
    );
    let counts = op_info::operation_info_fact_counts(&kb);
    let dups: Vec<String> = counts
        .iter()
        .filter(|(_, &n)| n > 1)
        .map(|(s, n)| format!("{} × {n}", kb.qualified_name_of(*s)))
        .collect();
    assert!(
        dups.is_empty(),
        "stdlib carries duplicate OperationInfo facts: {dups:#?}"
    );
    for qn in [
        "anthill.prelude.PartialEq.eq",
        "anthill.prelude.WeakOrd.compare",
        // WI-20260825-1WBZT moved the arithmetic pre-registrations onto the syntax
        // categories (`Additive` / `Multiplicative`), so these three are the population
        // this row's own comment names — and the one a repoint could double-declare.
        "anthill.prelude.Additive.add",
        "anthill.prelude.Additive.sub",
        "anthill.prelude.Multiplicative.mul",
    ] {
        let sym = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("no symbol {qn}"));
        assert_eq!(
            counts.get(&sym),
            Some(&1),
            "{qn} reads exactly one OperationInfo"
        );
    }
}

#[test]
fn a_rule_naming_an_operation_is_not_a_second_declaration() {
    // CONTROL — passes either way BY DESIGN, and MUST. A `[simp]` equation is what
    // gives a body-less operation its meaning (WI-881); a plain rule head is a law
    // about it (WI-818). Neither mints a competing declaration — measured, all 345
    // stdlib operation symbols carry kind `Operation` alone.
    let src = r#"
        namespace wi1049dup.law
          import anthill.prelude.{Bool}
          sort L
            entity l(n: anthill.prelude.Int64)
            operation flag(v: L) -> Bool
            rule flag(?v) <=> false [simp]
          end
        end
    "#;
    let errs = duplicate_errors(src);
    assert!(
        errs.is_empty(),
        "a rule head is not a redeclaration: {errs:#?}"
    );
}

#[test]
fn same_name_on_two_sorts_is_not_a_duplicate() {
    // CONTROL — passes either way BY DESIGN. Overloading ACROSS sorts is real and
    // specified (§8.7's ladder); the two `pick`s are distinct symbols in distinct
    // scopes, so a symbol-keyed check cannot conflate them.
    let src = r#"
        namespace wi1049dup.cross
          import anthill.prelude.{Int64}
          sort A
            entity a
            operation pick(v: A) -> Int64
          end
          sort B
            entity b
            operation pick(v: B) -> Int64
          end
        end
    "#;
    let errs = duplicate_errors(src);
    assert!(
        errs.is_empty(),
        "cross-sort same name is not a duplicate: {errs:#?}"
    );
}

/// The case the ticket's proposed instrument — count the `OperationInfo` facts —
/// would have MISSED, and the reason the verdict counts DECLARATIONS instead. Two
/// byte-identical declarations build one ground head, which hash-conses, so the
/// fact count stays at 1. The message says so in its own words ("kept 1 signature
/// record"), which is the measurement, not a restatement of it.
///
/// FAILS WHEN THE CHANGE IS BACKED OUT — and it also fails against a fact-count
/// verdict, so it is what distinguishes the two designs.
#[test]
fn an_identical_repeat_is_refused_too() {
    let src = r#"
        namespace wi1049dup.same
          import anthill.prelude.List.{cons}
          sort R
            sort T = ?
            operation r_op(x: T) -> T
            operation r_op(x: T) -> T
          end
        end
    "#;
    let errs = duplicate_errors(src);
    assert_eq!(errs.len(), 1, "identical repeat must be refused: {errs:#?}");
    assert!(errs[0].contains("(2 declarations)"), "{}", errs[0]);
    assert!(
        errs[0].contains("kept 1 signature record under that one name"),
        "the two identical heads hash-cons to ONE OperationInfo, which is exactly \
         what a fact-count verdict cannot see: {}",
        errs[0]
    );
}

/// TWO GENUINELY DISTINCT FILES WHOSE TEXT HAPPENS TO BE IDENTICAL are two
/// declarations. Found by `/code-review` against an earlier cut that keyed each
/// site on `(source text, span)` to absorb a re-presented file: it absorbed this
/// too, and the pair loaded completely clean — `DuplicateTypeDeclaration` does not
/// cover it either, because the fixture declares no sort. Nothing but this test
/// stands between that key and a silently missed duplicate, which is why the
/// per-phase log is counted RAW.
///
/// FAILS WHEN THE CHANGE IS BACKED OUT, and it also fails against the text-keyed
/// cut — the only test that separates those two.
#[test]
fn two_identical_files_are_two_declarations() {
    let file = r#"
        namespace wi1049dup.twofiles
          import anthill.prelude.Int64
          operation tf(x: Int64) -> Int64 = x
        end
    "#;
    let errs = match crate::common::try_load_kb_with_files(&[file, file]) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    let dups: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains("declared more than once"))
        .collect();
    assert_eq!(
        dups.len(),
        1,
        "two files declaring `tf` are two declarations, whatever their bytes: {errs:#?}"
    );
}

/// CONTROL — passes either way BY DESIGN, and it is what a fact-count verdict
/// would have BROKEN. `load_all` into a live KB re-presents already-loaded files, and
/// every type-parameter-bearing operation then banks a SECOND `OperationInfo`
/// (`load_operation` mints a `fresh_var` per declared type parameter, so the
/// re-emitted head cannot hash-cons to the first). Clearing the declaration log at
/// the top of each load phase is what makes the re-load one declaration, not two.
///
/// Measured: with the verdict on fact counts this refuses stdlib operations
/// (`MappedStream.map`, `FilteredStream.splitFirst`, `FilteredStream.filter`,
/// `DelayMonad.pure`, `anthill.kernel.struct_eq`, `anthill.reflect.field_access`
/// among them) and takes all three `*_idempotent_across_loads` suites down with it.
#[test]
fn re_presenting_the_same_files_is_not_a_duplicate() {
    use anthill_core::kb::load::{self, NullResolver};
    use anthill_core::parse;

    let src = "namespace wi1049dup.reload\n  sort Z\n    entity z\n  end\nend\n";
    let mut kb = crate::common::load_kb_with(src);
    let files = crate::common::collect_anthill_files(&crate::common::stdlib_dir());
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    parsed.push(parse::parse(src).unwrap());
    let refs: Vec<_> = parsed.iter().collect();
    let errs = match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => Vec::new(),
        Err(e) => e.iter().map(|e| e.to_string()).collect::<Vec<_>>(),
    };
    let dups: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains("declared more than once"))
        .collect();
    assert!(
        dups.is_empty(),
        "a re-load is not a redeclaration: {dups:#?}"
    );
    // And the second load DID re-emit: the fact count moved even though the
    // declaration count did not. Without this the test would pass vacuously on a
    // KB where the re-load had been skipped entirely.
    let op = kb
        .try_resolve_symbol("anthill.prelude.MappedStream.map")
        .expect("MappedStream.map resolves");
    assert!(
        op_info::operation_info_fact_counts(&kb)
            .get(&op)
            .copied()
            .unwrap_or(0)
            > 1,
        "the re-load must actually re-emit OperationInfo, else this control is vacuous"
    );
}
