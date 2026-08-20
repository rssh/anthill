//! WI-845 (proposal 058 §8, phase 5) — the SPEC AMENDMENT's one un-pinned sentence,
//! driven.
//!
//! The amendment replaces `kernel-language.md` §8.7's *"A consumer chooses which
//! instantiation to use via `import`"* with: **an `import` governs VISIBILITY — which
//! names one file's text may write — and nothing else.** Every other sentence of the
//! new §Instance-coherence text is already driven somewhere (wi843 the coexistence
//! gate, wi860/wi862 the default rows and `one_default`, wi861 rung 2a, wi844/wi858 the
//! bracket, wi1094 the named slot). That one is not, because before this ticket the
//! spec asserted the OPPOSITE and no test could have been written for either reading.
//!
//! So the claim under test is that **the candidate set is GLOBAL, not scoped**:
//!
//! | claim | driven by |
//! |---|---|
//! | importing one of two providers does not select it — the unselected call is still refused, NAMING BOTH | `an_import_does_not_select_among_two_visible_providers` |
//! | …and the un-imported rival is a real candidate, not just a name in a message: mark IT default and the same bracket-less call takes it | `a_default_on_the_unimported_provider_still_wins` |
//! | the program is otherwise runnable, and the bracket is what decides | `the_bracket_selects_and_the_import_only_makes_it_writable` |
//!
//! ARMS 1 AND 2 ARE EACH OTHER'S BACK-OUT, which is why there is no perturbation to
//! describe: they run the SAME four namespaces and the SAME bracket-less call, and
//! `OTHER_NS` differs from `OTHER_NS_DEFAULT` by the single word `default`. One word
//! moves the program from *refused, naming both* to *answers 9*. If the candidate set
//! were the caller's imports, arm 1 would load clean and arm 2 would answer `7` — the
//! imported witness — so neither arm can pass under the reading this ticket retired.
//!
//! MEASURED, and it is the sentence the whole ticket turns on: the refusal names its
//! candidates by QUALIFIED name — `providers: wi845.rival.Rival, wi845.other.Other` —
//! and `wi845.other.Other` is a sort `wi845.use` has no import for and could not write.
//! It is on the list because the program declares it, not because this file sees it.
//!
//! WHICH ARM IS A CONTROL AND PASSES EITHER WAY BY DESIGN:
//! `the_bracket_selects_and_the_import_only_makes_it_writable` and
//! `positive_control_a_broken_program_is_refused` — the first pins tier 1, which no
//! reading of scope touches, and exists so arm 1's refusal is known to be about
//! *selection* rather than about a program that never worked.
//!
//! Reference: `docs/kernel-language.md` §8.7 *Instance coherence*;
//! `docs/proposals/058-modular-instances.md` §8, §7 (the rejected scoped-implicit
//! alternative); `docs/design/058-implementation.md` §8 phase 5.

use anthill_core::eval::Value;

/// `Desc`, its carrier `Leaf`, and the `Holder` whose sort-level `requires` makes the
/// caller construct the dictionary at the call site — all in ONE namespace, so that the
/// only thing the arms below vary is which namespace each *provider* lives in and what
/// the caller imports.
const BASE: &str = r#"
namespace wi845.base
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
  end

  sort Holder
    sort HT = ?
    requires Desc[T = HT]
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
end
"#;

/// A witness for `Leaf` in its OWN namespace — the one the caller imports.
const RIVAL_NS: &str = r#"
namespace wi845.rival
  import anthill.prelude.Int64
  import wi845.base.{Desc, Leaf}

  sort Rival
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
end
"#;

/// A second witness in a THIRD namespace, which the caller never imports. Plain.
const OTHER_NS: &str = r#"
namespace wi845.other
  import anthill.prelude.Int64
  import wi845.base.{Desc, Leaf}

  sort Other
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 9
  end
end
"#;

/// The same third namespace, with its provision marked `default`. One word apart from
/// [`OTHER_NS`], which is what makes the pair a measurement rather than two programs.
const OTHER_NS_DEFAULT: &str = r#"
namespace wi845.other
  import anthill.prelude.Int64
  import wi845.base.{Desc, Leaf}

  sort Other
    default provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 9
  end
end
"#;

/// The caller. It imports `Rival` and NOT `Other`, so under the retired per-`import`
/// reading `Rival` would be the only candidate here.
fn caller(call: &str) -> String {
    format!(
        r#"
namespace wi845.use
  import anthill.prelude.Int64
  import wi845.base.{{Desc, Leaf, Holder}}
  import wi845.rival.Rival

  sort Driver
    operation drive(n: Int64) -> Int64 = {call}
  end
end
"#
    )
}

const UNSELECTED: &str = "Holder.probe(Leaf.leaf())";
const SELECTED: &str = "Holder.probe[Desc = Rival](Leaf.leaf())";

fn sources(other: &str, call: &str) -> Vec<String> {
    vec![
        BASE.to_string(),
        RIVAL_NS.to_string(),
        other.to_string(),
        caller(call),
    ]
}

fn load_errs(srcs: &[String]) -> Vec<String> {
    let refs: Vec<&str> = srcs.iter().map(String::as_str).collect();
    crate::common::try_load_kb_with_files(&refs)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{}", refs.concat()))
}

/// `Driver.drive(0)` on a FRESH interpreter — a shared one is poisoned by an earlier
/// trapped call. Building it here rather than via `common::interp_for`, which takes a
/// single source and this file is multi-namespace by construction.
fn eval_int(srcs: &[String], why: &str) -> i64 {
    let refs: Vec<&str> = srcs.iter().map(String::as_str).collect();
    let kb = match crate::common::try_load_kb_with_files(&refs) {
        Ok(kb) => kb,
        Err(errs) => panic!("{why}; the program did not load: {errs:?}"),
    };
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    match interp.call("wi845.use.Driver.drive", &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}"),
    }
}

// ── Positive control ─────────────────────────────────────────────────

/// The harness reports breakage, so a clean load below would be a real assertion.
#[test]
fn positive_control_a_broken_program_is_refused() {
    let mut srcs = sources(OTHER_NS, SELECTED);
    srcs.push(
        "\nnamespace wi845.control\n  sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end\nend\n"
            .to_string(),
    );
    load_errs(&srcs);
}

// ── The amendment's sentence ─────────────────────────────────────────

/// THE HEADLINE. Two witnesses for one `(spec, carrier)` in two DIFFERENT namespaces;
/// the caller imports exactly one of them and writes no bracket. Under the text this
/// ticket retired — "a consumer chooses which instantiation to use via `import`" — that
/// program is unambiguous and answers `7`. It is refused, and the refusal names
/// `Other`, a sort the caller cannot even write: proof that the candidate set is
/// assembled from what the program DECLARES, not from what this file imports.
#[test]
fn an_import_does_not_select_among_two_visible_providers() {
    let errs = load_errs(&sources(OTHER_NS, UNSELECTED));
    // ONE error carrying BOTH names, not two errors that between them mention both —
    // the claim is that a single refusal faced both candidates, and a joined-text
    // search cannot tell the two apart (review). The candidates are asserted by their
    // QUALIFIED names, which is what makes this a measurement of the candidate SET
    // rather than of the wording: `wi845.other.Other` is a sort `wi845.use` has no
    // import for and could not write.
    assert!(
        errs.iter()
            .any(|e| e.contains("wi845.rival.Rival") && e.contains("wi845.other.Other")),
        "one unselected dispatch must name BOTH candidates — importing one of them is \
         not a selection. Naming only `wi845.rival.Rival` would be scope-directed \
         selection with a spurious error on top; naming neither would be some other \
         refusal. Got:\n{}",
        errs.join("\n")
    );
}

/// AND THE UN-IMPORTED RIVAL IS A REAL CANDIDATE, not merely a name in a message. The
/// same program, differing only in the word `default` on `Other`'s provision — in the
/// namespace the caller never imports — makes the same bracket-less call answer **9**.
///
/// This is the arm that separates the two readings by a VALUE rather than by a
/// diagnostic: a scoped candidate set would answer `7` (the imported witness) whatever
/// a foreign namespace marked. It also drives §8.7's *fill silence, never overwrite
/// speech* from the other side — there is nothing in the caller to overwrite.
#[test]
fn a_default_on_the_unimported_provider_still_wins() {
    assert_eq!(
        eval_int(
            &sources(OTHER_NS_DEFAULT, UNSELECTED),
            "a `DefaultProvider` row is keyed by (spec, carrier) and consulted globally"
        ),
        9,
        "`default provides` in `wi845.other` must decide a bracket-less call in \
         `wi845.use`, which imports only `wi845.rival` — 7 would mean the caller's \
         import ranked the candidates, the scope-directed selection 058 §7 rejects"
    );
}

/// THE CONTROL, and it is deliberately insensitive to everything above: with the
/// bracket the call selects tier 1 and answers `7`. It exists so the refusal in the
/// headline is known to be about *selection* and not about a program that never ran —
/// and it is also where the import earns its keep, since `Rival` is a value the caller
/// must be able to WRITE.
#[test]
fn the_bracket_selects_and_the_import_only_makes_it_writable() {
    assert_eq!(
        eval_int(
            &sources(OTHER_NS, SELECTED),
            "an explicit selection is tier 1 and needs no default"
        ),
        7,
        "`[Desc = Rival]` selects the imported witness"
    );
}
