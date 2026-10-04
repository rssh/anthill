//! WI-20260821-JR7BB — a scope-local predicate declaration may not capture a rule
//! head that a sibling file resolves through an import.
//!
//! Imports are file-local (WI-995), while a declaration belongs to every file that
//! writes the same scope. Without the refusal below, adding `local.anthill` changes the
//! unchanged head in `importer.anthill` from a clause of `jr7.lib.p` into a clause of
//! `jr7.demo.p`: locals precede imports in the name ladder. That is a silent retarget.
//!
//! BACK-OUT MEASUREMENT: remove the `report_rule_head_import_captures` call in the
//! definition scan. The selective capture row fails: it falls through to the
//! loader-invariant diagnostic rather than naming the capture. The wildcard spelling
//! remains loud through the pre-existing visible-scope collision rule, and the one-file
//! contribution and `Bool.{ite}` controls pass either way by design.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term, Var};

const LIB: &str = r#"
namespace jr7.lib
  fact seed(1)
  rule p(?x) :- seed(?x)
end
"#;

fn importer(import: &str) -> String {
    format!(
        "namespace jr7.demo\n  import jr7.lib.{import}\n  fact imported_seed(2)\n  \
         rule p(?x) :- imported_seed(?x)\nend\n"
    )
}

const SIBLING: &str = r#"
namespace jr7.demo
  fact local_seed(3)
  rule p(?x) :- local_seed(?x)
end
"#;

fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

#[test]
fn selective_and_wildcard_imports_both_refuse_a_sibling_local_capture() {
    for import in ["{p}", "*"] {
        let importer = importer(import);
        let errs = crate::common::try_load_kb_with_named_files(&[
            ("lib.anthill", LIB),
            ("importer.anthill", &importer),
            ("local.anthill", SIBLING),
        ])
        .err()
        .unwrap_or_else(|| panic!("`import jr7.lib.{import}` must refuse the capture"));
        if import == "{p}" {
            let capture = errs
                .iter()
                .find(|e| e.contains("would capture") && e.contains("`p`"))
                .unwrap_or_else(|| {
                    panic!("`{import}`: expected the capture diagnostic; got {errs:#?}")
                });
            assert!(
                capture.contains("importer.anthill"),
                "must name the imported head: {capture}"
            );
            assert!(
                capture.contains("local.anthill"),
                "must name the local mint: {capture}"
            );
            assert!(
                capture.contains("jr7.demo"),
                "must name the shared scope: {capture}"
            );
            assert!(
                !errs.iter().any(|e| e.contains("loader invariant failing")),
                "the user-facing refusal must replace the old internal error: {errs:#?}"
            );
        } else {
            assert!(
                errs.iter()
                    .any(|e| e.contains("introduces that name at 2 scopes")
                        && e.contains("jr7.demo")
                        && e.contains("jr7.lib")),
                "the wildcard spelling must remain loudly refused too; got {errs:#?}"
            );
        }
    }
}

#[test]
fn a_selectively_imported_head_without_a_competing_local_mint_still_contributes() {
    let importer = importer("{p}");
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        ("lib.anthill", LIB),
        ("importer.anthill", &importer),
    ]));
    assert_eq!(clauses(&kb, "jr7.lib.p"), Some(2));
    assert_eq!(clauses(&kb, "jr7.demo.p"), None);

    let p = kb
        .try_resolve_symbol("jr7.lib.p")
        .expect("imported predicate exists");
    let x_name = kb.intern("x");
    let x = kb.fresh_var(x_name);
    let xv = kb.alloc(Term::Var(Var::Global(x)));
    let goal = kb.alloc(Term::Fn {
        functor: p,
        pos_args: smallvec::smallvec![xv],
        named_args: smallvec::SmallVec::new(),
    });
    let answers = kb.resolve(&[goal], &Default::default());
    assert_eq!(
        answers.len(),
        2,
        "both files contribute to the imported predicate"
    );
}

#[test]
fn bool_ite_selective_import_still_resolves_and_evaluates() {
    const SRC: &str = r#"
namespace jr7.ite_control
  import anthill.prelude.{Bool, Int64}
  import anthill.prelude.Bool.{ite}
  operation run() -> Int64 = ite(true, 1, 2)
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    match interp.call("jr7.ite_control.run", &[]) {
        Ok(Value::Int(1)) => {}
        other => panic!("the deferred `Bool.{{ite}}` import must still evaluate; got {other:?}"),
    }
}
