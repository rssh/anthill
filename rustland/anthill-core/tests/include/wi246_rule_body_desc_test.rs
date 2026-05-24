//! WI-246 regression: dropping the term-based rule body must NOT drop the
//! Description facts the old `convert_term` walk emitted for inline VARIABLE
//! descriptions (`?x {< … >}?`) appearing inside a rule body. In a GENERIC
//! (non-entity, non-reflect) body atom the loader now builds the body natively
//! via `build_body_atom_occurrence` and never calls `convert_term` on the atom,
//! so the description emission was re-added to that walk's `Var` arm. This test
//! locks that in.

use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term, Literal};
use anthill_core::kb::load::{self, NullResolver};

/// True iff the KB holds a `Description(_, text, _)` fact whose middle (text)
/// argument is the given string literal.
fn has_description_fact(kb: &KnowledgeBase, text: &str) -> bool {
    let Some(desc_sym) = kb.try_resolve_symbol("Description") else {
        return false;
    };
    kb.by_functor(desc_sym).iter().any(|&rid| {
        let head = kb.rule_head(rid);
        match kb.get_term(head) {
            Term::Fn { pos_args, .. } if pos_args.len() == 3 => {
                matches!(kb.get_term(pos_args[1]), Term::Const(Literal::String(s)) if s == text)
            }
            _ => false,
        }
    })
}

#[test]
fn body_var_inline_description_in_generic_atom_emits_description_fact() {
    // `some_pred` is an ordinary (non-entity) predicate, so the body atom takes
    // the native generic-Apply path in `build_body_atom_occurrence` — the path
    // that previously lost the description.
    let source = r#"
namespace test_desc
  rule has_value(?x)
    :- some_pred(?x {< the input value >}?)
end
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let parsed = parse::parse(source).expect("parse failed");
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    assert!(
        has_description_fact(&kb, "the input value"),
        "the inline description on the body variable `?x` must be emitted as a \
         Description fact (WI-246 must not drop it with the term body)",
    );
}
