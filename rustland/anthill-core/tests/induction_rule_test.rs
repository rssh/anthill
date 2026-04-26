//! Auto-generated `<Sort>.induction(?P) :- ho_apply(?P, ctor1), …`
//! emitted by the loader for sorts/enums with constructors.

mod common;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::{Term, TermId};
use anthill_core::parse;
#[allow(unused_imports)]
use anthill_core::persistence::print::TermPrinter;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = common::stdlib_dir();
    let files = common::collect_anthill_files(&stdlib);

    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

fn induction_rule_head_for(kb: &KnowledgeBase, qn_prefix: &str) -> Option<TermId> {
    // Find the auto-generated induction rule by its functor.
    let induction_qn = format!("{qn_prefix}.induction");
    let sym = kb.try_resolve_symbol(&induction_qn)?;
    kb.by_functor(sym).first().map(|&r| kb.rule_head(r))
}

#[test]
fn finite_enum_induction_rule_is_emitted() {
    let src = r#"
        namespace test.induction.color
          export Color
          enum Color
            entity red
            entity blue
            entity green
          end
        end
    "#;
    let kb = load_with(src);
    let head = induction_rule_head_for(&kb, "test.induction.color.Color")
        .expect("Color.induction rule missing");
    let printer = TermPrinter::new(&kb);
    match kb.get_term(head) {
        Term::Fn { functor, pos_args, .. } => {
            assert_eq!(kb.qualified_name_of(*functor),
                "test.induction.color.Color.induction");
            assert_eq!(pos_args.len(), 1, "induction takes one arg ?P");
        }
        other => panic!("expected Fn head, got {other:?}"),
    }

    // The rule body must reference each constructor exactly once
    // (via ho_apply). We can grep the body text.
    let sym = kb.try_resolve_symbol("test.induction.color.Color.induction").unwrap();
    let rid = kb.by_functor(sym)[0];
    let body_terms: Vec<String> = kb.rule_body(rid).iter()
        .map(|&t| printer.print_term(t))
        .collect();
    let body_blob = body_terms.join(" || ");
    for ctor in ["red", "blue", "green"] {
        assert!(body_blob.contains(ctor),
            "induction body missing constructor `{ctor}`:\n{body_blob}");
    }
}

#[test]
fn recursive_enum_induction_rule_has_one_case_per_constructor() {
    // Type-parameterised sorts skip induction emission for now;
    // exercise the recursive shape on a monomorphic enum instead.
    let src = r#"
        namespace test.induction.list
          export IntList
          enum IntList
            entity nil
            entity cons(head: Int, tail: IntList)
          end
        end
    "#;
    let kb = load_with(src);
    let sym = kb.try_resolve_symbol("test.induction.list.IntList.induction")
        .expect("IntList.induction symbol missing");
    let rid = kb.by_functor(sym).first().copied()
        .expect("no rule for MyList.induction");
    assert_eq!(kb.rule_body(rid).len(), 2,
        "expected 2 body goals (one per ctor), got {}", kb.rule_body(rid).len());
    let printer = TermPrinter::new(&kb);
    let body_blob: String = kb.rule_body(rid).iter()
        .map(|&t| printer.print_term(t))
        .collect::<Vec<_>>()
        .join(" || ");
    assert!(body_blob.contains("nil"), "body should mention `nil`: {body_blob}");
    assert!(body_blob.contains("cons"), "body should mention `cons`: {body_blob}");
}

#[test]
fn no_entities_no_induction_rule() {
    let src = r#"
        namespace test.induction.empty
          export Pure
          sort Pure
          end
        end
    "#;
    let kb = load_with(src);
    assert!(
        kb.try_resolve_symbol("test.induction.empty.Pure.induction").is_none(),
        "should not emit induction for empty sort"
    );
}

#[test]
fn nullary_constructor_uses_ref_term() {
    let src = r#"
        namespace test.induction.nullary
          export Bit
          enum Bit
            entity zero
            entity one
          end
        end
    "#;
    let kb = load_with(src);
    let sym = kb.try_resolve_symbol("test.induction.nullary.Bit.induction").unwrap();
    let rid = kb.by_functor(sym)[0];
    for &goal in kb.rule_body(rid) {
        let t = kb.get_term(goal);
        match t {
            Term::Fn { pos_args, .. } if pos_args.len() == 2 => {
                let ctor_term = kb.get_term(pos_args[1]);
                assert!(
                    matches!(ctor_term, Term::Ref(_)),
                    "nullary ctor should be Term::Ref, got {ctor_term:?}"
                );
            }
            other => panic!("expected ho_apply(?P, ctor) goal, got {other:?}"),
        }
    }
}
