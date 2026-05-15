//! Auto-generated `<Sort>.induction(?P) :- ho_apply(?P, ctor1), …`
//! emitted by the loader for sorts/enums with constructors.


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::{Term, TermId};
use anthill_core::parse;
#[allow(unused_imports)]
use anthill_core::persistence::print::TermPrinter;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);

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
fn recursive_field_emits_inductive_hypothesis() {
    // For `cons(head: Int, tail: IntList)` the body goal must wrap
    // in forall_impl with a `ho_apply(?P, ?tail)` antecedent — i.e.
    // the inductive hypothesis on the recursive position. The base
    // case `nil` stays as a flat ho_apply.
    let src = r#"
        namespace test.induction.ih
          export IntList
          enum IntList
            entity nil
            entity cons(head: Int, tail: IntList)
          end
        end
    "#;
    let kb = load_with(src);
    let sym = kb.try_resolve_symbol("test.induction.ih.IntList.induction").unwrap();
    let rid = kb.by_functor(sym)[0];
    let body = kb.rule_body(rid);
    assert_eq!(body.len(), 2, "expected 2 body goals (nil + cons)");

    // Find the cons goal — must be a forall_impl term.
    let printer = TermPrinter::new(&kb);
    let cons_goal = body.iter().copied().find(|&g| {
        matches!(kb.get_term(g),
            Term::Fn { functor, .. } if kb.resolve_sym(*functor) == "forall_impl")
    }).unwrap_or_else(|| {
        let dump: Vec<_> = body.iter().map(|&t| printer.print_term(t)).collect();
        panic!("no forall_impl in body: {dump:?}")
    });

    let printed = printer.print_term(cons_goal);
    assert!(printed.contains("(forall("), "missing forall: {printed}");
    assert!(printed.contains(" -: "), "missing -: separator: {printed}");
    assert!(printed.contains("ho_apply"), "missing ho_apply: {printed}");
    assert!(printed.contains("cons"), "consequent should reference cons: {printed}");

    // The other goal (nil base case) must be a flat ho_apply, not forall_impl.
    let nil_goal = body.iter().copied().find(|&g| g != cons_goal).unwrap();
    match kb.get_term(nil_goal) {
        Term::Fn { functor, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "ho_apply",
                "nil case should be flat ho_apply");
        }
        other => panic!("unexpected nil goal: {other:?}"),
    }
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
