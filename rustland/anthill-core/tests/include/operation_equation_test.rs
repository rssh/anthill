//! `operation foo(x) -> T = body` should yield a kernel rule
//! `eq(foo(?x), body[x → ?x])` that the resolver can apply as a
//! rewrite during proof search.


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::Term;
use anthill_core::parse;
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

#[test]
fn operation_body_emits_equation_rule() {
    let src = r#"
        namespace test.op_eq.simple
          import anthill.prelude.{Int64}
          import anthill.prelude.Numeric.{add}
          export double
          operation double(x: Int64) -> Int64 = add(x, x)
        end
    "#;
    let kb = load_with(src);
    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq.eq")
        .or_else(|| kb.try_resolve_symbol("eq"))
        .expect("eq symbol");
    let rules = kb.rules_by_functor(eq_sym);
    let printer = TermPrinter::new(&kb);
    let heads: Vec<String> = rules.iter()
        .map(|&r| printer.print_term(kb.rule_head(r)))
        .collect();
    let found = heads.iter().any(|h| h.contains("double") && h.contains("add"));
    assert!(found,
        "no eq(double(...), add(...)) rule found among:\n{heads:#?}");
}

#[test]
fn equation_rule_has_correct_shape() {
    let src = r#"
        namespace test.op_eq.shape
          import anthill.prelude.{Int64}
          import anthill.prelude.Numeric.{add}
          export double
          operation double(x: Int64) -> Int64 = add(x, x)
        end
    "#;
    let kb = load_with(src);
    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq.eq")
        .or_else(|| kb.try_resolve_symbol("eq"))
        .expect("eq symbol");
    let rule_id = kb.rules_by_functor(eq_sym).into_iter()
        .find(|&r| {
            let head = kb.rule_head(r);
            match kb.get_term(head) {
                Term::Fn { pos_args, .. } if pos_args.len() == 2 => {
                    matches!(kb.get_term(pos_args[0]),
                        Term::Fn { functor, .. } if kb.qualified_name_of(*functor)
                            .ends_with("op_eq.shape.double"))
                }
                _ => false,
            }
        })
        .expect("no eq() rule referencing double()");

    assert_eq!(kb.rule_body_nodes(rule_id).len(), 0);

    let head = kb.rule_head(rule_id);
    let (lhs, rhs) = match kb.get_term(head) {
        Term::Fn { pos_args, .. } if pos_args.len() == 2 => (pos_args[0], pos_args[1]),
        _ => panic!("expected binary eq() head"),
    };
    let printer = TermPrinter::new(&kb);
    let lhs_s = printer.print_term(lhs);
    let rhs_s = printer.print_term(rhs);
    assert!(lhs_s.contains("double"),
        "lhs should be the operation call, got {lhs_s}");
    assert!(rhs_s.contains("add"),
        "rhs should be the body, got {rhs_s}");
}

#[test]
fn no_body_no_equation_rule() {
    let src = r#"
        namespace test.op_eq.no_body
          import anthill.prelude.{Int64}
          export plain
          operation plain(x: Int64) -> Int64
        end
    "#;
    let kb = load_with(src);
    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq.eq")
        .or_else(|| kb.try_resolve_symbol("eq"))
        .expect("eq symbol");
    let rules = kb.rules_by_functor(eq_sym);
    let printer = TermPrinter::new(&kb);
    let heads: Vec<String> = rules.iter()
        .map(|&r| printer.print_term(kb.rule_head(r)))
        .collect();
    assert!(
        !heads.iter().any(|h| h.contains("test.op_eq.no_body.plain")),
        "found unexpected eq rule for body-less operation: {heads:?}"
    );
}
