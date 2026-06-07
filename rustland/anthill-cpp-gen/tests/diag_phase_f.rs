//! Diagnostic: dump OperationInfo for an op with Error effect to
//! discover how `effects` is stored.
use super::common;
use anthill_core::kb::term::Term;
use common::load_kb_with_lenient;

#[test]
#[ignore]
fn dump_phase_f_shapes() {
    let source = r#"
        namespace test.dumpf
          import anthill.prelude.{Int64, Error}
          import anthill.prelude.Error.{raise}
          export Calc
          sort Calc
            operation a(x: Int64) -> Int64 effects Error = x
            operation r() -> Int64 effects Error = raise("boom")
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);

    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo").unwrap();
    for rid in kb.rules_by_functor(op_info_sym) {
        let head = kb.rule_head(rid);
        let nm = if let Term::Fn { named_args, .. } = kb.get_term(head) {
            named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "name")
                .and_then(|(_, v)| match kb.get_term(*v) {
                    Term::Ref(s) => Some(kb.qualified_name_of(*s).to_string()),
                    _ => None,
                })
        } else { None };
        let Some(name) = nm else { continue };
        if !name.contains("test.dumpf") { continue; }
        println!("\n== {name} ==");
        dump_term(&kb, head, 2);
    }
}

fn dump_term(kb: &anthill_core::kb::KnowledgeBase, term: anthill_core::kb::term::TermId, indent: usize) {
    let pad = " ".repeat(indent);
    match kb.get_term(term) {
        Term::Fn { functor, named_args, pos_args } => {
            let qn = kb.qualified_name_of(*functor);
            println!("{pad}Fn {qn:?} pos={} named:", pos_args.len());
            for p in pos_args { dump_term(kb, *p, indent + 4); }
            for (n, v) in named_args {
                println!("{pad}  {} =", kb.resolve_sym(*n));
                dump_term(kb, *v, indent + 4);
            }
        }
        Term::Ref(s) => println!("{pad}Ref({})", kb.qualified_name_of(*s)),
        Term::Ident(s) => println!("{pad}Ident({})", kb.qualified_name_of(*s)),
        Term::Const(lit) => println!("{pad}Const({lit:?})"),
        other => println!("{pad}{other:?}"),
    }
}
