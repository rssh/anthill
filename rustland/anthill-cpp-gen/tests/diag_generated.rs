//! Diagnostic: dump shape of `fact Generated(...).profile` to figure
//! out why `extract_optional_string` returns None for `some(...)`.
use super::common::load_kb_with;
use anthill_core::kb::term::Term;

#[test]
#[ignore]
fn dump_generated_profile_shape() {
    let source = r#"
        namespace test.diag_gen
          import anthill.prelude.{Option}
          import anthill.realization.{Generated}
          fact Generated(
            source:      "test.diag_gen.X",
            artifact:    "out/X",
            language:    "cpp",
            profile:     some("cpp20-stl"),
            kind:        "controller",
            description: none
          )
        end
    "#;
    let kb = load_kb_with(source);
    let sym = kb.try_resolve_symbol("anthill.realization.Generated").unwrap();
    for rid in kb.by_functor(sym) {
        let head = kb.rule_head(rid);
        if let Term::Fn { named_args, .. } = kb.get_term(head) {
            for (name, val) in named_args {
                let n = kb.resolve_sym(*name);
                if n != "profile" && n != "description" { continue; }
                println!("\n== {n} ==");
                dump(&kb, *val, 2);
            }
        }
    }
}

fn dump(kb: &anthill_core::kb::KnowledgeBase, term: anthill_core::kb::term::TermId, indent: usize) {
    let pad = " ".repeat(indent);
    match kb.get_term(term) {
        Term::Fn { functor, named_args, pos_args } => {
            let qn = kb.qualified_name_of(*functor);
            println!("{pad}Fn {qn:?} pos={} named={}", pos_args.len(), named_args.len());
            for p in pos_args { dump(kb, *p, indent + 4); }
            for (n, v) in named_args {
                println!("{pad}  {} =", kb.resolve_sym(*n));
                dump(kb, *v, indent + 4);
            }
        }
        Term::Ref(s) => println!("{pad}Ref({})", kb.qualified_name_of(*s)),
        Term::Ident(s) => println!("{pad}Ident({})", kb.qualified_name_of(*s)),
        Term::Const(lit) => println!("{pad}Const({lit:?})"),
        other => println!("{pad}{other:?}"),
    }
}
