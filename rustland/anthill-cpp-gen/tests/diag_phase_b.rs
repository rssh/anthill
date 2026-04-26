//! Diagnostic: dump body shapes for if-then-else and field access.
use super::common;
use anthill_core::kb::term::{HandleKind, Literal, Term};
use anthill_core::kb::occurrence::OccurrenceId;
use common::load_kb_with;

#[test]
#[ignore]
fn dump_phase_b_shapes() {
    let source = r#"
        namespace test.dumpb
          import anthill.prelude.{Int, Bool, Float}
          export Calc, Pose
          entity Pose(x: Float, y: Float)
          sort Calc
            operation abs(n: Int) -> Int = if gt(n, 0) then n else 0
            operation pos_x(p: Pose) -> Float = (p).x
            operation pos_y(p: Pose) -> Float = ?p.y
          end
        end
    "#;
    let kb = load_kb_with(source);

    let op_impl_sym = kb.try_resolve_symbol("anthill.realization.OperationImpl").unwrap();
    for rid in kb.by_functor(op_impl_sym) {
        let head = kb.rule_head(rid);
        if let Term::Fn { named_args, .. } = kb.get_term(head) {
            let op = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "operation")
                .map(|(_, v)| *v).unwrap();
            let body = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "body")
                .map(|(_, v)| *v).unwrap();
            let op_name = match kb.get_term(op) {
                Term::Ref(s) => kb.qualified_name_of(*s).to_string(),
                _ => continue,
            };
            if !op_name.contains("test.dumpb") { continue; }
            println!("\n== {op_name} ==");
            dump_term(&kb, body, 2);
        }
    }
}

fn dump_term(kb: &anthill_core::kb::KnowledgeBase, term: anthill_core::kb::term::TermId, indent: usize) {
    let pad = " ".repeat(indent);
    match kb.get_term(term) {
        Term::Const(Literal::Handle(HandleKind::Occurrence, id)) => {
            let occ = OccurrenceId::from_raw(*id);
            let inner = kb.occurrence_store().term(occ);
            println!("{pad}OccHandle({id}) →");
            dump_term(kb, inner, indent + 2);
        }
        Term::Fn { functor, named_args, pos_args } => {
            let qn = kb.qualified_name_of(*functor);
            println!("{pad}Fn {qn:?} pos={} named:", pos_args.len());
            for p in pos_args {
                dump_term(kb, *p, indent + 4);
            }
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
