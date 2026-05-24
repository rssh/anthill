//! Diagnostic: dump the term shape of `case some(?w) -> body`.
use super::common;
use anthill_core::kb::term::Term;
use common::load_kb_with_lenient;

#[test]
#[ignore]
fn dump_match_binding_shapes() {
    let source = r#"
        namespace test.dump_mb
          import anthill.prelude.{Int, Option}
          export Calc
          sort Calc
            operation unwrap(o: Option[T = Int]) -> Int =
              match o
                case some(?w) -> ?w
                case none     -> 0
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);

    let op_impl_sym = kb.try_resolve_symbol("anthill.realization.OperationImpl").unwrap();
    for rid in kb.by_functor(op_impl_sym) {
        let head = kb.rule_head(rid);
        if let Term::Fn { named_args, .. } = kb.get_term(head) {
            let op = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "operation")
                .map(|(_, v)| *v).unwrap();
            let op_sym = match kb.get_term(op) {
                Term::Ref(s) => *s,
                _ => continue,
            };
            let op_name = kb.qualified_name_of(op_sym).to_string();
            if !op_name.contains("test.dump_mb") { continue; }
            println!("\n== {op_name} ==");
            // WI-305: the body occurrence lives in the op_body_node side-table.
            match kb.op_body_node(op_sym) {
                Some(node) => println!("{node:#?}"),
                None => println!("  (no body)"),
            }
        }
    }
}
