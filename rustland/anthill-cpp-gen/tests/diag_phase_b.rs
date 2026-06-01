//! Diagnostic: dump body shapes for if-then-else and field access.
use super::common;
use anthill_core::kb::term::Term;
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
    for rid in kb.rules_by_functor(op_impl_sym) {
        let head = kb.rule_head(rid);
        if let Term::Fn { named_args, .. } = kb.get_term(head) {
            let op = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "operation")
                .map(|(_, v)| *v).unwrap();
            let op_sym = match kb.get_term(op) {
                Term::Ref(s) => *s,
                _ => continue,
            };
            let op_name = kb.qualified_name_of(op_sym).to_string();
            if !op_name.contains("test.dumpb") { continue; }
            println!("\n== {op_name} ==");
            // WI-305: the body occurrence lives in the op_body_node side-table.
            match kb.op_body_node(op_sym) {
                Some(node) => println!("{node:#?}"),
                None => println!("  (no body)"),
            }
        }
    }
}
