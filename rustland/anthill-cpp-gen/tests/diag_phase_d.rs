//! Diagnostic: dump body shapes for match, constructor literals,
//! and collection literals.
use super::common;
use anthill_core::kb::term::Term;
use common::load_kb_with_lenient;

#[test]
#[ignore]
fn dump_phase_d_shapes() {
    let source = r#"
        namespace test.dumpd
          import anthill.prelude.{Int64, Bool, List}
          export Color, Calc
          sort Color
            entity Red
            entity Green
            entity Blue
          end
          sort Pose
            entity Pose(x: Int64, y: Int64)
          end
          sort Calc
            operation tag(c: Color) -> Int64 =
              match c
                case Red -> 0
                case Green -> 1
                case Blue -> 2
            operation make_pose(x: Int64) -> Pose = Pose(x: x, y: 0)
            operation pair(x: Int64) -> List[T = Int64] = [x, 1, 2]
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);

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
            if !op_name.contains("test.dumpd") { continue; }
            println!("\n== {op_name} ==");
            // WI-305: the body occurrence lives in the op_body_node side-table.
            match kb.op_body_node(op_sym) {
                Some(node) => println!("{node:#?}"),
                None => println!("  (no body)"),
            }
        }
    }
}
