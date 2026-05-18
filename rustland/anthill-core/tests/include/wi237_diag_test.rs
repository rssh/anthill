//! WI-237 diagnostic: dump what the typer rewrites `eq` / `lt` calls
//! to when the anthill-todo bundle is loaded with find_sort_info on
//! the same_symbol fix (so cmd_X bodies actually type-check).
//!
//! Not a real test — `#[ignore]` by default; run with
//!   cargo test -p anthill-core --test wi237_diag_test -- --ignored --nocapture


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::Term;
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

#[test]
#[ignore]
fn dump_eq_lt_rewrites() {
    let mut files = crate::common::collect_stdlib_and_rust_bindings();
    files.push(crate::common::workspace_root().join("anthill-todo/domain.anthill"));
    files.push(crate::common::workspace_root().join("anthill-todo/rules.anthill"));
    files.push(crate::common::workspace_root().join("rustland/anthill-todo/anthill/store.anthill"));
    files.push(crate::common::workspace_root()
        .join("rustland/anthill-todo/anthill/main.anthill"));

    let parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src)
            .unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let load_result = load::load_all(&mut kb, &refs, &NullResolver);
    match &load_result {
        Ok(_) => println!("[wi237] load OK"),
        Err(errs) => {
            println!("[wi237] load errors ({}):", errs.len());
            for e in errs { println!("  {e}"); }
        }
    }

    // Dump every dispatch_origin entry — (rewritten_term, original_spec_op).
    println!("[wi237] dispatch_origin entries:");
    let mut count = 0;
    for (rewritten_tid, spec_sym) in kb.dispatch_origin_iter() {
        let spec_qn = kb.qualified_name_of(spec_sym).to_string();
        // Render the rewritten term's `fn` symbol.
        let fn_desc = match kb.get_term(rewritten_tid) {
            Term::Fn { named_args, .. } => {
                named_args.iter()
                    .find(|(s, _)| kb.resolve_sym(*s) == "fn")
                    .map(|(_, v)| match kb.get_term(*v) {
                        Term::Ref(s) | Term::Ident(s) => kb.qualified_name_of(*s).to_string(),
                        other => format!("{other:?}"),
                    })
                    .unwrap_or_else(|| "<no fn>".to_string())
            }
            other => format!("{other:?}"),
        };
        println!("  origin spec={spec_qn}  ->  rewritten fn={fn_desc}");
        count += 1;
        if count > 60 { println!("  ... (truncated)"); break; }
    }
    println!("[wi237] total dispatch_origin: {count}");

    // Also dump dispatch_rewrites count.
    let printer = TermPrinter::new(&kb);
    let _ = printer; // (printer kept for future per-term rendering)

    // ── Ordered.lt resolution probe ─────────────────────────────────
    let names = [
        "anthill.prelude.Ordered",
        "anthill.prelude.Ordered.lt",
        "anthill.prelude.Ordered.compare",
        "anthill.prelude.Int",
        "anthill.prelude.Int.lt",
        "anthill.prelude.Int.compare",
        "anthill.prelude.Int.Ordered.lt",
        "anthill.prelude.Int.Ordered.compare",
    ];
    for name in names {
        let resolved = kb.try_resolve_symbol(name);
        match resolved {
            Some(sym) => {
                let info = anthill_core::kb::op_info::lookup_operation_info(&kb, sym);
                let has_body = info.as_ref().map(|i| i.body_node.is_some()).unwrap_or(false);
                let has_info = info.is_some();
                println!("[wi237] resolve {name} -> Some  has_info={has_info} has_body={has_body}");
            }
            None => println!("[wi237] resolve {name} -> None"),
        }
    }
}
