//! Diagnostic: emit lf1 LeaderController with the current cpp-gen
//! to see how `sort with operations + no carrier + no bodies` lowers.
use super::common;
use std::path::PathBuf;
use anthill_cpp_gen::{emit_namespace_header, emit_traits_struct};
use common::{collect_anthill_files, load_kb_with_extras};

#[test]
#[ignore]
fn emit_lf1_leader_controller() {
    let lf1_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/webots-modelling/lf1");
    let files = collect_anthill_files(&lf1_dir);
    let extras: Vec<PathBuf> = files;
    let mut kb = load_kb_with_extras("namespace _anchor end", &extras);

    println!("\n=== LeaderController traits class ===\n");
    match emit_traits_struct(&mut kb, "anthill.examples.lf1.LeaderController") {
        Ok(cpp) => println!("{cpp}"),
        Err(e) => println!("ERROR: {}", e.message),
    }

    println!("\n=== FollowerController traits class ===\n");
    match emit_traits_struct(&mut kb, "anthill.examples.lf1.FollowerController") {
        Ok(cpp) => println!("{cpp}"),
        Err(e) => println!("ERROR: {}", e.message),
    }

    println!("\n=== Full namespace header ===\n");
    match emit_namespace_header(&mut kb, "anthill.examples.lf1") {
        Ok(cpp) => println!("{cpp}"),
        Err(e) => println!("ERROR: {}", e.message),
    }
}
