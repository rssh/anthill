//! Integration tests for Ring/Polynom testcase.
//!
//! Verifies:
//! - Ring spec with infix operators (+, *) in rules
//! - Polynom sort with `requires Ring[R]` (positional binding)
//! - Arrow types `(R) -> R` and `(R, R) -> R` in operation params
//! - All files parse and load into KB without errors
use anthill_core::kb::KnowledgeBase;

/// Load stdlib + ring-polynom testcase into a fresh KB.
fn load_ring_polynom_kb() -> KnowledgeBase {
    let testcases_dir = crate::common::testcases_dir();
    let ring_path = testcases_dir.join("ring-polynom/ring.anthill");
    let polynom_path = testcases_dir.join("ring-polynom/polynom.anthill");
    crate::common::load_kb_with_user_files(&[
        crate::common::UserFile::Path(&ring_path),
        crate::common::UserFile::Path(&polynom_path),
    ])
}

#[test]
fn ring_polynom_loads_without_errors() {
    let mut kb = load_ring_polynom_kb();
    // Both Ring and Polynom should be resolvable
    let ring_term = kb.resolve_qualified_name_term("Ring");
    let polynom_term = kb.resolve_qualified_name_term("Polynom");
    assert_ne!(
        ring_term, polynom_term,
        "Ring and Polynom should be distinct sorts"
    );
}

#[test]
fn ring_has_operations() {
    let mut kb = load_ring_polynom_kb();

    // Ring operations should be resolvable by qualified name
    let ops = ["Ring.add", "Ring.mul", "Ring.neg", "Ring.zero", "Ring.one"];
    for op_name in &ops {
        let op_term = kb.resolve_qualified_name_term(op_name);
        let _ = op_term; // verify it resolves without panic
    }
}

#[test]
fn polynom_has_arrow_type_operations() {
    let mut kb = load_ring_polynom_kb();

    // Polynom operations should be resolvable, including those with arrow type params
    let ops = [
        "Polynom.eval",
        "Polynom.map_coeffs",
        "Polynom.zip_with",
        "Polynom.add",
        "Polynom.scale",
    ];
    for op_name in &ops {
        let op_term = kb.resolve_qualified_name_term(op_name);
        let _ = op_term; // verify it doesn't panic
    }
}

#[test]
fn polynom_has_requires_ring() {
    use anthill_core::kb::term::Term;

    let mut kb = load_ring_polynom_kb();

    // Query for SortRequiresInfo facts about Polynom
    let req_sym = kb.resolve_symbol("anthill.reflect.SortRequiresInfo");
    let results = kb.rules_by_functor(req_sym);
    assert!(!results.is_empty(), "should have SortRequiresInfo facts");

    // At least one should reference Polynom
    let polynom_term = kb.resolve_qualified_name_term("Polynom");
    let has_polynom_req = results.iter().any(|&fid| {
        let tid = kb.fact_term(fid);
        match kb.get_term(tid) {
            Term::Fn { named_args, .. } => named_args.iter().any(|(_, val)| *val == polynom_term),
            _ => false,
        }
    });
    assert!(
        has_polynom_req,
        "Polynom should have a SortRequiresInfo fact"
    );
}
