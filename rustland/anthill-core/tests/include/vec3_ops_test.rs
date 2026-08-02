//! Vec3 vector operations (WI-137): vec_add / vec_sub / vec_scale
//! / vec_zero rules in `anthill.geometry` resolve to the expected
//! per-component arithmetic via SLD evaluation.


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// WI-931 — stdlib AND the rust host bindings. The vec rules do per-component
/// `Float` ARITHMETIC, and `fact Numeric[T = Float]` lives in the binding layer
/// (proposal 038), so a stdlib-only KB loads these rules but cannot answer them:
/// MEASURED, the driven goal below yields 0 solutions without the bindings and 1
/// with. That gap was invisible while the tests only asserted that names resolved.
fn load_with(extra: &str) -> KnowledgeBase {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    // Errors are RAISED, not discarded: a swallowed load error is how a test ends
    // up asserting things about a KB that never finished loading.
    load::load_all(&mut kb, &refs, &NullResolver)
        .unwrap_or_else(|errs| panic!("load failed: {:#?}",
            errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()));
    kb
}

#[test]
fn vec_ops_symbols_resolve() {
    // Smoke test: the operation symbols vec_add / vec_sub /
    // vec_scale / vec_zero resolve in the loaded KB. Their bodies
    // run through SLD when consumed; the test itself does not
    // need to invoke the resolver.
    let kb = load_with(r#"
        namespace test.vec3.smoke
          rule Marker(?x) :- ?x = 1
        end
    "#);
    for op in ["anthill.geometry.vec_add", "anthill.geometry.vec_sub",
               "anthill.geometry.vec_scale", "anthill.geometry.vec_zero"] {
        assert!(
            kb.try_resolve_symbol(op).is_some(),
            "missing vec op: {op}"
        );
    }
}

/// A user-source rule that calls `vec_add` through its IMPORTED SHORT NAME both
/// loads AND answers.
///
/// The `answers` half was added by WI-931 and it is the point of the test. This
/// asserted only that the rule LOADED, and a load says nothing about what the name
/// inside it reaches: when `anthill.geometry` briefly gained a `Vec3.vec_add/2`
/// operation, the imported short name bound to THAT instead of the relational
/// `vec_add/3`, this goal went from one solution to zero, and this test — the one
/// test in the tree that names the situation — kept passing. Driving it is what
/// makes it evidence (CLAUDE.md: a test for a capability must drive the
/// capability).
///
/// The solution's BOUND VALUE is deliberately not asserted: these clauses build
/// `Vec3(x: ?ax + ?bx, …)` and SLD leaves the sums SYMBOLIC for Z3 to discharge,
/// which is why the relational spelling exists at all.
#[test]
fn vec_ops_callable_from_user_rule() {
    let mut kb = load_with(r#"
        namespace test.vec3.use
          import anthill.geometry.{Vec3, vec_add}

          rule try_add(?c)
            :- vec_add(Vec3(x: 1.0, y: 2.0, z: 3.0),
                       Vec3(x: 4.0, y: 5.0, z: 6.0),
                       ?c)
        end
    "#);
    assert!(
        kb.try_resolve_symbol("test.vec3.use.try_add").is_some(),
        "user rule referencing vec_add did not load"
    );
    assert_eq!(
        crate::common::query_unary(&mut kb, "test.vec3.use.try_add").len(),
        1,
        "the imported short name `vec_add` must reach the relational rule and answer",
    );
}

#[test]
fn algebraic_law_rules_present() {
    let kb = load_with(r#"
        namespace test.vec3.laws
          rule Marker(?x) :- ?x = 1
        end
    "#);
    let probes = [
        "anthill.geometry.vec_add_comm",
        "anthill.geometry.vec_add_assoc",
        "anthill.geometry.vec_add_identity",
        "anthill.geometry.vec_scale_distrib_v",
        "anthill.geometry.vec_scale_distrib_s",
        "anthill.geometry.vec_scale_assoc",
        "anthill.geometry.vec_scale_identity",
        "anthill.geometry.vec_sub_def",
    ];
    for qn in probes {
        assert!(
            kb.try_resolve_symbol(qn).is_some(),
            "missing algebraic-law rule: {qn}"
        );
    }
}
