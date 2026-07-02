//! WI-615 / proposal 051 — `===` structural identity test.
//!
//! `a === b` desugars (pratt) to `struct_eq(a, b)` → `anthill.kernel.struct_eq`,
//! registered as `BuiltinTag::Eq`, so the resolver runs the SAME structural
//! `builtin_eq` comparator `=`/`eq` shortcut to today — but under its own symbol,
//! so the Phase-2 flip of `=`/`eq` to dispatched semantic equality (WI-616)
//! leaves `===` structural. Phase-1 behaviour verified here: `===` is a total,
//! dispatch-free structural equality test that needs no `Eq` instance.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::parse;
use smallvec::SmallVec;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let parsed_extra =
        parse::parse(extra).unwrap_or_else(|e| panic!("parse extra: {e:?}"));
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).unwrap();
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parsed_extra);
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => {}
        Err(errs) => {
            for e in &errs {
                eprintln!("LOAD ERR: {}", e);
            }
            panic!("load failed with {} errors", errs.len());
        }
    }
    kb
}

fn int_term(kb: &mut KnowledgeBase, n: i64) -> TermId {
    kb.alloc(Term::Const(Literal::Int(n)))
}

fn ref_term(kb: &mut KnowledgeBase, qualified: &str) -> TermId {
    let sym = kb
        .try_resolve_symbol(qualified)
        .unwrap_or_else(|| panic!("symbol {qualified} not in KB"));
    kb.alloc(Term::Ref(sym))
}

/// `rule same(?x, ?y) :- ?x === ?y` — the whole point is that the body `===`
/// desugars to `struct_eq` and runs as the structural comparator at resolution.
const SRC: &str = r#"
    namespace test.wi615
      import anthill.prelude.Int64
      sort Pair
        entity pair(a: Int64, b: Int64)
      end
      -- A user entity with NO `fact Eq[...]` — `===` must still compare it.
      sort Tag
        entity red
        entity blue
      end
      rule same(?x, ?y) :- ?x === ?y
    end
"#;

fn same_solutions(kb: &mut KnowledgeBase, a: TermId, b: TermId) -> usize {
    let same = kb
        .try_resolve_symbol("test.wi615.same")
        .expect("test.wi615.same not in KB");
    let goal = kb.alloc(Term::Fn {
        functor: same,
        pos_args: SmallVec::from_slice(&[a, b]),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

#[test]
fn struct_eq_on_equal_ints_succeeds() {
    let mut kb = load_with(SRC);
    let a = int_term(&mut kb, 7);
    let b = int_term(&mut kb, 7);
    assert_eq!(same_solutions(&mut kb, a, b), 1, "7 === 7 must hold");
}

#[test]
fn struct_eq_on_unequal_ints_fails() {
    let mut kb = load_with(SRC);
    let a = int_term(&mut kb, 7);
    let b = int_term(&mut kb, 8);
    assert_eq!(same_solutions(&mut kb, a, b), 0, "7 === 8 must not hold");
}

#[test]
fn struct_eq_on_structurally_equal_compounds_succeeds() {
    let mut kb = load_with(SRC);
    let pair = kb.try_resolve_symbol("test.wi615.Pair.pair").unwrap();
    let a_field = kb.intern("a");
    let b_field = kb.intern("b");
    let mk_pair = |kb: &mut KnowledgeBase, x: i64, y: i64| {
        let xv = int_term(kb, x);
        let yv = int_term(kb, y);
        kb.alloc(Term::Fn {
            functor: pair,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(a_field, xv), (b_field, yv)]),
        })
    };
    let p1 = mk_pair(&mut kb, 1, 2);
    let p2 = mk_pair(&mut kb, 1, 2);
    assert_eq!(same_solutions(&mut kb, p1, p2), 1, "pair(1,2) === pair(1,2) must hold");

    let q1 = mk_pair(&mut kb, 1, 2);
    let q2 = mk_pair(&mut kb, 1, 3);
    assert_eq!(same_solutions(&mut kb, q1, q2), 0, "pair(1,2) === pair(1,3) must not hold");
}

#[test]
fn struct_eq_evaluates_in_an_operation_body() {
    // `===` is a Bool-returning TEST, so it must also work when EVALUATED in an
    // operation body — not only as a rule-body goal. Registered on the eval side
    // (`anthill.kernel.struct_eq` → `builtin_eq`) mirroring `Eq.eq`; without that
    // registration this call errors `UnknownOperation`.
    use anthill_core::eval::Value;
    let src = "namespace test.wi615.eval\n\
               import anthill.prelude.{Int64, Bool}\n\
               operation same(a: Int64, b: Int64) -> Bool = a === b\n\
               end\n";
    let mut interp = crate::common::interp_for(src);
    let t = interp
        .call("test.wi615.eval.same", &[Value::Int(4), Value::Int(4)])
        .expect("same(4,4) must evaluate");
    assert_eq!(t.as_bool(), Some(true), "4 === 4 in an op body must be true");
    let f = interp
        .call("test.wi615.eval.same", &[Value::Int(4), Value::Int(5)])
        .expect("same(4,5) must evaluate");
    assert_eq!(f.as_bool(), Some(false), "4 === 5 in an op body must be false");
}

#[test]
fn struct_eq_needs_no_eq_instance() {
    // `Tag` declares NO `fact Eq[T = Tag]`. `===` is total and dispatch-free, so
    // it still compares two `Tag` values structurally — the property that
    // distinguishes it from the (Phase-2) dispatched `=`/`eq`.
    let mut kb = load_with(SRC);
    let red = ref_term(&mut kb, "test.wi615.Tag.red");
    let red2 = ref_term(&mut kb, "test.wi615.Tag.red");
    assert_eq!(same_solutions(&mut kb, red, red2), 1, "red === red must hold with no Eq instance");

    let red3 = ref_term(&mut kb, "test.wi615.Tag.red");
    let blue = ref_term(&mut kb, "test.wi615.Tag.blue");
    assert_eq!(same_solutions(&mut kb, red3, blue), 0, "red === blue must not hold");
}
