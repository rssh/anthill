//! WI-352 — load-time `flow` derivation + `provenance` builtin + `keep_modify`.
//!
//! A foldLeft-shaped `reduce` is defined and loaded; the load-time
//! flow-derivation pass must assert exactly proposal 046's `flow` facts, and
//! the `feed` rules + `provenance` builtin must then resolve `keep_modify` to
//! the kept/re-keyed places.

use std::collections::HashSet;

use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use smallvec::SmallVec;

const REDUCE: &str = r#"
namespace anthill.test.wi352
  import anthill.prelude.{List, Int}

  operation reduce(xs: List[T = Int], z: Int, f: (a: Int, t: Int) -> Int) -> Int =
    match xs
      case nil() -> z
      case cons(h, rest) -> reduce(rest, f(z, h), f)
end
"#;

fn load_reduce() -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    parsed.push(parse::parse(REDUCE).expect("parse reduce"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    // flow_derive runs in the load pipeline regardless of any typecheck errors.
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

/// Resolve `anthill.test.wi352.reduce.<suffix>` to its place symbol.
fn place(kb: &KnowledgeBase, suffix: &str) -> Symbol {
    kb.try_resolve_symbol(&format!("anthill.test.wi352.reduce.{suffix}"))
        .unwrap_or_else(|| panic!("place reduce.{suffix} should resolve"))
}

fn make_var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

/// The symbol a (Ref / nullary-Fn) place term denotes.
fn term_sym(kb: &KnowledgeBase, t: TermId) -> Option<Symbol> {
    match kb.get_term(t) {
        Term::Ref(s) => Some(*s),
        Term::Fn { functor, .. } => Some(*functor),
        _ => None,
    }
}

#[test]
fn flow_facts_for_reduce_match_046() {
    let kb = load_reduce();
    let flow_sym = kb
        .try_resolve_symbol("anthill.reflect.feed.Flow.flow")
        .expect("feed.Flow.flow functor");

    // The reduce places (to filter out other ops' facts + the entity schema).
    let reduce_places: HashSet<Symbol> = ["xs", "z", "f", "f.a", "f.t", "f.result", "result"]
        .iter()
        .map(|s| place(&kb, s))
        .collect();

    // Derived (from_sym, kind_short, to_sym) for facts over reduce's places.
    let mut actual: HashSet<(Symbol, String, Symbol)> = HashSet::new();
    for rid in kb.by_functor(flow_sym) {
        let head = kb.rule_head(rid);
        let Term::Fn { named_args, .. } = kb.get_term(head) else { continue };
        let (mut from, mut to, mut kind) = (None, None, None);
        for (f, v) in named_args {
            match kb.resolve_sym(*f) {
                "from" => from = term_sym(&kb, *v),
                "to" => to = term_sym(&kb, *v),
                "kind" => kind = term_sym(&kb, *v).map(|s| kb.resolve_sym(s).to_string()),
                _ => {}
            }
        }
        if let (Some(from), Some(to), Some(kind)) = (from, to, kind) {
            if reduce_places.contains(&from) && reduce_places.contains(&to) {
                actual.insert((from, kind, to));
            }
        }
    }

    let expected: HashSet<(Symbol, String, Symbol)> = [
        (place(&kb, "z"), "direct", place(&kb, "f.a")),
        (place(&kb, "xs"), "element_of", place(&kb, "f.t")),
        (place(&kb, "f.result"), "direct", place(&kb, "z")),
        (place(&kb, "z"), "direct", place(&kb, "result")),
        (place(&kb, "f.result"), "direct", place(&kb, "result")),
    ]
    .into_iter()
    .map(|(a, k, b)| (a, k.to_string(), b))
    .collect();

    assert_eq!(actual, expected, "derived flow facts must match 046 §Derived-from-a-body");
}

/// Whether `keep_modify(place, into)` holds — a genuine (residual-free)
/// resolution through the `feed` rules + `provenance` builtin. Queried in
/// *checking* mode (both args ground): the resolver delays a rule whose body
/// has a builtin with an unbound output (the `provenance(?r, …)` constraint),
/// so the enumerate form `keep_modify(p, ?r)` is left residual — the keep/drop
/// *verdict* is what matters and is what a consumer (WI-353) checks. The
/// keep/drop logic itself (`origin`+`provenance` over the derived `flow`) also
/// enumerates correctly; this asserts it via the public rule.
fn keep_modify_holds(kb: &mut KnowledgeBase, place_sym: Symbol, into: Symbol) -> bool {
    let km = kb
        .try_resolve_symbol("anthill.reflect.feed.keep_modify")
        .expect("keep_modify");
    let p_term = kb.alloc(Term::Ref(place_sym));
    let into_term = kb.alloc(Term::Ref(into));
    let goal = kb.alloc(Term::Fn {
        functor: km,
        pos_args: SmallVec::from_slice(&[p_term, into_term]),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .any(|s| s.residual.is_empty())
}

#[test]
fn keep_modify_for_reduce_callback_params() {
    let mut kb = load_reduce();
    let (fa, ft) = (place(&kb, "f.a"), place(&kb, "f.t"));
    let (z, xs, result) = (place(&kb, "z"), place(&kb, "xs"), place(&kb, "result"));

    // Modifying the accumulator param `f.a` surfaces on the seed `z` (an input)
    // and on `result` (its loop-carried fresh output escapes), and NOT on `xs`.
    assert!(keep_modify_holds(&mut kb, fa, z), "f.a modify must keep on z");
    assert!(keep_modify_holds(&mut kb, fa, result), "f.a modify must keep on result");
    assert!(!keep_modify_holds(&mut kb, fa, xs), "f.a modify must NOT surface on xs");

    // Modifying the element param `f.t` surfaces on `xs` (the list it came from)
    // only — not on the seed `z` or the `result`.
    assert!(keep_modify_holds(&mut kb, ft, xs), "f.t modify must keep on xs");
    assert!(!keep_modify_holds(&mut kb, ft, z), "f.t modify must NOT surface on z");
    assert!(!keep_modify_holds(&mut kb, ft, result), "f.t modify must NOT surface on result");
}

#[test]
fn provenance_builtin_reads_symbol_kind() {
    let mut kb = load_reduce();
    let prov = kb
        .try_resolve_symbol("anthill.reflect.feed.provenance")
        .expect("provenance builtin");
    let query = |kb: &mut KnowledgeBase, p: Symbol| -> Option<String> {
        let p_term = kb.alloc(Term::Ref(p));
        let v = make_var(kb, "p");
        let goal = kb.alloc(Term::Fn {
            functor: prov,
            pos_args: SmallVec::from_slice(&[p_term, v]),
            named_args: SmallVec::new(),
        });
        let sols = kb.resolve(&[goal], &ResolveConfig::default());
        let s = sols.first()?;
        let reified = kb.reify(v, &s.subst);
        term_sym(kb, reified).map(|s| kb.resolve_sym(s).to_string())
    };
    let (z, result, f_result, f_a) = (
        place(&kb, "z"),
        place(&kb, "result"),
        place(&kb, "f.result"),
        place(&kb, "f.a"),
    );
    assert_eq!(query(&mut kb, z).as_deref(), Some("input"));
    assert_eq!(query(&mut kb, result).as_deref(), Some("op_result"));
    assert_eq!(query(&mut kb, f_result).as_deref(), Some("fresh_output"));
    // A callback param is a flow target — no provenance, query fails.
    assert_eq!(query(&mut kb, f_a), None);
}
