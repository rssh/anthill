/// WI-720: the `Fn{c,[],[]}`→`Ref(c)` alloc/discrim canon must be
/// load-order-independent for EVERY constructor, not just the four prelude ones
/// WI-719 pre-registers.
///
/// A user-defined nullary constructor built as `Fn{c,[],[]}` — e.g. the
/// empty-parens application `red()`, or (in general) any Fn-building fill/literal
/// path — in a FACT file loaded BEFORE the file that declares the constructor's
/// sort used to key its discrim slot as `Functor{red,0,0}` (the sort body had not
/// run `register_entity_of`, so `is_constructor_symbol(red)` was false and the
/// alloc canon was off), while a later-loaded rule spelling the same constructor
/// keyed `Ref(red)` — a silent discrim miss.
///
/// WI-720 marks every sort-nested `entity` as a constructor in
/// `scan_definitions` pass 1 (which defines every name across every file before
/// any body loads), so the canon is settled before any fact/rule converts. A
/// WRITTEN bare `red` already lowered to `Ref(red)` directly and so was never
/// affected; the reproducing surface is the Fn-built `red()`.

use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term, Var, Literal};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use smallvec::SmallVec;

/// Declares the sort (`enum Color`), the fact shape (`entity Paint`), and the
/// rules that match a constructor by its `red()` / `green()` spelling.
const DECL_SRC: &str = r#"
namespace demo720
  enum Color
    entity red
    entity green
  end

  entity Paint(id: String, c: Color)

  rule is_red(?id)
    :- Paint(id: ?id, c: red())

  rule is_green(?id)
    :- Paint(id: ?id, c: green())
end
"#;

/// Facts built with the empty-parens constructor application `red()`/`green()`,
/// which lowers to `Fn{c,[],[]}` (subject to the alloc canon) — the reproducing
/// form. Loaded BEFORE `DECL_SRC` in `load_facts_first`.
const FACT_SRC: &str = r#"
namespace demo720
  fact Paint(id: "P1", c: red())
  fact Paint(id: "P2", c: green())
end
"#;

fn load_kb(sources: &[&str]) -> KnowledgeBase {
    let parsed: Vec<_> = sources.iter()
        .map(|s| parse::parse(s).expect("parse source"))
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .unwrap_or_else(|errs| {
            for e in &errs { eprintln!("Load error: {e}"); }
            panic!("load failed with {} errors", errs.len());
        });
    kb
}

/// Resolve `demo720.<rule>(?id)` and return the sorted `?id` bindings. Loud: a
/// solution whose `?id` is unbound / not a String panics rather than dropping.
fn ids_of(kb: &mut KnowledgeBase, rule_qn: &str) -> Vec<String> {
    let sym = kb.try_resolve_symbol(rule_qn)
        .unwrap_or_else(|| panic!("symbol '{rule_qn}' not found"));
    let id_sym = kb.intern("id");
    let vid = kb.fresh_var(id_sym);
    let v = kb.alloc(Term::Var(Var::Global(vid)));
    let query = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(&[v]),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig { max_solutions: 20, ..ResolveConfig::default() };
    let solutions = kb.resolve(&[query], &cfg);
    let mut ids: Vec<String> = solutions.iter()
        .map(|sol| {
            let t = sol.subst.resolve_as_value(vid)
                .map(|val| val.expect_term())
                .unwrap_or_else(|| panic!("?id unbound in solution"));
            match kb.get_term(t) {
                Term::Const(Literal::String(s)) => s.clone(),
                other => panic!("?id is not a String literal: {other:?}"),
            }
        })
        .collect();
    ids.sort();
    ids
}

/// The order-dependent case: facts convert BEFORE the sort body loads.
#[test]
fn facts_before_decl_resolve_user_constructor() {
    let mut kb = load_kb(&[FACT_SRC, DECL_SRC]);
    assert_eq!(ids_of(&mut kb, "demo720.is_red"), vec!["P1"],
        "the omitted/Fn-built `red()` in a fact converted before the enum body \
         must key `Ref(red)` (WI-720), so is_red matches exactly P1");
    // Discriminating: a var-fill / mis-key would let P2's `green()` leak in.
    assert_eq!(ids_of(&mut kb, "demo720.is_green"), vec!["P2"],
        "is_green matches exactly P2");
}

/// Control: the natural order (declaration first) must resolve identically —
/// pins order-INDEPENDENCE, not merely a reordered load.
#[test]
fn decl_before_facts_resolve_user_constructor() {
    let mut kb = load_kb(&[DECL_SRC, FACT_SRC]);
    assert_eq!(ids_of(&mut kb, "demo720.is_red"), vec!["P1"]);
    assert_eq!(ids_of(&mut kb, "demo720.is_green"), vec!["P2"]);
}
