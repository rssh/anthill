//! WI-718 — the prelude nullary constructor `none` (and `some`/`nil`/`cons`) is
//! a CONSTRUCTOR from `register_prelude`, before any `.anthill` file loads, so the
//! `Fn{c,[],[]}`→`Ref(c)` alloc/discrim canon is settled at the first assert.
//!
//! Why it matters (WI-697): a nullary ctor keys the discrim tree as `Functor(c)`
//! BEFORE its sort registers it and canonicalizes to `Ref(c)` AFTER. If a ground
//! fact carrying a bare/omitted `none` converts BEFORE `option.anthill` runs
//! `register_entity_of(none)`, it keys `Fn{none,0,0}`, while a `none()` pattern
//! converted afterward keys `Ref(none)` — a SILENT discrim miss (`resolve` trusts
//! the tree as complete). WI-716 sharpened the hazard: an omitted optional field
//! is now a concrete `none()` fill (was a spelling-independent var), so its stored
//! key is subject to the split.
//!
//! The fix pre-registers the four prelude constructors at bootstrap (WI-719,
//! `register_prelude_constructor`) and marks every sort-nested entity at scan
//! pass 1 (WI-720, `mark_constructor_symbol`), so the flag — and the canon — are
//! constant from the first assert, load-order-independently.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use smallvec::SmallVec;

/// Direct invariant (pins WI-719). Right after `register_prelude` — with NO
/// `.anthill` file loaded — each prelude constructor must already answer
/// `is_constructor_symbol` true. This is the guarantee WI-720's scan-time marking
/// cannot provide for a `register_prelude`-only setup (it never scans the stdlib
/// sort bodies), so it isolates WI-719's pre-registration: reverting the
/// `register_prelude_constructor(none/some/nil/cons, …)` calls fails this test.
#[test]
fn register_prelude_marks_prelude_constructors() {
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    for qn in [
        "anthill.prelude.Option.none",
        "anthill.prelude.Option.some",
        "anthill.prelude.List.nil",
        "anthill.prelude.List.cons",
    ] {
        let s = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("{qn} must be DEFINED by register_prelude"));
        assert!(
            kb.is_constructor_symbol(s),
            "{qn} must be a CONSTRUCTOR right after register_prelude (WI-718/WI-719), \
             before any .anthill file loads — else a fact converted pre-option.anthill \
             keys Fn{{c,0,0}} while a later none() pattern keys Ref(c): a silent discrim miss"
        );
    }
}

// ── Behavioral acceptance: the load-order silent-miss ───────────────────────

// `note` is optional; A provides `some("hi")`, B omits it (→ WI-716 none() fill).
// Rules match by the `none()` / `some(?)` structure. Loaded via `load_facts_first`
// with THIS source ahead of `option.anthill`, so its facts convert before the
// Option sort body would register `none` — the WI-697 pre-registration order.
const PROJECT_SRC: &str = r#"
    namespace test.wi718
      import anthill.prelude.Option

      entity Thing(id: String, note: Option[String])

      rule no_note(?id)      :- Thing(id: ?id, note: none())
      rule has_note(?id, ?n) :- Thing(id: ?id, note: some(?n))

      fact Thing(id: "A", note: some("hi"))
      fact Thing(id: "B")
    end
"#;

/// Load the full stdlib but with `PROJECT_SRC` ordered FIRST — so its `fact
/// Thing(id: "B")` (omitted `note` → none() fill) converts before `option.anthill`
/// in body-load order, reproducing the CLI `-p project -p stdlib` hazard WI-719
/// documents. Pass 1 defines every name across every file first, so the
/// project's `Option`/`some`/`none` still resolve.
fn load_facts_first() -> KnowledgeBase {
    let stdlib = crate::common::collect_anthill_files(&crate::common::stdlib_dir());
    let mut parsed = vec![parse::parse(PROJECT_SRC).expect("parse project src")];
    for p in &stdlib {
        let src = std::fs::read_to_string(p).unwrap();
        parsed.push(parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display())));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).unwrap_or_else(|e| panic!("load: {e:?}"));
    kb
}

/// Query `qn(?id, <arity-1 more fresh vars>)` and return the sorted String
/// bindings of the FIRST arg (`?id`). Loud: an unbound / non-String `?id` panics
/// rather than silently dropping — so the assertions test the exact matched row,
/// not just cardinality.
fn ids_of(kb: &mut KnowledgeBase, qn: &str, arity: usize) -> Vec<String> {
    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not in KB"));
    let id_sym = kb.intern("id");
    let id_vid = kb.fresh_var(id_sym);
    let mut args = vec![kb.alloc(Term::Var(Var::Global(id_vid)))];
    for _ in 1..arity {
        let v = kb.fresh_var(id_sym);
        args.push(kb.alloc(Term::Var(Var::Global(v))));
    }
    let goal = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(&args),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let mut ids: Vec<String> = sols
        .iter()
        .map(|sol| {
            let t = sol
                .subst
                .resolve_as_value(id_vid)
                .map(|val| val.expect_term())
                .unwrap_or_else(|| panic!("?id unbound in a {qn} solution"));
            match kb.get_term(t) {
                Term::Const(Literal::String(s)) => s.clone(),
                other => panic!("?id is not a String literal: {other:?}"),
            }
        })
        .collect();
    ids.sort();
    ids
}

/// WI-718 core acceptance: the omitted-optional fact `Thing(id: "B")` — asserted
/// while `option.anthill` has not yet loaded — IS found by a `none()` query. Under
/// the WI-697 bug the fact keyed `Fn{none}` and the query `Ref(none)`, so this
/// returned 0 (a silent miss); the fix makes both key `Ref(none)`.
#[test]
fn omitted_optional_fact_before_option_anthill_found_by_none_query() {
    let mut kb = load_facts_first();
    assert_eq!(
        ids_of(&mut kb, "test.wi718.no_note", 1),
        vec!["B"],
        "the omitted-optional fact Thing(id: \"B\") (note = none()), converted before \
         option.anthill, must be FOUND by a none() query — and match exactly B, not A \
         (whose note is some). An empty result == the WI-697/WI-718 silent miss."
    );
}

/// Dual (soundness, WI-716): the same omitted-optional fact must NOT match a
/// `some(?)` query — only A has a value. Pins that the none() fill is a genuine
/// value, not a wildcard, even under the pre-registration load order.
#[test]
fn omitted_optional_fact_before_option_anthill_not_matched_by_some_query() {
    let mut kb = load_facts_first();
    assert_eq!(
        ids_of(&mut kb, "test.wi718.has_note", 2),
        vec!["A"],
        "only A carries a note; B omits it (none()), so has_note (some(?n)) must match \
         exactly A — B must be absent (its none() fill is a value, not a some wildcard)."
    );
}
