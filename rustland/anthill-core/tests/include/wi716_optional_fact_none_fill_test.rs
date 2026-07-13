//! WI-716 — a GROUND FACT stores an absent OPTIONAL field as `none()`, not an
//! unbound fresh var.
//!
//! The loader's partial-named-arg expansion fills every absent named slot so
//! the discrimination tree indexes a functor's facts/patterns uniformly. The
//! FILLER differs by role: for a fact VALUE an absent `Option[..]` field means
//! `none()` (value semantics); for a query/rule PATTERN it means "matches
//! anything" (a fresh var). Before the fix both used a var, so a fact that
//! omitted an optional field read as `forall v. E(field: v)` and spuriously
//! unified a `some(?)` query — an item with no value matched as if it had one.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use smallvec::SmallVec;

fn load_with(extra: &str) -> KnowledgeBase {
    let files = crate::common::collect_anthill_files(&crate::common::stdlib_dir());
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).unwrap();
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).unwrap_or_else(|e| panic!("load: {e:?}"));
    kb
}

fn fresh(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let s = kb.intern(name);
    let v = kb.fresh_var(s);
    kb.alloc(Term::Var(Var::Global(v)))
}

fn call(kb: &mut KnowledgeBase, qn: &str, args: &[TermId]) -> TermId {
    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not in KB"));
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

// `note` is optional; A provides it, B omits it. `has_note` matches the
// `some(?)` shape; `any_thing` matches any Thing regardless of `note`.
const SRC: &str = r#"
    namespace test.wi716
      import anthill.prelude.Option

      entity Thing(id: String, note: Option[String])

      rule has_note(?id, ?n) :- Thing(id: ?id, note: some(?n))
      rule any_thing(?id)    :- Thing(id: ?id)

      fact Thing(id: "A", note: some("hello"))
      fact Thing(id: "B")
    end
"#;

/// Core WI-716 acceptance: `Thing(id: "B")` omits `note`, so its stored `note`
/// is `none()`, NOT an unbound var — a rule matching `note: some(?n)` finds
/// ONLY "A". Before the fix B's var-filled `note` unified `some(?n)` and this
/// returned TWO solutions (B with `?n` unbound), the soundness bug.
#[test]
fn omitted_optional_fact_does_not_match_some_pattern() {
    let mut kb = load_with(SRC);
    let id = fresh(&mut kb, "id");
    let n = fresh(&mut kb, "n");
    let goal = call(&mut kb, "test.wi716.has_note", &[id, n]);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        sols.len(),
        1,
        "only A has a note; B omits it (stored none()), so has_note must NOT \
         match B via some(?n). Got {} solutions (2 == the WI-716 bug).",
        sols.len()
    );
}

/// The dual: the var-fill for PATTERNS is preserved. A bare `Thing(id: ?)`
/// pattern still matches BOTH A and B even though B's `note` is now `none()`
/// (a `none()` fact slot unifies the pattern's fresh `note` var). So the fix
/// does not over-restrict a query that simply omits the optional field.
#[test]
fn omitted_field_pattern_still_matches_all() {
    let mut kb = load_with(SRC);
    let id = fresh(&mut kb, "id");
    let goal = call(&mut kb, "test.wi716.any_thing", &[id]);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        sols.len(),
        2,
        "a pattern omitting `note` must still match both A and B — the var-fill \
         is correct for patterns. Got {} solutions.",
        sols.len()
    );
}

// ── Value-position extensions (post code-review) ────────────────────────────
// none()-fill keys on VALUE POSITION, not "is a fact": it also covers an
// entity-DERIVING rule head, and it must NOT reach a reflect `Term`-typed
// field's quoted content (a pattern).

const SRC_DERIVED: &str = r#"
    namespace test.wi716d
      import anthill.prelude.Option
      entity Thing(id: String, note: Option[String])

      fact src("C")
      rule Thing(id: ?id) :- src(?id)                 -- DERIVES Thing; note omitted
      rule has_note(?id, ?n) :- Thing(id: ?id, note: some(?n))
    end
"#;

/// An entity-DERIVING rule head is a value the rule PRODUCES, so an omitted
/// optional in the head must be `none()`, not a `forall v` var — a `Thing`
/// derived with no note must NOT match `some(?n)`. (The same soundness bug the
/// fact fix closes, reached through a rule head; the fact-only fix left it open.)
#[test]
fn entity_deriving_rule_head_stores_none_for_omitted_optional() {
    let mut kb = load_with(SRC_DERIVED);
    let id = fresh(&mut kb, "id");
    let n = fresh(&mut kb, "n");
    let goal = call(&mut kb, "test.wi716d.has_note", &[id, n]);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        sols.len(),
        0,
        "the derived `Thing(id: ?id)` omits `note`, so its note is none() — \
         has_note (matching some(?n)) must find nothing. Got {}.",
        sols.len()
    );
}

const SRC_REFLECT: &str = r#"
    namespace test.wi716r
      import anthill.prelude.Option
      import anthill.reflect.Term
      entity Thing(id: String, note: Option[String])
      entity Holder(pat: Term)

      rule get_pat(?p) :- Holder(pat: ?p)
      fact Holder(pat: Thing(id: "z"))                -- Thing is a QUOTED pattern
    end
"#;

/// A reflect `Term`-typed field holds a quoted PATTERN, not a value: an omitted
/// optional inside it must stay a VAR (so the pattern matches anything), NOT get
/// defaulted to `none()` by the enclosing fact's value context. Otherwise a
/// stored `FactHolds(pattern: E(id: ?x))`-style query would silently match only
/// `none()`-valued facts. This pins the stored pattern's `note` slot as a
/// `Term::Var` — the regression the reflect-`Term` guard prevents.
#[test]
fn reflect_term_field_keeps_var_for_omitted_optional() {
    let mut kb = load_with(SRC_REFLECT);
    let p = fresh(&mut kb, "p");
    let p_vid = match kb.get_term(p) {
        Term::Var(Var::Global(v)) => *v,
        other => panic!("expected a Global var, got {other:?}"),
    };
    let goal = call(&mut kb, "test.wi716r.get_pat", &[p]);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(sols.len(), 1, "get_pat must find the one Holder");

    // Chase ?p's binding to the stored quoted pattern term (skip var→var links).
    let mut cur = p_vid;
    let pat = loop {
        let bound = sols[0]
            .subst
            .iter_terms()
            .find(|(v, _)| *v == cur)
            .map(|(_, t)| t)
            .expect("?p (or its chain) must be bound to the stored pattern");
        match kb.get_term(bound) {
            Term::Var(Var::Global(v)) => cur = *v,
            _ => break bound,
        }
    };
    // The bound pattern is `Thing(id: "z", note: <fill>)`; the omitted `note`
    // must be a var (pattern), not `Ref(none)` (value).
    match kb.get_term(pat) {
        Term::Fn { named_args, .. } => {
            let named_args = named_args.clone();
            assert!(
                named_args
                    .iter()
                    .any(|(_, t)| matches!(kb.get_term(*t), Term::Var(_))),
                "the quoted pattern's omitted optional must stay a var, not none(); \
                 got named args {named_args:?}"
            );
        }
        other => panic!("expected the quoted `Thing(...)` Fn, got {other:?}"),
    }
}
