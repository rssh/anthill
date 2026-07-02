//! WI-300 — rule-body `requires(X)` requirement guards (guard tier).
//!
//! A rule-body `requires(Eq[T])` desugars (converter) to `find_dictionary(Eq[T])`,
//! which the typer sweep rewrites to `find_dictionary(Eq, Eq.eq, ?x, ?y)` using the
//! body's `eq(?x, ?y)` call as the witness whose carrier types decide the instance.
//! At resolution the guard checks `provides Eq` at the current binding:
//!   * ground carrier WITH a provider     → the rule fires;
//!   * ground carrier with NO provider     → the rule does not fire (even though the
//!     structural `eq` would succeed — the guard is what blocks it);
//!   * under-determined carrier            → SUSPEND (no definite solution).
//! Body `eq` is `BuiltinTag::Eq` (structural), so the fire/don't-fire/suspend outcome
//! is governed ENTIRELY by the `requires` guard.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::parse;
use smallvec::SmallVec;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let parsed_extra = parse::parse(extra).unwrap_or_else(|e| panic!("parse extra: {e:?}"));
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

/// Like [`load_with`] but returns the load errors instead of panicking.
fn try_load_with(extra: &str) -> Result<KnowledgeBase, Vec<String>> {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let parsed_extra = parse::parse(extra).unwrap_or_else(|e| panic!("parse extra: {e:?}"));
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
        Ok(_) => Ok(kb),
        Err(errs) => Err(errs.iter().map(|e| e.to_string()).collect()),
    }
}

const SRC: &str = r#"
    namespace test.wi300
      import anthill.prelude.Int64
      -- A carrier that DECLARES it provides Eq …
      sort Witheq
        entity we(v: Int64)
      end
      -- … and one that does not.
      sort Noeq
        entity ne(v: Int64)
      end
      fact Eq[T = Witheq]

      -- Fires only when the argument type provides Eq; the inner `eq` is the
      -- structural builtin, so the guard alone decides fire / don't-fire.
      rule related(?x, ?y) :- requires(Eq[T]), eq(?x, ?y)
    end
"#;

/// `we(v: n)` / `ne(v: n)` entity term.
fn mk(kb: &mut KnowledgeBase, ctor: &str, n: i64) -> TermId {
    let functor = kb
        .try_resolve_symbol(ctor)
        .unwrap_or_else(|| panic!("ctor {ctor} not in KB"));
    let v = kb.intern("v");
    let nv = kb.alloc(Term::Const(Literal::Int(n)));
    kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(v, nv)]),
    })
}

/// An unbound global query variable as a term.
fn fresh(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

fn related_solutions(kb: &mut KnowledgeBase, a: TermId, b: TermId) -> Vec<anthill_core::kb::resolve::Solution> {
    let related = kb
        .try_resolve_symbol("test.wi300.related")
        .expect("test.wi300.related not in KB");
    let goal = kb.alloc(Term::Fn {
        functor: related,
        pos_args: SmallVec::from_slice(&[a, b]),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[goal], &ResolveConfig::default())
}

fn definite_count(kb: &mut KnowledgeBase, a: TermId, b: TermId) -> usize {
    related_solutions(kb, a, b)
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

#[test]
fn guard_fires_when_carrier_provides_eq() {
    let mut kb = load_with(SRC);
    let a = mk(&mut kb, "test.wi300.Witheq.we", 7);
    let b = mk(&mut kb, "test.wi300.Witheq.we", 7);
    assert_eq!(
        definite_count(&mut kb, a, b),
        1,
        "Witheq provides Eq and we(7) == we(7): the rule must fire"
    );
}

#[test]
fn guard_fires_but_eq_fails_for_unequal_values() {
    let mut kb = load_with(SRC);
    let a = mk(&mut kb, "test.wi300.Witheq.we", 7);
    let b = mk(&mut kb, "test.wi300.Witheq.we", 8);
    assert_eq!(
        definite_count(&mut kb, a, b),
        0,
        "guard fires (Witheq provides Eq) but we(7) != we(8): no solution"
    );
}

#[test]
fn guard_blocks_when_carrier_has_no_provider() {
    // The distinguishing case: `eq(ne(7), ne(7))` is structurally TRUE, but Noeq
    // declares no `fact Eq[T = Noeq]`, so the guard does not fire — the rule yields
    // nothing. Without the guard (plain `eq`) this would be a solution.
    let mut kb = load_with(SRC);
    let a = mk(&mut kb, "test.wi300.Noeq.ne", 7);
    let b = mk(&mut kb, "test.wi300.Noeq.ne", 7);
    assert_eq!(
        definite_count(&mut kb, a, b),
        0,
        "Noeq provides no Eq: the guard must block the rule despite eq succeeding"
    );
}

#[test]
fn guard_suspends_on_under_determined_carrier() {
    // Both arguments unbound → the carrier type is under-determined → the guard
    // SUSPENDS (never NAF-decides). No DEFINITE solution is produced.
    let mut kb = load_with(SRC);
    let a = fresh(&mut kb, "a");
    let b = fresh(&mut kb, "b");
    assert_eq!(
        definite_count(&mut kb, a, b),
        0,
        "under-determined carrier must suspend, yielding no definite solution"
    );
}

#[test]
fn ungroundable_requires_is_a_loud_error() {
    // `requires(Eq[T])` with NO body call to any of Eq's operations cannot be
    // grounded — the guard would never be decidable. That is reported as a hard
    // error (loud, not a silent skip), not left to fail quietly at resolution.
    let src = r#"
        namespace test.wi300.bad
          import anthill.prelude.Int64
          sort Thing
            entity thing(v: Int64)
          end
          rule solo(?x) :- requires(Eq[T])
        end
    "#;
    let errs = try_load_with(src)
        .err()
        .expect("ungroundable requires must fail to load");
    assert!(
        errs.iter().any(|e| e.contains("ground the requirement")),
        "expected a grounding error, got: {errs:?}"
    );
}

#[test]
fn two_requires_on_same_spec_is_a_loud_error() {
    // The guard tier strips the spec's type-args, so it cannot attribute which
    // type-parameter each `requires` names. Two `requires` on the SAME spec base
    // in one rule would both check the same witness/carrier — an unsound silent
    // discharge. It must fail loudly instead (attribution is Tier B).
    let src = r#"
        namespace test.wi300.dup
          import anthill.prelude.Int64
          sort Thing
            entity thing(v: Int64)
          end
          fact Eq[T = Thing]
          rule twin(?a, ?b, ?c) :- requires(Eq[A]), requires(Eq[B]), eq(?a, ?b), eq(?b, ?c)
        end
    "#;
    let errs = try_load_with(src)
        .err()
        .expect("two requires on the same spec must fail to load");
    assert!(
        errs.iter().any(|e| e.contains("at most one `requires` on spec")),
        "expected a same-spec duplication error, got: {errs:?}"
    );
}
