//! WI-760: the in-language `anthill.realization.realizes_effect` rule set,
//! exercised AT THE RESOLUTION LAYER.
//!
//! `effect_gate_test` covers the same contract through the Rust accessor; this
//! pins the RULES themselves, so a regression in the anthill source is
//! attributed to the rules rather than to `realizes_effect`'s plumbing.
//!
//! The overlay ladder cannot be expressed as ordered rules: `query_view` only
//! stable-sorts facts-before-rules and the discrimination tree iterates a
//! HashMap, so candidate order is non-deterministic. Priority is therefore made
//! SEMANTIC with a negation guard — the base arm fires only when no overlay for
//! that profile exists, so the arms are mutually exclusive and exactly one
//! answer comes back regardless of enumeration order.

use super::common;

use anthill_core::eval::value::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, Var};
use anthill_core::kb::KnowledgeBase;
use common::load_kb_with;

const SRC: &str = "namespace test.wi760rules
end
";

/// `some(x)` / `none()` as goal values — `Option.some` carries a NAMED `value`.
fn opt(kb: &mut KnowledgeBase, v: Option<&str>) -> Value {
    match v {
        Some(s) => {
            let f = kb.try_resolve_symbol("anthill.prelude.Option.some").expect("some");
            let value = kb.intern("value");
            Value::Entity {
                functor: f,
                pos: std::rc::Rc::from(Vec::new()),
                named: std::rc::Rc::from(vec![(value, Value::Str(s.to_string()))]),
            }
        }
        None => {
            let f = kb.try_resolve_symbol("anthill.prelude.Option.none").expect("none");
            Value::Entity {
                functor: f,
                pos: std::rc::Rc::from(Vec::new()),
                named: std::rc::Rc::from(Vec::new()),
            }
        }
    }
}

/// Resolve `realizes_effect(lang, profile, effect, ?r)`. Returns every DEFINITE
/// answer's receiver short name — plural on purpose, so a rule set that yields
/// two answers is visible rather than silently taking the first.
fn realizes(kb: &mut KnowledgeBase, lang: &str, profile: Option<&str>, effect: &str) -> Vec<String> {
    let functor = kb
        .try_resolve_symbol("anthill.realization.realizes_effect")
        .expect("anthill.realization.realizes_effect must be loaded from stdlib");
    let r_sym = kb.intern("r");
    let vid = kb.fresh_var(r_sym);
    let prof = opt(kb, profile);
    let goal = Value::Entity {
        functor,
        pos: std::rc::Rc::from(vec![
            Value::Str(lang.to_string()),
            prof,
            Value::Str(effect.to_string()),
            Value::Var(Var::Global(vid)),
        ]),
        named: std::rc::Rc::from(Vec::new()),
    };
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let mut out: Vec<String> = sols
        .iter()
        .filter(|s| s.residual.is_empty())
        .filter_map(|s| match s.subst.resolve_as_value(vid) {
            Some(Value::Term { id, .. }) => match kb.get_term(*id) {
                Term::Ref(s) | Term::Ident(s) => Some(kb.resolve_sym(*s).to_string()),
                Term::Fn { functor, .. } => Some(kb.resolve_sym(*functor).to_string()),
                _ => None,
            },
            _ => None,
        })
        .map(|qn| qn.rsplit('.').next().unwrap_or(&qn).to_string())
        .collect();
    out.sort();
    out.dedup();
    out
}

#[test]
fn flat_form_matches_wi576_contract() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(realizes(&mut kb, "cpp", None, "Error"), vec!["ResultWrap"]);
    assert_eq!(realizes(&mut kb, "cpp", None, "Modify"), vec!["MutRef"]);
    // Outside the supported set — the answer the capability gate turns into an error.
    assert!(realizes(&mut kb, "cpp", None, "ConsoleOutput").is_empty());
    // An unknown profile still sees the language base (`key: none`).
    assert_eq!(realizes(&mut kb, "cpp", Some("cpp20-stl"), "Error"), vec!["ResultWrap"]);
}

#[test]
fn nested_form_matches_wi576_contract() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(realizes(&mut kb, "scala", Some("std"), "Modify"), vec!["ByValue"]);
    assert_eq!(realizes(&mut kb, "scala", Some("std"), "Error"), vec!["ResultWrap"]);
    assert_eq!(realizes(&mut kb, "rust", Some("std"), "Modify"), vec!["MutRef"]);
    // scala_caps declares Console; scala_std does not. The profile selects.
    assert!(realizes(&mut kb, "scala", Some("std"), "Console").is_empty());
    assert!(realizes(&mut kb, "scala", Some("std"), "Async").is_empty());
}

#[test]
fn nested_form_requires_a_profile() {
    let mut kb = load_kb_with(SRC);
    assert!(realizes(&mut kb, "rust", None, "Modify").is_empty());
    assert!(realizes(&mut kb, "scala", None, "Modify").is_empty());
    // Contrast: cpp's flat facts carry `key: none`, so the base resolves.
    assert_eq!(realizes(&mut kb, "cpp", None, "Modify"), vec!["MutRef"]);
}

/// A language declaring BOTH representations must still answer exactly once,
/// with the profile-keyed entry winning — whichever form carries it.
///
/// The pre-WI-760 reader merged flat and nested hits into ONE list before
/// applying `[profile?, none]`, so a nested profile entry outranked a flat
/// base. Guarding the base against flat overlays alone would let both arms fire
/// here and return two receivers. No stdlib language declares both, so nothing
/// else in the suite covers it.
#[test]
fn nested_profile_entry_suppresses_the_flat_base() {
    let mut kb = load_kb_with(
        r#"
        namespace test.wi760both
          import anthill.realization.{EffectMapping, LanguageMapping, ReceiverForm,
                                      ReceiverRule, TypeMapping, TraitReturnForm}
          import anthill.prelude.Option.{some, none}

          -- flat LANGUAGE BASE for "dual"
          fact EffectMapping(effect: "Modify", receiver: SharedRef,
                             lang: some("dual"), key: none)

          -- nested PROFILE entry for the same (language, effect)
          fact LanguageMapping(
            language:     "dual",
            profile:      some("p1"),
            effect_map:   [EffectMapping(effect: "Modify", receiver: MutRef)],
            receiver_map: [],
            type_map:     [],
            trait_return: ImplTrait
          )
        end
    "#,
    );

    // Under p1 the nested profile entry wins, and the base must NOT also fire.
    assert_eq!(realizes(&mut kb, "dual", Some("p1"), "Modify"), vec!["MutRef"]);
    // With no profile there is no overlay to prefer, so the flat base answers.
    assert_eq!(realizes(&mut kb, "dual", None, "Modify"), vec!["SharedRef"]);
    // An unrelated profile falls through to the base.
    assert_eq!(realizes(&mut kb, "dual", Some("p2"), "Modify"), vec!["SharedRef"]);
}

#[test]
fn does_not_leak_across_languages() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(realizes(&mut kb, "cpp", None, "Modify"), vec!["MutRef"]);
    assert!(realizes(&mut kb, "python", None, "Modify").is_empty());
}
