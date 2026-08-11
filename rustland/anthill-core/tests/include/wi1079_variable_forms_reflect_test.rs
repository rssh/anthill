//! WI-1079 — the ENGINE's two logical-variable forms now have a reflect representation, and
//! they are DIFFERENT forms rather than one with a flag.
//!
//! Before this ticket both `Term::Var(Var::Global)` and `Term::Var(Var::Rigid)` classified as
//! `TypeExtractor::Error`, whose own doc calls its payload "the offending input". A skolem is
//! a perfectly well-formed type — an opaque constant, `Var::Rigid`'s doc names it "Skolem
//! constant … or eigenvariable" — so `extract` was total in the letter and wrong in the
//! spirit. The scope question was settled by the user rather than by a reachability count:
//! the reflect layer's job IS to represent the language's types, so a form it cannot express
//! is a defect whether or not today's corpus reaches it.
//!
//! ## THREE THINGS ARE NOW DISTINGUISHABLE, and each was conflated with the others before
//!
//! | form | carrier | means |
//! |---|---|---|
//! | `TypeVar(name)` | `make_type_var` | a PLACEHOLDER — a type the extractor could not name (`?param` for an un-annotated lambda binder, `?_` for an un-lowerable carrier) |
//! | `FlexVar(name, id)` | `Term::Var(Var::Global)` | an INSTANTIATED forall — unifies with anything |
//! | `Skolem(name, id)` | `Term::Var(Var::Rigid)` | an OPENED existential or a body-check rigid — unifies with nothing but itself |
//!
//! WHY NOT A `rigid: Bool` FIELD ON `TypeVar`, which was the smaller option: `TypeVar` is not
//! the variable. Measured at its producers — it is minted for `?param` and `?_`, never for an
//! engine variable, and a DECLARED type parameter reads as `SortRef(T)`. A flag would have
//! given one entity two questions, which is the defect class this repo names most often.
//!
//! ## `id` IS THE IDENTITY AND `name` IS NOT
//!
//! Two skolems minted for one parameter name are different types that render alike (`?E` vs
//! `?E` — the trap WI-1063 records as "these render alike but are not the same type"). Every
//! row below that builds two variables builds them from the SAME name, so no assertion here
//! can be satisfied by rendering.
//!
//! ## What fails when this is backed out — DRIVEN, whole `wi_tests` binary
//!
//! Deleting the `ViewHead::Var` arm in `type_head` (both carriers back to `Error`) costs
//! **15** rows, and only 2 of them are in this file — which is the useful part of the
//! measurement:
//!
//! | | |
//! |---|---|
//! | this file | [`a_rigid_reifies_as_a_skolem_and_a_flex_var_as_a_flex_var`], [`two_skolems_of_one_name_are_two_types`] |
//! | the rewritten pin | `kb::typing::wi963_…::a_bare_logic_var_is_its_own_type_form_not_a_placeholder`, which held the OLD verdict ("a bare `Var` … is not in the type vocabulary at all") |
//! | `value_contains_rigid`'s callers | WI-1013 (×3), WI-219, WI-732 (×2), WI-759 (×2), WI-946 (×5) |
//!
//! THAT LAST GROUP IS THE SIMPLIFICATION'S CONTROL, and it is why the deletion is safe rather
//! than merely tidy. `value_contains_rigid` used to open with two hand-rolled carrier arms
//! testing `Var::Rigid` before delegating the rest to `extract_type` — they existed because
//! `extract_type` could not answer. They are gone and the `Skolem` arm answers instead; those
//! twelve rows are what proves the new arm really carries the load the hand-rolled ones did,
//! since they fail the moment it stops firing.
//!
//! The two remaining rows here ([`the_placeholder_type_var_is_neither_of_them`],
//! [`a_de_bruijn_var_is_not_one_of_these_forms`]) pass under that back-out by design, and say
//! so at their sites: they fix the BOUNDARY of the claim rather than measuring the change.
//!
//! ## THE DEFECT WAS LIVE, and by a wide margin — counted, not argued
//!
//! The ticket asked whether a skolem ever REACHES `extract` today, expecting a negative that
//! would be "hard to prove". It is emphatically positive. Counted at `type_head`'s `Error`
//! bail ON MAIN, a bare stdlib load classifies a logical variable as a malformed term **4911
//! times** — 3503 rigid, 1408 flex — and the `anthill-todo` tier adds more (6414 flex). Every
//! one of those was a well-formed type reported through the variant whose payload its own doc
//! calls "the offending input".
//!
//! So this is not the WI-1061/WI-1063 situation where the corpus reaches the new code zero
//! times and a test file is the only coverage. The population is enormous and always was —
//! which is also why the suite catches the back-out in 15 places rather than in this file
//! alone.
//!
//! (Two instrument traps, both hit while measuring this, both recorded because the numbers
//! would otherwise be wrong: a census over `cargo test` needs `--nocapture`, since libtest
//! shows only FAILING tests' output; and a per-tier loop that runs the CLI from the wrong
//! working directory reports a clean, plausible ZERO for every tier. The suite's millions of
//! hits were the positive control that exposed the second.)
//!
//! ## The criterion this closes, stated on WI-391 before the defect existed
//!
//! "No type is ever represented as an opaque value — every type value's backing term must
//! classify into exactly one STRUCTURAL `TypeExtractor` variant; `TypeExtractor.Error` is
//! reserved for malformed USER input, never a system-minted shape" (user, 2026-06-11). A
//! skolem is system-minted by definition — `rigidify_op_type_params` mints it — so reporting
//! one as `Error` broke that rule directly.
//!
//! REFERENCE: WI-1078 (the same conflation one level up, in the rule rather than the data
//! model), WI-1063 (the ρ this represents, and the render-alike trap), WI-1083 (`PolyType` —
//! the BOUND variable of a `forall`, the third form, which needs a binder and is not here),
//! WI-963 (`make_type_var`'s own three facts), `docs/kernel-language.md` §8.1.

use anthill_core::eval::builtins::register_standard_builtins;
use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::term::{Term, Var};
use anthill_core::kb::KnowledgeBase;

use crate::common::load_kb_with;

fn entity_functor(v: &Value) -> Option<Symbol> {
    match v {
        Value::Entity { functor, .. } => Some(*functor),
        _ => None,
    }
}

fn field<'a>(v: &'a Value, key: Symbol) -> Option<&'a Value> {
    match v {
        Value::Entity { named, .. } => named.iter().find(|(k, _)| *k == key).map(|(_, x)| x),
        _ => None,
    }
}

/// Reify one variable term through the REAL builtin — `anthill.reflect.extract` over
/// `Interpreter::call` — and return `(variant symbol, name, id)`.
///
/// Driven through eval rather than through the Rust `extract_type` on purpose: the ticket's
/// deliverable is that a PROGRAM can `case` over these forms, and a Rust-level assertion would
/// pass while the entity the stdlib declares was still missing or misnamed.
fn extract_var(kb: KnowledgeBase, v: Var) -> (Symbol, String, i64) {
    let mut kb = kb;
    let ty = kb.alloc(Term::Var(v));
    let name_key = kb.intern("name");
    let id_key = kb.intern("id");
    let mut interp = Interpreter::new(kb);
    register_standard_builtins(&mut interp).expect("register builtins");
    let r = interp
        .call("anthill.reflect.extract", &[Value::term(ty)])
        .expect("extract should evaluate");
    let functor = entity_functor(&r).unwrap_or_else(|| panic!("extract returned {r:?}"));
    let name = match field(&r, name_key) {
        Some(Value::Term { id, .. }) => match interp.kb().get_term(*id) {
            Term::Ref(s) => interp.kb().local_name_of(*s).to_owned(),
            other => panic!("`name` should be a Ref, got {other:?}"),
        },
        other => panic!("`name` field missing: {other:?}"),
    };
    let id = match field(&r, id_key) {
        Some(Value::Int(n)) => *n,
        other => panic!("`id` field missing or not an Int: {other:?}"),
    };
    (functor, name, id)
}

fn ctor(kb: &KnowledgeBase, short: &str) -> Symbol {
    kb.try_resolve_symbol(&format!("anthill.prelude.TypeExtractor.{short}"))
        .unwrap_or_else(|| panic!("TypeExtractor.{short} must be declared in the stdlib"))
}

/// THE HEADLINE, and the ticket's own measurement: a rigid reifies as `Skolem` and a flexible
/// one as `FlexVar`. Both used to be `Error`.
///
/// Built from ONE name, so the two verdicts cannot come from the rendering — what separates
/// them is the `Var` kind alone.
///
/// CONTROL: on main both calls return `Error` (with the offending term as its `term` field),
/// so both assertions fail.
#[test]
fn a_rigid_reifies_as_a_skolem_and_a_flex_var_as_a_flex_var() {
    let mut kb = load_kb_with("");
    let name = kb.intern("E");
    let rigid = Var::Rigid(kb.fresh_var(name));
    let flex = Var::Global(kb.fresh_var(name));
    let skolem_ctor = ctor(&kb, "Skolem");
    let flex_ctor = ctor(&kb, "FlexVar");

    let (f, n, _) = extract_var(kb, rigid);
    assert_eq!(f, skolem_ctor, "a `Var::Rigid` is an OPAQUE CONSTANT");
    assert_eq!(n, "E", "and it carries the name a diagnostic prints");

    let kb2 = load_kb_with("");
    let (f2, n2, _) = extract_var(kb2, flex);
    assert_eq!(f2, flex_ctor, "a `Var::Global` is a UNIFIABLE HOLE");
    assert_eq!(n2, "E", "same name, different form — the kind is what decides");
}

/// IDENTITY IS THE `id`, NOT THE NAME. Two skolems minted for one parameter name are
/// different types; a consumer that compared names would read them as one, which is exactly
/// the confusion this ticket exists to end.
///
/// CONTROL: the two ids are asserted DIFFERENT while the two names are asserted EQUAL, so a
/// representation that dropped `id` (or filled it from the name symbol) fails the first
/// assertion, and one that accidentally made the names differ fails the second.
#[test]
fn two_skolems_of_one_name_are_two_types() {
    let mut kb = load_kb_with("");
    let name = kb.intern("E");
    let a = Var::Rigid(kb.fresh_var(name));
    let b = Var::Rigid(kb.fresh_var(name));

    let kb2 = load_kb_with("");
    let (_, na, ia) = extract_var(kb, a);
    let (_, nb, ib) = extract_var(kb2, b);

    assert_eq!(na, nb, "they render alike — that is the trap");
    assert_ne!(ia, ib, "and they are NOT the same type; `id` is what says so");
}

/// THE PLACEHOLDER IS STILL A THIRD THING. `make_type_var` mints `TypeVar`, which carries a
/// name and NO id — it is not a variable, it is a type the extractor could not name. This row
/// is what says the ticket added variants rather than repurposing the one that was there.
///
/// CONTROL: passes on main too (it is the pre-existing behaviour), and it is here so the rows
/// above cannot be satisfied by a change that collapsed the three forms into one. It fails if
/// `TypeVar` is given an `id` field or routed to either new variant.
#[test]
fn the_placeholder_type_var_is_neither_of_them() {
    let mut kb = load_kb_with("");
    let name = kb.intern("?param");
    let tv = kb.make_type_var(name);
    let type_var_ctor = ctor(&kb, "TypeVar");
    let id_key = kb.intern("id");

    let mut interp = Interpreter::new(kb);
    register_standard_builtins(&mut interp).expect("register builtins");
    let r = interp
        .call("anthill.reflect.extract", &[Value::term(tv)])
        .expect("extract should evaluate");

    assert_eq!(
        entity_functor(&r),
        Some(type_var_ctor),
        "an un-nameable type stays the PLACEHOLDER form, got {r:?}",
    );
    assert!(
        field(&r, id_key).is_none(),
        "and it carries no identity — a placeholder is not a variable: {r:?}",
    );
}

/// A DE BRUIJN VAR IS STILL `Error`, and that is a decision rather than an omission: a
/// DeBruijn index is a RULE's binder, opened to a fresh `Global` before anything type-checks,
/// so a type carrying one is a rule term being read as a type. The BOUND variable of a
/// `forall` is a different thing again and arrives with `PolyType` (WI-1083).
///
/// CONTROL: passes on main (everything was `Error` there). It is here to pin the boundary of
/// what this ticket claims — without it, "we represent the variable forms" would read as
/// covering a form nothing yet produces in type position.
#[test]
fn a_de_bruijn_var_is_not_one_of_these_forms() {
    let mut kb = load_kb_with("");
    let ty = kb.alloc(Term::Var(Var::DeBruijn(0)));
    let error_ctor = ctor(&kb, "Error");

    let mut interp = Interpreter::new(kb);
    register_standard_builtins(&mut interp).expect("register builtins");
    let r = interp
        .call("anthill.reflect.extract", &[Value::term(ty)])
        .expect("extract should evaluate");

    assert_eq!(
        entity_functor(&r),
        Some(error_ctor),
        "a rule binder in type position is not a type form: {r:?}",
    );
}
