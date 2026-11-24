//! WI-20261113-5CZ9F — proposal 074 stage 4: A NAMED PROVIDER FIXES ITS PARAMETERS
//! (`docs/proposals/074-typeclass-instance-is-a-dictionary.md` §2, "A provider named"; T11;
//! kernel-language §5.4, §8.7).
//!
//! T11's instance is derived through an isomorphism: `ProjAdditive` provides `Additive[T = Y]`
//! from `Additive[T = X]` and an `Iso` between `X` and `Y`. Its `provides` binds `Y` and leaves
//! `X`, which its `requires` read, to whoever names it. Before the stage every call that reached
//! it was refused "construction is cyclic" — named or not, and even `Additive.add(true, false)`
//! — the bracket's type arguments dropped where the selection was read, and `ProjAdditive` a
//! candidate at every `Y`. Now a bracket naming it fixes its parameters (`InstanceSelection::
//! args`), and §8.7's order passes over a provider that leaves open a parameter its `requires`
//! read (narrowed with the user 2026-11-24: a parameter nothing reads, and a provider with
//! values of its own, are chosen as before).
//!
//! CONTROLS — the back-out ledger at the end of this file.

use anthill_core::eval::Interpreter;

use crate::common::{interp_for, load_errors_of, show_value};

fn call(interp: &mut Interpreter, op: &str) -> String {
    match interp.call(op, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(v) => show_value(interp.kb(), &v),
        Err(e) => panic!("`{op}`: {e:?}"),
    }
}

/// T11's declarations, as the proposal writes them.
const T11: &str = "
  sort Meters
    entity m(v: Int64)
  end
  sort Iso
    sort A = ?
    sort B = ?
    operation to(a: A) -> B
    operation from(b: B) -> A
  end
  sort MetersIso
    provides Iso[A = Int64, B = Meters]
    operation to(a: Int64) -> Meters = m(v: a)
    operation from(b: Meters) -> Int64 =
      match b
        case m(v) -> v
  end
  sort ProjAdditive
    sort X = ?
    sort Y = ?
    requires Additive[T = X]
    requires Iso[A = X, B = Y]
    provides Additive[T = Y]
    operation add(a: Y, b: Y) -> Y = Iso.to(Iso.from(a) + Iso.from(b))
    operation neg(a: Y) -> Y = Iso.to(Additive.neg(Iso.from(a)))
    operation zero() -> Y = Iso.to(Additive.zero[T = X]())
  end
";

fn program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace p074s4.{ns}\n  import anthill.prelude.{{Int64, Bool, Additive}}\n  import anthill.realization.runtime.Dictionary\n{decls}{body}\nend\n"
    )
}

fn answers(ns: &str, decls: &str, body: &str, ops: &[(&str, &str)]) {
    let mut interp = interp_for(&program(ns, decls, body));
    for (op, want) in ops {
        assert_eq!(call(&mut interp, &format!("p074s4.{ns}.{op}")), *want, "{op}");
    }
}

fn refusal(ns: &str, decls: &str, body: &str) -> String {
    let errors = load_errors_of(&program(ns, decls, body));
    assert!(!errors.is_empty(), "{ns}: expected a refusal");
    errors.join("\n")
}

// ── A named provider fixes its parameters ─────────────────────────────────────────────────

/// T11: named in `Dictionary.instance`'s key and handed to `sumM` (stage 9's rule), and named in
/// the call's bracket, `ProjAdditive[X = Int64, Y = Meters]` answers `m(v: 5)` — `X = Int64`
/// fixes its construction at `Int64`'s `Additive` and `MetersIso`.
#[test]
fn t11_a_named_provider_fixes_its_parameters() {
    let body = "  operation d() -> Additive[T = Meters] =
    Dictionary.instance[Additive[T = Meters], Additive = ProjAdditive[X = Int64, Y = Meters]]()
  operation sumM(d: Additive[T = Meters], a: Meters, b: Meters) -> Meters = a + b
  operation viaDictionary() -> Meters = sumM(d(), m(v: 2), m(v: 3))
  operation viaBracket() -> Meters =
    Additive.add[Additive = ProjAdditive[X = Int64, Y = Meters]](m(v: 2), m(v: 3))";
    answers("t11", T11, body, &[("viaDictionary", "m(v: 5)"), ("viaBracket", "m(v: 5)")]);
}

/// The bracket's other spellings: `X` alone, `Y` fixed by the call's type; positional, one and
/// both.
#[test]
fn a_named_providers_parameters_by_every_spelling() {
    let body = "  operation onlyX() -> Meters = Additive.add[Additive = ProjAdditive[X = Int64]](m(v: 2), m(v: 3))
  operation pos() -> Meters = Additive.add[Additive = ProjAdditive[Int64]](m(v: 2), m(v: 3))
  operation pos2() -> Meters = Additive.add[Additive = ProjAdditive[Int64, Meters]](m(v: 2), m(v: 3))";
    answers(
        "spellings",
        T11,
        body,
        &[("onlyX", "m(v: 5)"), ("pos", "m(v: 5)"), ("pos2", "m(v: 5)")],
    );
}

/// Two sites naming `ProjAdditive` at two `X` each answer through their own: an `Iso` from
/// `Int64` and one from `Tens`, which scales by ten. The type arguments are part of the
/// selection `resolve_cache` is keyed by, so the second is no copy of the first.
#[test]
fn two_sites_at_two_x_answer_through_their_own() {
    let tens = "  sort Tens
    entity t(v: Int64)
  end
  sort TensAdd
    provides Additive[T = Tens]
    operation add(a: Tens, b: Tens) -> Tens = match a case t(x) -> match b case t(y) -> t(v: x + y)
    operation neg(a: Tens) -> Tens = a
    operation zero() -> Tens = t(v: 0)
  end
  sort TensIso
    provides Iso[A = Tens, B = Meters]
    operation to(a: Tens) -> Meters = match a case t(v) -> m(v: v * 10)
    operation from(b: Meters) -> Tens = match b case m(v) -> t(v: v)
  end
";
    let body = "  operation viaInt() -> Meters = Additive.add[Additive = ProjAdditive[X = Int64]](m(v: 2), m(v: 3))
  operation viaTens() -> Meters = Additive.add[Additive = ProjAdditive[X = Tens]](m(v: 2), m(v: 3))";
    answers(
        "twox",
        &format!("{T11}{tens}"),
        body,
        &[("viaInt", "m(v: 5)"), ("viaTens", "m(v: 50)")],
    );
}

// ── What §8.7's order passes over, and the refusals ───────────────────────────────────────

/// A bracket writing a type the goal fixes otherwise is refused, not ignored:
/// `ProjAdditive[X = Int64, Y = Tens]` at `Additive[T = Meters]`. Found by `/code-review`:
/// MEASURED before the check, it answered `m(v: 5)` through the goal's `Y = Meters`.
#[test]
fn a_bracket_writing_another_type_than_the_goal_fixes_is_refused() {
    let tens = "  sort Tens
    entity t(v: Int64)
  end
";
    let text = refusal(
        "conflict",
        &format!("{T11}{tens}"),
        "  operation go() -> Meters = Additive.add[Additive = ProjAdditive[X = Int64, Y = Tens]](m(v: 2), m(v: 3))",
    );
    assert!(
        text.contains("with `Y = Tens`, where the goal fixes its `Y` at `Meters`"),
        "{text}"
    );
}

/// The bare `Additive = ProjAdditive` fixes nothing of `X`: refused, naming it.
#[test]
fn the_bare_provider_is_refused_naming_its_open_parameter() {
    let text = refusal(
        "bare",
        T11,
        "  operation go() -> Meters = Additive.add[Additive = ProjAdditive](m(v: 2), m(v: 3))",
    );
    assert!(
        text.contains("nothing fixes its `X`") && text.contains("`Additive = ProjAdditive[X = …]`"),
        "{text}"
    );
}

/// The unnamed `m(v: 2) + m(v: 3)`, `ProjAdditive` the only provider at `Meters`: no provider is
/// chosen there, and the refusal names `ProjAdditive` and the bracket that chooses it.
#[test]
fn an_unnamed_call_it_alone_answers_names_it_and_its_bracket() {
    let text = refusal("unnamed", T11, "  operation go() -> Meters = m(v: 2) + m(v: 3)");
    assert!(
        text.contains("no provider is chosen here")
            && text.contains("`p074s4.unnamed.ProjAdditive` provides it but leaves `X` open")
            && text.contains("`Additive = ProjAdditive[X = …]`"),
        "{text}"
    );
    assert!(!text.contains("cyclic"), "{text}");
}

/// `Additive.add(true, false)` is refused about `Bool` — no `Iso` reaches it, so `ProjAdditive`
/// is not advised — and not as a cycle.
#[test]
fn a_goal_nothing_answers_is_refused_about_its_type_not_as_a_cycle() {
    let text = refusal("bool", T11, "  operation go() -> Bool = Additive.add(true, false)");
    assert!(
        text.contains("Additive[T = anthill.prelude.Bool]") && text.contains("no impl provides"),
        "{text}"
    );
    assert!(!text.contains("cyclic") && !text.contains("ProjAdditive"), "{text}");
}

/// A cycle among provisions that fix every parameter keeps its message.
#[test]
fn a_true_cycle_keeps_its_message() {
    let decls = "
  sort Sp
    sort T = ?
    operation f(x: T) -> Int64
  end
  sort Sq
    sort T = ?
    operation g(x: T) -> Int64
  end
  sort A1
    requires Sq[T = Int64]
    provides Sp[T = Int64]
    operation f(x: Int64) -> Int64 = 1
  end
  sort A2
    requires Sp[T = Int64]
    provides Sq[T = Int64]
    operation g(x: Int64) -> Int64 = 2
  end
";
    let text = refusal("cycle", decls, "  operation go() -> Int64 = Sp.f(3)");
    assert!(
        text.contains("construction is cyclic") && text.contains("no type written at a use changes that"),
        "{text}"
    );
}

/// CONTROL: a provider whose open parameter nothing reads is chosen as before — `B` is declared
/// and unused, and `m(v: 2) + m(v: 3)` adds through it.
#[test]
fn a_parameter_nothing_reads_leaves_the_provider_chosen() {
    let decls = "
  sort Meters
    entity m(v: Int64)
  end
  sort Loose
    sort B = ?
    provides Additive[T = Meters]
    operation add(a: Meters, b: Meters) -> Meters = match a case m(x) -> match b case m(y) -> m(v: x + y)
    operation neg(a: Meters) -> Meters = a
    operation zero() -> Meters = m(v: 0)
  end
";
    answers("loose", decls, "  operation go() -> Meters = m(v: 2) + m(v: 3)", &[("go", "m(v: 5)")]);
}

// ── The back-out ledger (measured 2026-11-24, one optimized build, a temporary switch per part
// read at run time, over the whole of `anthill-core` — 11626 rows; the control, no switch, every
// row passed) ───────────────────────────────────────────────────────────────────────────────
//
// | part backed out | rows that fail |
// |---|---|
// | the bracket's type arguments applied to the pinned provider (step 0) | `t11_a_named_provider_fixes_its_parameters`, `a_named_providers_parameters_by_every_spelling`, `two_sites_at_two_x_answer_through_their_own` |
// | the refusal of a pinned provider that leaves a read parameter open | `the_bare_provider_is_refused_naming_its_open_parameter` |
// | §8.7's order passing over such a provider | `an_unnamed_call_it_alone_answers_names_it_and_its_bracket`, `a_goal_nothing_answers_is_refused_about_its_type_not_as_a_cycle` |
// | the advice given only where the provider's `requires` have provisions (`could_answer_named`) | `a_goal_nothing_answers_is_refused_about_its_type_not_as_a_cycle` |
// | the type arguments in the selection's key (`WrittenTypeArg`'s `Hash` / `Eq`) | `two_sites_at_two_x_answer_through_their_own` (both answer `m(v: 5)`) |
// | a written argument disagreeing with the goal's binding refused (added after `/code-review`, not in the switched run) | `a_bracket_writing_another_type_than_the_goal_fixes_is_refused` — MEASURED on the CLI before the check: `m(v: 5)` |
// | an effect row's kind anchor counted as reading its parameter | 3 of `wi_34822_clause_parameter_one_spelling_test` |
// | a provider with values of its own, or a data sort, not exempted | `wi210_dispatch_test::dispatch_polymorphic_candidate_matches_any_per_call_value`, `wi_sqzpq_type_pattern_test::a_ground_call_at_an_open_slot_advises_both_repairs` |
//
// PASS EITHER WAY BY DESIGN: `a_true_cycle_keeps_its_message` (a cycle among provisions that fix
// every parameter is the resolver's, untouched) and `a_parameter_nothing_reads_leaves_the_provider_chosen`
// (the control on the rule's width: a parameter nothing reads is never open).
