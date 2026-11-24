//! WI-20261113-Q2C01 — proposal 074 stage 3: A SORT WITH OPERATIONS AND NO PARAMETER HAS A
//! DICTIONARY (`docs/proposals/074-typeclass-instance-is-a-dictionary.md` §2, the third row of
//! "Which sorts have a dictionary", with no parameter; kernel-language §8.2).
//!
//! `Ticker { operation now() -> Int64 }` has a dictionary, and a value typed `Ticker` is its
//! provider: `c: Ticker` is handed one (`Dictionary.instance[Ticker]()`), `requires Ticker` is a
//! demand its caller fills, and a call with nothing handed takes the provider chosen at load —
//! the one provider with no conditions, the default, or one a bracket names. A module, which
//! nothing provides (`anthill.prelude.Time`, a program's `Prog`), is its own provider. Decided
//! with the user 2026-11-24 (the census, recorded on the ticket): `requires` is subtyping and a
//! demand at once, so a value of a sort that requires a sort with a dictionary, used where that
//! sort's provider is expected, gets the provider its `requires` finds at load; and a sort whose
//! operation returns `Self` has values of its own.
//!
//! The examples' `Program`s and lf1's controllers are modules and run as before: their suites
//! (`wi_acg10_census_test`, `classic_mini_test`, anthill-cli's `wi_zw6n5_lf1_scaffold_test`) are
//! unchanged. `ProjAdditive`'s own dictionary is `wi_2ksaa_dictionary_instance_test::
//! a_sort_nothing_provides_is_its_own_provider`; `anthill run` is anthill-cli's
//! `run_cmd_test::a_parameterless_sorts_provider_keeps_its_effect`.
//!
//! CONTROLS, measured with a temporary switch per part in one build, then removed — see the
//! ledger at the end of this file.

use anthill_core::eval::effects::{EffectHandler, HandlerAction};
use anthill_core::eval::{Interpreter, Value};

use crate::common::{interp_for, load_errors_of, show_value};

fn shown(interp: &mut Interpreter, op: &str) -> String {
    match interp.call(op, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(v) => show_value(interp.kb(), &v),
        Err(e) => panic!("`{op}`: {e:?}"),
    }
}

/// A program of `body` in namespace `q2c01.{ns}`, with the imports the rows share.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace q2c01.{ns}
  import anthill.prelude.{{Int64, String, Additive, Time}}
  import anthill.prelude.Time.{{Clock}}
  import anthill.realization.runtime.Dictionary
{body}
end
"#
    )
}

/// What each operation of `ops` answers in the program `body`, shown.
fn answers(ns: &str, body: &str, ops: &[&str]) -> Vec<String> {
    let mut interp = interp_for(&program(ns, body));
    ops.iter()
        .map(|op| shown(&mut interp, &format!("q2c01.{ns}.{op}")))
        .collect()
}

fn refused(ns: &str, body: &str) -> Vec<String> {
    let errors = load_errors_of(&program(ns, body));
    assert!(!errors.is_empty(), "expected a refusal of:\n{body}");
    errors
}

fn says(errors: &[String], text: &str) -> bool {
    errors.iter().any(|e| e.contains(text))
}

fn frozen_clock() -> EffectHandler {
    Box::new(|_interp, _op, _args| Ok(HandlerAction::Pure(Value::Str("2000-01-01T00:00:00Z".into()))))
}

const TICKER: &str = "  sort Ticker
    operation now() -> Int64
  end
";
const SYS: &str = "  sort SysTicker
    provides Ticker
    operation now() -> Int64 = 7
  end
";
const OTHER: &str = "  sort Other
    provides Ticker
    operation now() -> Int64 = 9
  end
";
const USE_NOW: &str = "  operation useNow(c: Ticker) -> Int64 = Ticker.now()\n";

// ── A parameter typed at the sort holds its provider ───────────────────────────────────────

/// `use(c: Ticker)` takes `Dictionary.instance[Ticker]()`, and `Ticker.now()` in its body reads
/// that provider: the one provider's 7, and each provider a bracket names. Before the stage the
/// call in the body was refused "no provider can be selected here", and the built-in refused
/// `Ticker` as a sort with no parameter. FAILS with the parameter's slot backed out and with the
/// built-in's refusal restored.
#[test]
fn a_parameter_typed_at_the_sort_holds_its_provider() {
    let one = format!("{TICKER}{SYS}{USE_NOW}  operation viaOne() -> Int64 = useNow(Dictionary.instance[Ticker]())");
    assert_eq!(answers("param1", &one, &["viaOne"]), ["7"]);
    let two = format!(
        "{TICKER}{SYS}{OTHER}{USE_NOW}  operation viaSys() -> Int64 = useNow(Dictionary.instance[Ticker, Ticker = SysTicker]())
  operation viaOther() -> Int64 = useNow(Dictionary.instance[Ticker, Ticker = Other]())"
    );
    assert_eq!(answers("param2", &two, &["viaSys", "viaOther"]), ["7", "9"]);
}

/// `use() requires Ticker = Ticker.now()` reads the provider its caller passes: the one provider
/// at a bare call (7), the one its bracket names (9), and the one the caller is handed, which a
/// handed provider covers as a clause would (9). MEASURED before the stage: it loaded and died at
/// run time, `OperationBodyMissing("Ticker.now")` — the caller built `Dictionary(impl: Ticker)`,
/// a requirement of a sort with no parameter read as a refinement. FAILS with that reading
/// restored (`clause_is_dispatchable`).
#[test]
fn a_clause_reads_the_provider_its_caller_passes() {
    let req = "  operation useReq() -> Int64 requires Ticker = Ticker.now()\n";
    let one = format!("{TICKER}{SYS}{req}  operation bare() -> Int64 = useReq()");
    assert_eq!(answers("req1", &one, &["bare"]), ["7"]);
    let two = format!(
        "{TICKER}{SYS}{OTHER}{req}  operation named() -> Int64 = useReq[Ticker = Other]()
  operation handed(a: Ticker) -> Int64 = useReq()
  operation viaHanded() -> Int64 = handed(Dictionary.instance[Ticker, Ticker = Other]())"
    );
    assert_eq!(answers("req2", &two, &["named", "viaHanded"]), ["9", "9"]);
    let errors = refused("req3", &format!("{TICKER}{SYS}{OTHER}{req}  operation bare() -> Int64 = useReq()"));
    assert!(says(&errors, "ambiguous among providers"), "{errors:?}");
}

/// `go() = Ticker.now()`, handed nothing, takes the provider chosen at load as any provider at
/// one type is: the one provider (7), the default where two answer (9), the one its bracket names
/// (9); two and no default is refused, naming the bracket. Before the stage: "no provider can be
/// selected here". The first three FAIL with the load-time choice backed out, the default one
/// with the default keyed off no type-var only; the refusal passes either way, by design.
#[test]
fn a_call_handed_nothing_takes_the_provider_chosen_at_load() {
    let go = "  operation go() -> Int64 = Ticker.now()\n";
    assert_eq!(answers("go1", &format!("{TICKER}{SYS}{go}"), &["go"]), ["7"]);
    let dflt = "  sort Other
    default provides Ticker
    operation now() -> Int64 = 9
  end
";
    assert_eq!(answers("go2", &format!("{TICKER}{SYS}{dflt}{go}"), &["go"]), ["9"]);
    let named = format!("{TICKER}{SYS}{OTHER}  operation go() -> Int64 = Ticker.now[Ticker = Other]()");
    assert_eq!(answers("go3", &named, &["go"]), ["9"]);
    let errors = refused("go4", &format!("{TICKER}{SYS}{OTHER}{go}"));
    assert!(says(&errors, "ambiguous among providers"), "{errors:?}");
    assert!(says(&errors, "`Ticker.now[Ticker = …](…)`"), "{errors:?}");
}

/// A provider with constructors may be named (decided with the user 2026-11-24, following
/// WI-20261122-CXR5B over the ticket's row "naming one with constructors is refused"): no value
/// at a call of a sort with no parameter decides its provider, so a bracket naming one is the
/// only way to choose between two such providers. `Dictionary.instance[Ticker, Ticker = ScT]()`
/// and `Ticker.now[Ticker = ScT]()` answer `ScT`'s 8 beside `SysTicker`. Passes with any part of
/// this stage backed out but the parameter's slot and the built-in, by design: CXR5B's rule.
#[test]
fn a_provider_with_constructors_may_be_named() {
    let body = format!(
        "{TICKER}{SYS}  sort ScT
    provides Ticker
    entity sc
    operation now() -> Int64 = 8
  end
{USE_NOW}  operation viaKey() -> Int64 = useNow(Dictionary.instance[Ticker, Ticker = ScT]())
  operation viaBracket() -> Int64 = Ticker.now[Ticker = ScT]()"
    );
    assert_eq!(answers("cons", &body, &["viaKey", "viaBracket"]), ["8", "8"]);
}

// ── Refused at load ────────────────────────────────────────────────────────────────────────

/// A provider's value where its provider is expected is refused, naming the spelling: `use(sc)`
/// answered 1 before the stage, a `ScT` read as a `Ticker`. The type written as a value is
/// refused too. The first FAILS with `provider_conforms_to` reading `Ticker` as its providers.
#[test]
fn a_providers_value_is_refused_where_its_provider_is_expected() {
    let sct = "  sort ScT
    provides Ticker
    entity sc
    operation now() -> Int64 = 8
  end
";
    let errors = refused("val1", &format!("{TICKER}{sct}{USE_NOW}  operation go() -> Int64 = useNow(sc)"));
    assert!(says(&errors, "does not make a value of `q2c01.val1.ScT` a `q2c01.val1.Ticker`"), "{errors:?}");
    assert!(says(&errors, "pass `Dictionary.instance[q2c01.val1.Ticker]()`"), "{errors:?}");
    let errors = refused("val2", &format!("{TICKER}{SYS}{USE_NOW}  operation go() -> Int64 = useNow(Ticker)"));
    assert!(says(&errors, "useNow.c"), "{errors:?}");
}

/// A call two handed providers answer is refused at load, naming both: two parameters, a
/// parameter and a clause, and the same where the call is a callee's own requirement — of the
/// operation, or of its sort. Each answered from the first written before (7, 7, 9, 9). Each
/// FAILS with the tie it is refused for backed out.
#[test]
fn a_call_two_handed_providers_answer_is_refused() {
    let both = format!("{TICKER}{SYS}{OTHER}");
    let errors = refused("tie1", &format!("{both}  operation stamps(a: Ticker, b: Ticker) -> Int64 = Ticker.now()"));
    assert!(says(&errors, "two providers of `Ticker` the operation is handed answer, the parameter `a` and the parameter `b`"), "{errors:?}");
    let errors = refused("tie2", &format!("{both}  operation pc(a: Ticker) -> Int64 requires Ticker = Ticker.now()"));
    assert!(says(&errors, "the parameter `a` and the clause `requires Ticker`"), "{errors:?}");
    let errors = refused(
        "tie3",
        &format!(
            "{both}  operation useReq() -> Int64 requires Ticker = Ticker.now()
  operation stamps(a: Ticker, b: Ticker) -> Int64 = useReq()"
        ),
    );
    assert!(says(&errors, "a call of `q2c01.tie3.useReq` that two providers"), "{errors:?}");
    let errors = refused(
        "tie4",
        &format!(
            "{both}  sort UserT
    requires Ticker
    operation g() -> Int64 = Ticker.now()
  end
  operation stamps(a: Ticker, b: Ticker) -> Int64 = UserT.g()"
        ),
    );
    assert!(says(&errors, "a call of `q2c01.tie4.UserT.g` that two providers"), "{errors:?}");
}

/// A lambda's binder typed at the sort is handed a provider as an operation's parameter is:
/// `apply1(f: (c: Ticker) -> Int64)` applies `f` to `Other`'s, and `Ticker.now()` in the lambda
/// reads it (9) where two providers answer and nothing else chooses. FAILS with the binder's
/// slot backed out (refused, two providers and no default).
#[test]
fn a_lambda_binder_typed_at_the_sort_holds_its_provider() {
    let body = format!(
        "{TICKER}{SYS}{OTHER}  operation apply1(f: (c: Ticker) -> Int64) -> Int64 =
    f(Dictionary.instance[Ticker, Ticker = Other]())
  operation go() -> Int64 = apply1(lambda (c: Ticker) -> Ticker.now())"
    );
    assert_eq!(answers("lam", &body, &["go"]), ["9"]);
}

/// The way out of two handed providers is a helper handed one (proposal 074 §2): `stamps(a, b) =
/// (nowOf(a), nowOf(b))` answers each one's `now()`. FAILS with the parameter's slot backed out.
#[test]
fn a_helper_handed_one_provider_reads_it() {
    let body = format!(
        "{TICKER}{SYS}{OTHER}  operation nowOf(c: Ticker) -> Int64 = Ticker.now()
  operation stamps(a: Ticker, b: Ticker) -> (Int64, Int64) = (nowOf(a), nowOf(b))
  operation go() -> (Int64, Int64) =
    stamps(Dictionary.instance[Ticker, Ticker = SysTicker](), Dictionary.instance[Ticker, Ticker = Other]())"
    );
    assert_eq!(answers("idiom", &body, &["go"]), ["(7, 9)"]);
}

// ── Effects ─────────────────────────────────────────────────────────────────────────────────

/// The operations keep their effects: `now() -> String effects Clock`, run through a handed
/// provider, a clause and the provider chosen at load, under a frozen clock, each answering the
/// clock's time; a caller that does not declare `Clock` is refused. (`anthill run`, which binds
/// `Clock` to the host's time: anthill-cli's `run_cmd_test`.)
#[test]
fn the_operations_keep_their_effects() {
    let body = "  sort Ticker
    operation now() -> String effects Clock
  end
  sort SysTicker
    provides Ticker
    operation now() -> String effects Clock = Time.now()
  end
  operation use(c: Ticker) -> String effects Clock = Ticker.now()
  operation viaParam() -> String effects Clock = use(Dictionary.instance[Ticker]())
  operation useReq() -> String effects Clock requires Ticker = Ticker.now()
  operation viaClause() -> String effects Clock = useReq()
  operation go() -> String effects Clock = Ticker.now()";
    let mut interp = interp_for(&program("eff", body));
    interp
        .register_effect_handler("anthill.prelude.Time.Clock", frozen_clock())
        .expect("register the frozen clock");
    for op in ["viaParam", "viaClause", "go"] {
        assert_eq!(shown(&mut interp, &format!("q2c01.eff.{op}")), "\"2000-01-01T00:00:00Z\"", "{op}");
    }
    let errors = refused("eff2", &body.replace("operation go() -> String effects Clock", "operation go() -> String"));
    assert!(says(&errors, "undeclared effect: Clock"), "{errors:?}");
}

// ── Modules ─────────────────────────────────────────────────────────────────────────────────

/// A module — a sort with operations and no parameter that nothing provides — is its own
/// provider, the dictionary of its own bodies: `Dictionary.instance[Time]()` is `Dictionary(impl:
/// Time)`, and `Time.now()` through it answers the clock; a user's module answers through a
/// parameter, a clause and a call alike; a module one of whose operations has nothing to run is
/// refused, naming it. Before the stage the built-in refused `Time`; `requires Mod` was a
/// refinement, and a parameter typed `Mod` took no value at all. The first two FAIL with the
/// module's own dictionary backed out.
#[test]
fn a_module_is_its_own_provider() {
    let body = "  operation time() -> Time = Dictionary.instance[Time]()
  operation useT(t: Time) -> String effects Clock = Time.now()
  operation viaT() -> String effects Clock = useT(Dictionary.instance[Time]())";
    let mut interp = interp_for(&program("mod1", body));
    interp
        .register_effect_handler("anthill.prelude.Time.Clock", frozen_clock())
        .expect("register the frozen clock");
    assert_eq!(shown(&mut interp, "q2c01.mod1.time"), "Dictionary(impl: Time)");
    assert_eq!(shown(&mut interp, "q2c01.mod1.viaT"), "\"2000-01-01T00:00:00Z\"");
    let body = "  sort Mod
    operation k() -> Int64 = 11
  end
  operation useM(m: Mod) -> Int64 = Mod.k()
  operation viaParam() -> Int64 = useM(Dictionary.instance[Mod]())
  operation useReq() -> Int64 requires Mod = Mod.k()
  operation viaClause() -> Int64 = useReq()
  operation direct() -> Int64 = Mod.k()";
    assert_eq!(answers("mod2", body, &["viaParam", "viaClause", "direct"]), ["11", "11", "11"]);
    let errors = refused(
        "mod3",
        "  sort Lone
    operation k() -> Int64
  end
  operation useL(m: Lone) -> Int64 = 1
  operation go() -> Int64 = useL(Dictionary.instance[Lone]())",
    );
    assert!(says(&errors, "nothing provides `q2c01.mod3.Lone`, and its operation `q2c01.mod3.Lone.k` has no body"), "{errors:?}");
}

/// A module's own dictionary is a leaf, as a module's requirement was answered before the stage
/// (found by /code-review): two modules that require each other load and run (refused
/// "construction is cyclic" with each one's `requires` built as the other's sub-dictionary), and
/// a module whose operation is defined by clauses alone answers a requirement of it (refused as
/// an operation with nothing to run). Both load on the tree before the stage; each FAILS with its
/// part of the fix backed out.
#[test]
fn modules_requiring_each_other_and_clause_defined_operations_load() {
    let body = "  sort A
    requires B
    operation a() -> Int64 = 1
  end
  sort B
    requires A
    operation b() -> Int64 = 2
  end
  operation go() -> Int64 = A.a() * 10 + B.b()";
    assert_eq!(answers("mutual", body, &["go"]), ["12"]);
    let body = "  import anthill.prelude.Bool
  sort Spec
    operation rel(x: Int64) -> Bool
    rule rel(1, true) :- true
    operation k() -> Int64 = 4
  end
  sort User
    requires Spec
    operation f() -> Int64 = Spec.k()
  end
  operation go() -> Int64 = User.f()";
    assert_eq!(answers("clauses", body, &["go"]), ["4"]);
}

/// The provider chosen supplies each operation that runs through it: `Mid provides Sp` and
/// supplies no `name` (its own provider `W` does), so a dictionary of `Sp` built at `Mid` is
/// refused at load, by a clause and by the built-in alike. MEASURED with the check backed out:
/// both load and die `OperationBodyMissing("Sp.name")`.
#[test]
fn a_provider_that_supplies_no_member_is_refused_where_it_is_chosen() {
    let sp = "  sort Sp
    operation name() -> Int64
  end
  sort Mid
    provides Sp
    operation other() -> Int64 = 1
  end
  sort W
    entity w
    provides Mid
    operation name() -> Int64 = 42
  end
";
    let errors = refused("sub1", &format!("{sp}  operation useS() -> Int64 requires Sp = Sp.name()\n  operation go() -> Int64 = useS()"));
    assert!(says(&errors, "its provider `q2c01.sub1.Mid` supplies no `name` that runs"), "{errors:?}");
    let errors = refused(
        "sub2",
        &format!("{sp}  operation useS(s: Sp) -> Int64 = Sp.name()\n  operation go() -> Int64 = useS(Dictionary.instance[Sp]())"),
    );
    assert!(says(&errors, "its provider `q2c01.sub2.Mid` supplies no `name` that runs"), "{errors:?}");
}

// ── A value of a sort that requires it gets its provider ──────────────────────────────────

const DESC: &str = "  sort Desc
    sort T = ?
    operation d(x: T) -> Int64
  end
  sort IntDesc
    provides Desc[T = Int64]
    operation d(x: Int64) -> Int64 = 40
  end
  enum Shape
    requires Desc[T = Int64]
    entity circle(r: Int64)
  end
  operation probe(t: Desc[T = Int64]) -> Int64 = Desc.d(1)
";

/// `requires` is subtyping and a demand at once (decided with the user 2026-11-24): a `circle` is
/// a `Desc[T = Int64]`, and where `probe(t: Desc[T = Int64])` expects that provider, it gets the
/// one Shape's `requires` finds at load — IntDesc, the one provider, or the default — and answers
/// 40; two and no default, or none, is a load error. The same for a sort with no parameter:
/// `useNow(circle(r: 1))` over `Shape requires Ticker` answers SysTicker's 7. MEASURED on
/// bba37887f: `probe(circle(r: 1))` loaded and died entering `probe`, "its argument is a Entity,
/// not the instance". The two answers FAIL with the conversion backed out; the refusals pass
/// either way, by design.
#[test]
fn a_value_of_a_requiring_sort_gets_its_provider() {
    let go = "  operation go() -> Int64 = probe(circle(r: 1))\n";
    assert_eq!(answers("req1", &format!("{DESC}{go}"), &["go"]), ["40"]);
    let with_other = |mark: &str| {
        format!(
            "{}  sort OtherDesc\n    provides Desc[T = Int64]\n    operation d(x: Int64) -> Int64 = 50\n  end\n{go}",
            DESC.replace("    provides Desc[T = Int64]\n    operation d(x: Int64) -> Int64 = 40", &format!("    {mark}provides Desc[T = Int64]\n    operation d(x: Int64) -> Int64 = 40"))
        )
    };
    assert_eq!(answers("req2", &with_other("default "), &["go"]), ["40"]);
    // Refused at the call that converts the `circle`, where no provider is chosen. Before
    // proposal 074 stage 9 (WI-20261113-0FTHQ) the refusal was `probe`'s own body, `Desc.d(1)`
    // "2 instances provide `Desc`": the body now reads the dictionary `probe` is handed, `t`.
    let errors = refused("req3", &with_other(""));
    assert!(
        says(&errors, "constructing `q2c01.req3.Desc[T = anthill.prelude.Int64]` is ambiguous among providers"),
        "{errors:?}"
    );
    let errors = refused("req4", &format!("{}{go}", DESC.replace("Shape\n    requires Desc[T = Int64]", "Shape\n    requires Desc[T = String]")));
    assert!(says(&errors, "no impl provides q2c01.req4.Desc"), "{errors:?}");
    let shape = format!(
        "{TICKER}{SYS}{USE_NOW}  enum Shape
    requires Ticker
    entity circle(r: Int64)
  end
  operation go() -> Int64 = useNow(circle(r: 1))"
    );
    assert_eq!(answers("req5", &shape, &["go"]), ["7"]);
}

// ── Classes ─────────────────────────────────────────────────────────────────────────────────

/// A sort whose operation returns `Self` and receives on nothing has values of its own (decided
/// with the user 2026-11-24): `Mon { operation unit(x: Int64) -> Self }` is no sort with a
/// dictionary, and `Dictionary.instance[Mon]()` is refused so. Measured: the rule moves no class
/// of a sort with a parameter (the census traced every class it moved over anthill-core: `Mon`,
/// three times, in `wi_ck7pp_interface_call_test`). FAILS with the rule backed out.
#[test]
fn a_sort_returning_self_has_values_of_its_own() {
    let errors = refused(
        "self1",
        "  sort Mon
    operation unit(x: Int64) -> Self
  end
  sort Box
    entity box(v: Int64)
    provides Mon
    operation unit(x: Int64) -> Box = box(v: x)
  end
  operation f() -> Mon = Dictionary.instance[Mon]()",
    );
    assert!(says(&errors, "`Mon` is an abstract sort with values of its own"), "{errors:?}");
}

/// A rule variable typed at the sort is refused where it is written: a value typed `Ticker` is its
/// provider, which a fact does not hold. Refused before the stage only by the column it matched
/// ("expected ScT, got Ticker"), which still says so beside it.
#[test]
fn a_rule_variable_typed_at_the_sort_is_refused() {
    let errors = refused(
        "rule1",
        &format!(
            "{TICKER}  sort ScT
    provides Ticker
    entity sc
    operation now() -> Int64 = 8
  end
  fact src(sc)
  rule mine(?x: Ticker) :- src(?x)"
        ),
    );
    assert!(says(&errors, "a rule variable is typed `q2c01.rule1.Ticker`, a sort with a dictionary and no parameter"), "{errors:?}");
}

// ── Back-out ledger ─────────────────────────────────────────────────────────────────────────
//
// Each part backed out alone by a temporary switch in one build (2026-11-24), over the 837 rows
// of this file and the suites the stage moved or reads (wi_2ksaa, wi_ck7pp, wi_cxr5b, m460d,
// wi_a3nnd, wi1040, wi281, wi343, wi865, wi_9wvt7, wi_vnqtr, wi_0rrqp, wi_cbrd2, wi_s4d63,
// wi_g37hs, wi_12nkg, wi1042, wi_9bkz4, wi_kssa4, typing_test, wi_p0qgf); 837 / 0 with none
// backed out. The switches are removed.
//
// | part backed out | rows that fail |
// |---|---|
// | a `requires` of a sort with no parameter read as a refinement (`clause_is_dispatchable`) | 13: here `a_call_handed_nothing…`, `a_clause_reads…`, `a_module…`, `a_parameter…`, `a_provider_that_supplies_no_member…`, `a_value_of_a_requiring_sort…`, `the_operations_keep…`; `wi_2ksaa` `a_constant_is_refused…`, `an_operationless_spec…`, `dictionary_instance_refuses_what_has_no_dictionary`; `wi_ck7pp` `a_call_in_a_member…`, `a_provided_sorts_member…`; `wi_cxr5b` `a_spec_with_no_type_var…` |
// | a module's own dictionary in the resolution | 4: `m460d` `control_a_requires_caller…`, `the_two_programs_agree`; `wi_a3nnd` `a_type_parameter_written…`; here `a_module…` |
// | the own dictionary of a sort `Dictionary.instance` names | 5: `wi_2ksaa` `a_constant_is_refused…`, `a_sort_nothing_provides_is_its_own_provider`, `an_operationless_spec…`, `dictionary_instance_refuses…`; here `a_module…` |
// | a parameter typed at the sort holds its provider | 5: here `a_call_two_handed…`, `a_clause_reads…`, `a_helper_handed_one…`, `a_parameter…`, `a_provider_with_constructors…` |
// | a lambda's binder typed at the sort holds its provider | 1: here `a_lambda_binder…` |
// | a provider's value read as a value of the sort (`provider_conforms_to`) | 1: here `a_providers_value…` |
// | the provider chosen at load for a call handed nothing | 2: here `a_call_handed_nothing…`; `wi_ck7pp` `a_provided_sorts_member…` |
// | that choice stepping aside in a member of a sort with values of its own | 1: `wi_ck7pp` `control_a_sub_interface_body…` |
// | the "nothing can run" refusal kept for a provided sort with no parameter | 4: here `a_call_handed_nothing…`, `the_operations_keep…`; `wi_ck7pp` `a_call_in_a_member…`; `wi_cxr5b` `a_spec_with_no_type_var…` |
// | the default keyed at a sort's one type | 1: here `a_call_handed_nothing…` |
// | two handed providers at a call of the sort's operation | 1: here `a_call_two_handed…` |
// | … at a callee's operation-level `requires` | 1: here `a_call_two_handed…` |
// | … at a callee's sort-level `requires` | 1: here `a_call_two_handed…` |
// | a refining value converted to its provider (`InstanceConversion::ToProvider`) | 1: here `a_value_of_a_requiring_sort…` |
// | a chosen provider supplies each body-less operation (the resolution's check) | 2: here `a_provider_that_supplies_no_member…`; `wi_ck7pp` `a_provided_sorts_member…` |
// | a sort an operation returns has values of its own | 2: here `a_sort_returning_self…`; `wi_ck7pp` `result_only_user_member…` |
// | `Dictionary.instance` at a sort with no parameter (stage 1's refusal restored) | 11: here `a_clause_reads…`, `a_helper_handed_one…`, `a_lambda_binder…`, `a_module…`, `a_parameter…`, `a_provider_that_supplies_no_member…`, `a_provider_with_constructors…`, `the_operations_keep…`; `wi_2ksaa` `a_constant_is_refused…`, `an_operationless_spec…`, `dictionary_instance_refuses…` |
// | the refusal of a provider's value naming the spelling | 1: here `a_providers_value…` |
// | the refusal of a rule variable typed at the sort | 1: here `a_rule_variable…` |
// | a witness named in a type argument is no value's type there | 6: `wi_0rrqp` ×3, `wi_cbrd2` ×2, `wi_s4d63` `a_head_bound_and_a_column…` |
//
// Added after /code-review, each measured by its own back-out: a module's own dictionary built
// with its `requires` as sub-dictionaries fails `modules_requiring_each_other…` ("construction
// is cyclic"); an operation defined by clauses counted as one with nothing to run fails it too
// (the `User requires Spec` half).
//
// Two parts failed no row and their code was removed: a supplier check inside the load-time
// choice, which the resolution's check answers first; and the spec-application refusal widened to
// a sort with no parameter, which a bare `Ticker` never reaches (it is refused as a `Type`).
// `a_provider_with_constructors_may_be_named` fails only with the parameter's slot and the
// built-in backed out, by design: the rest is WI-20261122-CXR5B's rule.
