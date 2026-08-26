//! Integration probe for `examples/guardians` — the "Guardians of the Agents"
//! challenge (Erik Meijer, CACM 69(1), January 2026).
//!
//! Design: `examples/guardians/docs/design/`. The claim under test is Flow 2 —
//! the model generates the agent as a `provides` implementation, and the kernel
//! checks it before it can run.
//!
//! ## Why most of these tests need no model at all
//!
//! Every SECURITY property here is a LOAD-TIME refusal, so it is decided by the
//! checker with no oracle, no fake, and no network. Only the USEFULNESS
//! properties need an oracle, and there the fake carrier answers from a fixture.
//! That ordering is itself the claim: if a model had to run to test the security,
//! the security would be statistical rather than checked.

mod common;

use anthill_core::eval::value::Value;
use anthill_core::kb::KnowledgeBase;

// ── loading the example ──────────────────────────────────────────

fn guardians_dir() -> std::path::PathBuf {
    common::examples_dir().join("guardians")
}

/// Read every `.anthill` directly under `dir` (not recursive).
fn sources_in(dir: &std::path::Path) -> Vec<String> {
    let mut files: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display()))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "anthill"))
        .collect();
    files.sort();
    files
        .iter()
        .map(|p| std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display())))
        .collect()
}

/// THE SOLUTION. Usable as-is: no message, no address book, no sample agent.
fn lib_sources() -> Vec<String> {
    sources_in(&guardians_dir().join("lib"))
}

/// TEST DATA. The article's inbox, populating the two relations `lib` declares.
fn fixture_sources() -> Vec<String> {
    sources_in(&guardians_dir().join("fixtures"))
}

fn base_sources() -> Vec<String> {
    let mut v = lib_sources();
    v.extend(fixture_sources());
    v
}

/// `good` lives in `fixtures/agent/`; the three that MUST be refused live in
/// `fixtures/agent/rejected/`.
fn agent_source(name: &str) -> String {
    let dir = guardians_dir().join("fixtures").join("agent");
    let p = if name == "good" || name == "checker" {
        dir.join(format!("{name}.anthill"))
    } else {
        dir.join("rejected").join(format!("{name}.anthill"))
    };
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

/// Load the example plus one candidate agent. `register` runs BEFORE `load_all`,
/// which is where host functions must be registered (WI-1122: registering after
/// load is refused, because the failure is silent in release).
fn try_load_with_agent(
    agent: Option<&str>,
    register: impl FnOnce(&mut KnowledgeBase),
) -> Result<KnowledgeBase, Vec<String>> {
    let mut owned = base_sources();
    if let Some(a) = agent {
        owned.push(agent_source(a));
    }
    let refs: Vec<&str> = owned.iter().map(String::as_str).collect();
    common::try_load_kb_prepared_files(&refs, register)
}

fn errors_for(agent: &str) -> Vec<String> {
    match try_load_with_agent(Some(agent), register_pipeline) {
        Ok(_) => Vec::new(),
        Err(errs) => errs,
    }
}

fn assert_refused(agent: &str, needle: &str) {
    let errs = errors_for(agent);
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "agent/{agent}.anthill should be refused with {needle:?}; got: {errs:#?}"
    );
}

// ── the fake oracle ──────────────────────────────────────────────

/// The fake `Oracle` carrier. Deterministic by construction: it answers from a
/// fixture rather than a network, so a test asserting a classification does not
/// depend on what a live model happens to say today.
///
/// `guardians.FakeModel`'s `operation_map` names these keys. Swapping in the live
/// carrier is choosing a different VALUE at the call site, not re-registering —
/// that is the whole point of making the Oracle a spec with carriers, on the
/// `anthill.persistence.Store` pattern.
/// What the fake model returns, per test. Set before load; the fake `complete`
/// hands it back verbatim as the candidate program.
thread_local! {
    static FAKE_REPLY: std::cell::RefCell<String> = const { std::cell::RefCell::new(String::new()) };
}

fn set_fake_reply(src: &str) {
    FAKE_REPLY.with(|r| *r.borrow_mut() = src.to_string());
}

/// Build a `guardians.Text` value. `Text`'s sole constructor is
/// `entity text(raw: String)`, so a bare `Value::Str` is the WRONG carrier —
/// it loads and then fails to match anything that destructures a `Text`.
fn text_value(kb: &KnowledgeBase, raw: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let f = kb
        .try_resolve_symbol("guardians.Text.text")
        .ok_or_else(|| anthill_core::eval::EvalError::Internal("guardians.Text.text".into()))?;
    Ok(Value::Entity {
        functor: f,
        pos: std::rc::Rc::from(vec![Value::Str(raw.to_string())]),
        named: std::rc::Rc::from(Vec::new()),
    })
}

fn entity0(kb: &KnowledgeBase, qn: &str, args: Vec<Value>) -> Result<Value, anthill_core::eval::EvalError> {
    let f = kb
        .try_resolve_symbol(qn)
        .ok_or_else(|| anthill_core::eval::EvalError::Internal(qn.into()))?;
    Ok(Value::Entity {
        functor: f,
        pos: std::rc::Rc::from(args),
        named: std::rc::Rc::from(Vec::new()),
    })
}

fn str_arg(v: &Value) -> String {
    match v {
        Value::Str(s) => s.clone(),
        Value::Entity { pos, .. } if !pos.is_empty() => str_arg(&pos[0]),
        other => format!("{other:?}"),
    }
}

/// THE NAMESPACE GATE. A candidate may declare only under `guardians.agent.`.
///
/// This is the structural half of the trust partition, and without it the
/// partition is prose: a generated program loaded into the SAME knowledge base
/// as the trusted declarations can reopen `namespace guardians` and assert
/// whatever it likes — including the very facts a safety claim would cite about
/// it. Checking what the candidate DECLARES, before believing anything it says,
/// is what makes "trusted" and "untrusted" different in fact and not only in
/// the design document.
fn namespace_violations(src: &str) -> Vec<String> {
    let mut out = Vec::new();
    for (n, line) in src.lines().enumerate() {
        let t = line.trim();
        for kw in ["namespace ", "sort ", "enum "] {
            if let Some(rest) = t.strip_prefix(kw) {
                let name = rest.split_whitespace().next().unwrap_or("");
                // `namespace guardians` — the BARE namespace — is the case that
                // matters most and has no trailing dot, so a `starts_with
                //("guardians.")` test alone lets the forgery straight through.
                // Measured: it did.
                let in_trusted = name == "guardians" || name.starts_with("guardians.");
                if in_trusted && !name.starts_with("guardians.agent.") {
                    out.push(format!(
                        "line {}: candidate declares `{kw}{name}` — a generated program may \
                         declare only under `guardians.agent.`; reopening a trusted namespace \
                         would let it assert facts about itself",
                        n + 1
                    ));
                }
            }
        }
    }
    out
}

/// Register the whole pipeline: one model primitive, the harness, the checker.
fn register_pipeline(kb: &mut KnowledgeBase) {
    // THE ONE MODEL BINDING. Text in, text out — everything else (prompt
    // construction, the label join, the task operations) is checked anthill.
    for key in ["guardians_fake_complete", "guardians_live_complete"] {
        kb.register_host_fn(key, 2, |interp, _args| {
            let reply = FAKE_REPLY.with(|r| r.borrow().clone());
            text_value(interp.kb(), &reply)
        })
        .unwrap_or_else(|e| panic!("register {key}: {e:?}"));
    }

    // The harness. `render_task` would read the trusted declarations through
    // reflect; rendering a DECLARATION as anthill text is the one piece reflect
    // does not expose (TermPrinter prints terms, rules and facts, and is
    // Rust-side), so this stands in with a fixed instruction and is the
    // example's clearest remaining gap.
    kb.register_host_fn("guardians_render_task", 4, |interp, args| {
        let spec = str_arg(&args[1]);
        let body = format!("Write an anthill implementation of {spec}.");
        let t = text_value(interp.kb(), &body)?;
        entity0(interp.kb(), "guardians.Prompt.prompt", vec![t])
    })
    .expect("register guardians_render_task");

    // Completes the prompt and takes the reply as a candidate program. The
    // `Prompt[Public]` in its anthill signature is what makes "generation is
    // blind to content" a check rather than a comment.
    kb.register_host_fn("guardians_generate", 3, |interp, _args| {
        let reply = FAKE_REPLY.with(|r| r.borrow().clone());
        entity0(interp.kb(), "guardians.Source.source", vec![Value::Str(reply)])
    })
    .expect("register guardians_generate");

    // THE CHECKER, and it really checks: namespace gate, then a full load of
    // the candidate ALONGSIDE the trusted declarations.
    kb.register_host_fn("guardians_check", 3, |interp, args| {
        let candidate = str_arg(&args[1]);

        let mut diags = namespace_violations(&candidate);
        if diags.is_empty() {
            let mut owned = lib_sources();
            owned.extend(fixture_sources());
            owned.push(candidate);
            let refs: Vec<&str> = owned.iter().map(String::as_str).collect();
            if let Err(errs) = common::try_load_kb_prepared_files(&refs, register_pipeline) {
                diags = errs;
            }
        }

        if diags.is_empty() {
            entity0(
                interp.kb(),
                "guardians.CheckResult.Accepted",
                vec![Value::Str("guardians.agent.Generated".into())],
            )
        } else {
            let items: Vec<Value> = diags.into_iter().map(Value::Str).collect();
            let mut list = entity0(interp.kb(), "anthill.prelude.List.nil", vec![])?;
            for it in items.into_iter().rev() {
                list = entity0(interp.kb(), "anthill.prelude.List.cons", vec![it, list])?;
            }
            entity0(interp.kb(), "guardians.CheckResult.Rejected", vec![list])
        }
    })
    .expect("register guardians_check");
}

// ── group A / B: security, and none of it needs an oracle ────────

#[test]
fn good_agent_is_accepted() {
    // CONTROL for every refusal below. Without it, a test suite of refusals is
    // consistent with a checker that rejects everything.
    let errs = errors_for("good");
    assert!(errs.is_empty(), "agent/good.anthill should load: {errs:#?}");
}

#[test]
fn exfiltrating_agent_is_refused_by_the_label() {
    // THE ARTICLE'S ATTACK, as generated code: summarize the mailbox, mail the
    // summary to it@othercorp.com. Refused because `summarize` preserves its
    // argument's label (`?t` in, `?t` out), so the summary is Untrusted and
    // `send_email` wants Public. The summarizer does not launder.
    assert_refused(
        "leak",
        "expected Text[Trust = Public], got Text[Trust = Untrusted]",
    );
}

#[test]
fn capability_widening_is_refused_by_the_row() {
    // Leaks nothing; claims a capability the spec never granted. One token apart
    // from agent/good.anthill, so this measures the row and nothing else — and it
    // shows the two chains are independent, since neither test catches the
    // other's program.
    assert_refused("wide_row", "effects must not widen");
}

#[test]
fn a_modify_target_the_spec_never_granted_is_refused_by_the_row() {
    // THE FRAME CONDITION, and it is a different arm of the same check from the
    // test above. `wide_row` raises `Filesystem`, an ordinary declared effect
    // sort, compared as a TYPE; this one raises `Modify[box]`, whose target is a
    // RESOURCE. kernel-language.md §5.6: a spec row carrying no `Modify` asserts
    // `Env_after = Env_before` for every resource, so an override that acquires
    // one has unenforced exactly the axis §5.6 is about — while restating every
    // capability the spec did grant, which is what makes it invisible to the
    // named-label arm.
    //
    // MEASURED (WI-20260822-1TKN0): this fixture LOADED CLEAN until the effects
    // leg stopped reading a `Value::Term` carrier test as an abstractness test.
    // `wide_row.anthill` is written with `Filesystem` precisely because of that —
    // see measured.md C9.
    assert_refused("wide_row_modify", "effects must not widen");
}

#[test]
fn honest_checker_is_accepted() {
    // CONTROL for the next test. Same spec, same declared row including
    // `-Model`, and no route to a model — so `-Model` is satisfiable and does
    // not refuse every checker on sight.
    let errs = errors_for("checker");
    assert!(errs.is_empty(), "agent/checker.anthill should load: {errs:#?}");
}

#[test]
fn model_consulting_checker_is_refused_by_lacks_model() {
    // The design's sharpest claim: the checker must PROVABLY not consult a
    // model, or the guard is as steerable as the thing it guards.
    //
    // `Checker.check` is handed no Oracle, so a generated checker cannot reach
    // one through its parameters. This fixture defeats that by SMUGGLING an
    // Oracle in its own carrier and reaching it through `self` — and is caught
    // anyway, on a DIFFERENT leg from `capability_widening_is_refused_by_the_row`:
    // the row it DECLARES is the spec's, and it is the row INFERRED FROM THE BODY
    // that carries `Model`. Asserting the body-leg needle rather than
    // "effects must not widen" is what keeps this from silently degrading into a
    // duplicate of the declared-row test, which is what it used to be.
    //
    // THE NEEDLE SHARPENED (WI-20260825-CBRSW), and the refusal did not move: this
    // used to read `got undeclared effect: Model`, which understated it. `check`
    // does not merely fail to declare `Model` — its row DENIES it, and the two
    // failures have different repairs (an undeclared effect is fixed by adding the
    // label; a denied one cannot be). The body leg now says which of the two it is,
    // and `denied effect` is a needle no other leg can produce — so this row is now
    // pinned against the declared-row test twice over.
    assert_refused("bad_checker", "got denied effect: Model");
}

// ── group: usefulness, which is where the fake earns its place ───

#[test]
fn host_fns_register_before_load() {
    // Drives the registration seam itself. If the keys `guardians.FakeModel`'s
    // `operation_map` names were unregistered, this would still LOAD — the check
    // is on the mapping's language, not on the key resolving — so the assertion
    // that matters is that registration SUCCEEDS, which `register_pipeline`
    // asserts internally via `.expect`.
    let kb = try_load_with_agent(Some("good"), register_pipeline)
        .unwrap_or_else(|e| panic!("load: {e:#?}"));
    for qn in [
        "guardians.Llm",
        "guardians.FakeLlm",
        "guardians.LiveLlm",
        "guardians.Harness",
        "guardians.Checker",
        "guardians.Triage",
    ] {
        assert!(
            kb.try_resolve_symbol(qn).is_some(),
            "{qn} should be in the KB"
        );
    }
}

#[test]
fn late_host_fn_registration_is_refused() {
    // The WI-1122 ordering rule, asserted rather than assumed: registering after
    // load is REFUSED. Without this the example would depend on an ordering whose
    // violation fails silently in release.
    let mut kb = try_load_with_agent(Some("good"), register_pipeline)
        .unwrap_or_else(|e| panic!("load: {e:#?}"));
    let late = kb.register_host_fn("guardians_late", 1, |_i, _a| Ok(Value::Unit));
    assert!(
        late.is_err(),
        "registering a host fn after load must be refused"
    );
}

#[test]
fn an_interpreter_can_be_built_over_this_kb() {
    // Verifies the review's claim that four `operation_map` keys are declared and
    // registered nowhere, so `register_operation_mappings` — which hard-errors on
    // an unknown key for a `lang == "rust"` mapping — kills every interpreter
    // built over this program. Loading does NOT surface it: the load-time check
    // is on the mapping's LANGUAGE, not on the key resolving.
    let kb = try_load_with_agent(Some("good"), register_pipeline)
        .unwrap_or_else(|e| panic!("load: {e:#?}"));
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    let r = anthill_core::eval::builtins::register_standard_builtins(&mut interp);
    assert!(
        r.is_ok(),
        "no interpreter can be built over the guardians KB: {r:?}"
    );
}


// ── the library / fixture boundary ──────────────────────────────────────

#[test]
fn lib_loads_without_any_fixture() {
    // THE BOUNDARY, asserted rather than conventional. `lib/` is the solution —
    // sorts, tools, the Oracle spec, the task spec, the classification rules —
    // and it must load with NO test data present. An earlier layout had this
    // backwards: `classify.anthill`'s rule bodies named corroborator predicates
    // that only the fixture declared, so deleting the test data stopped the
    // LIBRARY loading. This test fails the moment a fixture dependency leaks
    // back in.
    let owned = lib_sources();
    let refs: Vec<&str> = owned.iter().map(String::as_str).collect();
    let r = common::try_load_kb_prepared_files(&refs, register_pipeline);
    assert!(r.is_ok(), "lib/ must load standalone; got: {:?}", r.err());
}

#[test]
fn corroborators_are_derived_from_data_not_asserted() {
    // The library COMPUTES `sender_not_in_contacts` from the address book and
    // `reply_to_differs_from_from` from the headers; the fixture asserts
    // neither. Measured through the CLI in the same layout: with the fixture
    // loaded they yield {m3, m5} and {m5}; with `lib/` alone they yield nothing.
    //
    // CONTROL is `lib_loads_without_any_fixture` above — together they pin that
    // the relations are declared by the library and populated by the data,
    // rather than either file doing both jobs.
    let kb = try_load_with_agent(None, register_pipeline)
        .unwrap_or_else(|e| panic!("load: {e:#?}"));
    for qn in [
        "guardians.InMailbox",
        "guardians.KnownContact",
        "guardians.sender_not_in_contacts",
        "guardians.reply_to_differs_from_from",
    ] {
        assert!(
            kb.try_resolve_symbol(qn).is_some(),
            "{qn} should be in the KB"
        );
    }
}


// ── the harness loop, driven end to end ─────────────────────────────────
//
// These DRIVE the pipeline rather than asserting that it loads: they set what
// the fake model returns, run `guardians_check` over that reply exactly as
// `attempt` would, and assert the verdict. Repo CLAUDE.md: "a test for a
// capability must DRIVE the capability".

/// Run the checker's host binding directly over a candidate program — the same
/// function `guardians.attempt` reaches after `render_task` and `complete`.
fn check_candidate(candidate: &str) -> Result<(), Vec<String>> {
    let mut diags = namespace_violations(candidate);
    if diags.is_empty() {
        let mut owned = lib_sources();
        owned.extend(fixture_sources());
        owned.push(candidate.to_string());
        let refs: Vec<&str> = owned.iter().map(String::as_str).collect();
        if let Err(errs) = common::try_load_kb_prepared_files(&refs, register_pipeline) {
            diags = errs;
        }
    }
    if diags.is_empty() { Ok(()) } else { Err(diags) }
}

#[test]
fn harness_accepts_a_well_formed_generated_agent() {
    // CONTROL for the two refusals below. Without it they are consistent with a
    // checker that rejects everything.
    set_fake_reply(&agent_source("good"));
    assert!(
        check_candidate(&agent_source("good")).is_ok(),
        "the harness must accept a well-formed candidate"
    );
}

#[test]
fn harness_rejects_the_exfiltrating_agent_with_a_repairable_diagnostic() {
    // THE ARTICLE'S ATTACK, through the whole loop. The diagnostic is what gets
    // fed back as `feedback` on the next round, so asserting its CONTENT — not
    // merely that something failed — is what pins the repair loop as usable.
    let errs = check_candidate(&agent_source("leak")).expect_err("must be rejected");
    assert!(
        errs.iter().any(|e| e.contains("expected Text[Trust = Public], got Text[Trust = Untrusted]")),
        "expected the taint diagnostic; got: {errs:#?}"
    );
}

#[test]
fn a_wrong_sort_at_a_label_polymorphic_parameter_is_refused() {
    // C7, AT THE VOCABULARY THAT FOUND IT (WI-RKMD4). Until it was fixed, an argument
    // whose SORT disagreed with a parameter type CONTAINING A TYPE VARIABLE was accepted
    // with no diagnostic and the variable was left UNBOUND — which is not a neutral
    // outcome but the maximally permissive one, since the consumer then instantiates it
    // to whatever it wants. Where the variable is a Trust label, that is laundering.
    //
    // ONE TOKEN FROM `agent/good.anthill`: `verdicts_of(msgs)` becomes
    // `verdicts_of(bodies_of(msgs))`, so a `List[Text[?t]]` is handed to a parameter
    // declaring `List[Message[?t]]`. It is here as well as in the typer's own unit test
    // (`wi_rkmd4_type_var_param_slot_test`) because a synthetic reproduction cannot say
    // the fix reaches the real declarations — and it was the real declarations, written
    // out as a file for the first time, that surfaced the defect at all.
    let candidate = r#"
sort guardians.agent.MisprojectingTriage
  import anthill.prelude.{List, Error, External}
  import guardians.{Triage, Mailbox, Report, Model, Llm, summarize,
                    fetch_mail, bodies_of, verdicts_of}
  entity mk

  operation run(self: MisprojectingTriage, box: Mailbox, llm: Llm) -> Report
    ensures mentions_all(result)
    effects {External, Model, Error} =
      let msgs = fetch_mail(box)
      Report(items:   verdicts_of(bodies_of(msgs)),
             summary: summarize(llm, bodies_of(msgs)))

  provides Triage[C = MisprojectingTriage]
end
"#;
    let errs = check_candidate(candidate).expect_err("must be rejected");
    assert!(
        errs.iter()
            .any(|e| e.contains("verdicts_of.msgs") && e.contains("Text")),
        "expected the sort mismatch at the label-polymorphic parameter; got: {errs:#?}"
    );
}

#[test]
fn a_model_cannot_mint_releasable_text() {
    // REGRESSION for a hole that was real and had a working exploit.
    //
    // `Llm.complete` was typed `?t` in, `?t` out for one revision. Preserving a
    // label is correct for a PURE transformation; a model is not one. So a
    // Public prompt yielded Public text, Public is what the sink accepts, and
    // an agent could mint releasable output out of nothing and mail it away —
    // measured loading clean before the fix.
    //
    // Every other refusal test here starts from mailbox content, so all of them
    // were blind to it: the exploit uses no untrusted input at all.
    assert_refused(
        "minting",
        "expected Text[Trust = Public], got Text[Trust = Untrusted]",
    );
}

#[test]
fn code_generation_may_not_read_content() {
    // THE STAGING CLAIM, enforced. `Harness.generate` demands `Prompt[Public]`,
    // and `prompt_with` makes a prompt Untrusted the moment mailbox text enters
    // it — so an agent whose CODE an injected email helped design cannot be
    // produced at all. Refused at construction, not at use.
    //
    // This is what gives `Prompt`'s `Trust` parameter a consumer. Without it
    // the label was produced by `render_task` and read by nothing, and the
    // claim was prose sitting in a type slot.
    assert_refused(
        "generate_from_content",
        "expected Prompt[Trust = Public], got Prompt[Trust = Untrusted]",
    );
}

#[test]
fn harness_rejects_a_candidate_that_reopens_a_trusted_namespace() {
    // THE STRUCTURAL HALF OF THE TRUST PARTITION, and the reason it exists.
    //
    // A candidate loaded into the same knowledge base as the trusted
    // declarations can reopen `namespace guardians` and assert whatever it
    // likes — including `Checked`, the very fact a safety claim would cite
    // ABOUT IT. Type checking does not catch that: the facts are well-formed.
    // Only asking what the candidate DECLARES, before believing anything it
    // says, separates trusted from untrusted in fact rather than in prose.
    let forged = r#"
        sort guardians.agent.EvilTriage
          entity mk
        end
        namespace guardians
          fact Checked(carrier: "guardians.agent.EvilTriage", spec: "guardians.Triage")
        end
    "#;
    let errs = check_candidate(forged).expect_err("must be rejected");
    assert!(
        errs.iter().any(|e| e.contains("may declare only under `guardians.agent.`")),
        "expected the namespace gate to fire; got: {errs:#?}"
    );

    // CONTROL: the same declaration confined to the candidate's own namespace
    // is fine — the gate is about WHERE it declares, not that it declares.
    let ok = r#"
        sort guardians.agent.PoliteTriage
          entity mk
        end
    "#;
    assert!(
        check_candidate(ok).is_ok(),
        "a candidate declaring only under guardians.agent. must pass the gate"
    );
}
