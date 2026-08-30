## Attributes

- id: WI-20260830-7MK73-implement-a-real-model-behind
- created: 2026-08-30T16:35:06Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T16:35:06Z

- acceptance: cargo-test, scaland-sbt-test

- tags: guardians

## Description

IMPLEMENT A REAL MODEL BEHIND `guardians.LiveLlm`, so the example's live/fake distinction is exercised rather than only declared.

WHAT IS THERE NOW. `rustland/anthill-core/tests/guardians_test.rs` registers BOTH carriers against one closure:

    for key in ["guardians_fake_complete", "guardians_live_complete"] {
        kb.register_host_fn(key, 2, |interp, _args| {
            let reply = FAKE_REPLY.with(|r| r.borrow().clone());
            text_value(interp.kb(), &reply)
        })
    }

`LiveLlm` is a second fake. It ignores its prompt argument (`_args`) and answers from a thread-local.

WHAT THAT COSTS, and it is two claims the example makes and does not demonstrate.

FIRST, `Permission` AND `External` ARE ORTHOGONAL. That is proposal 064's four-quadrant argument, and the example is cited as its evidence: `FakeLlm.open` carries `Permission[Llm]` with NO `External` -- the same authority path exercised, nothing leaving the process -- while `LiveLlm` carries both. With one stub behind both, the top-right quadrant is populated by a declaration and nothing else. A test can assert the fake is not external; nothing shows the live one IS.

SECOND, SWAPPING THE MODEL IS CHOOSING A VALUE. The README says so outright: "`Llm` is a spec; `LiveLlm` and `FakeLlm` are carriers. Choosing between them is choosing a VALUE, not re-registering a host function, and no agent source changes." That is exactly right about the anthill side and vacuous while the host side is one function under two names.

THIRD, SINCE 01421d5a, `Llm` CARRIES AN EFFECT ROW PARAMETER -- `effects E = ?`, instantiated at `{External}` by `LiveLlm` and `{}` by `FakeLlm`. That commit's argument is that externality is a fact about the CARRIER. One stub behind both makes the row a claim about nothing.

WHAT MUST NOT CHANGE. `examples/guardians/README.md` §"Why almost none of the tests need a model": every SECURITY property here is a load-time refusal, decided with no oracle, no fake and no network, and that ordering is itself the claim -- "if a model had to run to test the security, the security would be statistical rather than checked." So:

  * the DEFAULT `cargo test` run must make no network call and need no credentials;
  * the live path is opt-in (feature flag or env var), and skipped, not failed, when unconfigured;
  * no key, endpoint or token is committed; read them from the environment;
  * the existing refusal tests keep their current diagnostics and stay offline.

SHAPE. `LiveLlm.open(endpoint, model)` already takes what a client needs and already carries `Permission[Llm]`; `complete` already declares `{External, Error}` on that carrier. So this is a host binding for `guardians_live_complete` that issues one HTTP request and maps the reply into `LlmOutput`, plus configuration -- no anthill-side change is required, which is itself worth confirming.

ACCEPTANCE: with the live path configured, `LiveLlm.complete` performs a real request and its reply reaches `summarize`; with it unconfigured, the whole guardians suite is green and offline; a test asserts `FakeLlm` performs no external call while still consuming `Permission[Llm]`; and the article's claim that choosing a carrier is choosing a value is true of the host side as well as the anthill side.

RELATED. WI-20260830-THZ8R part D records the same shape of gap in `render_task`, which accepts `tools` and `feedback` and drops them. Both are host stand-ins that a signature promises more than.

