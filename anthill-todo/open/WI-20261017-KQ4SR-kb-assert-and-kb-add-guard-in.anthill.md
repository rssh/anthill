## Attributes

- id: WI-20261017-KQ4SR-kb-assert-and-kb-add-guard-in
- created: 2026-10-17T12:41:03Z

- status: Open
- status_agent: claude
- status_at: 2026-10-17T12:42:39Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261017-KE2GP-037-step-4-the-store-rows-say

- tags: proposal-037

## Description

KB.assert AND KB.add_guard IN THE INTERPRETER. Plan: docs/design/037-implementation.md, decision D9 and §1.4. Proposal 037 Rule 8 says a base sort has a default implementation, which WI-20260922-BRT4Y holds to its declarations. KB is a base sort, but the interpreter implements only kb() and loaded. KB.assert and KB.add_guard (stdlib/anthill/reflect/reflect.anthill:736-744) are body-less, not @[host_implemented], and no operation_map names them. So BRT4Y does not ask about them, and an interpreted call fails at run time with OperationBodyMissing. Only the generated-Rust host bridge implements them (KbBridge, rustland/anthill-stl/src/reflect/bridge.rs:1117-1144, over assert_checked and add_guard_labeled). THE CHANGE: two host functions in eval/builtins.rs's HOST_FNS over the same KnowledgeBase methods, named in rustland/anthill-stl/anthill/reflect.anthill's binding block, with the two declarations tagged @[host_implemented], so the load check holds them. TO DECIDE HERE: (1) What an assert means while a KB.loaded layer is live. Layers are applied in place, so an assert lands among the layer's rules and the layer's discard takes it away. (2) Whether the KB value argument names where the assert goes, the root or the innermost layer. kb_execute and kb_facts_of ignore their KB argument today. AFTER WI-20261017-KE2GP: that ticket builds the refusal of a KB write while a layer is live, for store writes (the plan's D7), and the same guard answers (1) here unless this ticket decides otherwise.

