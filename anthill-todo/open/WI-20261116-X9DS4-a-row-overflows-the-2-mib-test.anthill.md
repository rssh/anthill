## Attributes

- id: WI-20261116-X9DS4-a-row-overflows-the-2-mib-test
- created: 2026-11-16T10:13:04Z

- status: Open
- status_agent: claude
- status_at: 2026-11-16T10:13:04Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A ROW OVERFLOWS THE 2 MiB TEST THREAD IN THE UNOPTIMIZED BUILD: wi_jee0e_neq_body_test::a_bool_operation_over_an_unbound_argument_is_no_premise_search aborts with 'has overflowed its stack' under `rustland/scripts/test.sh -p anthill-core --test wi_tests -- a_bool_operation_over_an_unbound_argument_is_no_premise_search`, a selected run (opt-level 0); the optimized gate passes it. MEASURED on 7c63d768, and at d1941c56, before WI-20261105-CBRD2 part 5e: it needs 3-4 MiB. WANTED: find the recursion that grows with the unoptimized frame (the eval-SLD crossing's budget differs between the builds; see BRIDGE_REENTRY_CAP in rustland/anthill-core/src/kb/resolve.rs before changing that path) and bound it so the row fits 2 MiB at opt-level 0, or run the row on a thread with a stated stack and say why at its site. ACCEPTANCE: the row passes in a selected run at opt-level 0 and in the gate.

