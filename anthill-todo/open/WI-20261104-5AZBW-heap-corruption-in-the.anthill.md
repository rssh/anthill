## Attributes

- id: WI-20261104-5AZBW-heap-corruption-in-the
- created: 2026-11-04T12:52:49Z

- status: Open
- status_agent: user
- status_at: 2026-11-04T12:52:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: test-infra

## Description

HEAP CORRUPTION IN THE OPTIMIZED TEST BINARIES: a test binary dies, rarely, freeing memory it does not own. THREE OCCURRENCES. (1) 2026-10-06, wi_tests, SIGABRT 'malloc: pointer being freed was not allocated' in drop<KnowledgeBase> -> SortOpsTable -> HashMap<Symbol, HashMap<Symbol, Symbol>> (test wi084_const_phase1_test::bodyless_const_has_kind_and_type_but_no_body), one line after an unrelated FAILED in another thread; 1 abort in 6 optimized executions that day; not reproduced (first 235 tests x6, x4 under MallocScribble=1 MallocPreScribble=1); docs/measurements/test-infrastructure/full-run-2026-10-06-core-opt2.txt, fourth run. (2) 2026-11-04 12:59, a temporary 1301-row binary of wi_tests' suites on a CLEAN tree, SIGSEGV KERN_INVALID_ADDRESS at 0x0 in drop_glue<eval::value::Value> <- drop_glue<OpSignature> <- op_info::build_op_signatures <- typing::sorts::type_check_sorts <- load::load_all_with <- common::run_on_shared_base (test wi_50b2k_binder_inference_test::part_b_a_rule_body_data_slot_checks_its_children_against_the_declaration); the first execution after its build, then 11 green. (3) 2026-11-04 14:28, the full gate's wi_tests, SIGABRT 'pointer being freed was not allocated' in drop<Interpreter> -> KnowledgeBase -> SymbolTable -> HashMap<ScopeId, Scope> -> a Scope's HashMap<String, Symbol> -> String dealloc (test wi_0qv5a_match_arm_guard_test::an_unguarded_match_is_unmoved); every other gate target green, wi_tests re-run alone 8928/0. About 2 in 16 large-binary executions on 2026-11-04, against 1 in 6 on 2026-10-06; every crash is a DROP of plain Rust data, so the corrupting write is elsewhere and earlier. SUSPECTS, none established: tests/common's SendableKb 'unsafe impl Send' (an Rc a deep copy still shares with its pool base, refcounted from two threads) — but occurrence (1) predates the shared base and deep_clone (WI-20261009-D0SD4), so not it alone; the tree-sitter C parser, which every load runs; kb/term.rs's transmute. WHAT: find the write and fix it. Measure the rate first — N optimized executions of wi_tests (the same binary, test.sh's full-run settings) — then under ANTHILL_TEST_FRESH_LOAD=1 (no shared base, no SendableKb) to say whether the copy is involved; catch the write with macOS Guard Malloc (DYLD_INSERT_LIBRARIES=/usr/lib/libgmalloc.dylib, no nightly toolchain needed) or AddressSanitizer/ThreadSanitizer on nightly. Read each crash report's faulting thread (~/Library/Logs/DiagnosticReports/<binary>-*.ips) first. ACCEPTANCE: the cause named and fixed; 20 consecutive optimized executions of wi_tests with no abort and no segfault; where the cause is a broken invariant, a test that fails while it is broken.

## Changes

### 2026-11-20T18:28:54Z — feedback — user

Occurrence 2026-11-20 (Linux/WSL2, 24 CPUs, optimized gate build): wi_tests died with SIGSEGV (signal 11, no Rust message, no stack-overflow report) in 2 of 11 executions of the same opt-level-2 binary within half an hour, both inside a full scripts/test.sh run (logs target/test-run-20261120-175553.log, after 7 852 rows; -180415.log, after 269). The rows in flight differed entirely between the two (first: wi285 deep else-if, wi_hzvqa, wi_kssa4 examples sweep, wi_m32c2, wi_mhrn1; second: typer_capability_matrix sweeps, op_fn_value, provision_written_through_alias, spec_op_requirement_at_member). The same binary run directly 6 times and once through test.sh -p anthill-core --test wi_tests: clean; the next two full gates (HEAD, and the same tree rebuilt): clean. The tree's only change from HEAD removed a test counter and two side-effect-free reads in the resolver's search (WI-20261105-CBRD2 part 6i), so no behavior change; a code-layout shift is the most it could have made.

