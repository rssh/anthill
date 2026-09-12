## Attributes

- id: WI-20260912-1QVWA-defect-lookup-operation-info-s
- created: 2026-09-12T20:35:57Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-12T22:16:41Z

- acceptance: cargo-test, scaland-sbt-test

## Description

defect: `lookup_operation_info`'s miss path is a FULL SCAN, and 95% of typer lookup time is spent finding nothing

Asking "is this functor an operation?" about a symbol that is NOT one costs a linear
scan over every `anthill.reflect.OperationInfo` fact, which then returns `None`.
`constrain_application` asks the operation table first, scans the whole list, finds
nothing, and only then falls through to `kb.entity_field_types(functor)` — which is
where the answer was. Entity CONSTRUCTORS are the population that pays this.

MEASURED, one stdlib load (debug CLI, empty namespace, ANTHILL_LOAD_TIMING=1,
min-of-K, alternated, quiet box):

  lookup_operation_info_full        3363 calls   198.3 ms
    slow path (no cached signature) 1790 calls   196.5 ms
      FULL SCAN returning None      1712 calls   189.0 ms   <- 95% of the total
    fast path                       1573 calls     ~2.1 ms   (100x cheaper per call)

  collect_rule_var_types split: head 51.8ms | body 230.1ms | resolve 1.3ms
  (the body half is 475 nodes at ~0.48 ms each — all of it this lookup)

PROVED BY MEMOIZING THE MISSES (same binary, one env flag, min-of-9 alternated):

  memo off   0.84 s load    collect_rule_var_types 274.6 ms
  memo on    0.72 s load    collect_rule_var_types  36.4 ms   (7.5x)

Output identical (124 lines; only hash-iteration ORDER moved, which a real fix must
avoid by using a deterministic structure).

WHY IT SURFACED NOW, and why this is NOT a WI-743 defect. WI-743 (`68a77f13`, a closed
sort IS a generator — derive its domain) is the TRIGGER, not the fault. A derived domain
clause is a disjunction of constructor applications (`?x <=> cons(head: ?h, tail: ?t)`),
so every disjunct is one of these futile scans; 125 derived clauses over 254 constructors
multiplied a waste that was already there. Bisected: 0.70-0.72 s at the four commits
before it, 0.83 s at it and after, holding to HEAD. The suite moved the same way —
wi_tests 0.1483 -> 0.1733 s/test (+17%), and the archived run logs step 0.081 -> 0.096
s/test at the same point. Making the DERIVATION lazy would hide this and leave the
defect for every other rule.

THE FALLBACK'S OWN COMMENT IS WRONG and should be corrected with the fix
(`op_info.rs`, above the scan): "Post-typecheck callers (the typer, then eval / reflect /
codegen) hit the fast path above." The typer misses on 53% of calls (1790/3363).
`build_op_signatures` DOES run first, so the index exists — it simply holds no entry for
a non-operation, and nothing short-circuits that case.

BLAST RADIUS: ~15% of every stdlib load. Every test loads the stdlib once (34 test files
each define their own `load_with_stdlib`, no caching), so it is ~15% of the whole suite —
about 10 minutes per full `scripts/test.sh` run at default threads.

FIX DIRECTIONS (not decided here):
  1. Negative cache — a set of symbols the scan found nothing for. Smallest change,
     recovers the whole 0.12 s. Must be deterministic (see the ordering note above)
     and keyed so it cannot outlive the KB it describes.
  2. Ask `entity_field_types` first when the functor is a known constructor — removes
     the question instead of caching the answer.
  3. Index `OperationInfo` facts by symbol so a MISS is O(1) — fixes every caller of
     the scan, not only the typer. Widest, and the only one that helps the load-time
     callers the comment names (const-purity gate, eq-dispatch-table build).

REPRO: `ANTHILL_LOAD_TIMING=1 anthill check <empty-namespace.anthill>`, min-of-K,
alternated between pre-built binaries, on an idle box. Do NOT sample while anything is
building: measured noise floor is ~2% alternated on a quiet box versus ~33% under
concurrent builds, and 33% is larger than this entire effect.

## Changes

### 2026-09-12T22:16:34Z — feedback — claude

FIX DIRECTION 3, the widest of the three: `OperationInfo` facts are indexed by the
`Symbol` their `name` field refers to (`KnowledgeBase::op_info_index`, a
`SymbolKeyedFactIndex`), so a MISS is a bucket lookup instead of a walk of every such
fact. Built inside `op_info::build_op_signatures`' existing pass (one walk, two products),
reset at the top of `load_phase_inner` beside the sibling index resets. Deterministic by
construction — a bucket is an order-preserving subsequence of the `rules_by_functor`
scan, no hash iteration enters any answer, so the ordering hazard the memo experiment hit
does not arise.

Direction 1 (a negative cache) was not taken: it caches the answer where this removes the
question, and it would serve only `lookup_operation_info`. Direction 2 (ask
`entity_field_types` first) reorders ONE caller and leaves the scan for the rest.

THREE KEYED READERS NOW SHARE ONE RID SOURCE (`op_info::op_info_fact_rids`, an
allocation-free iterator that is the bucket when the index exists and the full walk
before that): `lookup_operation_info`'s fallback, `operation_is_declared` (the resolver
bridge's speculative per-candidate probe, whose WI-1092 no-Vec property is preserved) and
`typing::lookup_operation_field` — the third had the same miss shape and was not in the
ticket.

KEYED BY THE RAW SYMBOL, not `canonical_sort_sym`: the scan it replaces compares
`head_name_ref(head) == Some(op_sym)` with raw `==`, and canonicalizing would merge two
distinct symbols sharing a qualified name, flipping a `None` to a `Some`. That is the one
documented departure from `SymbolKeyedFactIndex`' canonical-key rule, recorded on the
struct doc and on `get`/`insert` as well as on the KB field.

SOUND BUILD-ONCE by `sort_info_index`' argument: `OperationInfo` is `constant`
(`fact_monotonicity`), so a runtime `Store.persist`/`retract`/`update` of it is a loud
error, and every loader assert runs strictly before the build.

MEASURED (the ticket's protocol: alternated min-of-K, pre-built debug binaries, idle box).
`anthill check` over an empty namespace: 857 -> 654 ms, and 864 -> 647 ms re-measured on
the shipped tree, against a 0.3% noise floor for two copies of one binary (926 vs 923).
`type_check_sorts` 419 -> 270 ms and 606 -> 222 ms on the two occasions it was taken.
Suite-wide, from this box's archived run logs, `wi_tests`: 442.3 / 444.3 / 447.2 / 773.1 s
without the index against 326.7 / 334.4 / 334.8 / 338.6 s with it (-26% on min-of-K; the
773 s outlier began with a full recompile and is reported, not explained away).
`load_with_visited` is NOT served (the index is `None` for the whole load phase) and the
two paired measurements land on opposite sides of zero, i.e. inside the noise.

THE TICKET'S "ORDER MOVED" CAVEAT WAS A PRE-EXISTING DEFECT, not a property of the memo
experiment: two runs of the UNCHANGED baseline binary already print the 121-line coherence
report in different orders. The shipped binary's output is the same SET as the baseline's.
Left alone here and not filed: it is a separate report-ordering question.

TWO DOC CORRECTIONS THE TICKET ASKED FOR, plus one it did not.
  * `op_info.rs`'s fallback comment no longer claims post-typecheck callers hit the fast
    path; it now states that every MISS reaches the fallback by construction, with the
    numbers. Its companion example was also wrong and is fixed: `check_const_purity` runs
    AFTER `type_check_sorts`, so it is not a pre-build caller; `build_eq_dispatch_index` is.
  * `reflect.anthill`'s `fact_monotonicity` comment said `constant` over `OperationInfo`
    was belt-and-suspenders "because `op_records` tolerates a runtime add via its scan
    fallback". This index does not tolerate one — its fallback is chosen by whether the
    index EXISTS, not by whether the symbol is in it — so that line is now load-bearing and
    says so.

FOUR TESTS, in `kb::typing::tests::wi_1qvwa_op_info_index_tests`, each with its control
measured:
  1. `the_index_answers_exactly_what_the_scan_answers` — the census is EVERY symbol the KB
     has minted (`symbol_count`), not a fixture's names, with the cached signatures cleared
     so the fallback is the only tier in play; asserts hundreds of operations AND thousands
     of misses so neither arm can agree its way to a pass by answering empty.
     CONTROL: remove `index.insert` (index published, `Some`, empty) -> fails at `eq`.
  2. `a_retracted_operation_fact_is_dropped_by_the_index_as_it_is_by_the_scan` — the one
     input the two arms are not interchangeable on, and it fails UPWARD (a signature
     outliving its declaration).
     CONTROL: drop `is_rule_alive` from `op_info_fact_rids` -> the INDEX half fails, the
     SCAN half still passes.
  3. `a_second_load_phase_is_not_read_through_the_first_phases_index` — a second `load_all`
     into a live KB, whose rule body names a nullary operation bare; the loader asks
     `is_nullary_operation` WHILE the phase loads.
     CONTROL: back out `kb.op_info_index = None` in `load_phase_inner` -> `:- flag` is built
     as `Ref(Symbol(3900))` instead of the nullary call, WI-20260902-VNWAW's shape exactly.
     (The `declared_arity` row passes either way, which is why the loader-time reading is
     what this asserts.)
  4. `asserting_an_operation_info_fact_over_a_live_index_is_refused` — raised by
     `/code-review`: the field doc's "a future writer must drop the index" was held by prose
     alone. Now a `debug_assert!` at `push_value_head_entry`'s head-functor block (the ONE
     funnel every fact assertion passes, which the three `assert_metadata_fact*` wrappers
     are not), guarded on `op_info_index.is_some()` so a load pays nothing.
     CONTROL: neutralize the assert -> `should_panic` fails.

`/code-review high` run: no correctness defect found in the mechanism; all four low-severity
findings (the raw-key contract, the const-purity example, the unenforced standing rule, the
one-sided measurement spread) are fixed above rather than spun out.

ACCEPTANCE. Full Rust workspace via `rustland/scripts/test.sh`: 36 binaries, 0 failures
(`wi_tests` 4601 passed, lib 606 passed). `scaland`: `sbt test` `[success]`, 609 tests —
untouched, and it has no equivalent reader to port (`OperationInfo` appears there only as a
declared reflect entity name in `load/Prelude.scala`).

