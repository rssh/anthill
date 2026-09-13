## Attributes

- id: WI-20260911-8Y5BE-codegen-feature-the-reflect
- created: 2026-09-11T05:58:35Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-13T09:28:24Z

- acceptance: cargo-test, scaland-sbt-test

## Description

CODEGEN + FEATURE: the reflect face's Error is the ONE type on it with no anthill declaration, so nothing enforces bridge == spec for it and every failure degenerates to a Rust `Error(String)` a handler can only substring-match. Give KB.execute's stream a DECLARED payload — `E = Error[ResolveStreamFailure]` — generated into Rust like every other type on that face. BLOCKED on a codegen rule; do that FIRST.

WHY IT MATTERS. reflect/mod.rs labels it: `Solution` / `LogicalQuery` / the introspection types are GENERATED from reflect.anthill (WI-540, 'the single source of truth … so the compiler enforces bridge == spec'), and then, under a separate '── Error (Rust-only infra) ──' banner, `pub struct Error(pub String)`. raise_load_failed states the rule this violates: an ENTITY rather than a bare string, because a handler that fires must be able to DESTRUCTURE the payload. The loose signature is what let it happen — `fact Effect[T = Error[?]]` means the payload is ANY sort, so `Error(String)` is a legal instantiation, just the one no handler can read.

STEP 1 — CODEGEN (the blocker, MEASURED). `Error[P]` maps TWO different ways and only one is right:
  * an effects clause → `Result<_, P>`, wrapper STRIPPED (rust.rs:1901; the delivered `KB.loaded` / `effects Error[LoadFailed]` precedent, 027.4);
  * a TYPE-ARGUMENT slot (`E = Error[P]` inside `Stream[T = …, E = …]`) → `Error<P>`, wrapper KEPT.
Built it to see: the generator emitted `Result<Box<dyn Stream<Solution, Error<ResolveStreamFailure>>>, ResolveStreamFailure>` — the Err position right, the stream's E wrong, and `pub struct Error(pub String)` takes no generics, so anthill-stl does not compile. THE FIX is to make the type-argument slot follow the rule the effects clause already follows: an `Error[P]` effect label strips to `P`. NOT the alternative of making Rust `Error` generic — that leaves `execute`'s own Err (`P`) disagreeing with its stream's E (`Error<P>`) for one channel.

STEP 2 — THE PAYLOAD. A 4-variant enum, from a CENSUS of that face's six Error sites, not a guess: malformed_query (bridge.rs:317 'sort is not a sort reference', :368 'unsupported query variant'), unsupported_operation (:741 'Stream::find is unsupported'), stream_misused (:593 'stream already consumed', :657 'Stream::head on an empty solution stream'), evaluation_failure (:624, the fault channel). A 2-variant enum was considered and rejected: the other four sites would need a string catch-all, which puts back exactly the stringly-typed problem the enum removes. `detail` stays prose on the three CALLER-BUG variants — the variant is what a handler branches on, the text is for a human; only evaluation_failure is about the query's own execution and carries structure.

evaluation_failure(goals: List[T = Term], reason: String, at: Option[T = NodeOccurrence]). NOT a Solution variant, and the spec settles it: execute's own doc says undecidedness rides as the `undecided` DATA case and `E = Error` is 'reserved for GENUINE errors'. `undecided` says a goal HAS no answer (legitimate); this says a goal could not be ASKED. Adding `faulted` beside definite/undecided would claim a fault is a kind of ANSWER — the same category error as Delay faking an outcome.

`at` IS REACHABLE, measured with a probe at the fault site: the goal arrives as `Value::Node` carrying `SourceSpan { source: SourceId(81), span: 157..177 }`, and span.rs:90 `line_col` renders it. OPTIONAL because a σ-rebuilt goal arrives as `Value::Entity`, which has no span field — an absent location is honest, not missing. An OCCURRENCE rather than a rendered string, matching Solution.undecided's own doc ('inspect residual elements through the occurrence-aware reflect ops').

SCOPE NOTE: this changes `Stream<Solution, Error>` to `Stream<Solution, ResolveStreamFailure>` everywhere the reflect solution stream is threaded — the adapter, head_option, find, the test drain. Contained, not a one-line edit.

ACCEPTANCE: reflect.anthill declares the enum and execute's row names it; 'ResolveStreamFailure' is in anthill-stl/build.rs emit_only; the generated trait reads Stream<Solution, ResolveStreamFailure> and split_first returns Result<Option<…>, ResolveStreamFailure>; all six bridge sites construct a variant, none a string; a faulted query yields evaluation_failure with a Some(at) whose span resolves to the fixture's line; a CONTROL asserts a σ-rebuilt goal yields None rather than a zero span; cargo-test green via scripts/test.sh.

## Changes

### 2026-09-13T09:27:57Z — feedback — claude

DELIVERED against every acceptance row. Codegen: Error[P] in a type-argument slot strips to P in both mappers (an_error_label_in_a_type_argument_slot_strips_to_its_payload). reflect.anthill declares enum ResolveStreamFailure {malformed_query, unsupported_operation, stream_misused, evaluation_failure(goals, reason, at)}; execute's row and stream E name it; emit_only lists it; the generated trait reads Result<Box<dyn Stream<Solution, ResolveStreamFailure>>, ResolveStreamFailure>. All six bridge sites build a variant. ResolveError gains at: Option<Rc<NodeOccurrence>>, filled by the step loop from the goal being stepped (Value::Node only). a_faulted_query_takes_the_error_arm slices the fixture to 'PartialOrd.gt(?x, 1)' on line 6; the control a_fault_on_a_rebuilt_goal_has_no_location uses a host conjunction unify(?x,'a'), gt(?x,1) whose goal was PROBED as Value::Entity -> at None.

BEYOND THE TICKET, from /code-review: take_n and exists now report the fault too (they pumped the resolver without checking errors); fault dedup stays keyed on the MESSAGE alone, and a later located copy fills an unlocated entry (keying on location too printed duplicate warnings for mixed carriers); goals is documented as the reporting pull's residual, which can be empty when the fault came from an earlier branch that yielded nothing.

THE RIPPLE, measured: a bare 'effects Error' row does NOT admit Error[ResolveStreamFailure], so every caller must name the payload. anthill-todo main.anthill needed it on ten operations, up to main (query_id_set, collect_id_set, walk_solutions, cmd_next, cmd_list, cmd_list_plain, cmd_list_tagged, undated_gate, dispatch, main) and three core fixtures (kb_query, wi182, wi531).

LEFT OPEN, not fixed: the INTERPRETER face never produces this payload - kb_execute maps a lowering failure to EvalError::Internal and stream_split_first's PumpResolver ignores rest.errors(), so a faulted goal still arrives there as an undecided row. The declaration describes the host bridge exactly and the interpreter face as an upper bound. The codegen strip keys on the short name 'Error', like the file's List/Option mappings.

