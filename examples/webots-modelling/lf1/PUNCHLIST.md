# lf1 punchlist

Concrete tasks to take this scaffold to a runnable + provable example. Roughly in dependency order.

## Codegen track

- [x] **`examples/webots-modelling/lf1/webots/`** — hand-author anthill sorts mirroring the Webots C++ API. Project-local, not in stdlib (webots is vendor-specific). Minimum subset for lf1:
  - [x] `Robot` (base) — `step`, `get_basic_time_step`, device getters
  - [x] `GPS` — `enable`, `get_values` returning a 3-vector
  - [x] `InertialUnit` — `enable`, `get_roll_pitch_yaw` returning a 3-vector
  - [x] `Gyro` — `enable`, `get_values` returning a 3-vector
  - [x] `Motor` — `set_position`, `set_velocity`
  - [x] `Emitter` — `send(bytes)`, `set_channel`/`get_channel`, `set_range`/`get_range`. World-file properties (`baud_rate`, `byte_size`, `signal_speed`, `aperture`, `type`) live in a `LinkParameters` fact in `safety.anthill` for the proof's `comm_delay_max` derivation, not on the binding sort.
  - [x] `Receiver` — `enable`, `get_queue_length`, `get_data_size`, `get_data`, `next_packet`, `get_signal_strength`, `get_emitter_direction`, `set_channel`/`get_channel`
  - [x] `Vec3` shared value type (`webots/types.anthill`)
  - [x] `NamespaceMapping` fact pointing `anthill.examples.lf1.webots` → `webots::`
  - [x] one `Implementation{...}` fact per sort pointing at the C++ class (`webots/realization.anthill`)
  - [x] `CONVERSION.md` checklist so the rest of the API can be batched out later
  - [x] **Validate parsing**: all webots/*.anthill files load cleanly through `anthill-core` (117 facts; only unresolved-name warnings for missing imports, no parse errors). Confirmed: constructor-form facts (`fact Implementation(target: ..., carrier: [...])`) parse, multiple top-level facts parse, multi-line imports parse, list literals as fact arg values parse. Only real fix needed during validation was the `effects` syntax (`Modify[self]` — bracket form for the type-level target binding, `Modify(self)` is the term-level form).
- [x] **Math vocabulary (minimal)** — `sqrt`, `hypot`, `fmod`, `pow`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `exp`, `log`, `log10`, `log2`, plus `pi`, `e`, `tau` constants on `anthill.prelude.Float`. cpp-gen lowers them to `std::*` and adds `<cmath>` automatically.
- [x] **Vec3 / EulerAngles lifted to shared library** — `anthill.geometry` (stdlib). `webots/types.anthill` removed; both lf1 controllers and webots binding sorts import from the shared namespace. WI-081's quaternion + 3D rotation operations are the next addition.
- [ ] **List / IndexedSeq vocabulary** — `IndexedSeq.{nth, length}` on a typeclass orthogonal to Collection/Iteration; List satisfies it. cpp-gen lowers to container-agnostic `xs.size()` / bounds-checked `xs[i]`. Done; future: sub-spec `RandomAccess` for O(1) guarantees.
- [x] **`anthill-cpp-gen` crate** — KB-driven anthill → C++ emitter, profile `cpp20-stl`. Per `docs/proposals/029-rust-mapping-split.md`, `docs/cpp-forward-mapping.md`.
  - [x] crate scaffolded at `rustland/anthill-cpp-gen/`, in workspace
  - [x] **entity → struct** with primitive type lowering (Int64 → int64_t, Float → double, Bool → bool, String → std::string, Unit → void); declaration-order field emission; `sort_ref` unwrapping. End-to-end smoke test against lf1's webots/types.anthill emitting Vec3 and EulerAngles correctly.
  - [x] traits-class emission for sorts with operations (declaration + body forms; topo-sorted alongside data types)
  - [x] `std::variant` emission for sorts with constructors (nullary and field-carrying, generic and non-generic)
  - [x] effect lowering — `Error` → `tl::expected<T, std::string>`; `Error.raise(e)` → `tl::make_unexpected(e)`. (`Modify` mutable-ref lowering still pending.)
  - [x] `Implementation` / `NamespaceMapping` / `CarrierBinding` consumption (fact-driven; replaces the hardcoded primitive table)
  - [x] parameterized type lowering (`List[T = X]` → `std::vector<X>`, `Option[T = X]` → `std::optional<X>`, generic sorts via slice 1 of generic-sort support)
  - [x] namespace wrapping (`namespace foo::bar { ... }` with topo-sorted entities and traits classes inside)
  - [x] **expression body lowering** — Phases A–F: literals, parameter refs, function calls, if-then-else, field access, let chains, lambdas, match (with value-binding patterns), constructor literals, list/tuple/set literals, typeclass operator dispatch (`add` → `+`), Error-effect return wrapping, wildcard `let _ =` discard
  - [x] **generic sorts** — slices 1+2: `template<typename T>` for sorts with `sort T = ?`, generic sum sorts (`template<typename T> using Tree = std::variant<...>`), keyword-clash canonicalisation
  - [ ] runtime header (`anthill_runtime.hpp`) with `is_satisfied` detection trait
- [x] **Operation bodies in anthill** — `leader_follower.anthill` has real bodies for all 5 controller operations: `update_leader_pose`, `desired_position` (full 2-D yaw rotation), `advance_waypoint` (precision-based via `IndexedSeq.nth` + `hypot`), and both `compute_controls` (atan2 yaw + log10-shaped pitch).
- [ ] **Project layout** here — mirror the reference:
  - [ ] `worlds/` (symlink or copy of `multirotor_leader_follower1.wbt`)
  - [ ] `mavic_base.cpp` / `mavic_base.hpp` — verbatim copies of the reference's `common/MavicBase.{cpp,hpp}`, carried as the Quoted("cpp") block referenced by `leader_follower.anthill`
  - [ ] `controllers/leader/` and `controllers/follower/` containing generated `.cpp/.hpp` + Makefile with `CFLAGS += -std=c++20`
- [ ] **End-to-end run** — generate, compile, launch in Webots, confirm the formation flies as the reference does.

## Proof track

### Landed (kernel-checked end-to-end via proposal 030)

- [x] **`anthill-smt-gen` crate** — KB → SMT-LIB 2.6 emitter; Z3 round-trip for linear-real-arithmetic obligations. Commits `14a0f54`, `2bd2d9d`, `2fc4a37`, `3b616b7`.
- [x] **State `KinematicAssumptions`, `LinkParameters`, `GpsErrorBound`, `DistanceBounds`** as facts with the lf1 RTK numbers (ε = 0.1 m, v_max = 8 m/s, T_c = 0.032 s, d ∈ [1, 20] m).
- [x] **Per-step inductive obligations** (LRA): `lower_violation` / `upper_violation`, `base_lower_violation` / `base_upper_violation` (gps); `lower_violation_transponder`, `bounded_excursion_lower/upper_violation_transponder` (transponder). All discharge `unsat`.
- [x] **Reachability lift** ∀k. d_min ≤ d_k ≤ d_max — implemented via induction-tactic discharge of `reachability_band`. The rule now carries an explicit `-:` conclusion (post-030 cleanup) so the universal claim is first-class in the registry; the induction meta-tactic dispatches the four base × step sub-queries; β.3's MetaCompose check verifies recursively. The Φ-prerequisite (proposal 025 Phase 2.6b nested-implication resolution) is no longer needed because proposal 030's witness machinery factors out the soundness gate.
- [x] **Per-flight refutation** (QF_NRA): `safety_min_distance` / `safety_max_distance` (gps), `safety_no_collision_transponder` / `safety_bounded_excursion_transponder` (transponder). Each chases body through `reachable_real` → `real_pose_at` (initial-geometry facts) → `position_distance` (nonlinear) and refutes the violation hypothesis at the lf1 launch geometry.
- [x] **Ranking-function discharge** of `PostArmedExcursionBound.max_ticks = 6` via `post_armed_excursion_bound` proof block (LIA, ranking tactic). R = −upc ∈ [0, 6] strictly decreases each bad tick.
- [x] **`anthill check` end-to-end audit**: prove writes sidecar witnesses + content-addressed blobs (XDG cache); check replays SmtDischarge witnesses, recurses through MetaCompose witnesses, re-reads source declarations for ScopeAxioms. Lf1 reports 43/43 pass (11 user proofs + 1 Specialization + 31 auto-registered ScopeAxioms; 0 trusted, 0 failed).

### Remaining gaps (load-bearing modeling assumptions, NOT discharged by Z3)

These are the axiomatic content the lf1 proof rests on. Each is documented inline in `safety_common.anthill` (§Predicate status); listed here for visibility:

1. **Step-distance bound** `|distance_at_step(k+1) − distance_at_step(k)| ≤ δ`. Inlined as the body clause `step_distance_bound(?delta), lte(abs(?step), ?delta)` in every per-step violation rule. *Derivable in principle* from `real_pose_at`'s transition rule + KinematicAssumptions velocity envelope + triangle inequality on `position_distance`, but the derivation is a hybrid-systems claim outside Z3's QF_LRA / QF_NRA scope. Future: dReal or KeYmaera X discharge; until then, the proof is conditional on KinematicAssumptions holding.
2. **`KinematicAssumptions` inner-loop envelope**. The Mavic2Pro PID + motor mixing (carried verbatim as `mavic_base.{cpp,hpp}`) is *assumed* to keep |v_drone| ≤ v_max. If the real inner loop violates this in flight, the whole proof says nothing. Empirically validated per Webots run; no symbolic discharge planned.
3. **`gps_drift_axiom`** / `transponder_step_distance_bound`'s measurement-noise term. Sensor error model; treated as an axiom. The 0.1 m / 0.15 m numbers come from the GPS module's spec / transponder calibration; not derivable from kernel rules.
4. **`distance_at_step(k, d) ↔ position_distance(real_pose_at(k, Leader), real_pose_at(k, Follower))` bridge**. Definitional rule but Z3 doesn't unfold it during the inductive discharge — the proof reasons at the scalar `d` level. Conceptually the bridge bundles assumptions 1–3.
5. **`PostArmedExcursionBound.max_ticks = 6` literal** in source. The ranking-tactic proof witnesses that R ∈ [0, 6] is sound, but the literal `6` is plugged in as a fact rather than auto-derived from the ranking-tactic outcome. Tracked: the ranking tactic accepting a `pessimistic_bound: N` argument that emits a `RankingProof(name, measure, max_ticks)` fact directly.

### Future infrastructure improvements

- [ ] **`by z3(upper: <bound>)` strategy argument** so the step-distance bound check (`δ ≤ 2.0 m`) can move from `rustland/anthill-smt-gen/tests/lf1_real_spec_test.rs` into an inline `proof` block.
- [ ] **Counterexample extraction** when Z3 reports `sat` — reify the model back through the KB into anthill terms so users see the witness directly. Today the CLI prints the raw model in `--verbose` mode.
- [ ] **Continuous-time gap.** Document the per-step modeling assumption rigorously, or export to a hybrid-systems tool (dReal / KeYmaera X) to discharge gap #1 mechanically.
- [ ] **Mark `gps_drift_axiom` / `transponder_step_distance_bound` measurement-noise terms as explicit `TrustedAxiom`-witnessed ProofRecords** so `anthill check --report-trust` surfaces them. Today they're inline body clauses; promoting them to citable lemmas with proof blocks of `by trust("sensor spec; …")` form (when that tactic lands) would make the trust surface auditable.

## Settled decisions

- **Mavic2Pro inner stabilization loop is carried as a Quoted("cpp", ...) block**, not modeled in anthill. The codegen pipeline emits sibling sources `mavic_base.cpp` / `mavic_base.hpp` verbatim into the generated project; LeaderController and FollowerController become C++ subclasses of `MavicBase` whose `computeControls()` override is the codegen target. Rationale: well-trodden PID math, no value to modeling, the safety argument lives on the outer loop. Tracked: **WI-082** (kernel extension to let `Quoted` reference an external source file — until that lands, project layout convention carries the files).
- **`Vec3` is project-local in lf1 for now.** Defined in `leader_follower.anthill` (or the project's webots bindings, when authored). A shared math vocabulary covering Vec3 + quaternion + 3D rotations is a follow-up: tracked as **WI-081**. Lift Vec3 there once that landing is in flight; until then duplication is acceptable.
- **Emitter/Receiver are modeled directly with their signal-level fields exposed.** A `LinkParameters` fact carries world-file-level properties (range, signal speed, baud rate, byte size, packet size); the safety proof's `comm_delay_max` is *derived* from these via a rule rather than asserted (see `safety.anthill`). Propagation delay is included in the derivation even though it's typically negligible at these scales — keeping it makes the bound rigorous and self-documenting.
- **Sensors and channels are modeled webot-specifically, not abstractly.** Names mirror the C++ API: `webots.GPS`, `webots.InertialUnit`, `webots.Gyro`, `webots.Emitter`, `webots.Receiver`. No abstract `Sensor[T]` / `Channel[T]` layer for now. Rationale: the priority is API generation (codegen end-to-end), and abstracting before a second consumer (blefusku) tells us what the abstraction has to cover would be premature. Lift path when blefusku lands: introduce abstract `Channel[T]` / sensor sorts, have both webots and blefusku-side concrete sorts `provides` them, retrofit the safety proof to quantify over the abstract layer. Same "lift on second consumer" convention as for the bindings location.
- **Borrow semantics are elided.** `Robot::getGPS` returns `webots::GPS *` — semantically a non-owning, non-null, controller-lifetime borrow. Anthill currently has no language-level borrow / lifetime / nullability annotations, so the spec models it as a plain `-> GPS` return and lets the `CarrierBinding(host_type: "webots::GPS *")` carry the pointer info to codegen. The well-formed-world-file assumption (every named device exists) is implicit. Tracked as **WI-086** (anthill.realization.directMemory sublibrary with `Borrowed[T]` and friends). Until that lands, retrofit when the work item is in flight.

## Open decisions

- (none currently — the abstract `Channel[T = Pose]` question is deferred until a second consumer of inter-actor messaging appears; for lf1 we model `Emitter`/`Receiver` directly with their signal-level fields exposed for the safety proof)
