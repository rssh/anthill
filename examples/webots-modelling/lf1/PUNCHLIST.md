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
- [ ] **Math vocabulary (minimal)** — scalar math (`atan2`, `hypot`, `log10`, `fmod`, `abs`, `cos`, `sin`, `pi`) needed by the outer loop. Live on `anthill.prelude.Float` for now. Each maps to `<cmath>` / `<numbers>` via `Implementation` facts.
- [ ] **Vec3 (project-local)** — defined in `leader_follower.anthill`. Lift to a shared math library once **WI-081** is in flight.
- [ ] **`anthill-cpp-gen` crate** — KB-driven anthill → C++ emitter, profile `cpp20-stl`. Per `docs/proposals/029-rust-mapping-split.md`, `docs/cpp-forward-mapping.md`.
  - [x] crate scaffolded at `rustland/anthill-cpp-gen/`, in workspace
  - [x] **entity → struct** with primitive type lowering (Int → int64_t, Float → double, Bool → bool, String → std::string, Unit → void); declaration-order field emission; `sort_ref` unwrapping. End-to-end smoke test against lf1's webots/types.anthill emitting Vec3 and EulerAngles correctly.
  - [ ] traits-class emission for sorts with operations
  - [ ] `std::variant` emission for sorts with constructors
  - [ ] effect lowering (`tl::expected` for `Error`, mutable references for `Modify`)
  - [ ] `Implementation` / `NamespaceMapping` / `CarrierBinding` consumption (fact-driven, replaces the hardcoded primitive table)
  - [ ] parameterized type lowering (`List[T = X]` → `std::vector<X>`, `Option[T = X]` → `std::optional<X>`)
  - [ ] namespace wrapping (`namespace foo::bar { ... }`)
  - [ ] runtime header (`anthill_runtime.hpp`) with `is_satisfied` detection trait
- [ ] **Operation bodies in anthill** — fill out `leader_follower.anthill` with bodies expressible in the proposal-026 expression sublanguage. For the trig-heavy parts (`atan2`, `log10`-based pitch shaping) either lower via the math vocabulary or emit `Quoted("cpp", "...")` blocks until expression coverage is complete.
- [ ] **Project layout** here — mirror the reference:
  - [ ] `worlds/` (symlink or copy of `multirotor_leader_follower1.wbt`)
  - [ ] `mavic_base.cpp` / `mavic_base.hpp` — verbatim copies of the reference's `common/MavicBase.{cpp,hpp}`, carried as the Quoted("cpp") block referenced by `leader_follower.anthill`
  - [ ] `controllers/leader/` and `controllers/follower/` containing generated `.cpp/.hpp` + Makefile with `CFLAGS += -std=c++20`
- [ ] **End-to-end run** — generate, compile, launch in Webots, confirm the formation flies as the reference does.

## Proof track

- [ ] **Arithmetic-aware tactic in the SLD evaluator.** Build on proposal 026 (already landed M1–M5, commit `6939272`) so `?d_min <= ?d <= ?d_max`-style guards over `Float` literals can actually be discharged. Smallest viable form: linear arithmetic over `Float` constants and additions.
- [ ] **State `KinematicAssumptions` and `DistanceBounds` as facts** for the lf1 protocol with concrete numbers.
- [ ] **Discharge `inductive_invariant`** under those facts. This is the v1 proof target.
- [ ] **Optional: SMT export pass** (`anthill-smt-gen` or similar) for parts the native tactic can't reach. Not required for v1.
- [ ] **Optional: continuous-time gap.** Document the per-step modeling assumption rigorously, or eventually export to a hybrid-systems tool. Long-term.

## Settled decisions

- **Mavic2Pro inner stabilization loop is carried as a Quoted("cpp", ...) block**, not modeled in anthill. The codegen pipeline emits sibling sources `mavic_base.cpp` / `mavic_base.hpp` verbatim into the generated project; LeaderController and FollowerController become C++ subclasses of `MavicBase` whose `computeControls()` override is the codegen target. Rationale: well-trodden PID math, no value to modeling, the safety argument lives on the outer loop. Tracked: **WI-082** (kernel extension to let `Quoted` reference an external source file — until that lands, project layout convention carries the files).
- **`Vec3` is project-local in lf1 for now.** Defined in `leader_follower.anthill` (or the project's webots bindings, when authored). A shared math vocabulary covering Vec3 + quaternion + 3D rotations is a follow-up: tracked as **WI-081**. Lift Vec3 there once that landing is in flight; until then duplication is acceptable.
- **Emitter/Receiver are modeled directly with their signal-level fields exposed.** A `LinkParameters` fact carries world-file-level properties (range, signal speed, baud rate, byte size, packet size); the safety proof's `comm_delay_max` is *derived* from these via a rule rather than asserted (see `safety.anthill`). Propagation delay is included in the derivation even though it's typically negligible at these scales — keeping it makes the bound rigorous and self-documenting.
- **Sensors and channels are modeled webot-specifically, not abstractly.** Names mirror the C++ API: `webots.GPS`, `webots.InertialUnit`, `webots.Gyro`, `webots.Emitter`, `webots.Receiver`. No abstract `Sensor[T]` / `Channel[T]` layer for now. Rationale: the priority is API generation (codegen end-to-end), and abstracting before a second consumer (blefusku) tells us what the abstraction has to cover would be premature. Lift path when blefusku lands: introduce abstract `Channel[T]` / sensor sorts, have both webots and blefusku-side concrete sorts `provides` them, retrofit the safety proof to quantify over the abstract layer. Same "lift on second consumer" convention as for the bindings location.
- **Borrow semantics are elided.** `Robot::getGPS` returns `webots::GPS *` — semantically a non-owning, non-null, controller-lifetime borrow. Anthill currently has no language-level borrow / lifetime / nullability annotations, so the spec models it as a plain `-> GPS` return and lets the `CarrierBinding(host_type: "webots::GPS *")` carry the pointer info to codegen. The well-formed-world-file assumption (every named device exists) is implicit. Tracked as **WI-086** (anthill.realization.directMemory sublibrary with `Borrowed[T]` and friends). Until that lands, retrofit when the work item is in flight.

## Open decisions

- (none currently — the abstract `Channel[T = Pose]` question is deferred until a second consumer of inter-actor messaging appears; for lf1 we model `Emitter`/`Receiver` directly with their signal-level fields exposed for the safety proof)
