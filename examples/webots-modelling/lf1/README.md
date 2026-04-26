# lf1 — leader-follower controller in anthill

This example models a two-drone leader-follower flight pattern as an anthill specification, with the goal of generating a Webots C++ controller from the spec and proving safety properties (min/max separation).

## Reference implementation

Existing C++ controller this example replaces:
`/Users/rssh/packages/cyberbotics/webots/projects/ips-drones/multirotor_leader_follower1/`

- `worlds/multirotor_leader_follower1.wbt` — two Mavic 2 Pro drones (leader + follower)
- `controllers/leader_patrol/leader_patrol.cpp` — leader patrols 4 corners of a 40×40 square at altitude 12, broadcasts pose via `Emitter` (channel "radio")
- `controllers/mavic_follower/mavic_follower.cpp` — follower receives leader pose via `Receiver`, holds a constant offset (default `--offset=-4,0,0`) in the leader's body frame
- `common/MavicBase.cpp/.hpp` — shared base class wrapping the Mavic 2 Pro hardware (GPS, Gyro, IMU, 4 motors) with a fixed-gain stabilization inner loop. Uses C++20 (`<numbers>`, `string_view::starts_with`).

The whole reference is ~275 lines. The anthill spec replaces the *outer loop* (the controller logic in `computeControls`); the inner stabilization loop is carried verbatim as a `Quoted("cpp", ...)` block — see `leader_follower.anthill` and the PUNCHLIST entry for `mavic_base.{cpp,hpp}`. The generated `LeaderController` and `FollowerController` are C++ subclasses of the (Quoted) `MavicBase`, with their `computeControls()` overrides emitted from the anthill spec.

## Goals

1. **Generate the leader and follower C++ controllers from anthill specs.** Compile and run them in Webots. Same world file. Same observable behavior.
2. **Prove safety properties** about the leader-follower protocol: under stated assumptions, the inter-drone distance stays in a bounded range — never below `d_min` (no collision) and never above `d_max` (formation maintained).

## Status

**Codegen track: end-to-end through clang.** Running `./build.sh`
produces a self-contained Webots project tree at `./build/` whose
generated headers + hand-authored shims compile cleanly under
`clang++ -std=c++17 -fsyntax-only -Wall -Wextra`. To actually fly
the drones in Webots, link the controllers against `libController`
via `make` (see "Building" below) and open the generated
`multirotor_leader_follower1.wbt`.

**Proof track: still partial.** The discrete-step safety obligation
in `safety.anthill` waits on arithmetic-aware tactics in the SLD
evaluator (proposal 026 follow-up).

## Files

- `leader_follower.anthill` — sorts + operations for `Pose`,
  `Controls`, waypoint state, and the two controllers. Real bodies
  for all five operations using anthill expression bodies.
- `realization.anthill` — `fact Generated(...)` declarations
  pointing the codegen at each controller binary's intended output
  path.
- `safety.anthill` — assumptions and safety properties (constraints).
- `world.anthill` — environmental assumptions referenced by the
  proof.
- `webots/*.anthill` — project-local bindings for the Webots C++ API
  (Robot, GPS, Gyro, InertialUnit, Motor, Emitter, Receiver) plus
  the per-binding `fact Implementation(...)` carrier mappings.
- `cpp/` — hand-authored C++ that's not modelled in anthill:
  - `mavic_base.{cpp,hpp}` — Mavic2Pro inner stabilisation loop,
    copied verbatim from the Cyberbotics reference. Uses raw
    `webots::*` headers; no anthill awareness.
  - `LeaderController_main.cpp` / `FollowerController_main.cpp` —
    thin shims that subclass `MavicBase`, marshal between
    `MavicBase::{Pose,Controls}` and the anthill-generated value
    types, and dispatch each tick through the anthill traits
    classes.
- `worlds/multirotor_leader_follower1.wbt` — Webots world (carried
  from the reference, with the two `controller "..."` slots updated
  to match our generated folder names).
- `build.sh` — one-shot project scaffold runner. Produces
  `./build/` (gitignored).
- `PUNCHLIST.md` — remaining work.

## Building

```bash
./build.sh                        # scaffolds ./build/ from .anthill specs + cpp/ + worlds/

export WEBOTS_HOME=/Applications/Webots.app/Contents   # macOS
# or:  WEBOTS_HOME=/usr/local/webots                   # Linux

(cd build/controllers/LeaderController   && make)
(cd build/controllers/FollowerController && make)

# Open build/worlds/multirotor_leader_follower1.wbt in Webots.
```

`build.sh` runs `anthill codegen cpp-project` against the .anthill
specs in this directory; the output dir is `./build/` by default,
overridable via `OUT_DIR=… ./build.sh`. Re-run it whenever any
.anthill file changes — `make` then rebuilds only the affected
controllers.

The two follower drones share one binary (`FollowerController`);
the world file passes per-instance offsets via
`controllerArgs ["--offset=…"]`.

## Dependency chain

To make goal (1) — codegen — work end-to-end, in build order:

1. **`examples/webots-modelling/lf1/webots/`** — hand-authored anthill sorts mirroring the Webots C++ API (`Robot`, `GPS`, `Gyro`, `InertialUnit`, `Motor`, `Emitter`, `Receiver`, plus `Vec3`/`Pose` value types and a small math vocabulary). `Implementation` and `NamespaceMapping` facts point at `webots::*` C++ classes. Lives in the example for now, not in `stdlib/`. The same convention applies to other consumer-specific bindings (blefusku's proto, ArduPilot's Lua sandbox, etc.). When a second consumer of the same vendor API appears, the mapping can be lifted into a shared location (sibling crate or a `bindings/webots/` directory) — but only at that point, not preemptively. **Not started.**
2. **`anthill-cpp-gen` crate** — KB-driven anthill → C++ emitter, profile `cpp20-stl` (lf1 uses `-std=c++20`, see profile note below). See `docs/cpp-forward-mapping.md` and `docs/proposals/029-rust-mapping-split.md`. **Not started.**
3. **Project layout in this directory** — eventually will mirror the reference: `worlds/lf1.wbt` (or symlink to the reference), `controllers/leader/` and `controllers/follower/` containing generated `.cpp`/`.hpp` plus a Makefile that adds `-std=c++20` to `CFLAGS`. **Not started.**

For goal (2) — proof — additionally:

4. **Discrete-step proof support in anthill.** The continuous-time invariance property is approximated as: given a per-step distance change bound `Δd_max` derivable from velocity bounds and control period, prove the inductive step `d_min ≤ d_k ≤ d_max ⇒ d_min ≤ d_{k+1} ≤ d_max`. Requires arithmetic-aware reasoning in the SLD evaluator, which proposal 026 (expression evaluator) is the foundation for. **Partially in place — proposal 026 M1–M5 landed (commit `6939272`); arithmetic-aware proof tactics for invariants are a separate open work item.**
5. **(Optional later) SMT bridge.** Export proof obligations as SMT-LIB to Z3 / dReal for the parts the native reasoner cannot discharge. **Not started; not required for v1.**

## Profile choice — `cpp20-stl`

Webots's user-controller toolchain doesn't fix a C++ standard via the stock `Makefile.include` — `-std=c++NN` is up to the project's own `CFLAGS`. The reference controller already requires C++20 (uses `<numbers>` and `std::string_view::starts_with`), so this example targets the `cpp20-stl` profile from `docs/cpp-forward-mapping.md` (concepts + native `requires` clauses on top of the traits-class idiom). The default `cpp17-stl` profile remains the conservative choice for projects that can't or don't want to bump the standard.

## Proof scope (v1)

Continuous-time control-theoretic invariance is **out of scope**. The v1 target is the *discrete-step* version of the safety property:

> Given:
> - per-step max distance change `Δd_max` (derived from velocity bounds + control period + comm delay)
> - initial separation `d_0 ∈ [d_min + Δd_max, d_max - Δd_max]`
>
> Prove:
> - for all `k ≥ 0`: `d_min ≤ d_k ≤ d_max`

This is an inductive invariant the SLD reasoner can in principle discharge once arithmetic facts are wired through the expression evaluator. The continuous-time gap (between sample steps the drone is still moving) is treated as a modeling assumption captured in `Δd_max`, not a separate proof obligation. A full hybrid-systems proof is a longer-term project, possibly via SMT export.

## Sequenced work plan

Roughly, in dependency order:

1. Author `examples/webots-modelling/lf1/webots/` — start with `Robot`, `GPS`, `InertialUnit`, `Gyro`, `Motor` for the inner loop; then `Emitter`, `Receiver` for the leader-follower comm. Hand-write a one-page conversion checklist alongside.
2. Build `anthill-cpp-gen` skeleton (proposal 029 → `cpp20-stl` profile). Get it generating compilable empty trait specializations from a tiny test spec first.
3. Flesh out `leader_follower.anthill` with operation bodies expressible in the proposal-026 expression sublanguage (or `Quoted("cpp", ...)` blocks for math-heavy bits we can't yet express).
4. Generate, compile, and run the leader controller in Webots. Confirm it patrols. Then the follower. Confirm formation holds.
5. Discharge the safety obligations in `safety.anthill` by adding arithmetic tactics to the SLD reasoner (or via SMT export).

Items 1–4 are the codegen track. Item 5 is the proof track and can run in parallel once the spec is stable.
