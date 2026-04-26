// MavicBase — Mavic2Pro inner stabilisation loop scaffold.
//
// Hand-authored, anthill-independent (flavour A in the project's
// realisation taxonomy). Subclasses of MavicBase live in the
// generated controller folders (`*_main.cpp`) and override
// `compute_controls(...)` with calls into the anthill-generated
// traits classes for the outer loop.
//
// THIS IS A STUB. The real Mavic2Pro inner loop (fixed-gain PID +
// motor mixing) ships verbatim from the Cyberbotics reference at
// `webots/projects/ips-drones/multirotor_leader_follower1/common/`.
// The stub here exists so the project compiles for syntax checks
// before the real PID is dropped in.

#pragma once

#include "anthill_geometry.hpp"   // Vec3, EulerAngles
#include "lf1.hpp"                // Pose, Controls (anthill-generated)

namespace anthill::lf1::runtime {

using anthill::examples::lf1::Controls;
using anthill::examples::lf1::Pose;

class MavicBase {
public:
    explicit MavicBase(int basic_time_step_ms);
    virtual ~MavicBase() = default;

    // Runs the simulation loop until Webots tells us to stop.
    // Calls step() per tick → reads sensors → synthesises Pose →
    // calls compute_controls(pose) → sends the resulting Controls
    // to the motors.
    void run();

protected:
    // Override in subclasses to compute outer-loop controls from a
    // pose. The default implementation hovers in place.
    virtual Controls compute_controls(const Pose& pose) = 0;

    // Hook called once per tick before `compute_controls`. Default
    // is a no-op; the FollowerController override drains the
    // receiver queue here.
    virtual void pre_step() {}

    int basic_time_step() const { return basic_time_step_ms_; }

private:
    int basic_time_step_ms_;
};

}  // namespace anthill::lf1::runtime
